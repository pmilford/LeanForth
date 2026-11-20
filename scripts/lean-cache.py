#!/usr/bin/env python3
"""A caching stand-in for pinned Lean and its exporter in the local test suites.

Usage: the Makefile runs its recipes with LEAN set to this script and
LEANEXPORT to scripts/leanexport-cache.py (which runs this script with
--leanexport first), unless LEAN_CACHE=0; CI always runs with LEAN_CACHE=0.
Each takes the real tool's own arguments and environment, and these:

  LEANFORTH_LEAN            the real Lean binary (required); leanexport is
                            the one in the same toolchain's bin folder
  LEANFORTH_LEAN_CACHE      1 (use the cache), 0 (always run the tool, store
                            nothing) or verify (always run the tool, store
                            what is missing, and fail with status 125 when a
                            stored entry's status or output differs from
                            what the tool did; a differing .olean is only
                            logged, as "verified olean-differs")
  LEANFORTH_LEAN_CACHE_DIR  the cache folder (created when missing)
  LEANFORTH_LEAN_CACHE_LOG  optional: a file to which every call appends a
                            line "hit|miss|verified|differs|run REASON WHAT"

Lean is deterministic in what the tests read: the same toolchain, given the
same source text, options, LEAN_* environment and imported modules, prints
the same messages and exits with the same status; leanexport, given the
same arguments and modules, writes the same export. The .olean it writes is
not always the same bytes (VARYING_OLEAN): a replayed .olean is one Lean
wrote for the same inputs, and every call that imports it is keyed by the
bytes replayed. This script caches
two kinds of call only. For Lean, `lean [-DOPTION=VALUE]... [-o OUT.olean]
[--run] FILE.lean` with nothing after the file; for leanexport, any call.
The key is the SHA-256 of everything such a call reads:

  - the toolchain: SHA-256 of the lean binary and of the shared libraries
    beside it, `lean --githash`, and the name and size of every file of its
    library folder (recomputed whenever the binary, a shared library or the
    library folder itself changes on disk);
  - Lean: the options, --run and whether -o is given, in order; the source
    file's text; and the main module's name as Lean 4.35 derives it, from the
    source's path relative to the working folder (`_stdin` when the source
    lies outside it). Lean echoes the path as given in its messages: that
    spelling, the -o path and the LEAN_PATH folders are replaced by
    placeholders when stored and by the current ones on replay;
  - leanexport: its arguments, in order;
  - every LEAN_PATH folder outside the toolchain: each file's relative path
    and SHA-256 (the .olean files compiled earlier in the same test);
  - every other LEAN_* environment variable but the Makefile's own
    (LEAN_CACHE, LEAN_CACHE_DIR, LEAN_BINARY: NOT_READ_BY_LEAN);
  - whether stdout and stderr are the same file (then they are captured as
    one stream, in the tool's own order).

An entry holds the exit status, the output and the .olean written. A hit
replays them: the same bytes on stdout and stderr, the same file at the -o
path, the same exit status. Everything else execs the real tool unchanged:
--version, --githash, --print-prefix, --stdin, --run with program
arguments, a missing source, a source whose text names an IO input (files,
stdin, environment, processes, clocks, random numbers: IO_INPUTS), and any
call that imports an .olean from LEAN_PATH that this script did not see
compiled by a cacheable call (so an IO input cannot hide in an imported
module). Only exit statuses 0 and 1 are stored; a run killed by a signal,
or whose output reports exhausted memory or stack, is not. The tests that
read the output, the Forth side of every comparison included, always run;
only Lean's or the exporter's own run is skipped.

Entries are written to a temporary folder and renamed into place, so
several make jobs and worktrees can share one cache folder. This script
deletes nothing but its own temporary folders (a run killed part way may
leave one, named .tmp-*); to empty the cache, delete its folder by name.
"""
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

import lean_pin  # scripts/lean_pin.py, beside this script

FORMAT = 1
# Source text that may read anything besides the source, the options and the
# imported modules: such calls always run Lean.
IO_INPUTS = [b"IO.FS", b"readFile", b"readBinFile", b"FS.lines", b"getStdin", b"IO.getEnv",
             b"IO.Process", b"include_str", b"monoMsNow", b"monoNanosNow", b"IO.rand",
             b"getRandomBytes", b"currentDir", b"appPath", b"appDir", b"pathExists",
             b"readDir", b"FilePath.metadata", b"isDir"]
# Code Lean runs when it imports the module or elaborates the file, wherever it
# stands outside a string or comment (see code_only).
CODE_INPUTS = [b"initialize"]
STORED_STATUS = (0, 1)
RESOURCE_FAILURES = [b"out of memory", b"stack overflow", b"deep recursion"]
MAX_PATH_FILES, MAX_PATH_BYTES = 1000, 512 * 1024 * 1024
# Measured 2026-11-03: four compiles of tests/reference/stack-clamp.lean
# wrote four different .olean files (1,783,384 and 1,783,512 bytes) with the
# same messages and status; program-contracts.lean, composition.lean and
# checked-add.lean wrote the same bytes each time. A replayed .olean is
# therefore one that Lean wrote for these inputs, not necessarily the bytes
# a new run would write; what imports it is keyed by the bytes replayed.
VARYING_OLEAN = "tests/reference/stack-clamp.lean"
# LEAN_* variables that are no input of Lean: LEAN_PATH, keyed by its
# folders' contents, and the Makefile's own settings, which make passes on
# to the recipes when they are given on its command line.
NOT_READ_BY_LEAN = {"LEAN_PATH", "LEAN_CACHE", "LEAN_CACHE_DIR", "LEAN_BINARY"}
BLOCK = 1 << 20


class Uncacheable(Exception):
    """This call must run the real tool; the message says why."""


def code_only(text):
    """text with its comments, string literals and the characters '"' blanked.

    Conservative: a doubt keeps text rather than blanking it, and a file that
    ends inside a string or comment is returned whole, so that a word is only
    ever hidden when it certainly stands inside a string or a comment.
    """
    out, i, n = bytearray(), 0, len(text)
    while i < n:
        two = text[i:i + 2]
        if two == b"--":
            end = text.find(b"\n", i)
            i = n if end < 0 else end
        elif two == b"/-":
            depth, i = 1, i + 2
            while i < n and depth:
                pair = text[i:i + 2]
                depth += (pair == b"/-") - (pair == b"-/")
                i += 2 if pair in (b"/-", b"-/") else 1
            if depth:
                return text
        elif text[i:i + 3] in (b"'\"'", b"'\\\"") or text[i:i + 4] == b"'\\\"'":
            i += 3 if text[i + 1:i + 2] == b'"' else 4
        elif text[i:i + 1] == b'"' or text[i:i + 3] == b'r#"' or text[i:i + 2] == b'r"':
            hashes = 1 if text[i:i + 3] == b'r#"' else 0
            raw = text[i:i + 1] == b"r"
            i += 1 + raw + hashes
            closer = b'"' + b"#" * hashes
            while i < n and text[i:i + len(closer)] != closer:
                i += 2 if (text[i:i + 1] == b"\\" and not raw) else 1
            if i >= n:
                return text
            i += len(closer)
        else:
            out.append(text[i])
            i += 1
    return bytes(out)


def sha256_file(path):
    digest = hashlib.sha256()
    with open(path, "rb") as stream:
        for block in iter(lambda: stream.read(BLOCK), b""):
            digest.update(block)
    return digest.hexdigest()


def read(path):
    with open(path, "rb") as stream:
        return stream.read()


def write(path, data):
    with open(path, "wb") as stream:
        stream.write(data)


def log(what, reason, subject):
    path = os.environ.get("LEANFORTH_LEAN_CACHE_LOG")
    if path:
        with open(path, "a", encoding="utf-8") as stream:
            stream.write(f"{what} {reason.replace(' ', '_')} {subject}\n")


# The call and its key.

def parse(args):
    """A cacheable Lean call's (options, out, run, source); else Uncacheable."""
    options, out, run, source, index = [], None, False, None, 0
    while index < len(args):
        arg = args[index]
        if source is not None:
            raise Uncacheable("arguments after the source")
        if arg.startswith("-D") and "=" in arg:
            options.append(arg)
        elif arg == "-o" and out is None and index + 1 < len(args):
            index += 1
            out = args[index]
        elif arg == "--run" and not run:
            run = True
        elif arg.endswith(".lean") and not arg.startswith("-"):
            source = arg
        else:
            raise Uncacheable(f"argument {arg}")
        index += 1
    if source is None or not os.path.isfile(source):
        raise Uncacheable("no source file")
    if out is not None and not os.path.isdir(os.path.dirname(os.path.abspath(out))):
        raise Uncacheable("no folder for the .olean")
    return options, out, run, source


def module_path(source):
    """What Lean 4.35 names the main module after: the source's path relative
    to the working folder, or nothing (`_stdin`) when it lies outside it."""
    relative = os.path.relpath(os.path.abspath(source), os.getcwd())
    return None if relative == ".." or relative.startswith(".." + os.sep) else relative


def stat_key(path):
    info = os.stat(path)
    return [os.path.realpath(path), info.st_ino, info.st_size, info.st_mtime_ns]


def write_atomically(path, data):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    handle, temporary = tempfile.mkstemp(dir=os.path.dirname(path), prefix=".tmp-")
    with os.fdopen(handle, "wb") as stream:
        stream.write(data)
    os.replace(temporary, path)


def toolchain(lean, cache):
    """(fingerprint, prefix): SHA-256 naming the toolchain, memoized under the
    stat of the binary, its shared libraries and its library folder."""
    prefix = os.path.dirname(os.path.dirname(os.path.realpath(lean)))
    # One literal "lib/lean": scripts/changed-tests.py reads a bare "lib" as the repository's
    # lib folders, which would make every target that runs under the cache read src/lib.
    library = os.path.join(prefix, "lib/lean")
    shared = sorted(os.path.join(library, name) for name in os.listdir(library)
                    if name.endswith(".so"))
    memo_key = json.dumps([stat_key(lean), stat_key(library)] + [stat_key(p) for p in shared])
    memo = os.path.join(cache, "toolchains", hashlib.sha256(memo_key.encode()).hexdigest())
    try:
        return read(memo).decode("ascii").strip(), prefix
    except OSError:
        pass
    githash = subprocess.run([lean, "--githash"], capture_output=True, check=True).stdout
    files = []
    for root, folders, names in os.walk(library):
        folders.sort()
        files += [[os.path.relpath(os.path.join(root, name), library),
                   os.path.getsize(os.path.join(root, name))] for name in sorted(names)]
    whole = json.dumps({"lean": sha256_file(lean), "githash": githash.decode().strip(),
                        "shared": [[os.path.basename(p), sha256_file(p)] for p in shared],
                        "library": files})
    fingerprint = hashlib.sha256(whole.encode()).hexdigest()
    write_atomically(memo, fingerprint.encode())
    return fingerprint, prefix


def olean_mark(cache, digest):
    return os.path.join(cache, "oleans", digest[:2], digest)


def mark_olean(cache, path):
    """Remember an .olean written by a cacheable call."""
    mark = olean_mark(cache, sha256_file(path))
    if not os.path.exists(mark):
        write_atomically(mark, b"")


def search_path(prefix, cache):
    """LEAN_PATH's folders as key material; Uncacheable for an unmarked .olean."""
    entries = []
    for folder in os.environ.get("LEAN_PATH", "").split(os.pathsep):
        if not folder:
            continue
        real = os.path.realpath(folder)
        if real == prefix or real.startswith(prefix + os.sep):
            entries.append(["toolchain", os.path.relpath(real, prefix)])
            continue
        if not os.path.isdir(real):
            entries.append(["missing", folder])
            continue
        files, total = [], 0
        for root, folders, names in os.walk(real):
            folders.sort()
            for name in sorted(names):
                path = os.path.join(root, name)
                total += os.path.getsize(path)
                if len(files) >= MAX_PATH_FILES or total > MAX_PATH_BYTES:
                    raise Uncacheable(f"LEAN_PATH folder too large: {folder}")
                digest = sha256_file(path)
                if name.endswith(".olean") and not os.path.exists(olean_mark(cache, digest)):
                    raise Uncacheable(f"unmarked module {path}")
                files.append([os.path.relpath(path, real), digest])
        entries.append(["folder", files])
    return entries


def same_file(first, second):
    try:
        a, b = os.fstat(first), os.fstat(second)
    except OSError:
        return False
    return (a.st_dev, a.st_ino) == (b.st_dev, b.st_ino)


def common_key(fingerprint, prefix, cache):
    environment = sorted((k, v) for k, v in os.environ.items()
                         if k.startswith("LEAN_") and k not in NOT_READ_BY_LEAN)
    return {"format": FORMAT, "toolchain": fingerprint, "environment": environment,
            "lean_path": search_path(prefix, cache), "merged": same_file(1, 2)}


# Paths echoed in output.

def spellings(source, out):
    """Each path the tool may echo, by role: replaced when stored, restored on replay."""
    roles = []
    if source is not None:
        roles += [("source", source), ("source-absolute", os.path.abspath(source)),
                  ("source-real", os.path.realpath(source))]
    if out is not None:
        roles += [("out", out), ("out-absolute", os.path.abspath(out))]
    folders = os.environ.get("LEAN_PATH", "").split(os.pathsep)
    roles += [(f"path-{n}", folder) for n, folder in enumerate(folders) if folder]
    return [(f"\0lean-cache:{role}\0".encode(), path.encode()) for role, path in roles]


def generalize(data, roles):
    for placeholder, path in sorted(roles, key=lambda role: -len(role[1])):
        data = data.replace(path, placeholder)
    return data


def specialize(data, roles):
    for placeholder, path in roles:
        data = data.replace(placeholder, path)
    return data


def mentions(path, roles):
    """Whether a (large) file contains any of the spellings, read in blocks."""
    words = [spelling for _, spelling in roles]
    overlap = max((len(word) for word in words), default=1)
    tail = b""
    with open(path, "rb") as stream:
        for block in iter(lambda: stream.read(BLOCK), b""):
            if any(word in tail + block for word in words):
                return True
            tail = block[-overlap:]
    return False


# Running, storing and replaying.

def run_into(command, merged, work):
    """Run command with stdout and stderr into work's files: its status."""
    with open(os.path.join(work, "stdout"), "wb") as out, \
            open(os.path.join(work, "stderr"), "wb") as err:
        return subprocess.run(command, stdout=out, stderr=out if merged else err).returncode


def copy_out(path, stream):
    with open(path, "rb") as source:
        shutil.copyfileobj(source, stream, BLOCK)
    stream.flush()


def storable(status, work):
    with open(os.path.join(work, "stderr"), "rb") as stream:
        text = stream.read(BLOCK).lower()
    with open(os.path.join(work, "stdout"), "rb") as stream:
        text += stream.read(BLOCK).lower()
    return status in STORED_STATUS and not any(word in text for word in RESOURCE_FAILURES)


def differences(entry, work):
    """The files of a fresh run that differ from its stored entry. Lean 4.35
    does not always write the same .olean bytes for the same source (see
    VARYING_OLEAN), so verify mode logs a differing .olean but does not fail."""
    names = {name for name in os.listdir(work) if name != "key.json"}
    names |= {name for name in os.listdir(entry) if name != "key.json"}
    return sorted(name for name in names if not os.path.exists(os.path.join(entry, name))
                  or not os.path.exists(os.path.join(work, name))
                  or sha256_file(os.path.join(entry, name)) != sha256_file(os.path.join(work, name)))


class Call:
    """One cacheable call: its command, key, and how its output is kept."""

    def __init__(self, command, material, roles, out=None, small=True, subject=""):
        self.command, self.roles, self.out, self.small = command, roles, out, small
        self.material = json.dumps(material, sort_keys=True)
        self.key = hashlib.sha256(self.material.encode()).hexdigest()
        self.subject = subject

    def replay(self, entry, cache):
        """Give a stored entry's output, .olean and status."""
        if os.path.exists(os.path.join(entry, "olean")):
            shutil.copyfile(os.path.join(entry, "olean"), self.out)
            mark_olean(cache, self.out)
        for name, stream in (("stdout", sys.stdout.buffer), ("stderr", sys.stderr.buffer)):
            if self.small:
                stream.write(specialize(read(os.path.join(entry, name)), self.roles))
                stream.flush()
            else:
                copy_out(os.path.join(entry, name), stream)
        return int(read(os.path.join(entry, "status")))

    def record(self, work, cache, status):
        """Put a fresh run's files into the form an entry keeps them in."""
        write(os.path.join(work, "status"), b"%d" % status)
        write(os.path.join(work, "key.json"), self.material.encode())
        before = getattr(self, "before", None)
        if self.out and os.path.exists(self.out) and os.stat(self.out).st_mtime_ns != before:
            shutil.copyfile(self.out, os.path.join(work, "olean"))
        names = ("stdout", "stderr") if self.small else ("stderr",)
        for name in names:
            path = os.path.join(work, name)
            write(path, generalize(read(path), self.roles))
        return self.small or not mentions(os.path.join(work, "stdout"), self.roles)

    def answer(self, mode, cache):
        """Replay or run this call; its exit status."""
        entry = os.path.join(cache, "entries", self.key[:2], self.key)
        if mode == "1" and os.path.exists(os.path.join(entry, "status")):
            status = self.replay(entry, cache)
            log("hit", "-", self.subject)
            return status
        os.makedirs(os.path.dirname(entry), exist_ok=True)
        work = tempfile.mkdtemp(dir=os.path.dirname(entry), prefix=".tmp-")
        try:
            self.before = (os.stat(self.out).st_mtime_ns
                           if self.out and os.path.exists(self.out) else None)
            merged = same_file(1, 2)
            status = run_into(self.command, merged, work)
            raw = {name: os.path.join(work, name) for name in ("stdout", "stderr")}
            if self.small:
                outputs = {name: read(path) for name, path in raw.items()}
            keep = storable(status, work) and self.record(work, cache, status)
            for name, stream in (("stdout", sys.stdout.buffer), ("stderr", sys.stderr.buffer)):
                if self.small:
                    stream.write(outputs[name])
                    stream.flush()
                else:
                    copy_out(raw[name], stream)
            if keep and self.out and os.path.exists(os.path.join(work, "olean")):
                mark_olean(cache, os.path.join(work, "olean"))
            if os.path.exists(os.path.join(entry, "status")):
                differ = differences(entry, work)
                if differ not in ([], ["olean"]):
                    sys.stderr.write(f"lean-cache: verify: the run of {self.subject} differs "
                                     f"from the cache entry {entry} in {', '.join(differ)}\n")
                    log("differs", ",".join(differ), self.subject)
                    return 125
                log("verified", "olean-differs" if differ else "-", self.subject)
            elif keep:
                try:
                    os.rename(work, entry)
                except OSError:
                    pass  # another job stored the same entry first
                log("miss", "-", self.subject)
            return status
        finally:
            if os.path.isdir(work):
                shutil.rmtree(work)


def lean_call(lean, args, cache):
    options, out, run, source = parse(args)
    text = read(source)
    code = code_only(text)
    inputs = [word.decode() for word in IO_INPUTS if word in text]
    inputs += [word.decode() for word in CODE_INPUTS if word in code]
    if inputs:
        raise Uncacheable(f"source names {inputs[0]}")
    fingerprint, prefix = toolchain(lean, cache)
    material = common_key(fingerprint, prefix, cache)
    material.update({"tool": "lean", "options": options, "run": run,
                     "olean": out is not None, "module": module_path(source),
                     "source": hashlib.sha256(text).hexdigest()})
    return Call([lean] + args, material, spellings(source, out), out=out, subject=source)


def export_call(lean, args, cache):
    fingerprint, prefix = toolchain(lean, cache)
    material = common_key(fingerprint, prefix, cache)
    material.update({"tool": "leanexport", "arguments": args})
    return Call([os.path.join(prefix, "bin", "leanexport")] + args, material,
                spellings(None, None), small=False, subject="leanexport:" + ":".join(args))


def main(args):
    lean = os.environ.get("LEANFORTH_LEAN")
    if not lean:
        sys.exit("lean-cache: LEANFORTH_LEAN must name the real Lean binary")
    # A bare name (the Makefile's LEAN default `lean`, when no .tools toolchain is beside the
    # checkout, as in a worktree) is found on PATH: execv takes a path, and the toolchain's
    # leanexport is found beside the real file (fix-batch-4, 2026-11-18).
    # Never an elan proxy, which downloads a toolchain when ELAN_HOME is not
    # set, nor anything not known to be a toolchain's binary, and a name
    # found on PATH only when it is Lean 4.35.0 (scripts/lean_pin.py; reviews
    # fix-batch Re-check 2 and F5 of fix-cli-present). An explicit path is
    # judged by where it is (proxy, layout), which runs nothing, so each call
    # costs no extra run; a wrapper, a copy or a hard link of a proxy given by
    # path is refused, not run.
    if os.sep not in lean:
        found = shutil.which(lean)
        reason = found and lean_pin.refusal(found)
        lean = found or lean
    else:
        reason = (lean_pin.proxy(lean) or lean_pin.layout(lean)) if os.path.exists(lean) else None
    if reason:
        sys.exit(f"lean-cache: refused: {reason}")
    mode = os.environ.get("LEANFORTH_LEAN_CACHE", "1")
    if mode not in ("0", "1", "verify"):
        sys.exit(f"lean-cache: LEANFORTH_LEAN_CACHE must be 0, 1 or verify, not {mode}")
    export = args[:1] == ["--leanexport"]
    args = args[1:] if export else args
    tool = (os.path.join(os.path.dirname(os.path.dirname(os.path.realpath(lean))), "bin",
                         "leanexport") if export else lean)
    cache = os.environ.get("LEANFORTH_LEAN_CACHE_DIR")
    if mode != "0" and cache:
        cache = os.path.abspath(cache)
        try:
            call = export_call(lean, args, cache) if export else lean_call(lean, args, cache)
            return call.answer(mode, cache)
        except Uncacheable as reason:
            log("run", str(reason), "leanexport" if export else (args or ["-"])[-1])
    sys.stdout.flush()
    os.execv(tool, [tool] + args)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
