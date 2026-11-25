#!/usr/bin/env python3
"""Sample a running Gforth's Forth return stack (a profiler for LeanForth).

usage: PROF_SYMS=FILE profile-sample.py OUT.prof INTERVAL -- CMD ARGS...

Runs CMD as a child, seizes it with ptrace and every INTERVAL seconds stops
it, reads its registers and its Forth return stack, and maps each return
address (a threaded-code address whose cell before it is a call of a colon
definition) to the colon definition that holds it, through the symbol table
that scripts/profile-symbols.fs writes from inside the same process to the
file PROF_SYMS names (CMD must load it after src/main.fs). Writes OUT.prof:
a first line "# samples N wall S interval I", then one line per distinct
stack, "count<TAB>word;caller;...;outermost", innermost first; the
innermost entry is the word whose code the interpreter was in, or "<libc>"
before it when the CPU was in the C library. scripts/profile-summary.py
turns it into tables. The child's exit status is the sampler's.

Limits: x86-64 Linux, Gforth 1.0's gforth-fast (its instruction pointer in
rbx and its return-stack pointer in r14: gforth and Gforth 0.7.3 keep them
elsewhere), and only the process's first thread is sampled, so a check
under --jobs N above 1 shows the driving task, not the workers: profile at
--jobs 1. Each sample costs a ptrace stop (about 1% at 10 ms). A
development tool, not part of the product; first written as the perf-scan's
tools/sample.py (agent PERF1, 2026-11-12; kept in
docs/development/measurements/perf-scan-2026-11-18/tools/), kept here with
its symbol table's source positions (2026-11-25).
"""
import bisect
import ctypes
import os
import signal
import sys
import time

libc = ctypes.CDLL(None, use_errno=True)
libc.ptrace.restype = ctypes.c_long
libc.ptrace.argtypes = [ctypes.c_long, ctypes.c_long, ctypes.c_void_p, ctypes.c_void_p]
PTRACE_CONT, PTRACE_GETREGS = 7, 12
PTRACE_SEIZE, PTRACE_INTERRUPT = 0x4206, 0x4207
PTRACE_O_EXITKILL = 0x100000  # the traced check dies with the sampler
REGS = ("r15 r14 r13 r12 rbp rbx r11 r10 r9 r8 rax rcx rdx rsi rdi orig_rax rip cs "
        "eflags rsp ss fs_base gs_base ds es fs gs").split()


class Regs(ctypes.Structure):
    _fields_ = [(n, ctypes.c_ulong) for n in REGS]


class Symbols:
    """The colon definitions' starts and names, and the stacks' bottoms."""

    def __init__(self, text):
        ents, self.rp0 = [], None
        for line in text.splitlines():
            part = line.split(" ")
            if part[0] == "RP0":
                self.rp0 = int(part[1], 16)
            elif len(part) >= 3 and part[1] == "c":
                ents.append((int(part[0], 16), part[2]))
        ents.sort()
        self.starts = [e[0] for e in ents]
        self.names = [e[1] for e in ents]
        self.startset = set(self.starts)
        self.lo, self.hi = self.starts[0], self.starts[-1] + 65536

    def name(self, addr):
        return self.names[bisect.bisect_right(self.starts, addr) - 1]


def read_symbols(path):
    if not os.path.exists(path):
        return None
    text = open(path).read()
    return Symbols(text) if "SP0 " in text else None


def regions(pid, sym, mem):
    """The C library's ranges, and the native code region a call cell points into."""
    tok = int.from_bytes(os.pread(mem, 8, sym.starts[len(sym.starts) // 2]), "little")
    lib, code = [], (0, 0)
    for line in open("/proc/%d/maps" % pid):
        f = line.split()
        lo, hi = [int(v, 16) for v in f[0].split("-")]
        if len(f) >= 6 and any(k in f[5] for k in ("libc.so", "ld-linux", "libm")):
            lib.append((lo, hi))
        if lo <= tok < hi:
            code = (lo, hi)
    return lib, code


def stack_of(regs, sym, mem, lib, code):
    ip, rp, rip = regs.rbx, regs.r14, regs.rip
    line = ["<libc>"] if any(x <= rip < y for x, y in lib) else []
    line.append(sym.name(ip) if sym.lo <= ip < sym.hi else "<ip?>")
    if not (sym.rp0 - (1 << 16) < rp <= sym.rp0):
        return line + ["<other-stack>"]
    try:
        buf = os.pread(mem, sym.rp0 - rp, rp)
    except OSError:
        buf = b""
    for i in range(0, len(buf) - 7, 8):
        a = int.from_bytes(buf[i:i + 8], "little")
        if sym.lo <= a < sym.hi:
            try:
                prev = int.from_bytes(os.pread(mem, 8, a - 8), "little")
            except OSError:
                continue
            if prev in sym.startset or code[0] <= prev < code[1]:
                line.append(sym.name(a))
    return line


def main(argv):
    out, interval = argv[1], float(argv[2])
    cmd = argv[argv.index("--") + 1:]
    symf = os.environ["PROF_SYMS"]
    if os.path.exists(symf):
        os.unlink(symf)
    pid = os.fork()
    if pid == 0:
        fd = os.open("/dev/null", os.O_RDONLY)
        os.dup2(fd, 0)
        try:
            os.execvp(cmd[0], cmd)
        except OSError as e:
            print("profile-sample: cannot run %s: %s" % (cmd[0], e.strerror), file=sys.stderr)
            os._exit(127)
    signal.signal(signal.SIGTERM, lambda *_: sys.exit(143))
    try:
        return sample(out, interval, pid, symf)
    finally:  # never leave the check running: killed and reaped
        try:  # a child already reaped is no longer ours: no kill
            wp, st = os.waitpid(pid, os.WNOHANG)
            if wp == 0 or os.WIFSTOPPED(st):
                os.kill(pid, signal.SIGKILL)
                os.waitpid(pid, 0)
        except ChildProcessError:
            pass


def sample(out, interval, pid, symf):
    if libc.ptrace(PTRACE_SEIZE, pid, None, ctypes.c_void_p(PTRACE_O_EXITKILL)) != 0:
        print("profile-sample: ptrace seize failed, errno", ctypes.get_errno(), file=sys.stderr)
        return 5
    sym = mem = lib = code = None
    samples, status, nsamp, start = {}, 0, 0, time.time()
    while True:
        time.sleep(interval)
        wp, st = os.waitpid(pid, os.WNOHANG)
        if wp == pid:
            if os.WIFEXITED(st) or os.WIFSIGNALED(st):
                status = st
                break
            if os.WIFSTOPPED(st):  # a signal stop: pass the signal on
                sig = os.WSTOPSIG(st)
                libc.ptrace(PTRACE_CONT, pid, None, ctypes.c_void_p(sig if (st >> 16) == 0 else 0))
                continue
        if sym is None:
            sym = read_symbols(symf)
            if sym is None:
                continue
            mem = os.open("/proc/%d/mem" % pid, os.O_RDONLY)
        if libc.ptrace(PTRACE_INTERRUPT, pid, None, None) != 0:
            continue
        wp, st = os.waitpid(pid, 0)
        if os.WIFEXITED(st) or os.WIFSIGNALED(st):
            status = st
            break
        regs = Regs()
        if libc.ptrace(PTRACE_GETREGS, pid, None, ctypes.byref(regs)) != 0:
            print("profile-sample: cannot read registers (x86-64 Linux only), errno",
                  ctypes.get_errno(), file=sys.stderr)
            return 5
        if lib is None:
            lib, code = regions(pid, sym, mem)
        key = ";".join(stack_of(regs, sym, mem, lib, code))
        samples[key] = samples.get(key, 0) + 1
        nsamp += 1
        libc.ptrace(PTRACE_CONT, pid, None, None)
    with open(out, "w") as f:
        f.write("# samples %d wall %.1f s interval %g\n" % (nsamp, time.time() - start, interval))
        for s, c in sorted(samples.items(), key=lambda x: -x[1]):
            f.write("%d\t%s\n" % (c, s))
    code_out = os.WEXITSTATUS(status) if os.WIFEXITED(status) else 5
    print("profile-sample: exit %d, %d samples" % (code_out, nsamp), file=sys.stderr)
    return code_out


if __name__ == "__main__":
    sys.exit(main(sys.argv))
