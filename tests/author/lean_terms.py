"""Lean's own terms for the authoring words' fixtures (plan task 8.1.2; test-only).

A fixture's Lean source (tests/reference/author-STEM.lean) is compiled by
pinned Lean 4.35.0 (the toolchain's bin/lean, never an elan proxy). Its
declarations then reach check_author.py by two independent paths, each
written in the tree-dump format of tests/author/dump.fs:

1. Lean's environment itself: a metaprogram (LEAN_DUMP, run by the same
   Lean) writes whether each declaration is protected, and its universe
   parameters, type and value exactly as Lean holds them: every node, de
   Bruijn index, constant name and universe argument, level, binder name
   and binder kind.
2. The pinned exporter (lean4export 3.1.0, the toolchain's bin/leanexport):
   its NDJSON stream, read here (Export). The exporter shares nodes that
   are equal apart from binder names and binder kinds (a later declaration
   can come out with an earlier one's binder names and kinds; checked with
   three alpha-equivalent theorems), so from this path binder names and
   kinds are not compared (structural()), nor protection, which the export
   does not carry; everything else is.

Both apply dump.fs's stated identifications and nothing else: a Pi binder
that prints as -> (explicit, unused, anonymous or hygienic) is written
[arrow]; levels and Sorts are written as level expressions; a natural-number
literal as (lit VALUE LIMBS) and a projection as (projection (proj TYPE
INDEX) TERM), as dump.fs writes the words' (lit#, proj#). A node the words
cannot build yet (let, string literals, metadata) is written as itself, so
it never equals anything the words build. Finite evidence about these
files; it never accepts a theorem.

Usage: python3 tests/author/lean_terms.py EXPORT.ndjson NAME...   (prints dumps)
"""
import json
import os
import pathlib
import re
import subprocess
import sys
TEST_LIMIT = int(os.environ.get("TEST_TIMEOUT", "1800"))  # seconds; make exports it

LEAN_VERSION = {"version": "4.35.0", "githash": "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"}
EXPORTER = {"name": "lean4export", "version": "3.1.0"}
# The records LeanForth's words write (src/author/export.fs): its own
# exporter's name, the format and Lean's version, no Lean build.
LEANFORTH_META = {"exporter": {"name": "leanforth", "version": "0.1.0-dev"},
                  "format": {"version": "3.1.0"},
                  "lean": {"githash": "none", "version": "4.35.0"}}
KINDS = {"default": 0, "implicit": 1, "strictImplicit": 2, "instImplicit": 3}
DECL_KINDS = {"thm": 0, "def": 1, "axiom": 2}


class ExportError(Exception):
    pass


class Export:
    """The names, levels, expressions and declarations of one export; with
    leanforth, the records of LeanForth's words instead of pinned Lean's."""

    def __init__(self, lines, leanforth=False):
        self.leanforth = leanforth
        self.names = {0: ()}
        self.levels = {0: ("zero", None)}
        self.exprs = {}
        self.decls = {}
        self.order = []   # each declaration's name, in record order
        for line in lines:
            if line.strip():
                self.record(json.loads(line))

    def meta(self, meta):
        if self.leanforth and meta != LEANFORTH_META:
            raise ExportError(f"unexpected metadata of LeanForth's records: {meta}")
        if not self.leanforth and (meta["exporter"] != EXPORTER or meta["lean"] != LEAN_VERSION):
            raise ExportError(f"unexpected exporter or Lean: {meta}")

    def record(self, r):
        if "meta" in r:
            self.meta(r["meta"])
        elif "in" in r:
            kind = "str" if "str" in r else "num"
            item = r[kind]
            part = ("str", item["str"]) if kind == "str" else ("num", item["i"])
            self.names[r["in"]] = self.names[item["pre"]] + (part,)
        elif "il" in r:
            (kind, value), = ((k, v) for k, v in r.items() if k != "il")
            self.levels[r["il"]] = (kind, value)
        elif "ie" in r:
            (kind, value), = ((k, v) for k, v in r.items() if k != "ie")
            self.exprs[r["ie"]] = (kind, value)
        elif "inductive" in r:
            for group in ("types", "ctors", "recs"):
                for item in r["inductive"][group]:
                    self.declare("inductive", item)
        else:
            (kind, item), = r.items()
            self.declare(kind, item)

    def declare(self, kind, item):
        self.decls[self.name(item["name"])] = (kind, item)
        self.order.append(self.name(item["name"]))

    def name(self, index):
        parts = self.names[index]
        if not parts:
            return "[anonymous]"
        return ".".join(text if tag == "str" else f"#{text}" for tag, text in parts)

    def hygienic(self, index):
        parts = list(self.names[index])
        while parts and parts[-1][0] == "num":
            parts.pop()
        return bool(parts) and parts[-1] == ("str", "_hyg")

    def level(self, index):
        kind, value = self.levels[index]
        if kind == "zero":
            return "0"
        if kind == "succ":
            return f"(succ {self.level(value)})"
        if kind in ("max", "imax"):
            return f"({kind} {self.level(value[0])} {self.level(value[1])})"
        if kind == "param":
            return f"(param {self.name(value)})"
        raise ExportError(f"unknown level {kind}")

    def uses(self, index, k):
        kind, value = self.exprs[index]
        if kind == "bvar":
            return value == k
        if kind == "app":
            return self.uses(value["fn"], k) or self.uses(value["arg"], k)
        if kind in ("lam", "forallE"):
            return self.uses(value["type"], k) or self.uses(value["body"], k + 1)
        if kind == "mdata":
            return self.uses(value["expr"], k)
        if kind == "letE":
            return (self.uses(value["type"], k) or self.uses(value["value"], k)
                    or self.uses(value["body"], k + 1))
        if kind == "proj":
            return self.uses(value["struct"], k)
        return False

    def binder(self, value, pi):
        info = KINDS[value["binderInfo"]]
        name = value["name"]
        arrow = (pi and info == 0 and (name == 0 or self.hygienic(name))
                 and not self.uses(value["body"], 0))
        return "[arrow] 0" if arrow else f"{self.name(name)} {info}"

    def term(self, index):
        kind, value = self.exprs[index]
        if kind == "bvar":
            return f"#{value}"
        if kind == "sort":
            return f"(Sort {self.level(value)})"
        if kind == "const":
            levels = "".join(" " + self.level(u) for u in value["us"])
            return f"(const {self.name(value['name'])}{levels})"
        if kind == "app":
            return f"(app {self.term(value['fn'])} {self.term(value['arg'])})"
        if kind in ("lam", "forallE"):
            tag = "lam" if kind == "lam" else "pi"
            binder = self.binder(value, kind == "forallE")
            return f"({tag} {binder} {self.term(value['type'])} {self.term(value['body'])})"
        if kind == "natVal":  # dump.fs: first cell (the value), then the number of limbs
            number = int(value)
            return f"(lit {number} {1 if number else 0})"
        if kind == "proj":  # the projection of its leaf and the structure
            leaf = f"(proj {self.name(value['typeName'])} {value['idx']})"
            return f"(projection {leaf} {self.term(value['struct'])})"
        return f"(lean-only {kind})"

    def declaration(self, name):
        """(kind or None, None, universe names, type dump, value dump or 'none'):
        the export does not say whether a declaration is protected."""
        if name not in self.decls:
            raise ExportError(f"Lean's export has no declaration {name}")
        kind, item = self.decls[name]
        universes = [self.name(u) for u in item.get("levelParams", [])]
        value = self.term(item["value"]) if kind in ("thm", "def") else "none"
        return DECL_KINDS.get(kind), None, universes, self.term(item["type"]), value

    def resolved(self, name):
        """The declaration's whole record with every name, level and
        expression read (types and values structural(), as the pinned
        exporter merges binder names and kinds): its kind, name, all,
        levelParams, type, value, hints, safety, isUnsafe, as they stand."""
        if name not in self.decls:
            raise ExportError(f"no declaration {name}")
        kind, item = self.decls[name]
        out = {"kind": kind}
        for key, value in item.items():
            if key == "name":
                out[key] = self.name(value)
            elif key in ("all", "levelParams"):
                out[key] = [self.name(part) for part in value]
            elif key in ("type", "value"):
                out[key] = structural(self.term(value))
            else:
                out[key] = value
        return out


BINDER = re.compile(r"\((lam|pi) (\[arrow\] 0|\S+ \d)")


def structural(dump):
    """A dump with every binder's name and kind left out."""
    return BINDER.sub(r"(\1 _", dump)


# The metaprogram of path 1: dump.fs's format, from Lean's environment.
LEAN_DUMP = r"""
open Lean

def lfName (n : Name) : String :=
  if n.isAnonymous then "[anonymous]" else
  ".".intercalate (n.components.map fun
    | .str _ s => s
    | .num _ i => s!"#{i}"
    | .anonymous => "")

partial def lfLevel : Level → String
  | .zero => "0"
  | .succ l => s!"(succ {lfLevel l})"
  | .max a b => s!"(max {lfLevel a} {lfLevel b})"
  | .imax a b => s!"(imax {lfLevel a} {lfLevel b})"
  | .param n => s!"(param {lfName n})"
  | .mvar _ => "(lean-only mvar)"

def lfKind : BinderInfo → Nat
  | .default => 0 | .implicit => 1 | .strictImplicit => 2 | .instImplicit => 3

partial def lfHygienic : Name → Bool
  | .num p _ => lfHygienic p
  | .str _ s => s == "_hyg"
  | .anonymous => false

partial def lfTerm : Expr → String
  | .bvar i => s!"#{i}"
  | .sort l => s!"(Sort {lfLevel l})"
  | .const n us => "(const " ++ lfName n ++ String.join (us.map (" " ++ lfLevel ·)) ++ ")"
  | .app f a => s!"(app {lfTerm f} {lfTerm a})"
  | .lam n t b bi => s!"(lam {lfName n} {lfKind bi} {lfTerm t} {lfTerm b})"
  | .forallE n t b bi =>
    if bi == .default && (n.isAnonymous || lfHygienic n) && !b.hasLooseBVar 0 then
      s!"(pi [arrow] 0 {lfTerm t} {lfTerm b})"
    else s!"(pi {lfName n} {lfKind bi} {lfTerm t} {lfTerm b})"
  | .lit (.natVal n) => s!"(lit {n} {if n == 0 then 0 else 1})"
  | .proj s i e => s!"(projection (proj {lfName s} {i}) {lfTerm e})"
  | e => s!"(lean-only {e.ctorName})"

-- A dump's name: its parts split at dots, a part #N numeric (Name.num).
def lfParse (s : String) : Name :=
  (s.splitOn ".").foldl (init := .anonymous) fun n part =>
    if part.startsWith "#" then .num n (part.drop 1).toNat! else .str n part

def lfDecl (name : String) : CoreM Unit := do
  let ci ← getConstInfo (lfParse name)
  let kind := match ci with | .thmInfo _ => "0" | .defnInfo _ => "1" | .axiomInfo _ => "2"
                            | _ => "-"
  let value := match ci with | .thmInfo t => lfTerm t.value | .defnInfo d => lfTerm d.value
                             | _ => "none"
  let prot := if isProtected (← getEnv) (lfParse name) then " protected" else ""
  IO.println s!"dump: {kind} {name}{prot}{String.join (ci.levelParams.map (" u:" ++ lfName ·))}"
  IO.println s!"dump:   type {lfTerm ci.type}"
  IO.println s!"dump:   value {value}"
"""


def lean_dump(lean, prefix, module, names, workdir):
    """Path 1: Lean's own dumps of names, by a metaprogram importing module:
    name -> (kind or None, universe names, type, value)."""
    workdir = pathlib.Path(workdir)
    program = workdir / "LeanForthDump.lean"
    calls = "\n".join(f"#eval lfDecl {json.dumps(name)}" for name in names)
    program.write_text(f"import Lean\nimport {module}\n{LEAN_DUMP}\n{calls}\n", encoding="utf-8")
    env = dict(os.environ, LEAN_PATH=f"{workdir}:{prefix}/lib/lean")
    run = subprocess.run([lean, "-DwarningAsError=true", str(program)], capture_output=True,
                         text=True, timeout=TEST_LIMIT, env=env)
    program.unlink()
    if run.returncode != 0:
        raise ExportError(f"Lean's dump failed:\n{run.stdout}{run.stderr}")
    lines = [line[len("dump: "):] for line in run.stdout.splitlines()
             if line.startswith("dump: ")]
    return parse_dumps(lines, lambda kind: None if kind == "-" else int(kind))


def parse_dumps(lines, kind_of):
    """Declarations from dump lines (dump.fs's format, three per declaration):
    name -> (kind, protected, universe names, type, value)."""
    decls = {}
    for head, type_, value in zip(lines[0::3], lines[1::3], lines[2::3]):
        kind, name, *rest = head.split(" ")
        protected = rest[:1] == ["protected"]
        universes = [u[len("u:"):] for u in rest[protected:]]
        decls[name] = (kind_of(kind), protected, universes,
                       type_[len("  type "):], value[len("  value "):])
    return decls


def compile_and_export(lean, source, names, workdir):
    """Compile source with pinned Lean into workdir; Lean's own dumps of names
    and the pinned exporter's (their dependencies too): (Lean's printed
    lines, {name: Lean's dump}, Export)."""
    workdir = pathlib.Path(workdir)
    module = "AuthorFixture"
    olean = workdir / f"{module}.olean"
    run = subprocess.run([lean, "-DwarningAsError=true", "-o", str(olean), str(source)],
                         capture_output=True, text=True, timeout=TEST_LIMIT)
    if run.returncode != 0:
        raise ExportError(f"Lean failed on {source}:\n{run.stdout}{run.stderr}")
    printed = run.stdout.splitlines()
    prefix = subprocess.run([lean, "--print-prefix"], capture_output=True, text=True,
                            timeout=60, check=True).stdout.strip()
    try:
        dumps = lean_dump(lean, prefix, module, names, workdir)
        env = dict(os.environ, LEAN_PATH=str(workdir),
                   PATH=f"{prefix}/bin:{os.environ.get('PATH', '')}")
        exporter = os.environ.get("LEANEXPORT") or f"{prefix}/bin/leanexport"  # may be cached
        # The exporter reads a name at its dots, so one with a numeric part
        # (#N) is not asked for: it comes as the dependency of another.
        export = subprocess.run([exporter, module, "--", *[n for n in names if "#" not in n]],
                                capture_output=True, text=True, timeout=TEST_LIMIT, env=env)
    finally:
        for made in workdir.glob(f"{module}.*"):
            made.unlink()
    if export.returncode != 0:
        raise ExportError(f"leanexport failed on {source}:\n{export.stderr}")
    return printed, dumps, Export(export.stdout.splitlines())


def main(args):
    with open(args[0], encoding="utf-8") as stream:
        export = Export(stream)
    for name in args[1:]:
        kind, _, universes, type_, value = export.declaration(name)
        print(kind, name, *[f"u:{u}" for u in universes])
        print("  type", type_)
        print("  value", value)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
