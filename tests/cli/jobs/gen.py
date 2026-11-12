#!/usr/bin/env python3
"""rvS7: synthetic lean4export 3.1.0 NDJSON exports for scheduler probes.

wide K:      K theorems tK : forall A : Prop, A -> A := fun A a => a (independent).
chainK K:    def c0 : Prop -> Prop := fun A => A; def c(k+1) := fun A => ck A  (a chain
             of K definitions, each unfolding to the one before), then K theorems
             using the last one, each needing the whole chain unfolded.
renamed K:   theorem r0 : forall A0 : Prop, A0 -> A0 := fun A0 a0 => a0, then K-1
             theorems rk : forall X : Prop, (forall Ak : Prop, Ak -> Ak) -> X -> X
             := fun X h x => x, whose inner binders equal r0's up to their names;
             the importer makes each such class one node (ADR 0014 Amendment 7),
             so the binders h above them are new copies, which a worker must
             make as the source did.
dupl K:      def D : Prop -> Prop := fun A => A; def C := fun A => D A; K slow-ish
             filler theorems; a second `def D` (duplicate: rejected); then theorems
             that mention only C (unfolding meets D: the duplicate's slot is not in
             their readiness set).
"""
import json, sys

class Ex:
    def __init__(s):
        s.lines = [{"meta": {"exporter": {"name": "lean4export", "version": "3.1.0"},
                             "format": {"version": "3.1.0"},
                             "lean": {"githash": "eb6cafb7290e8bd5f2937522d8d804f58f02bafc",
                                      "version": "4.35.0"}}}]
        s.names = {}; s.n = 0; s.e = 0; s.exprs = {}
    def name(s, text):
        if text in s.names: return s.names[text]
        pre = 0
        parts = text.split(".")
        acc = ""
        for p in parts:
            acc = p if not acc else acc + "." + p
            if acc in s.names: pre = s.names[acc]; continue
            s.n += 1; s.lines.append({"in": s.n, "str": {"pre": pre, "str": p}})
            s.names[acc] = s.n; pre = s.n
        return pre
    def ex(s, key, rec):
        if key in s.exprs: return s.exprs[key]
        k = s.e; s.e += 1
        rec = dict(rec); rec["ie"] = k; s.lines.append(rec); s.exprs[key] = k
        return k
    def sort0(s): return s.ex(("sort0",), {"sort": 0})
    def bvar(s, i): return s.ex(("bvar", i), {"bvar": i})
    def pi(s, nm, ty, body, bi="default"):
        return s.ex(("pi", nm, ty, body, bi), {"forallE": {"binderInfo": bi, "body": body, "name": s.name(nm), "type": ty}})
    def lam(s, nm, ty, body, bi="default"):
        return s.ex(("lam", nm, ty, body, bi), {"lam": {"binderInfo": bi, "body": body, "name": s.name(nm), "type": ty}})
    def const(s, nm): return s.ex(("const", nm), {"const": {"name": s.name(nm), "us": []}})
    def app(s, f, a): return s.ex(("app", f, a), {"app": {"fn": f, "arg": a}})
    def thm(s, nm, ty, val):
        n = s.name(nm); s.lines.append({"thm": {"all": [n], "levelParams": [], "name": n, "type": ty, "value": val}})
    def defn(s, nm, ty, val):
        n = s.name(nm)
        s.lines.append({"def": {"all": [n], "hints": {"regular": 1}, "levelParams": [], "name": n,
                                "safety": "safe", "type": ty, "value": val}})
    def out(s):
        """The exporter's form: keys sorted (as wide60 and dupl80 are written)."""
        return "".join(json.dumps(l, ensure_ascii=False, separators=(",", ":"), sort_keys=True)
                       + "\n" for l in s.lines)

def idthm(x):
    P = x.sort0()
    ty = x.pi("A", P, x.pi("a", x.bvar(0), x.bvar(1)))
    val = x.lam("A", P, x.lam("a", x.bvar(0), x.bvar(0)))
    return ty, val

def wide(k):
    x = Ex(); ty, val = idthm(x)
    for i in range(k): x.thm(f"t{i}", ty, val)
    return x

def renamed(k):
    x = Ex(); P = x.sort0()
    x.thm("r0", x.pi("A0", P, x.pi("a0", x.bvar(0), x.bvar(1))),
          x.lam("A0", P, x.lam("a0", x.bvar(0), x.bvar(0))))
    for i in range(1, k):
        idty = x.pi(f"A{i}", P, x.pi(f"a{i}", x.bvar(0), x.bvar(1)))
        ty = x.pi("X", P, x.pi("h", idty, x.pi("x", x.bvar(1), x.bvar(2))))
        val = x.lam("X", P, x.lam("h", idty, x.lam("x", x.bvar(1), x.bvar(0))))
        x.thm(f"r{i}", ty, val)
    return x

def p2p(x):
    P = x.sort0(); return x.pi("A", P, P)

def chain(k):
    x = Ex(); P = x.sort0(); T = p2p(x)
    x.defn("c0", T, x.lam("A", P, x.bvar(0)))
    for i in range(1, k):
        x.defn(f"c{i}", T, x.lam("A", P, x.app(x.const(f"c{i-1}"), x.bvar(0))))
    last = f"c{k-1}"
    # theorem uK : forall A : Prop, A -> c_last A := fun A a => a
    for i in range(k):
        ty = x.pi("A", P, x.pi("a", x.bvar(0), x.app(x.const(last), x.bvar(1))))
        val = x.lam("A", P, x.lam("a", x.bvar(0), x.bvar(0)))
        x.thm(f"u{i}", ty, val)
    return x

def dupl(k):
    x = Ex(); P = x.sort0(); T = p2p(x)
    x.defn("D", T, x.lam("A", P, x.bvar(0)))
    x.defn("C", T, x.lam("A", P, x.app(x.const("D"), x.bvar(0))))
    ty, val = idthm(x)
    for i in range(k): x.thm(f"f{i}", ty, val)
    x.defn("D", T, x.lam("A", P, x.bvar(0)))   # duplicate name: rejected
    for i in range(k):
        ty2 = x.pi("A", P, x.pi("a", x.bvar(0), x.app(x.const("C"), x.bvar(1))))
        x.thm(f"g{i}", ty2, val)
    return x

def double(k, copies=1):
    """d0 : Prop -> Prop := fun A => A; d(k+1) := fun A => dk (dk A): dK A
    reduces to A in 2^K - 1 head unfoldings, each making new nodes. Then
    big : forall A : Prop, A -> dK A := fun A a => a, which Lean accepts
    (lazy delta unfolds the chain), with a scratch that grows with 2^K, and
    four small theorems beside it (the identity on propositions). With
    copies 2 (kind double2), big2, the same theorem again, follows."""
    x = Ex(); P = x.sort0(); T = p2p(x)
    x.defn("d0", T, x.lam("A", P, x.bvar(0)))
    for i in range(1, k + 1):
        prev = x.const(f"d{i-1}")
        x.defn(f"d{i}", T, x.lam("A", P, x.app(prev, x.app(prev, x.bvar(0)))))
    ty = x.pi("A", P, x.pi("a", x.bvar(0), x.app(x.const(f"d{k}"), x.bvar(1))))
    val = x.lam("A", P, x.lam("a", x.bvar(0), x.bvar(0)))
    x.thm("big", ty, val)
    for i in range(2, copies + 1): x.thm(f"big{i}", ty, val)
    ty, val = idthm(x)
    for i in range(4): x.thm(f"small{i}", ty, val)
    return x

if __name__ == "__main__":
    kind, k = sys.argv[1], int(sys.argv[2])
    gens = {"wide": wide, "chain": chain, "dupl": dupl,
            "renamed": renamed, "double": double,
            "double2": lambda k: double(k, 2)}
    sys.stdout.write(gens[kind](k).out())
