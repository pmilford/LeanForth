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
lets K:      (review rvRS F2) d0 : Prop -> Prop := let x0 : Prop -> Prop := fun A =>
             A; x0, then K-1 definitions dk := fun B => (let xk : Prop -> Prop :=
             fun A => A; xk) B, whose lets are equal to d0's up to their names: the
             importer makes them one node, so the applications above them are new
             copies, which a worker must make as the source did.
refs N:      (review rvRS F1, its probe gen_refs.py) 20 universe parameters vs =
             v1..v20; for i < N D_i.{vs} : Sort v1 -> Sort 1 := fun a => (Prop ->
             Prop) and f_i.{vs} : (a : Sort v1) -> D_i.{vs} a := fun a p => p; K :
             PP -> PP -> PP := fun a b => b (PP = Prop -> Prop); then B : PP :=
             K (f_0.{0..0} Q) (K (f_1.{0..0} Q) ... (fun p => p)) (Q = forall p :
             Prop, p), whose check instantiates each f_i's type and so makes the N
             references D_i.{0..0} (384 bytes each by --memory-per-check's count).
             refsz N: Z_i : Sort 1 := D_i.{0..0} Q in place of B, so that every such
             reference is in the tier; refsbz N: B, then the Z_i.
"""
import json, sys

class Ex:
    def __init__(s):
        s.lines = [{"meta": {"exporter": {"name": "lean4export", "version": "3.1.0"},
                             "format": {"version": "3.1.0"},
                             "lean": {"githash": "eb6cafb7290e8bd5f2937522d8d804f58f02bafc",
                                      "version": "4.35.0"}}}]
        s.names = {}; s.n = 0; s.e = 0; s.exprs = {}; s.levels = {}; s.l = 0
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
    def const(s, nm, us=()):
        return s.ex(("const", nm, tuple(us)), {"const": {"name": s.name(nm), "us": list(us)}})
    def level(s, key, rec):
        """A universe level (kind refs only): a parameter or a successor."""
        if key not in s.levels:
            s.l += 1; s.levels[key] = s.l; s.lines.append(dict(rec, il=s.l))
        return s.levels[key]
    def param(s, nm): return s.level(("param", nm), {"param": s.name(nm)})
    def sort1(s): return s.ex(("sort1",), {"sort": s.level(("succ", 0), {"succ": 0})})
    def app(s, f, a): return s.ex(("app", f, a), {"app": {"fn": f, "arg": a}})
    def let(s, nm, ty, val, body):
        return s.ex(("let", nm, ty, val, body), {"letE": {"body": body, "name": s.name(nm),
                                                          "nondep": False, "type": ty,
                                                          "value": val}})
    def thm(s, nm, ty, val):
        n = s.name(nm); s.lines.append({"thm": {"all": [n], "levelParams": [], "name": n, "type": ty, "value": val}})
    def defn(s, nm, ty, val, params=()):
        n = s.name(nm); ps = [s.name(p) for p in params]
        s.lines.append({"def": {"all": [n], "hints": {"regular": 1}, "levelParams": ps, "name": n,
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

def lets(k):
    x = Ex(); P = x.sort0(); PP = p2p(x); idf = x.lam("A", P, x.bvar(0))
    x.defn("d0", PP, x.let("x0", PP, idf, x.bvar(0)))
    for i in range(1, k):
        x.defn(f"d{i}", PP, x.lam("B", P, x.app(x.let(f"x{i}", PP, idf, x.bvar(0)), x.bvar(0))))
    return x

def refs(n, b=True, z=False, k=20):
    x = Ex(); P = x.sort0(); PP = p2p(x); T1 = x.sort1()
    Q = x.pi("p", P, x.bvar(0))
    params = [f"v{j}" for j in range(1, k + 1)]
    vs = [x.param(p) for p in params]
    Sv = x.ex(("sortv1",), {"sort": vs[0]})
    for i in range(n):
        x.defn(f"D{i}", x.pi("a", Sv, T1), x.lam("a", Sv, PP), params)
        x.defn(f"f{i}", x.pi("a", Sv, x.app(x.const(f"D{i}", vs), x.bvar(0))),
               x.lam("a", Sv, x.lam("p", P, x.bvar(0))), params)
    x.defn("K", x.pi("a", PP, x.pi("b", PP, PP)), x.lam("a", PP, x.lam("b", PP, x.bvar(0))))
    zeros = [0] * k
    if b:
        acc = x.lam("p", P, x.bvar(0))
        for i in reversed(range(n)):
            acc = x.app(x.app(x.const("K"), x.app(x.const(f"f{i}", zeros), Q)), acc)
        x.defn("B", PP, acc)
    if z:
        for i in range(n): x.defn(f"Z{i}", T1, x.app(x.const(f"D{i}", zeros), Q))
    return x

if __name__ == "__main__":
    kind, k = sys.argv[1], int(sys.argv[2])
    gens = {"wide": wide, "chain": chain, "dupl": dupl,
            "renamed": renamed, "double": double,
            "double2": lambda k: double(k, 2), "refs": refs, "lets": lets,
            "refsz": lambda n: refs(n, False, True), "refsbz": lambda n: refs(n, True, True)}
    sys.stdout.write(gens[kind](k).out())
