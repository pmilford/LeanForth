#!/usr/bin/env python3
"""The typed-term trial of inference (plan task 4.2.2a; review rvD2A F1,
adapted from the reviewer's generator).

Random well-typed terms with lambda arguments under binders, dependent
lambda chains as arguments, polymorphic variables of types such as
(B : Type) -> B -> A and the constant id.{0} or id.{1}; a quarter are
mutated (one variable replaced by another in scope), so most of those are
ill typed. Each case runs through inference and the definition, theorem,
redex and wrong-claim probes of tests/support/infer-trial.fs. A simple
named-term model types every unmutated case; inference must give it,
outcome ok and exactly the model's type in canonical form, and the
definition probe of (that type, term) must be ok. The generator also
counts what it made (lambda arguments under binders, dependent ones,
chains), and the run fails when the counts fall below what makes the
trial meaningful.

Usage (from the repository root):
  GFORTH=... python3 tests/core/infer_typed_trial.py [--seed S] [--cases N]
      [--mode M] [--tree DIR] [--out FILE]
  python3 tests/core/infer_typed_trial.py --compare OLD NEW
MODE 0 (the default) gives ample fuel and room, and the model's types are
checked; 1 a random fuel below 3,000 per run, 2 a term store of the input
plus up to 120: then only that every case ran is checked. --tree runs the
cases in another tree (an old version, for an old-against-new
differential), --out keeps the run's lines; --compare compares two such
outputs: every run must be equal, except that a run exhausted or full in
either, or unknown in one and rejected in the other, may differ (the
rejection analysis stays unknown when it runs out of fuel or room).
Planted faults in tests/mutants/faults.toml calibrate it: each of
infer-chain-unclosed, infer-arg-unclosed, infer-domain-unclosed and
infer-abstract-innermost gives model mismatches here.
Test-only; needs Python 3 and Gforth. Prints a summary; exits 0 when all
checks hold, 1 otherwise.
"""
import argparse
import collections
import os
import pathlib
import random
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
GFORTH = os.environ.get("GFORTH", "gforth")
HARNESS = "tests/support/infer-trial.fs"
# Per 1,000 cases: below these counts the trial would not reach the chain
# closing and the argument closing it is there to test (seed 1 gives about
# 670, 500 and 140).
MIN_LAMBDA_ARGUMENTS = 400
MIN_DEPENDENT = 250
MIN_CHAINS = 70


class Gen:
    """Terms as tuples: ('S', level), ('V', name), ('C', 'id', level),
    ('A', f, a), ('L', name, domain, body), ('P', name, domain, body)."""

    def __init__(self, seed):
        self.rng = random.Random(seed)
        self.counter = 0
        self.ill = 0

    def fresh(self, prefix):
        self.counter += 1
        return f"{prefix}{self.counter}"

    # The model: free variables, substitution, alpha-equivalence, levels.
    @staticmethod
    def free(e, n):
        t = e[0]
        if t == 'V':
            return e[1] == n
        if t in ('S', 'C'):
            return False
        if t == 'A':
            return Gen.free(e[1], n) or Gen.free(e[2], n)
        return Gen.free(e[2], n) or (e[1] != n and Gen.free(e[3], n))

    @staticmethod
    def subst(e, n, v):
        t = e[0]
        if t == 'V':
            return v if e[1] == n else e
        if t in ('S', 'C'):
            return e
        if t == 'A':
            return ('A', Gen.subst(e[1], n, v), Gen.subst(e[2], n, v))
        if e[1] == n:
            return (t, e[1], Gen.subst(e[2], n, v), e[3])
        return (t, e[1], Gen.subst(e[2], n, v), Gen.subst(e[3], n, v))

    @staticmethod
    def aeq(a, b, m=None):
        m = m or {}
        if a[0] != b[0]:
            return False
        t = a[0]
        if t == 'S':
            return a[1] == b[1]
        if t == 'C':
            return a == b
        if t == 'V':
            return m.get(a[1], a[1]) == b[1]
        if t == 'A':
            return Gen.aeq(a[1], b[1], m) and Gen.aeq(a[2], b[2], m)
        m2 = dict(m)
        m2[a[1]] = b[1]
        return Gen.aeq(a[2], b[2], m) and Gen.aeq(a[3], b[3], m2)

    @staticmethod
    def kind(e, ctx):
        """The Sort level of type e in ctx (name -> type), or None."""
        t = e[0]
        if t == 'S':
            return e[1] + 1
        if t == 'V':
            ty = ctx[e[1]]
            return ty[1] if ty[0] == 'S' else None
        if t == 'P':
            ka = Gen.kind(e[2], ctx)
            inner = dict(ctx)
            inner[e[1]] = e[2]
            kb = Gen.kind(e[3], inner)
            if ka is None or kb is None:
                return None
            return 0 if kb == 0 else max(ka, kb)
        return None

    @staticmethod
    def tvars(ctx, level=None):
        return [n for n, t in ctx if t[0] == 'S' and (level is None or t[1] == level)]

    # Generation.
    def gen_type(self, ctx, budget):
        tv = self.tvars(ctx)
        r = self.rng.random()
        if budget <= 0 or r < 0.4:
            if tv:
                return ('V', self.rng.choice(tv))
            return ('S', self.rng.choice([0, 1]))
        if r < 0.8:
            return ('P', self.fresh('h'), self.gen_type(ctx, budget - 1),
                    self.gen_type(ctx, budget - 1))
        b, level = self.fresh('B'), self.rng.choice([0, 1, 1])
        inner = ctx + [(b, ('S', level))]
        return ('P', b, ('S', level), ('P', self.fresh('h'), ('V', b),
                                        self.gen_type(inner, budget - 1)))

    def spines(self, head_type, target, ctx, depth):
        """Ways of applying something of head_type to reach target: lists
        of ('type', T) and ('term', domain) arguments."""
        out = []
        if self.aeq(head_type, target):
            out.append([])
        if depth == 0 or head_type[0] != 'P':
            return out
        x, a, b = head_type[1], head_type[2], head_type[3]
        if a[0] == 'S' and self.free(b, x):
            cands = [('V', n) for n in self.tvars(ctx, a[1])]
            if self.kind(target, dict(ctx)) == a[1]:
                cands.append(target)
            self.rng.shuffle(cands)
            for t in cands[:3]:
                for rest in self.spines(self.subst(b, x, t), target, ctx, depth - 1):
                    out.append([('type', t)] + rest)
        elif not self.free(b, x):
            for rest in self.spines(b, target, ctx, depth - 1):
                out.append([('term', a)] + rest)
        return out

    def heads(self, ctx, target):
        hs = []
        for n, ty in ctx:
            if ty[0] != 'S':
                for sp in self.spines(ty, target, ctx, 4):
                    hs.append((('V', n), sp))
        k = self.kind(target, dict(ctx))
        if k in (0, 1) and self.rng.random() < 0.5:
            hs.append((('C', 'id', k), [('type', target), ('term', target)]))
        return hs

    def lam_for(self, ctx, target, budget):
        y = self.fresh('y')
        body_type = self.subst(target[3], target[1], ('V', y))
        return ('L', y, target[2], self.gen_term(ctx + [(y, target[2])], body_type,
                                                 budget - 1))

    def gen_term(self, ctx, target, budget):
        if target[0] == 'P' and (budget <= 0 or self.rng.random() < 0.45):
            return self.lam_for(ctx, target, budget)
        if target[0] == 'S':
            return self.gen_type(ctx, 1)
        hs = self.heads(ctx, target)
        if budget <= 0:
            nullary = [h for h in hs if not h[1]]
            if nullary or budget <= -2:
                hs = nullary
        if not hs:
            if target[0] == 'P':
                return self.lam_for(ctx, target, budget)
            self.ill += 1
            return ('V', self.rng.choice([n for n, _ in ctx]))
        e, spine = self.rng.choice(hs)
        for kind, a in spine:
            e = ('A', e, a if kind == 'type' else self.gen_term(ctx, a, budget - 1))
        return e

    def codomain(self, ctx, ty):
        cur = ty
        while cur[0] == 'P' and self.rng.random() < 0.7:
            x, a, b = cur[1], cur[2], cur[3]
            if a[0] == 'S' and self.free(b, x):
                tv = self.tvars(ctx, a[1])
                if not tv:
                    break
                cur = self.subst(b, x, ('V', self.rng.choice(tv)))
            elif not self.free(b, x):
                cur = b
            else:
                break
        return cur

    def mutate(self, e):
        """One variable leaf replaced by another variable in scope."""
        paths = []

        def walk(e, path, ctx):
            t = e[0]
            if t == 'V':
                paths.append((path, ctx))
            elif t == 'A':
                walk(e[1], path + [1], ctx)
                walk(e[2], path + [2], ctx)
            elif t in ('L', 'P'):
                walk(e[2], path + [2], ctx)
                walk(e[3], path + [3], ctx + [e[1]])
        walk(e, [], [])
        if not paths:
            return e
        path, ctx = self.rng.choice(paths)
        if not ctx:
            return e
        new = ('V', self.rng.choice(ctx))

        def put(e, path):
            if not path:
                return new
            parts = list(e)
            parts[path[0]] = put(e[path[0]], path[1:])
            return tuple(parts)
        return put(e, path)

    def case(self):
        """A closed term, its type in the model, and whether it was mutated."""
        self.ill = 0
        ctx = []
        for _ in range(self.rng.randint(1, 3)):
            ctx.append((self.fresh('A'), ('S', self.rng.choice([1, 1, 1, 0]))))
        for _ in range(self.rng.randint(1, 4)):
            ctx.append((self.fresh('x'), self.gen_type(ctx, 2)))
        xs = [ty for _, ty in ctx if ty[0] != 'S']
        if self.rng.random() < 0.7:
            target = self.codomain(ctx, self.rng.choice(xs))
        else:
            target = self.gen_type(ctx, 1)
        body = self.gen_term(ctx, target, 4)
        mutated = self.rng.random() < 0.25
        if mutated:
            body = self.mutate(body)
        mutated = mutated or self.ill > 0
        term, ty = body, target
        for n, d in reversed(ctx):
            term, ty = ('L', n, d, term), ('P', n, d, ty)
        return term, ty, mutated


# Forth code and canonical text of a term (de Bruijn indices).
LEVELS = {0: "z", 1: "s z", 2: "s s z"}


def forth(e, ctx):
    t = e[0]
    if t == 'S':
        return f"{e[1]} make-sort"
    if t == 'C':
        return f"{e[2]} idl"
    if t == 'V':
        return f"{ctx[::-1].index(e[1])} make-var"
    if t == 'A':
        return f"{forth(e[1], ctx)} {forth(e[2], ctx)} make-app"
    word = 'make-lam' if t == 'L' else 'make-pi'
    return f"{forth(e[2], ctx)} {forth(e[3], ctx + [e[1]])} {word}"


def canon(e, ctx):
    t = e[0]
    if t == 'S':
        return f"S {LEVELS[e[1]]}"
    if t == 'C':
        return "C"
    if t == 'V':
        return f"V {ctx[::-1].index(e[1])}"
    if t == 'A':
        return f"A {canon(e[1], ctx)} {canon(e[2], ctx)}"
    return f"{t} {canon(e[2], ctx)} {canon(e[3], ctx + [e[1]])}"


def depth(e):
    t = e[0]
    if t in ('S', 'V', 'C'):
        return 1
    if t == 'A':
        return 1 + max(depth(e[1]), depth(e[2]))
    return 1 + max(depth(e[2]), depth(e[3]))


def coverage(e, binders, counts):
    """Count lambda arguments under binders, those whose domain names an
    enclosing binder (dependent), and chains of two or more lambdas there."""
    t = e[0]
    if t == 'A':
        a = e[2]
        if a[0] == 'L' and binders:
            counts['lambda arguments'] += 1
            if any(Gen.free(a[2], n) for n in binders):
                counts['dependent'] += 1
            if a[3][0] == 'L':
                counts['chains'] += 1
        coverage(e[1], binders, counts)
        coverage(e[2], binders, counts)
    elif t in ('L', 'P'):
        coverage(e[2], binders, counts)
        coverage(e[3], binders + [e[1]], counts)


CLAIMS = ["1 make-sort", "0 make-sort 0 make-var 1 make-var make-pi make-pi",
          "1 make-sort 0 make-var 1 make-var make-pi make-pi", "2 make-sort"]


def cases(seed, n, mode):
    """The Forth text of n cases, the expected types of the unmutated ones,
    and the generator's counts."""
    gen = Gen(seed)
    lines, expected = [f"{mode} mode !"], {}
    counts = collections.Counter()
    k = 0
    while k < n:
        term, ty, mutated = gen.case()
        if depth(term) > 40:
            continue
        coverage(term, [], counts)
        counts['mutated'] += mutated
        if not mutated:
            expected[k] = canon(ty, [])
        claim = gen.rng.choice(CLAIMS)
        lines.append(f"{k} begin-case {forth(term, [])} {claim} run-case")
        k += 1
    lines.append("bye")
    return "\n".join(lines) + "\n", expected, counts


RUN = re.compile(r"(I|DI|TI|DB|DR) (\d+) (\d+) (\d+) (\d+) ?(.*)$")
NAMES = {'0': 'ok', '1': 'invalid', '2': 'exhausted', '3': 'unknown', '4': 'rejected',
         '5': 'unsupported', '6': 'full'}


def runs(text):
    """(kind, case) -> (outcome, code, mask, type) for every run line."""
    out = {}
    for line in text.splitlines():
        m = RUN.search(line.rstrip())
        if m:
            out[(m.group(1), int(m.group(2)))] = (m.group(3), m.group(4), m.group(5),
                                                   m.group(6).strip())
    return out


def run_tree(tree, text):
    with tempfile.TemporaryDirectory() as tmp:
        path = pathlib.Path(tmp) / "cases.fs"
        path.write_text(text)
        result = subprocess.run([GFORTH, str(tree / HARNESS), str(path)], cwd=tree,
                                stdin=subprocess.DEVNULL, capture_output=True, text=True,
                                timeout=1800)
    return result.returncode, result.stdout + result.stderr


def compare(old_path, new_path):
    old, new = runs(pathlib.Path(old_path).read_text()), runs(pathlib.Path(new_path).read_text())
    # A case whose inference ran out of fuel or room in either run has its
    # inferred-type probes in the other run only.
    ran_out = {k for (kind, k), v in list(old.items()) + list(new.items())
               if kind == 'I' and v[0] in '26'}
    classes, bad = collections.Counter(), []
    for key in sorted(set(old) | set(new)):
        a, b = old.get(key), new.get(key)
        if a == b:
            classes['same'] += 1
            continue
        if a is None or b is None:
            classes['in one only'] += 1
            if key[1] not in ran_out:
                bad.append((key, a, b))
            continue
        classes[(NAMES[a[0]], NAMES[b[0]])] += 1
        limited = a[0] in '26' or b[0] in '26' or {a[0], b[0]} == {'3', '4'}
        if not limited:
            bad.append((key, a, b))
    print(f"infer-typed-trial compare: {dict(classes)}")
    for key, a, b in bad[:10]:
        print(f"  NOT ALLOWED {key}: {a} against {b}")
    return 1 if bad else 0


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--cases", type=int, default=2000)
    parser.add_argument("--mode", type=int, default=0, choices=[0, 1, 2])
    parser.add_argument("--tree", default=str(ROOT))
    parser.add_argument("--out")
    parser.add_argument("--compare", nargs=2)
    args = parser.parse_args()
    if args.compare:
        return compare(*args.compare)
    text, expected, counts = cases(args.seed, args.cases, args.mode)
    status, output = run_tree(pathlib.Path(args.tree).resolve(), text)
    if args.out:
        pathlib.Path(args.out).write_text(output)
    got = runs(output)
    problems = []
    if status != 0:
        problems.append(f"Gforth exited {status}: {output[-400:]}")
    missing = [k for k in range(args.cases) if ('I', k) not in got]
    if missing:
        problems.append(f"{len(missing)} cases printed no inference, first {missing[:5]}")
    mismatches = 0
    if args.mode == 0:
        for k, want in expected.items():
            outcome, _, _, ty = got.get(('I', k), (None, None, None, None))
            definition = got.get(('DI', k), ('missing',))[0]
            if outcome != '0' or ty != want or definition != '0':
                mismatches += 1
                if mismatches <= 5:
                    problems.append(f"case {k}: outcome {outcome}, definition probe "
                                    f"{definition}\n    got  {ty}\n    want {want}")
        if mismatches:
            problems.append(f"{mismatches} of {len(expected)} well-typed cases differ "
                            "from the model")
        if args.cases >= 500:
            for name, per in (('lambda arguments', MIN_LAMBDA_ARGUMENTS),
                              ('dependent', MIN_DEPENDENT), ('chains', MIN_CHAINS)):
                least = per * args.cases // 1000
                if counts[name] < least:
                    problems.append(f"only {counts[name]} {name} (at least {least})")
    mix = collections.Counter(NAMES.get(v[0], v[0]) for (kind, _), v in got.items()
                              if kind == 'I')
    print(f"infer-typed-trial: seed {args.seed}, {args.cases} cases, mode {args.mode}; "
          f"{len(got)} runs; inference {dict(sorted(mix.items()))}; "
          f"{len(expected)} well typed, {mismatches} differing from the model; "
          f"{counts['lambda arguments']} lambda arguments under binders, "
          f"{counts['dependent']} dependent, {counts['chains']} chains")
    for p in problems:
        print(p)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
