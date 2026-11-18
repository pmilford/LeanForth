# MF: the front end on Mathlib

Design (2026-11-17), revised after its independent design review (2026-11-18, "ready after fixes", 12 findings, all
answered: section 11); nothing built. Plan rows: slice MF of [SIMP_DATA.md](SIMP_DATA.md) §8 (which `by-simp` on
Mathlib, `norm_num` and `ring` wait for), FE3 and FE4 of [PLAN_DRAFT.md](../project/PLAN_DRAFT.md). Numbers come from
the commands in [the measurement folder](../development/measurements/mathlib-front-2026-11-17/README.md) unless marked
*estimate* or credited to the performance scan (`PERFORMANCE_SCAN.md`, branch `perf-scan`). Runs used the front end of
branch `s2-finish-2` (`cb12814d`), since merged; file references are to `main` (`b403ac21`). Appendices: A
measurements, B fixed sizes, C Lean source notes.

## For the owner (one page)

**What.** Today a user can write a theorem about natural numbers in LeanForth and have it checked against Lean's
`Init` (done check 2026-11-14-s1). MF makes the same command work against all of Mathlib, so that a statement about
real numbers can be written and checked:

    bin/leanforth check --snapshot mathlib.lfsnap --elab-data mathlib.elab.ndjson real.lf

The kernel side is ready (all 729,263 Mathlib declarations checked, snapshot saved). The front end had never run on it.

**What happened when we tried** (the saved Mathlib snapshot, Mathlib's elaboration data, the theorem `0 + 0 = 0`):

1. The data tool cannot write Mathlib's data whole: 11 of 1,844 "smart unfolding" bodies carry markers the format has
   no word for. (Stepped around for the test by leaving those 11 out.)
2. The reader refuses the data: Mathlib makes `instHSMul` a default instance a second time, which the reader takes
   for corruption. Lean keeps both. (Stepped around by deleting the repeat from a copy.)
3. The first instance question then ran 42 minutes without an answer and was stopped. The performance scan shows
   why: the front end's store of names checks all its entries on every new name, which grows with the square of the
   names met. A branch now in progress (`names-index`) fixes that; the run will be repeated on it.
4. A check that succeeds (a text in the low-level form) takes 294 s and 9.6 GB in all; Lean imports all of Mathlib in
   4-8 s (6.9 GB). About a minute of the 294 s is taking the snapshot's 729,263 results, which a text about real
   numbers mostly does not need.

**On a small cut of Mathlib** (4,906 declarations: real numbers, `add_zero`, `add_comm` and what they need), with
step 2 stepped around: `0 + 0 = 0` and `0 + n = n` are accepted, and so is the first statement about real numbers
written in LeanForth, `x + 0 = x + 0` by `rfl` (axioms `propext`, `Classical.choice`, `Quot.sound`, as Lean reports).
`exact add_zero x` and `rw [add_comm]` stop with "not supported yet": where exactly is the first job of MF3a.

**The plan.** Five slices, each ending in a command: MF1 Mathlib's data loads; MF2 instance records checked when
first needed (after `names-index`); MFR a text's run takes only the snapshot results it reaches; MF3a `x + 0 = x` by
`exact add_zero x`; MF3b `x + y = y + x` by `rw [add_comm]`. About 2,600-3,600 lines of Forth in all (*estimate*;
MF3a and MF3b are sized again once MF3a has found where the proof stops). Faster loading is its own later design.

**Trust.** Everything here is untrusted front-end work except MFR, which changes how the checker takes the snapshot's
results ([kernel] gate). The kernel checks every finished term against the snapshot it loaded itself: a wrong data
record or instance can only make a proof fail, take another route than Lean, or be refused by the kernel.

**Questions** (section 9): (1) data format 3.1; (2) instance records checked when first needed; (3) the theorems Lean
makes on demand, added later as a snapshot layer; (4) loading: profile first, then propose; (5) when to run the
full-Mathlib test. *Recommendation: yes to each, as worded there.*

## 1. Where things are (measured, appendix A)

| | Mathlib | `Init` |
| --- | ---: | ---: |
| export (`.tools/mathlib/mathlib.ndjson`; manifest in `.claude/work/IM/`, not beside it) | 6.26 GB | 346 MB |
| snapshot (`.claude/work/overnight/mathlib-d789e45f.lfsnap`, verdict version 9) | 2.30 GB | 133 MB |
| format-3 elaboration data (format 4: Mathlib 113 MB) | 45.5 MB | 3.7 MB |
| instance records / classes with instances / default instances | 43,808 / 2,311 / 52 | 2,938 / 277 / 34 |
| successful `check --snapshot … --elab-data …` of a kernel-form text (whole command) | 294 s, 9.61 GB | 17 s, 617 MB |
| … of `0 + 0 = 0` by `by-rfl` | no answer in 42 min, 4.8 GB | 112 s, 635 MB |
| … of `0 + 0 = 0` on the Mathlib slice (4,906 declarations, `--env`, no snapshot) | 47 s, 75 MB, accepted | — |
| pinned Lean: `import Mathlib` and one proof | 4.1-7.6 s, 6.9 GB | — |

A snapshot run binds the data by the export's SHA-256 in the data's header (`check-lf.fs`, `lfc-export-sha`). Mathlib's
manifest names no data (no `elab_records_sha256`), so a full-mode run (`--env mathlib.ndjson`) would read it unbound:
MF1 binds it.

## 2. The obstacles, in the order met

**O1. Format 3 cannot say 11 smart-unfolding bodies** (`export_elab.py`). Ten carry metadata: `save_info` (8; the
elaborator's mark on a postponed metavariable so editor information is kept, `mkSaveInfoAnnotation`,
TermElabM.lean:1495), `noImplicitLambda` (1; "add no `fun` here", :1735-1741) and a private marker of Mathlib's
`TermCongr` (1, `GradedMonoid.GMonoid.gnpowRec`). One has an anonymous binder name
(`Mathlib.Tactic.Ring.ExProd.evalIntCast`): a binder name, not metadata. Lean's `whnfEasyCases` steps through
metadata (WHNF.lean:396), but its `isDefEqQuick` keeps it (ExprDefEq.lean:1993-2023), smart unfolding's `go` keeps it
(WHNF.lean:729-733), and type inference passes it on (InferType.lean:248), so carrying it faithfully touches many
walkers. None of the 11 bodies is on MF's path. **Fix (MF1, format 3.1, [format]):** the tool writes these three
metadata keys, and only these, as an `inert` node, and the empty name for a binder; a file using either says format
3.1 in its header. The Forth reader enforces the same allowlist (any other key, including S2's `sunfoldMatch` and
`sunfoldMatchAlt`, Lean's `noindex`, `inaccessible`, `patternWithRef` or `let_fun` written as inert, refuses the
file) and decodes an inert node into the annotation node of `core/annotations.fs` (S2's tag 17) with a new key,
`lf-annot-inert`, that **every** walker answers unsupported on: whnf does not strip it, `wc-arg-marked?`
(`whnf.fs:715`) and `infer.fs:138` answer unsupported, the hand-over refuses it (error 200, its text reworded from
"a smart-unfolding marker" to "a marker"). So a body holding one is unusable, never wrong; carrying it as Lean does
waits for a theorem that needs it. Test fixture: a slice whose root is `GradedMonoid.GMonoid.gnpowRec` (slice B's 28
bodies hold none of the 11). Size: tool 60 lines of Python, reader 80, annotations 30.

**O2. A repeated default instance refused** (`elab-data.fs:353`, error 16, run 1). Lean conses each
`default_instance` attribute onto its class's list (`addDefaultInstanceEntry`, Instances.lean:390-394; its priority
set removes repeated priorities only), and `synthesizeUsingDefaultPrio` walks the list (SyntheticMVars.lean:119-125):
`instHSMul` (Init/Prelude.lean:1816-1817 and Mathlib's Algebra/Notation/Defs.lean:72, both 1000) is tried twice, the
second a no-op after the first's rollback. **Fix (MF1):** accept a repeated (class, instance) at another rank and keep
both cells in `lf-default-instances`; still refuse a repeated rank; any lookup of a default instance by name accepts
two cells. 20 lines.

**O3. The first instance question ran 42 minutes** (run 2, stopped; `lf-inst-classes`, `instances.fs:333-344`, which
checks every record's class before any search, FE1E §4 "When"). The performance scan measured the same pass on
`Init`: 82% of a `.lf` check is the name store, not the instance checks: 69% the stored-mode audit of every name
entry on every new name (`core/names.fs:147-150`, A1) and 12% linear name finds (`:166-171`, A2); the checks
themselves cost about 1.3 s for 2,938 records (0.44 ms each). The cost grows with the square of the names decoded,
hours on Mathlib. **Fix, first:** branch `names-index` (in progress; A1 and A2). Then the eager pass would take
about 20-60 s on Mathlib (*estimate*: 43,808 × 0.44 ms plus the root index). **Fix, then (MF2):** check lazily
(section 3), with the root lookup (`it-root-index`, `instances.fs:321`, linear over 2,311 roots: about 51 million key
comparisons to build) in a `lib/htab.fs` table. MF2 starts by repeating run 2 on `names-index`'s head; its size is
fixed by that run.

**O4. A successful Mathlib run is slow and large** (run 3: 294 s, 9.61 GB in all). Known parts (performance scan):
the snapshot's hash and re-interning (K4, about 100 s *estimate*), taking all 729,263 results (`ck-import-pass`,
`check-run.fs:862-871`, K2: 66.7 s recorded) and printing them. **Fix:** MFR takes and reports only the results the
text reaches ([kernel], section 8); the load itself goes to a later design (question 4).

**O5. The target proofs stop** (slice B, runs 15 and 16): `exact add_zero x` with error 139 raised at `add_zero`
(9:63), the catch-all "an elaboration step" (`errors.fs:178`), so possibly while elaborating the application rather
than in `exact`'s unification; `rw [add_comm]` with error 93. Lean's traces (`mf-defeq.out`, 344 lines): `exact`
unifies at default transparency, unfolding `HAdd.hAdd`, `Add.add`, `OfNat.ofNat`, `Zero.zero` on both sides and
reducing the instance chains (`AddZeroClass.toAdd`, `AddMonoid.toAdd`, `Real.instAdd`) by whnfCore; `rw` unifies at
instances transparency, raised to implicit, and needs `isDefEqProjInst` once `?inst` is synthesized (`AddCommMagma ℝ
=?= AddCommMagma ?m`, then `unfoldRight AddCommMagma.toAdd`). **Already on main:** `unfoldProjInst?` and
`whnfCoreUnfoldingAnyInstances` (`unfold.fs:133-150`), `packedInstanceOf?` (`defeq-delta.fs:135`), `isDefEqArgs`'s
`trySynthPending` for instance arguments (`defeq.fs:418-425`, Lean 453-455). **Still unsupported:** `isDefEqProj` on
projection nodes (`defeq.fs:925`; Lean 2263, `lazyProjDelta` on by default), `isDefEqProjInst` (`defeq.fs:762-765`;
Lean 2356), structure eta with fields (`:797`), `unstuckMVar`'s retry (`:428`). **Fix:** MF3a pins the stop, then
ports what `real_add_zero` needs; MF3b what `rw [add_comm]` needs.

**O6. `open Real`** (`author/namespaces.fs:7-10`): a namespace is known only when the text enters it or declares a
name in it. Lean registers every non-internal prefix of every declaration's name (AddDecl.lean:54-66), so the export
gives all of Mathlib's namespaces except those of empty `namespace` blocks; a tool record of `env.getNamespaces`
(42,379, `mf-namespaces.out`) is exact. **Fix:** FE2's namespace work, a `lib/htab.fs` set; MF's target writes full
names.

**O7. Unification hints.** Mathlib has 27 `unif_hint`s, all in category theory; `defeq.fs:72-79` handles a hint
correctly only when it is keyed at a definition, which answers unsupported (the samples, `Prefunctor.obj` and
`Quiver.Hom`, are). MF1 lists the 27 keys in the data's documentation and a test pins that each answers unsupported;
a hint table in the data waits for a theorem that needs one. (Measured in MF1, 2026-11-18: one hint is keyed at a
definition, `Shrink`, and 26 at a projection, since Lean keys a hint's side reduced at reducible transparency;
`defeq.fs` now answers unsupported at a projection head too, [ELABORATION_DATA.md](../programming/ELABORATION_DATA.md#unification-hints-not-in-the-data).)

**Not obstacles:** the name lookup `.lf` text uses (`groups.fs:253`, `lfa-const-named`) asks the text's own wordlist,
then the tier's hashed name table (`compact-names.fs`); only the text's own declaration list (`constants.fs:42`) is
searched linearly, and it grows with the text, not with Mathlib. Appendix B lists every fixed size checked.

## 3. MF2's rule: instance records checked when first needed

- **Step 1** (the class recomputed from the instance's type) runs on every record of a root before that root's tree is
  built; **step 2** (the keys recomputed) is already run there (`instances.fs:362-364`, `400-420`). **Step 3** (a
  default instance's class) runs on every default instance of a class before `lf-default-instances` returns its list.
  So every candidate a search can be given has been checked. Results stay in the `it-status` and `it-dstatus` slabs
  (no new table).
- **What is lost:** a record filed under a wrong root or class, under a root no one asks, is never found. It can only
  be missing where it belongs: a search fails or takes another route, and the kernel checks the result. The eager
  pass never caught a record missing from its class either, and Lean checks none of this (imported instances are
  trusted; their keys are never recomputed).
- **A refusal after earlier success.** A check that finds a difference refuses the data for the rest of the run, as
  today. Within one run the text then stops: exit 4, the data error with the refused record's name, and no
  declaration of the text reported accepted (a text that stops is not checked at all, `COMMAND_LINE.md`). Theorems
  accepted in earlier runs stand: the kernel checked them; the data only chose the route. Test: slice data with a
  record planted under the root the second theorem queries: the file exits 4 naming it; the first theorem alone
  exits 0.

## 4. The export question (simp design question 2): decided with SP2b, not MF

The theorems Lean makes on demand (28,592 for Mathlib, at most 134 MB) are needed by `simp` (SP2b, SP4), not by MF.
When the next export is made: (1) the exporter keeps the listed internal names ([import]); (2) re-export (6.5 min, 14
GB); (3) check it as a layer on today's snapshot (`check --snapshot mathlib.lfsnap --save-snapshot layer.lfsnap
NEW.ndjson`; *estimate* 10-20 minutes, against 3-4 hours from scratch); (4) its data; (5) the done check. Sound under
the approved layer rules (ADR 0020 Amendment 1, F5) if: declarations equal in content are taken and their lookups
replayed (R4 C1, C5); the kernel checks the new theorems and every base declaration whose saved lookups now answer
differently; each added name brings its dependencies (an unknown reference is refused); the data binds to the pair
(base identity, layer's export SHA-256) only for that base with that one layer, the layer's run having taken every
base declaration, any other stack refused (`COMMAND_LINE.md:238-240` extended).

## 5. Type classes on Mathlib: what FE3 must give first

From Lean's `pp.all` term and traces (`mf-real.out`, `mf-synth.out`):

| Need | Lean | Today | For MF |
| --- | --- | --- | --- |
| tabled search, Lean's order | `synthInstance?` | works (`synth.fs`; slice B: the target's searches succeed) | after O3, nothing more: searches are 1-3 deep, one candidate tried each |
| numerals | `0 : ℝ` is `@OfNat.ofNat ℝ 0 (@Zero.toOfNat0 ℝ Real.instZero)`; `2 : ℝ` needs `instOfNatAtLeastTwo` | works for `0 : ℝ` (run 14) | `2` and up in S8a1 |
| `binop%` | `x + 0` with the max type `ℝ` | works (run 14) | — |
| default instances | `instHAdd`, `instHSMul` twice | read | O2 |
| instance diamonds | `isDefEqProj`, `isDefEqProjInst`, structure eta | part (O5) | MF3a, MF3b |
| coercions (FE4) | `↑n : ℝ` | none | after MF |
| `class`/`instance` in text | — | none | not needed to state theorems about `ℝ` |

## 6. Measuring, and the Mathlib slice fixture

Every slice reports the **whole command's** wall time and peak memory on all of Mathlib, beside the baseline of run 3
(294 s, 9.61 GB, successful). Targets: MF2, the first instance question's pass under 10 s (measured from
`--resources`), the whole command at most run 3's; MFR, the results step under 5 s for a text that reaches about
5,000 declarations; MF3a/b, each further theorem like the target under 5 s. A load target waits for question 4.

**The slice fixture** keeps the tiers off all of Mathlib. It is cut at test time by `scripts/export-slice.py` from the
machine's export (every machine that runs tiers has it) with a committed root list, then `export_elab.py` with
Mathlib's RAW, then one snapshot of the slice per test run (performance scan A11), so each test file checks in
seconds, not 47 s. It is cached under `.claude/work/` keyed by (export SHA-256, root list, script SHA-256); the
script, the root list and the expected SHA-256s are committed, the 17.6 MB slice is not (MF3 will change the roots;
each committed version would stay in history). Measured: slice B, 4,906 declarations, cut in 346 s (1.6 GB), data in
5 s. The roots must include, for each search with an unknown type (`OfNat ?α 0`, `HAdd ?α ?β ?γ`, `Add ?α`), the
candidate Lean's order tries first (`Lean.Grind.CommRing.OfCommSemiring.instOfNatQ`, `Std.Time.WallTime.instHAddOffset_1`,
`…instAddQ`): without them slice A stopped with error 119 (run 11), as S1's `Init` slice once did. A run on all of
Mathlib is the done check of each MF slice (question 5).

## 7. Trust and gates, in plain language

All MF code is untrusted except MFR's change to how results are taken. The kernel checks every finished term against
declarations it read and checked itself; the axiom report lists `propext`, `Classical.choice` and `Quot.sound` for the
target, as Lean's `#print axioms`. So a wrong or missing data record, an instance record checked late, or an inert
marker can make a proof fail, take another route or be refused, never accepted wrongly. The front end never writes the
snapshot (S1 note B1's allowlist test stays). Gates: **[format]** MF1's format 3.1 (and section 4's layer binding);
**[kernel]** MFR; **[import]** section 4's exporter; **[parser]** every slice (terms node for node pinned Lean's). No
new axiom. The later load design carries [kernel], [format] and [import].

## 8. Slices

Each ends in a command, has its tests (seven classes, planted faults) and documentation in the slice, and fits one
agent. Sizes are lines of Forth with tests (*estimates*).

| Slice | Command at the end | Contains | Forth | Needs |
| --- | --- | --- | ---: | --- |
| MF1 | `scripts/export-elab.sh mathlib.elab.ndjson mathlib.ndjson Mathlib` exits 0 (format 3.1); `check --snapshot mathlib.lfsnap --elab-data mathlib.elab.ndjson tests/author/01-identity.lf` exits 0 | O1 (inert marker, allowlist in Forth, anonymous binder), O2, O7's list, the manifest binding, the fixture script and roots | 400 (+200 Python) | [format] |
| MF2 | `check --snapshot … --elab-data … tests/front/s1-rfl.lf` and `03-zero-add-exact.lf` on all of Mathlib: accepted, terms equal to Lean's, the pass under 10 s | run 2 repeated on `names-index`; section 3's rule and its refusal test; root `htab` | 300 | MF1, `names-index` |
| MFR | the same runs report only the text's declarations, results step under 5 s | take and report only the snapshot results the text reaches (`ck-import-pass`) | 300 | MF2, [kernel] |
| MF3a | `check …` of `mf-real.lf`'s first theorem: `real_add_zero` accepted, term node for node Lean's; its wrong twin (`x + 1 = x`) exits 4 with Lean's "Type mismatch" text | first pins the stop (`lf-delta-unfolded` hook, `--steps`, against `mf-defeq.out`), then ports what it needs (O5) | 800-1,500 | MF2, the fix batch |
| MF3b | `check … mf-real.lf`: `real_add_comm` too | `isDefEqProjInst` and what `rw` needs (O5) | 800-1,500 | MF3a, plug-in (a2) |

**What can start now:** MF1 (no dependency besides the gate). **Chains:** `names-index → MF2 → MFR`, `MF2 → MF3a →
MF3b`; SIMP_DATA's `MF → S8a1` becomes `MF3a → S8a1`, and `SP2b + MF3b → SP4`.

**Acceptance target** (MF3a and MF3b's done checks), in three forms:

| | |
| --- | --- |
| Mathematics | for every real number $x$, $x + 0 = x$; for all real $x, y$, $x + y = y + x$ |
| LeanForth | `theorem real_add_zero Real explicit: x   x 0 + x =   := by  x add_zero by-exact  end real_add_zero` and `theorem real_add_comm Real explicit: x  Real explicit: y   x y + y x + =   := by  by-rw[ ' add_comm ]  end real_add_comm` |
| Lean | `theorem real_add_zero (x : ℝ) : x + 0 = x := by exact add_zero x` and `theorem real_add_comm (x y : ℝ) : x + y = y + x := by rw [add_comm]` |

Pinned Lean 4.35.0 on pinned Mathlib: `mf-real.lean` exit 0 (1.3 s), `mf-real-wrong.lean` exit 1 with "Type mismatch"
(measurement folder, with `mf-real.lf`).

## 9. Questions for the owner

1. **Data format 3.1 ([format]):** accept a default instance named twice and an unnamed binder, as Lean does; and
   write three kinds of harmless metadata into the data, read as a marker the front end refuses to use? *Recommendation:
   yes.* Mathlib's data then loads whole; nothing can come out different from Lean, because a body holding a marker
   is simply not used, and none of the 11 is needed for MF.
2. **Check instance records when first needed, after `names-index` lands** (each class's records before its first
   search, each class's default instances before they are used)? *Recommendation: yes.* Every record a search can use
   is still checked first (Lean checks none); a wrong record nobody asks about can only make a search fail.
3. **The theorems Lean makes on demand: add them at the next Mathlib export and check that export as a layer on
   today's snapshot, under section 4's conditions** ([import], [format])? *Recommendation: yes, decided with SP2b,*
   which needs them; the kernel still checks each new theorem, and it saves about 3 hours of re-checking.
4. **Loading Mathlib:** instead of a target now, let a later design profile a successful Mathlib check and then propose
   a target and the snapshot or kernel changes it needs, or a server mode that keeps the library loaded?
   *Recommendation: yes.* A successful run takes 294 s and 9.6 GB today, hashing the snapshot alone about 30 s; the
   right fix depends on the profile.
5. **A full-Mathlib front-end test** (`make mathlib-front`, about 5-10 minutes *estimate*): you decided "no automatic
   Mathlib run". Run it only as the done check of each MF slice, by hand, never on a schedule? *Recommendation: yes;*
   the tiers use the slice fixture.

## 10. Reuse, and work in flight

**Reuse:** `lib/htab.fs` (root keys; later the namespace set), the `it-status`/`it-dstatus` slabs (check results),
`lib/slab.fs`, `lib/sha256.fs`, `lib/json.fs`, `lib/sort.fs`; `core/annotations.fs` (one more key); `lib-decode.fs`,
`meta-env.fs`, `whnf.fs`, `unfold.fs`, `defeq.fs`, `defeq-delta.fs`, `fun-info.fs`, `meta-config.fs`, `instances.fs`,
`synth.fs`; on the tool side `export_elab.py`'s shape checks and `scripts/export-slice.py`. **Replaced:** the linear
`it-root-index` by an `htab`; the eager pass by section 3's rule. **New general words:** none.

**Work in flight, in order:** `names-index` (core/names.fs; before MF2); the fix batch from the whole-code reviews
(`rw` and elaboration differences in the same files; before MF3a); plug-in slice (a2) and the architecture review's
app-builder and telescope files (`instances.fs`'s `lf-inst-telescope` is one of the copies; before MF3b); SP1a's
`discr-tree.fs` move out of `instances.fs`, which should also fix the performance scan's A5 (child lists walked
sibling by sibling; Mathlib roots hold up to 3,594 records), MF2 rebasing onto it if it lands first; snapshot c6-c8
(format 2), which the later load design depends on. MF1 touches `elab-data.fs`, `core/annotations.fs` and the tool;
SP1a's reader changes `elab-data.fs` too: MF1 is small and goes first.

## 11. Review

The review (2026-11-18, `.claude/work/pending-reports/2026-11-18-mathlib-front-design-review.md`) made 12 findings;
all were taken as proposed.

| # | Finding | Answered in |
| --- | --- | --- |
| 1 | targets from a run that stops at its first token (blocking) | §1 run 3 as baseline; O4; §6 whole-command numbers; MFR slice with [kernel]; Q4 |
| 2 | O3's cause is the name store (blocking) | owner page 3; O3; MF2 needs `names-index`, repeats run 2; "tenfold" dropped |
| 3 | MF2's safety rule, refusal after success | §3; MF2 row |
| 4 | inert annotation: not stripped in defeq, more walkers, allowlist in Forth, format 3.1, binder not mdata | O1; MF1 row; Q1 |
| 5 | O2 correct | O2 (the name lookup with two cells added) |
| 6 | O5 out of date, not pinned; split MF3 | O5; MF3a, MF3b |
| 7 | MF4 not a front-end slice | O4; Q4; §7 gates |
| 8 | work in flight; files on main | header; §10 |
| 9 | unification hints | O7 |
| 10 | namespaces wording | O6 |
| 11 | nightly Mathlib run against the owner's decision | §6; Q5 |
| 12 | sizes inconsistent | §8 (O3 gives none) |

Also from the review: the fixture cut at test time and cached (§6), the layer conditions (§4).

## Appendix A. Measurements

[The measurement folder's README](../development/measurements/mathlib-front-2026-11-17/README.md) has every command,
input path, hash and result (runs 1-16), the Lean files and their outputs.

## Appendix B. Fixed sizes checked (main `b403ac21`)

| Where | Value | Init needs | Mathlib needs | Verdict |
| --- | ---: | ---: | ---: | --- |
| `front/elab-data.fs:191` longest data line | 1 MiB | 11,219 B | 137,535 B | fits |
| `front/elab-data.fs:193` JSON tokens per line | 65,536 | — | about 28,600 | fits |
| `front/elab-data.fs:192` nesting depth | 8 | 8 | 8 (the format's) | fits |
| `front/elab-data.fs:896` default-instance rank | 65,535 | 34 | 52 | fits |
| `front/instances.fs:321` root lookup | linear | 277 roots | 2,311 roots | MF2 |
| `front/instances.fs:333-344` the pass | every record | 2,938 | 43,808 | MF2 |
| `core/names.fs:147-150, 166-171` name audit and finds | every entry per name | 26,701 names (scan) | quadratic | `names-index` |
| `front/synth.fs:111` `synthInstance.maxSize` | 128 | — | Lean's own | same as Lean |
| `front/lib-decode.fs:625` memo | one cell per tier declaration | 59,349 | 729,263 (5.8 MB) | fits |
| `defeq.fs:126`, `whnf.fs:124`, `tactic-run.fs:139`, `meta-config.fs:65` fuel | 1 M, 100 k, 100 k, 100 M | fits | unknown | measured in MF3a |
| `author/groups.fs:60` entries per text | 1,024 | per text | per text | fits |
| `author/namespaces.fs:46` bytes per name text | 256 | — | up to 235 B in the data (export unmeasured) | MF1 measures |
| `author/namespaces.fs:60` namespaces known | 1,024, the text's | — | 42,379 in the library | O6 |
| `author/constants.fs:42` text declarations | linear | per text | per text | fits |

## Appendix C. Lean source notes

Lean 4.35.0, `src/lean/Lean/`: `Meta/Instances.lean` `addDefaultInstanceEntry` 390-394, `getDefaultInstances` 432;
`Elab/SyntheticMVars.lean` `synthesizeUsingDefaultPrio` 119-125; `Elab/Term/TermElabM.lean` `mkSaveInfoAnnotation`
1495, `noImplicitLambda` 1735-1741; `Expr.lean` `mkAnnotation` 2090; `Meta/WHNF.lean` `whnfEasyCases` `.mdata` 396,
smart unfolding's `go` 729-733, `unfoldProjInst?` 766; `Meta/InferType.lean` 248; `Meta/ExprDefEq.lean`
`isDefEqQuick` 1993-2023, `isDefEqProj` 2263, `isDefEqProjInst` 2356, `isDefEqArgs` 453-455; `AddDecl.lean`
namespaces 54-66; `Namespace.lean` `isNamespace` 61. Mathlib `Algebra/Notation/Defs.lean:72`; Init
`Prelude.lean:1816-1817`.
