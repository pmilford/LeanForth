# S1 interface note: what the four S1 branches share

Plan slice S1 ([PLAN_DRAFT.md](../project/PLAN_DRAFT.md#phase-8-slices-owner-2026-11-13)). Status (2026-11-13):
**designed**; its re-check (2026-11-13, in the [review](../development/design-reviews/2026-11-13-front-end.md)) found R1, R2 and
M-a to M-d, fixed here. It settles B1-B5 and M1-M5 of the
[front-end design review](../development/design-reviews/2026-11-13-front-end.md) and cuts S1 into branches. Where
[FRONT_END.md](FRONT_END.md), [ADR 0021](../adr/0021-front-end.md), [FE1E_APPLICATIONS.md](FE1E_APPLICATIONS.md) or
[FE1G_TACTICS.md](FE1G_TACTICS.md) differ from it, this note wins; their trims are a later task. Lean references are to
pinned Lean 4.35.0's `src/lean/Lean/`.

## For the owner (one page)

**What S1 delivers.** You write in LeanForth `theorem t   0 0 + 0 =   := by   by-rfl   end t` (Lean: `theorem t :
0 + 0 = 0 := by rfl`) and run `bin/leanforth check --snapshot init.lfsnap --elab-data init.elab.ndjson t.lf`. LeanForth
works out, as Lean does, that `0` is the natural number zero and `+` natural-number addition, finding them in Lean's
instance tables in Lean's order; builds the proof term Lean builds (`@Eq.refl.{1} Nat (0 + 0)`); and its kernel checks
it: `t: accepted; axioms: none`, with no Lean in the run. `0 + 0 = 1` stops at `by-rfl` with Lean's message ("Tactic
`rfl` failed ..."), and nothing is checked. This is the first proof term LeanForth builds itself; the kernel stays the
only judge.

**Decisions** (each copies Lean; details in §1-§11):
1. While a file runs, the front end reads the library where the importer already holds it, read-only. What it builds
   on the way is thrown away; only the finished declaration reaches the kernel, by today's route.
2. Lean's "stuck, try again later" signal is ported exactly and never leaves the reasoning layer. Lazy unfolding moves
   to S2: S1's proof does not use it.
3. One undo mechanism serves instance search (which jumps between saved states) and tactics (which undo the last try).
4. Whether an argument is implicit or explicit is read from the declaration's own type or the hypothesis's own record,
   never from a shared copy. We count where Lean's export and Lean disagree, over all of Init and on the declarations
   S1 reads (target 0); a disagreement answers "not supported yet", never a guess.
5. Error numbers are allocated now, each branch its own range, so branches never collide.
6. A declaration is read whole and elaborated at `end NAME`, in Lean's order (the rule that was built).
7. The last branch owns the glue from statement to finished statement (where the type of `0` gets settled).
8. The front end gets its own work limit, `--elab-fuel N`; `--fuel N` stays the kernel's.
9. A missing or unchecked instance stops a search only when the search actually tries it. We measure first.
10. `by-exact` compares types as Lean's tactic does, with no automatic conversion.

**How it is built.** Four branches. `fe1g3` (the tactic runner, written) merges first. Then `s1-meta` (library access and
the unifier's missing pieces) and `s1-synth` (instance search) run in parallel. `s1-elab` (the statement, `#check`, the
S1 files) comes last. Midpoint you can run: a file with `0 0 + 0 = #check` prints `0 + 0 = 0 : Prop`.

**Gates.** [import] (decision 1, and binding the instance data to the export) when `s1-meta` and `s1-synth` merge.
[parser] (what numerals, `+`, `=` and instances mean, compared node for node with pinned Lean) and [bypass] (a wrong
term rejected by the kernel, a hole refused, an open goal stopping the text) at S1's end. There is no kernel change.

**Questions for you** (§12): the fuel flag's name (recommended `--elab-fuel`); the midpoint (recommended: accept it as
shown, not as "done"); the spelling of `sorry` (recommended: `by-sorry` as the tactic now, the term `sorry` in S5).

## 1. Environment route (B1)

While a `.lf` file runs, the Meta layer sees, as Lean's `getConstInfo` does, the library (the export's or snapshot's
tier that the importer stage holds, read and not sealed, `cli/check-lf.fs`) and the text's earlier declarations, each
added at its hand-over as Lean's `addDecl` makes a declaration visible to the next (Elab/MutualDef.lean).
`front/meta-env.fs` gets a run mode: `lf-menv-library! ( stage -- )` (0: none), bound by `cli/check-lf.fs` once the
library and its elaboration data are read, and `lf-menv-add ( decl -- outcome )` at each hand-over (`handover.fs`). A
handle is the stage's declaration number (the elaboration data's too) or the stage's count plus i for the text's i-th;
`lf-menv-find`, `-type`, `-value`, `-params`, `-kind`, `-hint`, `-status` answer in both modes; the fed mode
(`lf-menv-stage!`) stays for tests and plan 8.2.1g. The new `front/lib-decode.fs` decodes a library declaration (type,
value, recursor data) from the tier into the run's stores when `lf-menv-find` first meets it, memoized per run; names
cross by content, as `lfc-name` does. All Meta files read declarations through meta-env (`whnf.fs`, `infer.fs`,
`defeq.fs`, `meta-spine.fs` read `core/input.fs` today). **Resets:** `lfc-empty` also resets lib-decode's memo,
`lf-menv`'s text list and run mode, and the metavariable context and views, so a second text, the tests or an
`lfc-library-open` session never meet stale handles; lib-decode never enters `lfa-declarations`, so a kernel-form text
written whole never writes decoded library records. Rejected: feeding the library first (the text's records must
join the stage before sealing, ADR 0017 Amendment 2: a second library read).

**Trust ([import], [bypass]).** (1) `front/` calls only a stage's read-only words, never one that writes, extends, seals
or feeds it; a test holds `front/`'s `import/` words to an allowlist. (2) What it decodes or builds stays in the run's
scratch, which `lfc-empty` empties before sealing; only the hand-over's records reach the kernel, read like any
export's, and the writer refuses a metavariable (D2). (3) In a context with a fed input (tests; later 8.2.1e and
8.2.1g) it writes only above the input marks: every front-end test asserts `lf-input-intact?`, and a planted fault
writing below is caught. (4) The kernel checks against declarations it reads itself, so a wrong decode changes only the
elaborated term: the kernel guards validity, the [parser] comparisons guard meaning (D4). (5) **D13 amended**
(s1-meta): "`front/` may read a stage through `import/stage.fs`'s read-only words, as `meta-env.fs` and `elab-data.fs`
already do; only `cli/` drives the record route."

## 2. The stuck signal and FE1e0 (B2)

`lf-meta-stuck` (new `front/meta-config.fs`; value 16, outside ADR 0008's 0-6, so `outcome-sane` makes it invalid) is
Lean's `isDefEqStuck` (Meta/Basic.lean:33, 652). It is raised only under the isDefEqStuckEx bit, at Lean's sites:
LevelDefEq.lean:169 (`level-defeq.fs:28-33` answers false today), ExprDefEq.lean:2118 and 2182 (`defeq.fs:685-688` and
`349-351` answer unsupported today) and DiscrTree/Main.lean:359-397 (s1-synth's `discr-keys.fs`). It is caught only
where Lean catches it: `isDefEqAppFallback` (ExprDefEq.lean:2401: restore, try the late cases, raise again);
`isDefEqGuarded` (Basic.lean:2546) as the new `lf-meta-defeq-guarded ( t s -- flag outcome )`, false for this code only
(LeanForth's own unsupported, exhausted and full pass on); `trySynthInstance` (undef), `synthInstance` ("failed to
synthesize") and `synthPendingImp` (false), SynthInstance.lean:1019, 1027 and 1037. These only catch. The bit is set, in
its own configuration scope, by synthInstanceCore? (SynthInstance.lean:967, which also sets instances transparency,
foApprox and ctxApprox true, constApprox and univApprox false) and by `binop%`'s analyze (Elab/Extra.lean:307,
withNewMCtxDepth around isDefEqGuarded; s1-elab), so the code cannot reach the elaborator. Every mark rolls back on
`lf-meta-stuck` and passes it on (checkpointDefEq's `catch ex => s.restore; throw ex`, Basic.lean:2497); `outcome-sane` stays at the Meta layer's exits
(FE1E §3.4's test, and a planted fault that drops one catch). **Configuration:** Lean's Meta.Config bits (foApprox,
ctxApprox, quasiPatternApprox, constApprox, univApprox, isDefEqStuckEx, and assignSyntheticOpaque for §10), the transparency and
§8's budget move from `defeq.fs`'s record into `meta-config.fs`'s, read as Lean's `getConfig`; `lf-defeq-flags!` and
`lf-defeq-mode!` keep their names.

**FE1e0 is reopened in s1-meta** with the pieces of appendix D (getDecLevel, levelAssignDepth, the instance-typed
assignment, the synthesis hooks, whnf with delta and its helpers, format 2's facts in meta-env). Lazy delta moves to S2.

## 3. One undo trail (B3)

Lean's MetavarContext is a persistent value (`saveState`/`restore`; `getMCtx`/`setMCtx`/`withMCtx`,
SynthInstance.lean:261-654; checkpointDefEq, Basic.lean:2472; withNewMCtxDepth, Basic.lean:2008). LeanForth gets the
same from one trail in `front/mvars.fs`: while a scope is open, each change of a metavariable record (an assignment,
plain, level or delayed; a tag; a kind; the instance-typed flag) is a record (entry, old value, new value, parent), and
the current state is a position in that tree of records.

| Word | Stack effect | Lean |
| --- | --- | --- |
| `lf-mctx-mark` | `( -- mark outcome )` | opens a scope: `saveState`, `checkpointDefEq`, `commitWhen` |
| `lf-mctx-rollback` | `( mark -- outcome )` | latest scope only: back to its entry, its records dropped (`restore`) |
| `lf-mctx-commit` | `( mark -- outcome )` | latest scope only: kept for an outer scope; the trail empties when the last scope closes |
| `lf-mctx-snapshot` | `( -- snap outcome )` | `getMCtx` inside an open scope (invalid outside one) |
| `lf-mctx-switch` | `( snap -- outcome )` | `setMCtx`, `withMCtx`: undo to the common ancestor, then redo the target's records |
| `lf-mctx-depth{` `}lf-mctx-depth` | `( levels? -- scope outcome )` `( scope -- outcome )` | `withNewMCtxDepth (allowLevelAssignments)`; the exit rolls everything back and restores the depth and levelAssignDepth |

LIFO marks are the special case (a scope whose only snapshot is its entry): `defeq.fs`'s checkpoints and fe1g3's
`lf-tac-save`, `-restore`, `-commit` (through its `lfr-trail-*` words) keep their words and stack effects. A stale
snapshot (its scope closed) is refused, invalid; a switch target must lie under the innermost open scope, or the switch
is invalid (Lean switches only inside its synthesis depth scope); main's `lf-mctx-deeper`/`-shallower` go behind
`depth{ }`; postponed level constraints, part of Lean's saveState, stay unsupported (`level-defeq.fs:20-21`); metavariables made on another branch stay declared and unassigned;
full when the trail or the redo stack cannot grow. s1-meta owns it and merges it first (FE1e4 moves there). Tests:
switches back and forth leave only the target's assignments (fault `fe-trail-no-redo`); fe1g3's rollback tests pass.

## 4. Binder kinds (B4)

The term store shares nodes that differ only in binder kind (`present/binder-table.fs:1-10`), so a kind is read from a
**constant**'s declared type, `lf-menv-kinds ( d -- addr n )`: its leading Π binders, read syntactically (a library
declaration's from the tier's binder tags, `core/compact-exprs.fs`; a text declaration's as its binder words wrote
them, recorded by `lf-menv-add`); from a **local**'s view entry (`lctx-views.fs`, Lean's `LocalDecl.binderInfo`) for
mkForallFVars, mkLambdaFVars and introN; and **never** from a term-store or instantiated node. S1's readers: elabAppArgs
(binder k of a constant head is `kinds[k]`), `fun-info.fs`, `discr-keys.fs` (`ignoreArg`) and `synth.fs`
(getSubgoals). Unsupported until S5, which also decides how elaborated binders keep their kinds: a binder that only
unfolding reveals, and a local or metavariable applied to arguments. **S1 check** (s1-meta,
`tests/front/check_binder_kinds.py`): pinned Lean's binder info against the export's, for every binder of every Init
declaration's type, target 0. Lean's export shares expressions equal up to binder info (fe6a M1). S1 needs a count of 0 on
the declarations S1 reads (Eq, Eq.refl, HAdd, OfNat, Add and their instances); otherwise the list of differing
declarations ships in the elaboration data, covered by M6's manifest entry, and those answer unsupported where their
kinds are read. Measured (2026-11-13, merge B, `make reference-binder-kinds`): of Init's 59,349 exported
declarations 755 differ in 1,101 binders; S1's 16 differ in none.

## 5. Error-code ranges (B5)

| Codes | For | Slice |
| --- | --- | --- |
| 1-73 | the words, the runner, the stores, natural text read (FE1a) | built |
| 74-79 | the hand-over and instantiation (FE1c, FE1f; 74-77 used, 78-79 kept for S4's auxiliary declarations) | built |
| 80-99 | tactic proofs read and run, the first tactics (FE1g-2 to FE1g-4; all used on fe1g3) | S1 (fe1g3) |
| 100-109 | Meta errors a user sees ("invalid universe level", the stuck and trail refusals) | S1 (s1-meta) |
| 110-124 | instances: "failed to synthesize", the instance codes, one per unsupported instance rule | S1 (s1-synth) |
| 125-139 | elaboration: numerals, applications, `binop%`/`binrel%`, defaults, the glue, `#check`, fuel, the rest of FE1E §2.7's unsupported rows | S1 (s1-elab) |
| 140-199 | elaboration in FE2: one per Lean error and unsupported condition of its §4; structures, notation, commands | S5, S6 |
| 200-249 | tactics after FE1g-4 (FE1g-5 to FE1g-8, FE5's) | S2 on |
| 250-269, 270-299 | `decide`; `omega` and its opt-in flag | S3, S4 |

Wider than the review's, sized from the designs' counts with room (FE1e about 18 errors and 13 unsupported rows, FE2
over 40, FE1g-5 to 8 about 9): an entry costs nothing, a renumbering breaks pinned tests, and numbers stop depending on
merge order. Merge 2A writes every range and every S1 code name into `author/errors.fs`'s header before 2B and 3
start (the elaboration data's codes 1-38 stay apart).

## 6. When elaboration happens (M2)

Natural text is read whole, one declaration at a time; reading builds syntax only (FE1a), each name taking its explicit
arguments by its declared arity (a library constant's type in the stage, `lfc-arity`; a binder's syntax type). At
`end NAME` the declaration is elaborated in Lean's order (binders, statement, proof: a term against the statement, or a
tactic block step by step, each step's term arguments elaborated when it runs, against its goal) and handed over. A
hypothesis that a tactic introduces takes no values, because its type is unknown when it is read: `$` applies it, and a
value left under it is error 87 (unsupported). `#check` elaborates where it stands. This replaces ADR D8 and
FRONT_END §4.2 ("when the binder word runs") and FE1G §3.2 ("tactic words run when they are read"). FE2 §2.1 rule 3, a
scratch elaboration while reading, is S5's to decide, on §1's route.

## 7. The declaration glue (M3)

s1-elab owns it, in the new `front/elab-decl.fs`, after Elab/MutualDef.lean. (1) elabHeaders (209-290): each binder's
type by `elabType`, its local pushed on the view; the statement by `elabType`; `synthesizeSyntheticMVarsNoPostponing`
(SyntheticMVars.lean:649), where S1's default instances fire; mkForallFVars and `instantiateMVars`; a metavariable left
is Lean's error. (2) levelMVarToParam (1148): a level metavariable left is unsupported until S5. (3) The statement-alone
rule (1236-1242): a theorem's statement is elaborated before and without its proof and must end with no metavariable
(else unsupported until S5: LeanForth's limit, not Lean's rule; Lean allows holes in a theorem's header, those lines
being only its asynchronous path); its universe parameters count in the type alone (`handover.fs`). (4) elabFunValues
(515-552): a term proof is `elabTermEnsuringType` against it, then `synthesizeSyntheticMVarsNoPostponing`. The glue sets
FE1f's `lf-front-elaborate ( -- type value )` (`handover.fs:120`) and fe1g3's `lf-front-by-statement ( -- type )`; both
stop the run with their error at `end NAME`.

## 8. Fuel (M4)

`--elab-fuel N` (s1-elab; the budget lives in `meta-config.fs`) sets one budget per declaration for elaboration visits,
synthesis steps, unifier comparisons, whnf and tactic steps, as Lean's `maxHeartbeats` is one per declaration; default
100,000,000, as `--fuel`'s; running out is exhausted (exit 3; error 91 at a tactic step, else a 125-139 code). `--fuel`
stays the kernel's; the per-call limits of `defeq.fs`, `whnf.fs`, `tactic-run.fs` remain only as unit-test settings;
cases where Lean's limit and this one differ go to BEYOND_LEAN.md (owner, 2026-11-12).

## 9. Unsupported rules for instances (M5)

A left-out instance (`not_exported`), or one whose FE1E §4 class or key check could not finish (trusted for its class,
as the data's ranks are), makes a search answer unsupported only when the search tries it (Lean's `tryResolve` in
`generate`, SynthInstance.lean:594-627). A candidate never reached changes nothing; an `erased` one is never a
candidate, as in Lean; a mismatch the check finds still refuses the data. FE1E §2.7's and §4's wider rules are
withdrawn. **Measurements first** (s1-synth's first commit, on the S1 slice and on Init): for the roots `OfNat`, `HAdd`
and `Add`, the candidates and the left-out and unverified ones among them; for each S1 problem (`OfNat ?T 0`,
`OfNat Nat 0`, `HAdd ?α ?β ?γ`, `HAdd Nat Nat ?γ`, `Add ?α`, `Add Nat`), the candidates pinned Lean tries before its
answer or its stuck exit (`trace.Meta.synthInstance`). If a tried candidate is left out or unverified, s1-synth stops
and reports it: the fix is the exporter's, at the [import] gate. An unverified instance's key is trusted from the data,
so a wrong key could pick a different instance: a question of meaning, guarded by M6 and the [parser] comparisons.

## 10. `by-exact` (M1)

`by-exact` stays fe1g3's code: Lean's `evalExact` (Elab/Tactic/ElabTerm.lean:100) through
`Tactic.elabTermEnsuringType` (51-62). Its hook `lf-tac-elab` is `Tactic.elabTerm` (45-48: `Term.elabTerm` against the
goal, synthesis with no postponing, instantiation), which s1-elab sets. fe1g3 then compares the types by `isDefEq`
under assignSyntheticOpaque (§2's bit, in place of its error 93) and reports Lean's "Type mismatch" (96), never a
coercion. FE1E §2.6's `Term.elabTermEnsuringType` (a coercion answers unsupported) serves only term proofs (§7).

## 11. The S1 split

| # | Branch | Contents | Tests | Gate |
| --- | --- | --- | --- | --- |
| 1 | `fe1g3` | FE1g-3a and FE1g-4 as built (`by-sorry`, `by-intro:`, `by-exact`, `by-rfl` on stand-in statements); review; merge first | its own (`check_tactics.py`, Lean twins) | `by-sorry`'s report wording: [format] with S2 |
| 2 | `s1-meta` | merge A: §3, §2's code and configuration, appendix D's `lf-meta-whnf`, `-whnf-r`, `-whnf-forall` and `-instantiate-forall` (fed mode suffices; s1-synth's keys and subgoals need them), and the codes' header; merge B: §1, the rest of §2, §4, §5's header, D13 | stuck sites against pinned-Lean twins; trail; allowlist and `lf-input-intact?`; through `cli-check` with a library (as fe1g3's end-to-end test), a stand-in statement `0 + 0 = 0` of library constants closed by `by-rfl` and accepted by the kernel, and `0 + 0 = 1` refused with 97 | [import] |
| 3 | `s1-synth` | §9's measurements; the M6 manifest entry for the data file; FE1e2 `discr-keys.fs`, FE1e3 `instances.fs`, FE1e5 `synth.fs`; sets §2's hooks | every Init instance key recomputed; `check_synth.py` (`#synth` table, failures, stuck goals) | [import] (M6), [parser] |
| 4 | `s1-elab` | FE1e6-7 (`elab-pending.fs`, `elab-app.fs`, `elab-term.fs`, `#check`); §7; §8; §10's hook; codes 125-139; the S1 files | golden traces of C1 and C17 (`0 0 + 0 =`, the default-instance path); `check_elab.py`; `tests/front/s1-rfl.lf`, its Lean twin and its wrong twin `0 + 0 = 1`; the user page in three forms; the done check on full Init | [parser], [bypass] |

Order: 1; 2A; 2B and 3 in parallel (3 built against §2's and §3's words, rebased on 2A); 4, started on stubs of the
deferred words. Branches meet only in `author/errors.fs` (separate ranges), `tests/mutants/faults.toml` and the style
baseline (appendix B). Midpoint, in branch 4: `bin/leanforth check --env tests/front/s1-slice.ndjson --elab-data
tests/front/s1-slice.elab.ndjson tests/front/s1-check.lf` prints `0 + 0 = 0 : Prop`. S1 is done only when the done
checker runs the S1 command on the full Init snapshot and reports DONE.

## 12. Questions for the owner

1. **The front end's work limit.** The kernel's limit is `--fuel N`; the front end needs its own, because a search can
   run long where checking is quick. *Recommendation: `--elab-fuel N`*, which names what it limits. The alternatives
   are `--front-fuel` and `--heartbeats`; the last would suggest Lean's unit, which counts memory allocations, not steps.
2. **The midpoint.** S1's midpoint is a file of `0 0 + 0 = #check` lines printing `0 + 0 = 0 : Prop`. As in Lean, a
   file of only `#check` lines would end with exit 0 and "nothing checked by the kernel", in place of today's error 49.
   *Recommendation: yes, shown as a midpoint, never as "done"*: it is the elaborator's first output you can run.
3. **The spelling of `sorry`.** fe1g3 builds the tactic as `by-sorry`, following your rule that tactic words start with
   `by-`. Lean also has the term `sorry`, which needs string literals in the export (S5). *Recommendation: the tactic
   `by-sorry` now, the term `sorry` in S5*, settled at the [parser] gate.

## Appendix A. Probe (2026-11-13)

Pinned Lean (`.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`) ran `theorem t : 0 + 0 = 0 := by rfl` with
`pp.all` and `trace.Meta.isDefEq`:
- The term is `@Eq.refl.{1} Nat (@HAdd.hAdd.{0,0,0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (OfNat 0) (OfNat 0))`.
- The statement's elaboration raises the stuck signal on `HAdd ?α ?β ?γ =?= HAdd Char String.Pos.Raw String.Pos.Raw`
  (`String.instHAddCharRaw`), on `Add ?α` (the `Lean.Grind` instance of `Q`) and on `OfNat ?α 0`.
- The default instances `instHAdd` and `instOfNatNat` fire as FE1E §6.1's C16 describes.
- The closing `0 + 0 =?= 0` checks the instance, `Nat =?= Nat` and the literals; there is no delta step.

`theorem t2 : 0 + 0 = 1 := by rfl` fails with "Tactic `rfl` failed: The left-hand side ... is not definitionally equal
to the right-hand side" and the goal.

After `import Lean`, 1,135 constants are named `*._sunfold`, 389 of them in `Init` modules (`Nat.add._sunfold` among
them). The probe files were in the session scratchpad and were not kept.

## Appendix B. Files by branch (work in flight)

| Branch | Files |
| --- | --- |
| fe1g3 | `tactic-run.fs`, `tactic-basic.fs`, `tactic-syntax.fs`, `goal-print.fs`, 5 lines of `mvars.fs`, `infer.fs`'s `lf-get-level`, codes 80-99, 1 line of `check-lf.fs` |
| s1-meta | new `meta-config.fs` and `lib-decode.fs`; `mvars.fs`, `level-defeq.fs`, `defeq.fs`, `whnf.fs`, `infer.fs`, `meta-spine.fs`, `meta-env.fs`, `fun-info.fs`, `handover.fs` (`lf-menv-add`), `cli/check-lf.fs`; ADR 0021 D13; `author/errors.fs`'s header |
| s1-synth | new `discr-keys.fs`, `instances.fs` and `synth.fs`; `elab-data.fs`'s readers if needed; `import/manifest.fs` and `scripts/export-elab.sh` (M6) |
| s1-elab | new `elab-pending.fs`, `elab-app.fs`, `elab-term.fs` and `elab-decl.fs`; `tactic-basic.fs` (§10's hook); `cli/leanforth.fs` (`--elab-fuel`, `#check`-only files); codes 125-139; `docs/user/` |

## Appendix C. What later slices take from this note

| Slice | Takes |
| --- | --- |
| S2 | §3's trail (for `by-first` and the `rfl` alternatives), §2's whnf with lazy delta and `_sunfold` added, codes 200-249 |
| S3 | `lf-meta-whnf` with `reduceNat?` and matchers, codes 250-269 |
| S4 | codes 270-299, and 78-79 for auxiliary declarations |
| S5 | §1's route for a scratch elaboration while reading, §4's kinds for elaborated binders, §7's level and metavariable cases, codes 140-199 |
| every slice | §8's budget and §9's rule |

## Appendix D. FE1e0 in s1-meta: words and Lean sources

Still unsupported at the step that needs them: smart unfolding (does `f._sunfold` exist? Init has 389, appendix A;
from the stage if the export holds them, else FE1d2's records, S2), lazy delta (`isDefEqDelta`, ExprDefEq.lean:2421;
S2), matcher reduction and `reduceNat?` with its threshold (S3). S1's proof needs none of them: pinned Lean closes
`0 + 0 =?= 0` by Nat-literal arithmetic with no delta step (ExprDefEq.lean:2419-2420, isDefEqNat then isDefEqOffset,
Offset.lean:118; `nat-offset.fs` ports it).

| Word or change | Lean | File |
| --- | --- | --- |
| `lf-meta-dec-level ( type -- level outcome )`: getLevel, normalize, decLevel (an assignable `?v` becomes `succ ?w`; Lean's "invalid universe level" is an error, 100-109) | DecLevel.lean:57-76 | `infer.fs` |
| levelAssignDepth, kept by §3's depth scope | MetavarContext.lean:957 | `mvars.fs`, `level-defeq.fs` |
| checkTypesAndAssign's instance-typed branch (option `instanceSearchTypes`, default true); a per-metavariable flag on the trail, set by synth's subgoals | ExprDefEq.lean:640-660, SynthInstance.lean:358 | `mvars.fs`, `defeq.fs` |
| deferred `lf-meta-synth-pending ( mvar -- flag outcome )` and `lf-meta-synth ( type -- inst flag outcome )`, unsupported until s1-synth sets them | SynthInstance.lean:1037, ExprDefEq.lean:626 | `defeq.fs` |
| `lf-meta-whnf ( e -- e' outcome )`: whnfCore, then unfoldDefinition? and getUnfoldableConst? at the configured transparency, repeated | WHNF.lean:844, GetUnfoldableConst.lean:78 | `whnf.fs` |
| `lf-meta-whnf-r`, `lf-meta-whnf-forall`, `lf-meta-instantiate-forall ( e addr n -- e' outcome )`, forallTelescopeReducing's step | Basic.lean:2147, 872, 2186, 1626 | `whnf.fs`, `infer.fs` |
| `lf-menv-matcher?`, `-proj-fn?`, `-aux-recursor?` from format 2 (`elab-matcher-of`, `elab-projection-of`, the `aux_recursor` tag); a definition no record names is none of them | WHNF.lean (getMatcherInfo?, isAuxRecursor) | `meta-env.fs` |
