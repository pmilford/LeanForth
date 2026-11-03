# The checked environment (v0)

Status: implemented 2026-11-02 as plan task 2.2.2, following
[ADR 0012](../adr/0012-checked-environment.md), whose design the owner
accepted (gate answers G8–G11); the findings of its independent review,
and of that review's second round, were fixed the same day (see *Trust*). **Experimental [kernel] code, not
through the review gate and not independently audited.** The environment
decides nothing about a declaration's terms: the check that fills it is
`check-declaration` (plan task 2.2.3, [below](#check-declaration-plan-task-223);
also [experimental, not through its gate](../user/FIRST_CHECK.md)). Until
an outside Lean expert has audited the checker, every accepted result is
printed *accepted (experimental, not independently audited)*.

Source: `src/core/input.fs` (the input), `src/core/name-equal.fs`
(structural name equality), `src/kernel/environment.fs` (environments,
snapshots, lookups, handles, candidates), `src/kernel/env-publish.fs` (the
publisher and the serial driver), `src/kernel/check-declaration.fs` (the
check) with `src/kernel/env-signature.fs` (the environment's answers to
inference), and the store marks of `src/lib/store.fs`
([library notes](../development/FORTH_LIBRARY.md)).

## What it is

The checked environment is LeanForth's library of accepted declarations.
Each declaration of the input gets one numbered *slot*, in input order. A
slot is written once, by one part of the program (the *publisher*), after
the declaration's check has ended, and never changes afterwards. Only an
accepted slot can be used, and only by declarations later in the input. A
check works in its own scratch space, which is rolled back afterwards
whatever happened, and the publisher re-checks a few cheap facts before it
makes anything visible. An accepted slot holds the very input declaration
that was checked (indices of its terms, not copies), the slots it uses and
the statements it depends on without proof (*axioms*), computed from those
slots; in the first checker that set is always empty.

## Example in three forms

A definition and a theorem that uses it, then the definition's name again.

**Mathematics.** The polymorphic identity
$\mathrm{myId}_u : \prod_{\alpha : \mathrm{Sort}\ u} \alpha \to \alpha$,
$\mathrm{myId}_u := \lambda \alpha\ a.\ a$, for every universe level $u$;
then the theorem $\forall p : \mathrm{Prop},\ p \to p$, proved by
$\lambda p\ h.\ \mathrm{myId}_0\ p\ h$, which uses $\mathrm{myId}$ at level
$0$. A library holding both has two entries: the identity, which uses
nothing, and the theorem, which uses the identity; neither depends on an
axiom. Declaring $\mathrm{myId}$ a second time is an error, whatever its
body.

**LeanForth Forth.** The input lives in the term, level and name stores
(`src/core/`), built here with the helpers below; the environment then
gets one slot per declaration. Each is checked by `check-declaration`
(plan task 2.2.3; experimental [kernel] code, not through its review
gate), with fuel 100,000.

```forth
\ Helpers for the example (documentation only, not part of LeanForth).
[undefined] lf-env-hand-over [if] require ~+/src/kernel/env-publish.fs [then]
: made ( flag -- ) 0= abort" refused" ;
: ok! ( outcome -- ) outcome-ok <> abort" not ok" ;
: id ( c-addr u -- name ) 0 -rot lf-name-str made ;
\ Terms from handles (index identity), and printing them as Lean does.
: >Pi ( body domain -- term ) 2swap lf-hterm-pi made ;
: >fun ( body domain -- term ) 2swap lf-hterm-lam made ;
: app ( function argument -- term ) lf-hterm-app made ;
: var ( k -- term ) lf-hterm-bvar made ;
: named ( term c-addr u -- term )
  0 -rot lf-name-str made 2 pick swap lf-binder-default lf-pres-binder! ok! ;
' type lf-print-unicode lf-print-setup
: .lean ( term -- ) drop 10000 lf-print-term ok! ;

\ The names, the universe parameter u (in the session's level context),
\ Sort u and Prop.
s" u" id constant u
u lf-lscope-context-add made
lf-ssession-begin made
s" myId" id constant myId
s" myId_prop" id constant myId_prop
u lf-hlevel-param made lf-hterm-sort made 2constant Sort-u
lf-hlevel-zero made 2constant level-0
level-0 lf-hterm-sort made 2constant Prop
\ myId.{u} : (α : Sort u) → α → α := fun α a => a
1 var 0 var >Pi s" a" named Sort-u >Pi s" α" named 2constant myId-type
0 var 0 var >fun s" a" named Sort-u >fun s" α" named 2constant myId-value
\ myId_prop : ∀ (p : Prop), p → p := fun p h => myId.{0} p h
create level-args 2 cells allot  level-0 swap level-args 2!
myId lf-name-generation @ level-args 1 lf-cref-new made lf-cterm-new made
2constant myId.{0}
1 var 0 var >Pi s" h" named Prop >Pi s" p" named 2constant thm-type
myId.{0} 1 var app 0 var app 0 var >fun s" h" named Prop >fun s" p" named
2constant thm-value
myId myId-type drop lf-pres-declare ok!   \ the printer learns myId's arguments

\ The input: the two declarations, then myId once more; then loading ends.
create decl-buffer /lf-idecl allot
: new-decl ( name kind -- )
  decl-buffer /lf-idecl erase decl-buffer lf-idecl-kind ! decl-buffer lf-idecl-name ! ;
: roots ( type value -- )
  drop decl-buffer lf-idecl-value ! drop decl-buffer lf-idecl-type ! ;
: one-param ( name -- ) decl-buffer lf-idecl-params ! 1 decl-buffer lf-idecl-arity ! ;
: add ( -- ) decl-buffer lf-input-add ok! drop ;
myId lf-kind-definition new-decl myId-type myId-value roots u one-param add
myId_prop lf-kind-theorem new-decl thm-type thm-value roots add
myId lf-kind-definition new-decl myId-type myId-value roots u one-param add
lf-input-end ok!

\ The check: check-declaration, each with fuel 100,000.
100000 lf-check-budget
\ After a THROW in a check the run goes on in a new context holding the
\ same input (G-P6). This example has no way to load it again, so a THROW
\ would stop the run, failing closed.
: no-spare ( -- context ior ) 0 -1 ;

\ Reports: a slot's outcome, the slots it uses and its axioms; the
\ diagnostic's code, site and numbers.
: .list ( addr n -- ) 0 ?do i if ." , " then dup i cells + @ 0 .r loop drop ;
: .uses ( slot -- )
  dup lf-slot-count @ 0= if drop ." none" exit then
  dup lf-slot-deps @ lf-env lf-env-pool store-slot swap lf-slot-count @ .list ;
: .axioms ( d -- ) lf-env-axioms ok! if ." some" else ." none" then ;
: .record ( d -- )
  ." , uses " dup lf-env lf-env-slot .uses ." , axioms " .axioms ;
: .slot ( d -- )
  dup . ." : " dup lf-env-outcome dup outcome-text type ok? if .record else drop then cr ;
: .diag ( -- ) lf-diag@ 0 .r space count type ." : " swap . . ;
```

The four terms, as the term printer shows them:

```forth
myId-type .lean cr  myId-value .lean cr  thm-type .lean cr  thm-value .lean cr
```

```text
(α : Sort u) → α → α
fun α a ↦ a
∀ (p : Prop), p → p
fun p h ↦ myId p h
```

A new environment with room for 8 dependencies, the serial run of phase
2, then, in a view of the whole environment, each slot, the diagnostic of
the last check (code 51, *name already declared*: the name's ID 2 and the
accepted slot 0), a handle to slot 0 checked, and the three verdicts as
`check-declaration` prints them:

```forth
8 lf-env-new ok! lf-env-use ok!
' lf-check-declaration ' no-spare lf-env-run outcome-text type cr
lf-env-view ok!  0 .slot 1 .slot 2 .slot
.diag cr
0 lf-env-handle ok! lf-env-handle? outcome-text type cr
0 lf-check-verdict. cr  1 lf-check-verdict. cr  2 lf-check-verdict. cr
```

```text
ok
0 : ok, uses none, axioms none
1 : ok, uses 0, axioms none
2 : rejected
51 environment lf-env-own-name: 2 0
ok
accepted (experimental, not independently audited); axioms: none
accepted (experimental, not independently audited); axioms: none
rejected
```

**Lean.** Lean 4.35.0 accepts the two declarations and reports the
theorem's axioms (`#print axioms` collects them transitively, as the
environment does):

```lean
def myId.{u} (α : Sort u) (a : α) : α := a
theorem myId_prop (p : Prop) (h : p) : p := myId p h
#print axioms myId_prop
```

```text
'myId_prop' does not depend on any axioms
```

and refuses the second `myId` (its kernel's `alreadyDeclared`, rule N2):

```lean
def myId.{u} (α : Sort u) (a : α) : α := a
def myId.{u} (α : Sort u) (a : α) : α := a
```

```text
error: `myId` has already been declared
```

`python3 scripts/check-doc-examples.py --gforth GFORTH --lean LEAN
docs/programming/CHECKED_ENVIRONMENT.md` runs these blocks and compares
the output (done on 2026-11-02 with Gforth 1.0 and 0.7.3 and pinned Lean
4.35.0; all agree).

## Interface

Outcomes are ADR 0008's (`src/lib/outcome.fs`): 0 ok, 1 invalid,
2 exhausted, 3 unknown, 4 rejected, 5 unsupported, 6 full. No word here
ever turns a failure into ok.

### The input (`src/core/input.fs`)

| Word | Stack effect | Does |
| --- | --- | --- |
| `/lf-idecl`, `lf-idecl-name`, `-kind`, `-safety`, `-type`, `-value`, `-hint`, `-height`, `-arity`, `-params` | record and fields | one input declaration: name ID, kind (`lf-kind-definition` … `lf-kind-recursor`), safety and hint coded as the NDJSON reader codes them, type and value term indices (value −1 for none), up to `lf-param-capacity` (8) universe parameter name IDs |
| `lf-input-add` | `( decl -- i outcome )` | copy a filled record while loading: ok; invalid after loading ended or for a record out of range or with a reference that is not live; full when the input is full |
| `lf-input-end` | `( -- outcome )` | end loading: mark every input store (terms, levels, names, references, declarations) and record the input's fingerprint; invalid when already ended or the name store or its byte count is out of range |
| `lf-input-intact?` | `( -- flag )` | loading ended, every mark still valid (no reset, nothing rolled back below it) and the name bytes still in use |
| `lf-input-rollback` | `( -- outcome )` | return every input store to its mark (a check's scratch); invalid, with nothing changed, when the input is not intact |
| `lf-input-reset` | `( -- )` | start a new input in this context; every environment over the old one fails closed |
| `lf-input-count`, `lf-input-decl`, `lf-input-name`, `lf-input-params`, `lf-input-read`, `lf-input-fingerprint` | readers | `lf-input-read ( i -- decl outcome )` is the checked one |

### Environments, checks and lookups (`src/kernel/environment.fs`)

| Word | Stack effect | Does |
| --- | --- | --- |
| `lf-env-new` | `( deps -- env outcome )` | a new environment over this context's intact input, one slot per declaration, room for `deps` dependencies (0 … 65,536), allowlist version 0 (empty), final mode; invalid inside a job or for an input that is not intact, full when identities are spent or memory is short |
| `lf-env-use`, `lf-env`, `lf-env-free` | `( env -- outcome )`, `( -- env )`, `( env -- outcome )` | choose, read and free the current environment; `lf-env-use` and `lf-env-free` refuse (invalid) inside a job |
| `lf-env-begin` | `( i -- outcome )` | start the check of declaration `i` in this context: records the snapshot (identity, `i`), clears the candidate and the diagnostic; invalid in a spent context (below), without a valid environment or for a slot out of range or already final |
| `lf-env-spent?` | `( -- flag )` | whether a check threw in this context (G-P6): it can begin no other check and must be replaced |
| `lf-env-view` | `( -- outcome )` | a snapshot of every slot, for queries after a run |
| `lf-env-own-name` | `( -- outcome )` | N2 on the checked declaration's name: ok, rejected (an earlier one accepted), unknown or unsupported (an earlier one undecided or unsupported, K5, unknown first) |
| `lf-env-lookup` | `( name -- d outcome )` | find a constant (E5): `d ok` for the accepted earlier declaration of that name; rejected (N1: unknown, forward or self reference); unknown when an earlier one is undecided, else unsupported when one is unsupported (K5, unknown first); invalid when a same-named earlier slot is not final (started too early) |
| `lf-env-depend`, `lf-env-resolve` | `( d -- outcome )`, `( name -- d outcome )` | record a dependency on accepted slot `d` (ascending, distinct; its axiom set and provenance joined); full at `lf-env-dep-capacity` (16); resolve is lookup then depend |
| `lf-env-finish` | `( outcome -- )` | end the check with its outcome (invalid until called) |
| `lf-env-params`, `lf-env-arity?`, `lf-env-param?`, `lf-env-own-params` | | universe parameters: a slot's own list; L1 (exact number of levels), L2 (a parameter of the checked declaration), L3 (no parameter twice): ok or rejected |
| `lf-env-handle`, `lf-env-handle?` | `( d -- identity d outcome )`, `( identity d -- outcome )` | a handle to an accepted slot this context's snapshot may read; valid in a snapshot (identity′, `i`) only for the same identity, `d < i`, a final accepted slot; anything else is invalid |
| `lf-env-ready?` | `( name i -- flag )` | for a scheduler (G-P5): every declaration before `i` with that name has a final slot; false inside a job or a check |
| `lf-env-refused` | constant | the `THROW` code (-4110) of an internal word that writes shared state, called inside a job or a check: until a word list hides them (plan task 1.1.7), each such word refuses there before writing, and the job's or driver's `CATCH` makes the declaration invalid and spends the context |
| `lf-env-outcome`, `lf-env-axioms` | `( d -- outcome )`, `( d -- bits outcome )` | results, read within this context's snapshot (G-P4), so after a run within `lf-env-view`'s: a readable slot's outcome (invalid otherwise), an accepted slot's axiom set |

### Publishing (`src/kernel/env-publish.fs`)

| Word | Stack effect | Does |
| --- | --- | --- |
| `lf-env-hand-over` | `( -- outcome fault? )` | the publisher's only entry (E4), refused inside a job or a check (G-P1): for an ok candidate, re-check (every same-named earlier slot final and rejected; dependencies ascending, below, final, accepted; axiom set and provenance the unions of theirs, within the allowlist and "checked" in a final run; a safe definition or theorem with a value and distinct parameters), then append the dependencies (full if no room) and copy the input declaration; any other outcome alone; last, mark the slot final. It marks the pool first and publishes under `CATCH`: after a `THROW` before the final mark the slot stays not final and cleared, the pool rolled back (a slot already final keeps its record and dependencies). `fault?` true (the run must stop) after a `THROW`, inside a job or a check, with no slot to publish, when the pool cannot be marked, or when the publication ended without a final slot (then invalid, undone like a `THROW`) |
| `lf-env-step` | `( xt i -- outcome fault? )` | begin, run the check `xt ( -- )`, make sure the snapshot is still of `i` (else a fault, nothing published), hand over, roll the scratch back. The check runs as the job pool runs a job's word: with the owner token `context-check-owner` (so every guard that refuses a job refuses it: it can neither publish, step, run, nor make, choose or free environments or contexts), with the task's context and token restored afterwards, and with its stack checked: a `THROW`, a changed stack depth or a changed cell below it (a copy of `i`; `THROW` code `lf-env-unbalanced`, -4096, as `task.fs`'s `task-unbalanced`) makes the declaration invalid and spends the context |
| `lf-env-hand-over-job` | `( ior i -- outcome fault? )` | the parallel scheduler's entry, after the job that checked declaration `i` in this context ended with `ior`: records a `THROW` (G-P6, as `lf-env-thrown`), makes sure the snapshot is still of `i`, and hands over, as `lf-env-step` does; the scheduler then rolls the scratch back and replaces the context when `lf-env-spent?` holds |
| `lf-env-thrown` | `( ior -- )` | the check in this context ended with a `THROW`: invalid, recorded, the context spent (used by `lf-env-step` and `lf-env-hand-over-job`) |
| `lf-env-run` | `( check maker -- outcome )` | the serial publisher of phase 2: every declaration in input order, in the current context until a check throws, then in a new one from `maker ( -- context ior )`, which must hold the same input, loaded the same way (G-P6). It adopts only a context that is idle, neither the main nor the current one, and not spent, from a maker that leaves exactly two cells, checked before anything is freed; it frees the contexts it made and returns to the caller's, which it never frees. The check and the maker wait on the return stack while the other runs. ok when all slots are final; invalid when a fault stopped it, inside a job or a check, or when no new context could be adopted |
| `lf-env-before-final` | deferred `( -- )` | test-only fault injection between writing a slot and marking it final; compiled as a `DEFER` only when a test defines `lf-env-fault-hooks` before loading, otherwise an empty word |

### check-declaration (plan task 2.2.3)

`src/kernel/check-declaration.fs` is the check the publisher runs for each
declaration ([ADR 0011](../adr/0011-definite-rejection.md), "Order"; ADR
0012, E4). Steps, each ended by the first failure: 1 the audit (U1: a
safe definition or theorem, else *unsupported*, axioms included — owner
gate answer G3; a definition or theorem without a value is *invalid*; U2:
no `let`, literal, metadata or projection, each staged by an importer as a
leaf of `src/core/unsupported-forms.fs`; V1: closed, well-formed terms);
2 N2 on its name (`lf-env-own-name`); 3 L3 (`lf-env-own-params`); 4 the
declared type's type, inferred in *environment mode*; 5 that type a `Sort`
(S1); 6 for a theorem, a proposition (S3); 7 the value's type, after the
scratch of steps 4–6 is rolled back to the input marks; 8 the value's type
against the declared type (D1–D5). In environment mode
(`lf-minfer-start-env`, `src/kernel/mixed-infer.fs`) inference asks the
environment where Lean's kernel asks its own, in Lean's order
(`src/kernel/env-signature.fs`): at a constant, the lookup in the check's
snapshot (N1, K5), the number of universe arguments (L1), each argument
within the declaration's parameters (L2), then the accepted slot's own
stored type with its parameters replaced by the arguments, all at once; at
a `Sort`, L2 on its level. Deciding, each constant that passes is recorded
as a dependency (`lf-env-depend`, which joins its axiom set); while
inference runs aside (its proof test P2), as in Lean's `infer_only` mode,
nothing is recorded and L2 is skipped. A job started with `lf-minfer-start`
(`lf-mixed-infer`, the probes) never uses environment mode.

| Word | Stack effect | Does |
| --- | --- | --- |
| `lf-check-declaration` | `( -- )` | the check word for `lf-env-run` and `lf-env-step`: checks the declaration of this context's snapshot and ends with `lf-env-finish`; outside a check's snapshot, invalid |
| `lf-check-budget` | `( fuel -- )` | the fuel each later check in this context starts with (the audit and inference share it); a new context has 0, so every check is *exhausted* until a budget is set |
| `lf-check-step@` | `( -- step )` | the step at which the last check ended: 0 before its snapshot was found, 1–8 as above, `lf-step-done` (9) when every step succeeded |
| `lf-check-input` | `( fuel deps -- env outcome )` | check every declaration of this context's intact input in input order in a new environment (room for `deps` dependencies), left current; `outcome` is `lf-env-run`'s; a check that throws stops the run |
| `lf-check-verdict.` | `( d -- )` | print declaration `d`'s verdict within the current snapshot (after a run, `lf-env-view`'s): an accepted one as *accepted (experimental, not independently audited); axioms: none*, the axiom set read from its slot; any other as its outcome |
| `lf-check-label` | `( -- c-addr u )` | the label of an accepted result |
| `lf-env-signature`, `lf-env-level-scope` | `( name pairs count fuel deciding -- root identity fuel' 0 \| status )`, `( level fuel -- fuel' outcome )` | the environment's answers to inference, above |
| `lf-hterm-unsupported` | `( form -- index identity true \| false )` | for importers: a leaf for an unsupported form (`lf-form-let`, `-nat`, `-string`, `-mdata`, `-proj`) |

### Diagnostics

Failures record a reason in the context's diagnostic
([catalogue](DIAGNOSTICS.md)): 15 dependency list full, 16 dependency
pool full, 25 environment handle, 26 check started too early, 27 no
snapshot, 28 publisher re-check failed (part 6: a check that moved its
snapshot), 29 internal fault (a `THROW`, including a check's changed
stack or a refused internal word; a publication that ended without a
final slot; or a begin in a spent context),
35 dependency undecided, 41 dependency unsupported, 50 unknown constant
(N1), 51 name already declared (N2), 52 wrong number of universe levels
(L1), 53 undeclared universe parameter (L2), 54 duplicate universe
parameter (L3); and 20 (bad argument) for a bad name or start.
check-declaration adds 42 (U1: the kind and safety) and 43 (U2: the form
and the node), and records 20 for a definition or theorem without a value
and 55, 57 and 60 at its own site. Recording never changes an outcome;
`lf-env-begin` clears the record.

## The input is per context in v0

ADR 0012 (E1) makes the input one shared, read-only tier and the
environment shared. Since the per-task contexts (ADR 0009), the term,
level, name and reference stores are context members, so in v0 the input
— and its declarations, marks and fingerprint — lives in the context that
loaded it. The environment itself is outside every context, shared and
written only by the publisher. An environment records the fingerprint of
the input it was made over (every input store's records, identities,
count and generation below its mark, then the name bytes in use and
their count) and is valid only in a context whose input is intact and has
that fingerprint. So:

- the serial driver runs in the context that loaded the input, and after
  a `THROW` in a check in a new context from the caller's maker, which
  must load the same input again, the same way (G-P6): the fingerprint
  covers the input stores' identities and generations, so it records how
  the input was loaded, not only what it holds, and a context that loaded
  the input twice can be continued only by one that did the same;
- a context in which a check threw stays spent for good: when that is the
  main context, which can never be freed, the program can check nothing
  more in it, so a caller that may meet a `THROW` should start the run in
  a context of its own;
- for checks in several contexts, each context must load the same input
  from a fresh start (the tests do this; a context then gets the same IDs,
  indices and fingerprint);
- a context holding no input, or another one (even one that differs only
  in the text of its names), sees no environment: every word fails closed
  with invalid.

**What the fingerprint is for, and its limits** (ADR 0012, amended
2026-11-02). It guards against mistakes, such as checking in a context
that loaded another input. It is not a defence against forgery: its
FNV-style mixing is not a cryptographic hash, and two different inputs
can share one. It is computed once, when loading ends; later changes to
the input are caught by `lf-input-intact?`, as far as counts and
identities show, and by the tests' digests, never by the fingerprint.

Plan task 7.2.1 splits the stores into a shared input tier and
per-context scratch, after which one loaded input serves every context
and a replacement context needs no reload.

## What is implemented, and what is not

| ADR 0012 | v0 |
| --- | --- |
| E1 three kinds of storage | input (per context, see above), environment (shared, `ALLOCATE`d), context (candidate and snapshot); store marks end loading and roll scratch back after every check |
| E2 the record | state, outcome, the input declaration copied whole (name, kind, safety, type and value roots, hint, parameters), dependencies, axiom set, provenance |
| E3 snapshots and handles | identity serial that never repeats; snapshots (identity, `i`); handles and results read only within the snapshot; caches: none (task 4.2.7) |
| E4 staging and publishing | done, with the re-check (the name part as amended: every same-named earlier slot final and rejected), the final mark last and `THROW` recovery; a check that begins another declaration is a fault |
| E5 finding a constant | linear scan of earlier input names, structural name comparison, K5 unknown first; the name index is task 6.2.1 |
| E6 axiom sets | bit sets joined from direct dependencies and re-checked; allowlist version 0 is empty, so every set is empty; a test-only allowlist bit exercises the union |
| E7 contexts and one publisher | the candidate is a context record; the publisher is one task, and its entry, `lf-env-hand-over`, and the words that make, choose and free environments refuse inside a job or a check the serial driver runs (which holds the check owner token), and every internal word that writes shared state throws there (G-P1); a check's stack is checked as a job's is; a context in which a check threw, or whose stack changed, is spent and replaced by a validated one (G-P6); parallel checks by a scheduler, through `lf-env-hand-over-job`, are shown in the tests, not built (phase 7). The test scheduler publishes only between jobs, and the pool's lock in `job-submit` orders each publication before every check handed out later. Publishing while other checks still run relies on a slot's fields becoming visible before its final mark, as stores in program order do on x86-64; a lock or memory barrier around the mark (G-P2) belongs to the phase-7 scheduler |
| E8 run modes | final mode only; a provenance bit is joined and re-checked, but nothing loads saved results (tasks 2.2.5, 3.4.3) |
| E9 outcomes | as above |

`check-declaration` (task 2.2.3) is done ([above](#check-declaration-plan-task-223)).
Not done here: the failure-path suite
with allocation-failure injection (tasks 2.2.4, 1.4.6: no injection
exists, so "the k-th allocation fails" is untested), the replay record
(task 2.2.5), retiring or repurposing `src/kernel/mixed-signature-probe.fs`
and `src/core/generation-handles.fs` (ADR 0012 asks task 2.2.2 to do it;
left for after the context conversion), and replacing the hand-written
count saving in the existing modules with store marks.

## Measured limits (2026-11-02, this machine, `gforth` not `gforth-fast`)

| Limit | Value |
| --- | --- |
| Declarations per input | 32 (`lf-input-capacity`); Mathlib has 729,263 constants |
| Universe parameters per declaration | 8 (`lf-param-capacity`); Mathlib uses up to 30 |
| Dependencies per check | 16 (`lf-env-dep-capacity`) |
| Dependencies per environment | at most 65,536 (`lf-env-pool-max`), chosen when made |
| Memory | slot 176 bytes, candidate 176, worker record 16, input declaration 128, header 80 with the publisher's pool mark (64-bit cells); an environment of 27 slots and 8 dependencies 5,016 bytes, of 32 slots and 65,536 dependencies 1,054,344 |
| Time, Gforth 1.0 | 0.73 ms per run of the 27-declaration test input (1,000 runs, including making and freeing the environment; 0.65 ms before the second review round's guards, measured earlier the same day); 18 µs per lookup among 27 declarations (16.9 µs earlier, with the same lookup code: the machine's own variation) |
| Time, Gforth 0.7.3 | 1.54 ms per run (1.41 ms before); 31 µs per lookup (27 µs earlier) |

A lookup costs time linear in the input, and audits the name store each
time: fine for phase 2, far too slow at Mathlib scale (the name index,
task 6.2.1, and the scale assessment's data structures).

## Tests and evidence

`make test-environment`, part of `make test`:

- `tests/lib/store-mark.fs`: store marks, every refusal, and 20,000 random
  operations against an independent model.
- `tests/core/environment.fs`: ADR 0012's test rows 2–8 on a 27-declaration
  input reaching every outcome (ok, rejected, unknown, unsupported,
  invalid, exhausted, full), with a digest check after every step (only
  the declaration's own slot changes; the input region never; a failure
  appends nothing); handles; fuel at every step, no room, a `THROW` in the
  publisher and in a check (the context spent, the serial run going on
  in a new one from its maker, and stopping when the maker fails); axiom
  sets and provenance on synthetic records; the publisher's re-check
  against wrong claims, including an ok claim after an undecided or
  unsupported earlier declaration of its name; K5's tie-break (unknown
  first, in either order); a check that begins another declaration;
  results read within the snapshot; the fingerprint's coverage of every
  input store and the name bytes; refusals inside a job (simulated),
  including every internal word that writes shared state; a serial check
  that tries to publish, step, run, make, choose or free environments or
  contexts (all refused) or that changes the stack (invalid, the context
  replaced); makers that give something other than a fresh context
  (junk, the main, the current, an owned or a spent one, the caller's) or
  the wrong number of cells, each stopping the run; that a run frees
  every context it made (heap blocks counted); a THROW after the final
  mark and a publication that ends without a final slot; a run over an
  input loaded twice, and the main context spent for good; corrupted
  state; determinism; diagnostics.
- `tests/core/environment-tasks.fs` and `environment-tasks-serial.fs`
  (row 9): checks as jobs in two contexts, threads on Gforth 1.0,
  cooperative on 0.7.3 (interleaving confirmed by overlapping steps), and
  the serial host, publishing in two different orders, give the serial
  verdicts and the same environment content, also when one check throws
  in its job (its lane's context is then replaced); a check started too
  early ends invalid; a context without the input, or with names of other
  text, sees nothing; a real job can neither publish nor make, choose or
  free an environment, no internal word writes one inside it, and
  readiness says false there; the scheduler publishes through
  `lf-env-hand-over-job`, which refuses a job whose snapshot moved to
  another declaration.
- Row 10: planted faults in a scratch copy, one at a time, all caught:
  the 26 of the first version (including the six ADR 0012 names) and 8
  in the store marks, re-run after the review fixes, and 24 more that
  bring back each fault the independent review found (the swapped K5
  order, `lf-input-intact?` without its name-bytes clause, each input
  store and the name bytes left out of the fingerprint, the old name
  re-check, and the removal of each new guard); listed in the gate
  summary. After the second review round those 58 were adapted and all
  caught again, and 39 more revert each of its fixes one at a time: 37
  are caught; the two that survive remove the guard at the entry of
  `lf-env-write` and `lf-env-made`, whose first callee refuses before
  anything is written, so no behaviour can tell them apart.

The tests above drive the environment with a *synthetic check* that does
with it what `check-declaration` does (own name, lookups, dependencies),
and no typing. With check-declaration (plan task 2.2.3; also in `make
test-environment`, and the differentials in `make check`):

- Row 1: the 60 rows of the [expected results](../reviews/FIRST_CHECKER_EXPECTED.md)
  and the 22 of the binder-domain table (ADR 0003, Amendment 1), end to
  end through the environment against pinned Lean (`make
  test-first-checker-differential`, `test-binder-domains-differential`):
  every accepted row has a valid handle and an empty axiom set and prints
  its label; no other slot gives a handle. All 60 equal the table; three
  binder-domain rows meet the 64-node term store and give *unknown* or
  *full* instead (both failures; see the expected results).
- Row 4: 17 universe-scope cases against pinned Lean
  (`tests/reference/universe-scope-terms.lean`, `make
  test-universe-scope-differential`): zero, exact, too few and too many
  levels, undeclared parameters (in a `Sort`, in an argument, in a nested
  argument) and repeated ones, a callee's parameters swapped and
  unswapped, a caller's listed in another order, and nested `max`/`imax`
  arguments, one of them equal only after Lean's normalisation (*unknown*,
  K4).
- `tests/core/check-declaration.fs`: every outcome with its step and
  diagnostic, Lean's order (between steps, a function before its
  argument, a domain before its body, an undecided dependency before a
  later rejection, the audit before typing), the dependencies an accepted
  declaration records, the input unchanged, and fuel sweeps (exhausted
  below some fuel, then the final outcome; never accepted earlier).
- `tests/core/check-declaration-ndjson.fs`: the pinned NDJSON exports of
  four fixtures checked end to end and accepted, and changed copies
  rejected, unsupported (U1, U2) and invalid (V1).

## Trust

This is [kernel] code under the review gate of `AGENTS.md`: its rules
follow ADR 0011 and 0012 (Lean's behaviour as those records trace it), and
the tests above agree. An independent AI review of the first version
(2026-11-02) found two faults (an ok claim after an undecided earlier
declaration of its name, and a fingerprint blind to name text) and
several gaps; they are fixed here and recorded as amendments to ADR 0012.
Its second round (2026-11-02) found no path by which a failed check is
published or read as accepted, but guard gaps: checks the serial driver
runs were outside the one-writer rule, its checks' stack effects were not
checked, it trusted the maker's context, and internal words wrote shared
state unguarded. They are fixed here and recorded as clarifications in
ADR 0012, Amendment 1, items 5–11. The fixes still need an independent
review of the exact change and the owner's approval of a plain-language
summary. It is untrusted until then,
and every accepted result is *experimental — not independently audited*
after that.
