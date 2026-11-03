# The checked environment (v0)

Status: implemented 2026-11-02 as plan task 2.2.2, following
[ADR 0012](../adr/0012-checked-environment.md), whose design the owner
accepted (gate answers G8–G11). **Experimental [kernel] code, not through
the review gate and not independently audited.** It decides nothing about
a declaration's terms: the type check that fills it, `check-declaration`
(plan task 2.2.3), is not written yet, so nothing in LeanForth accepts a
theorem today. Until an outside Lean expert has audited the checker, every
accepted result is *experimental — not independently audited*.

Source: `src/core/input.fs` (the input), `src/core/name-equal.fs`
(structural name equality), `src/kernel/environment.fs` (environments,
snapshots, lookups, handles, candidates), `src/kernel/env-publish.fs` (the
publisher and the serial driver), and the store marks of
`src/lib/store.fs` ([library notes](../development/FORTH_LIBRARY.md)).

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
gets one slot per declaration. The check is a *stand-in* that does only
the environment's part of a check (its own name, then the constant its
value names) and **no typing at all**: its "ok" says nothing about the
terms, and stands in for `check-declaration` (task 2.2.3).

```forth
\ Helpers for the example (documentation only, not part of LeanForth).
[undefined] lf-env-publish [if] require ~+/src/kernel/env-publish.fs [then]
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

\ The names, the universe parameter u, Sort u and Prop.
lf-ssession-begin made
s" u" id constant u
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

\ The stand-in check: N2 on the declaration's own name, then the constant
\ its value names (myId, in the theorem), then ok. NO TYPING.
: go-on? ( outcome -- flag ) dup ok? if drop true else lf-env-finish false then ;
: theorem? ( -- flag ) lf-env-cand lf-cand-decl @ 1 = ;
: uses-myId ( -- flag ) theorem? if myId lf-env-resolve nip go-on? else true then ;
: stand-in ( -- )
  lf-env-own-name go-on? 0= if exit then uses-myId if outcome-ok lf-env-finish then ;

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
2, each slot, the diagnostic of the last check (code 51, *name already
declared*: the name's ID 2 and the accepted slot 0), and a handle to slot
0 checked in a view of the whole environment:

```forth
8 lf-env-new ok! lf-env-use ok!
' stand-in lf-env-run outcome-text type cr
0 .slot 1 .slot 2 .slot
.diag cr
lf-env-view ok!  0 lf-env-handle ok! lf-env-handle? outcome-text type cr
```

```text
ok
0 : ok, uses none, axioms none
1 : ok, uses 0, axioms none
2 : rejected
51 environment lf-env-own-name: 2 0
ok
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
| `lf-input-end` | `( -- outcome )` | end loading: mark every input store (terms, levels, names, references, declarations) and record the input's fingerprint; invalid when already ended |
| `lf-input-intact?` | `( -- flag )` | loading ended and every mark still valid (no reset, nothing rolled back below it) |
| `lf-input-rollback` | `( -- outcome )` | return every input store to its mark (a check's scratch); invalid, with nothing changed, when the input is not intact |
| `lf-input-reset` | `( -- )` | start a new input in this context; every environment over the old one fails closed |
| `lf-input-count`, `lf-input-decl`, `lf-input-name`, `lf-input-params`, `lf-input-read`, `lf-input-fingerprint` | readers | `lf-input-read ( i -- decl outcome )` is the checked one |

### Environments, checks and lookups (`src/kernel/environment.fs`)

| Word | Stack effect | Does |
| --- | --- | --- |
| `lf-env-new` | `( deps -- env outcome )` | a new environment over this context's intact input, one slot per declaration, room for `deps` dependencies (0 … 65,536), allowlist version 0 (empty), final mode; invalid for an input that is not intact, full when identities are spent or memory is short |
| `lf-env-use`, `lf-env`, `lf-env-free` | `( env -- outcome )`, `( -- env )`, `( env -- outcome )` | choose, read and free the current environment; only while no job runs |
| `lf-env-begin` | `( i -- outcome )` | start the check of declaration `i` in this context: records the snapshot (identity, `i`), clears the candidate and the diagnostic; invalid without a valid environment or for a slot out of range or already final |
| `lf-env-view` | `( -- outcome )` | a snapshot of every slot, for queries after a run |
| `lf-env-own-name` | `( -- outcome )` | N2 on the checked declaration's name: ok, rejected (an earlier one accepted), unknown or unsupported (an earlier one undecided, K5) |
| `lf-env-lookup` | `( name -- d outcome )` | find a constant (E5): `d ok` for the accepted earlier declaration of that name; rejected (N1: unknown, forward or self reference); unknown or unsupported (K5); invalid when a same-named earlier slot is not final (started too early) |
| `lf-env-depend`, `lf-env-resolve` | `( d -- outcome )`, `( name -- d outcome )` | record a dependency on accepted slot `d` (ascending, distinct; its axiom set and provenance joined); full at `lf-env-dep-capacity` (16); resolve is lookup then depend |
| `lf-env-finish` | `( outcome -- )` | end the check with its outcome (invalid until called) |
| `lf-env-params`, `lf-env-arity?`, `lf-env-param?`, `lf-env-own-params` | | universe parameters: a slot's own list; L1 (exact number of levels), L2 (a parameter of the checked declaration), L3 (no parameter twice): ok or rejected |
| `lf-env-handle`, `lf-env-handle?` | `( d -- identity d outcome )`, `( identity d -- outcome )` | a handle to an accepted slot; valid in a snapshot (identity′, `i`) only for the same identity, `d < i`, a final accepted slot; anything else is invalid |
| `lf-env-ready?` | `( name i -- flag )` | for a scheduler (G-P5): every declaration before `i` with that name has a final slot |
| `lf-env-outcome`, `lf-env-axioms` | `( d -- outcome )`, `( d -- bits outcome )` | results: a final slot's outcome (invalid before), an accepted slot's axiom set |

### Publishing (`src/kernel/env-publish.fs`)

| Word | Stack effect | Does |
| --- | --- | --- |
| `lf-env-publish` | `( -- outcome )` | E4: for an ok candidate, re-check (every same-named earlier slot final and none accepted; dependencies ascending, below, final, accepted; axiom set and provenance the unions of theirs, within the allowlist and "checked" in a final run; a safe definition or theorem with a value and distinct parameters), then append the dependencies (full if no room) and copy the input declaration; any other outcome alone; last, mark the slot final |
| `lf-env-hand-over` | `( -- outcome fault? )` | publish under `CATCH`: after a `THROW` the slot stays not final and cleared, the pool rolled back; `fault?` true means the run must stop |
| `lf-env-step` | `( xt i -- outcome fault? )` | begin, run the check `xt ( -- )` (a `THROW` makes it invalid), hand over, roll the scratch back |
| `lf-env-run` | `( xt -- outcome )` | the serial publisher of phase 2: every declaration in input order; ok when all slots are final, invalid when a fault stopped it |
| `lf-env-before-final` | deferred `( -- )` | test-only fault injection between writing a slot and marking it final |

### Diagnostics

Failures record a reason in the context's diagnostic
([catalogue](DIAGNOSTICS.md)): 15 dependency list full, 16 dependency
pool full, 25 environment handle, 26 check started too early, 27 no
snapshot, 28 publisher re-check failed, 29 internal fault (a `THROW`),
35 dependency undecided, 41 dependency unsupported, 50 unknown constant
(N1), 51 name already declared (N2), 52 wrong number of universe levels
(L1), 53 undeclared universe parameter (L2), 54 duplicate universe
parameter (L3); and 20 (bad argument) for a bad name or start. Recording
never changes an outcome; `lf-env-begin` clears the record.

## The input is per context in v0

ADR 0012 (E1) makes the input one shared, read-only tier and the
environment shared. Since the per-task contexts (ADR 0009), the term,
level, name and reference stores are context members, so in v0 the input
— and its declarations, marks and fingerprint — lives in the context that
loaded it. The environment itself is outside every context, shared and
written only by the publisher. An environment records the fingerprint of
the input it was made over (every input store's records, identities,
count and generation below its mark; not the name bytes) and is valid only
in a context whose input is intact and has that fingerprint. So:

- the serial driver runs in the context that loaded the input;
- for checks in several contexts, each context must load the same input
  from a fresh start (the tests do this; a context then gets the same IDs,
  indices and fingerprint);
- a context holding no input, or another one, sees no environment: every
  word fails closed with invalid.

Plan task 7.2.1 splits the stores into a shared input tier and
per-context scratch, after which one loaded input serves every context.

## What is implemented, and what is not

| ADR 0012 | v0 |
| --- | --- |
| E1 three kinds of storage | input (per context, see above), environment (shared, `ALLOCATE`d), context (candidate and snapshot); store marks end loading and roll scratch back after every check |
| E2 the record | state, outcome, the input declaration copied whole (name, kind, safety, type and value roots, hint, parameters), dependencies, axiom set, provenance |
| E3 snapshots and handles | identity serial that never repeats; snapshots (identity, `i`); handles validated as above; caches: none (task 4.2.7) |
| E4 staging and publishing | done, with the re-check, the final mark last and `THROW` recovery |
| E5 finding a constant | linear scan of earlier input names, structural name comparison; the name index is task 6.2.1 |
| E6 axiom sets | bit sets joined from direct dependencies and re-checked; allowlist version 0 is empty, so every set is empty; a test-only allowlist bit exercises the union |
| E7 contexts and one publisher | the candidate is a context record; the publisher is one task; parallel checks by a scheduler are shown in the tests, not built (phase 7). The test scheduler publishes only between jobs, and the pool's lock in `job-submit` orders each publication before every check handed out later. Publishing while other checks still run relies on a slot's fields becoming visible before its final mark, as stores in program order do on x86-64; a lock or memory barrier around the mark (G-P2) belongs to the phase-7 scheduler |
| E8 run modes | final mode only; a provenance bit is joined and re-checked, but nothing loads saved results (tasks 2.2.5, 3.4.3) |
| E9 outcomes | as above |

Not done here: `check-declaration` (task 2.2.3), the failure-path suite
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
| Memory | slot 176 bytes, candidate 176, input declaration 128, header 48 (64-bit cells); an environment of 27 slots and 8 dependencies 4,984 bytes, of 32 slots and 65,536 dependencies 1,054,312 |
| Time, Gforth 1.0 | 0.63 ms per run of the 27-declaration test input (1,000 runs, including making and freeing the environment); 14.6 µs per lookup among 27 declarations |
| Time, Gforth 0.7.3 | 1.39 ms per run; 26 µs per lookup |

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
  publisher and in a check; axiom sets and provenance on synthetic records;
  the publisher's re-check against wrong claims; corrupted state;
  determinism; diagnostics.
- `tests/core/environment-tasks.fs` and `environment-tasks-serial.fs`
  (row 9): checks as jobs in two contexts, threads on Gforth 1.0,
  cooperative on 0.7.3 (interleaving confirmed by overlapping steps), and
  the serial host, publishing in two different orders, give the serial
  verdicts and the same environment content; a check started too early
  ends invalid; a context without the input sees nothing.
- Row 10: 26 planted faults in a scratch copy, including the six ADR 0012
  names, all caught; listed in the change's gate summary.

The tests drive the environment with a *synthetic check* that does what
`check-declaration` will do with it (own name, lookups, dependencies) and
no typing. Row 1 (the 60-row table) and the universe-substitution rows of
row 4 need task 2.2.3.

## Trust

This is [kernel] code under the review gate of `AGENTS.md`: its rules
follow ADR 0011 and 0012 (Lean's behaviour as those records trace it), the
tests above agree, and it still needs an independent AI review of the
exact change and the owner's approval of a plain-language summary. It is
untrusted until then, and every accepted result is *experimental — not
independently audited* after that.
