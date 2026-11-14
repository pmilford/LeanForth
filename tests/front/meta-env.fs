\ Unit tests of the front end's environment view (plan FE1c;
\ src/front/meta-env.fs), over the Init slice tests/front/whnf-slice.ndjson
\ and its elaboration data: every kind of declaration found by name, its
\ parameters, type and value; every reducibility status; canUnfold and
\ getUnfoldableConst? under each transparency mode; the facts not yet
\ available answering unsupported for definitions; every refusal
\ (invalid: a declaration beyond the input, a mode beyond the six, a name
\ that is not valid or not declared); no elaboration data, and a refused
\ read of it, answer unsupported where the status is needed and nothing
\ else changes; the queries allocate nothing. Every T{ }T checks the data
\ stack's depth. tests/front/check_unfold.py compares the answers with
\ pinned Lean. Loaded under HEX: loading must not depend on BASE.
include ../support/tester.fs
include ../support/heap-watch.fs
hex require ./menv-slice.fs base @ decimal constant base-after-load
menv-load

T{ base-after-load lf-tr-modes lf-tr-implicit lf-tr-all -> 16 6 5 0 }T

\ ---- Finding declarations: each kind, the newest of the name.
: kind-of ( c-addr u -- kind ) menv-decl lf-menv-kind ;
T{ s" Nat.add" kind-of s" Nat.zero_add" kind-of s" Classical.choice" kind-of
   -> lf-kind-definition lf-kind-theorem lf-kind-axiom }T
T{ s" Quot.lift" kind-of s" Nat" kind-of s" Nat.succ" kind-of s" Nat.rec" kind-of
   -> lf-kind-quotient lf-kind-inductive lf-kind-constructor lf-kind-recursor }T
T{ s" Nat.add" menv-name lf-menv-find nip s" Nat.add" menv-decl lf-menv-name
   -> outcome-ok s" Nat.add" menv-name }T
\ A name no declaration has (a binder's), a name that is not valid.
T{ 0 s" motive" menv-part lf-menv-find -> -1 outcome-invalid }T
T{ -5 lf-menv-find 0 lf-menv-find -> -1 outcome-invalid -1 outcome-invalid }T

\ Parameters, type, value, hint.
T{ s" Nat.add" menv-decl lf-menv-params nip s" id" menv-decl lf-menv-params nip -> 0 1 }T
T{ s" Nat.add" menv-decl lf-menv-value nip s" Classical.choice" menv-decl lf-menv-value
   -> true false }T
T{ s" Nat.add" menv-decl lf-menv-type lf-term-root? -> true }T
T{ s" Nat.zero_add" menv-decl lf-menv-hint -> lf-hint-opaque 0 }T
T{ s" Nat.add" menv-decl lf-menv-hint drop -> lf-hint-regular }T

\ ---- Reducibility statuses: each of the five, the default without a
\ record.
: status ( c-addr u -- status outcome ) menv-decl lf-menv-status ;
T{ s" HAdd.hAdd" status s" Prod.fst" status s" Nat.div" status
   -> elab-semireducible outcome-ok elab-reducible outcome-ok elab-irreducible outcome-ok }T
T{ s" id" status s" Nat.add" status
   -> elab-implicit-reducible outcome-ok elab-instance-reducible outcome-ok }T
T{ -1 lf-menv-status lf-input-count lf-menv-status
   -> -1 outcome-invalid -1 outcome-invalid }T

\ ---- canUnfoldDefault under each mode, as bits all .. implicit.
: bits ( d -- u|-1 )
  0 lf-tr-modes 0 ?do
    over i lf-menv-can-unfold ok? 0= if 2drop drop -1 unloop exit then
    1 and i lshift or loop nip ;
: unfolds ( c-addr u -- u|-1 ) menv-decl bits ;
\ all default reducible instances none implicit: bits 0 1 2 3 4 5.
T{ s" HAdd.hAdd" unfolds s" Prod.fst" unfolds s" Nat.div" unfolds -> 3 47 1 }T
T{ s" id" unfolds s" Nat.add" unfolds -> 35 43 }T
\ Statuses do not depend on kind: a theorem's canUnfold under all holds.
T{ s" Nat.zero_add" unfolds -> 3 }T
T{ s" Nat.add" menv-decl 6 lf-menv-can-unfold s" Nat.add" menv-decl -1 lf-menv-can-unfold
   -> false outcome-invalid false outcome-invalid }T
T{ lf-input-count lf-tr-all lf-menv-can-unfold -> false outcome-invalid }T

\ ---- getUnfoldableConst?: definitions only.
: unfoldable ( c-addr u mode -- flag outcome ) >r menv-name r> lf-menv-unfoldable rot drop ;
T{ s" Nat.add" lf-tr-default unfoldable s" Nat.add" lf-tr-reducible unfoldable
   -> true outcome-ok false outcome-ok }T
T{ s" Nat.zero_add" lf-tr-all unfoldable s" Nat.rec" lf-tr-all unfoldable
   -> false outcome-ok false outcome-ok }T
T{ s" Quot.lift" lf-tr-all unfoldable s" Classical.choice" lf-tr-all unfoldable
   -> false outcome-ok false outcome-ok }T
T{ s" Nat.add" menv-name lf-tr-all lf-menv-unfoldable nip nip s" Nat.add" menv-decl
   -> outcome-ok s" Nat.add" menv-decl }T
T{ 0 s" motive" menv-part lf-tr-all lf-menv-unfoldable -> -1 false outcome-invalid }T
T{ s" Nat.add" menv-name lf-tr-modes lf-menv-unfoldable -> -1 false outcome-invalid }T

\ ---- Facts of format 2 (S1 appendix D): a definition's from the data, a
\ definition no record names none of them, other kinds false, the three
\ Eq.ndrec names auxiliary recursors; smart unfolding still unsupported
\ for a definition (no data has it).
: fact ( c-addr u xt -- flag outcome ) >r menv-decl r> execute ;
T{ s" Nat.add.match_1" ' lf-menv-matcher? fact s" Nat.rec" ' lf-menv-matcher? fact
   s" Nat.add" ' lf-menv-matcher? fact -> true outcome-ok false outcome-ok false outcome-ok }T
T{ s" HAdd.hAdd" ' lf-menv-proj-fn? fact s" HAdd.mk" ' lf-menv-proj-fn? fact
   s" instHAdd" ' lf-menv-proj-fn? fact -> true outcome-ok false outcome-ok false outcome-ok }T
T{ s" Nat.add" ' lf-menv-smart? fact s" Nat.zero_add" ' lf-menv-smart? fact
   -> false outcome-unsupported false outcome-ok }T
T{ s" Nat.casesOn" ' lf-menv-aux-recursor? fact s" Eq.ndrec" ' lf-menv-aux-recursor? fact
   s" Nat.add" ' lf-menv-aux-recursor? fact -> true outcome-ok true outcome-ok false outcome-ok }T
T{ s" Eq.refl" ' lf-menv-aux-recursor? fact s" Nat.succ" ' lf-menv-aux-recursor? fact
   -> false outcome-ok false outcome-ok }T
T{ -1 lf-menv-matcher? lf-input-count lf-menv-aux-recursor? -1 lf-menv-smart?
   -> false outcome-invalid false outcome-invalid false outcome-invalid }T
T{ -1 lf-menv-proj-fn? -> false outcome-invalid }T
\ The other two names isAuxRecursor lists; HEq.ndrec is no Eq.ndrec (the
\ data's answer); Fin.succ is no Nat.succ (review fe1c-2 L3); Nat's
\ namespace (reduceNat?).
T{ s" Eq.ndrec_symm" ' lf-menv-aux-recursor? fact s" Eq.ndrecOn" ' lf-menv-aux-recursor? fact
   -> true outcome-ok true outcome-ok }T
T{ s" HEq.ndrec" ' lf-menv-aux-recursor? fact -> false outcome-ok }T
T{ s" Nat.succ" menv-name lf-menv-nat-succ? s" Fin.succ" menv-name lf-menv-nat-succ?
   s" Nat" menv-name lf-menv-nat-succ? -> true false false }T
T{ s" Nat.add" menv-name lf-menv-nat-name? s" Fin.succ" menv-name lf-menv-nat-name?
   s" Nat" menv-name lf-menv-nat-name? s" Nat.add.match_1" menv-name lf-menv-nat-name?
   -> true false false false }T
\ Without data read against the stage a definition's facts are unknown.
0 lf-menv-stage!
T{ s" Nat.add.match_1" ' lf-menv-matcher? fact s" HAdd.hAdd" ' lf-menv-proj-fn? fact
   s" Nat.casesOn" ' lf-menv-aux-recursor? fact s" Nat.rec" ' lf-menv-matcher? fact
   -> false outcome-unsupported false outcome-unsupported false outcome-unsupported
      false outcome-ok }T
T{ s" Eq.ndrec" ' lf-menv-aux-recursor? fact -> true outcome-ok }T
menv-lib lf-menv-stage!

\ ---- The queries allocate nothing.
: queries ( -- )
  s" Nat.add" status 2drop s" Nat.div" unfolds drop s" Nat.add" lf-tr-default unfoldable 2drop
  s" Eq.ndrec" ['] lf-menv-aux-recursor? fact 2drop ;
T{ live-blocks @ queries live-blocks @ - -> 0 }T

\ ---- Without elaboration data the status is a missing fact: unsupported
\ where it is needed, all and none still answered; naming the stage
\ again restores every answer. A refused read (here of a sealed stage,
\ error 24) keeps nothing: the same as no data.
0 lf-menv-stage!
T{ s" Nat.add" status s" Nat.add" unfolds -> -1 outcome-unsupported -1 }T
T{ s" Nat.add" menv-decl lf-tr-all lf-menv-can-unfold
   s" Nat.add" menv-decl lf-tr-none lf-menv-can-unfold -> true outcome-ok false outcome-ok }T
T{ s" Nat.add" lf-tr-default unfoldable s" Nat.zero_add" lf-tr-default unfoldable
   -> false outcome-unsupported false outcome-ok }T
menv-lib lf-menv-stage!
T{ s" Nat.add" status s" Prod.fst" unfolds -> elab-instance-reducible outcome-ok 47 }T
\ Another stage named: its data, when read, is not this input's, and its
\ names are numbered otherwise: unsupported (review fe1c-2 L4).
create other /stage allot
12 other stage-init drop  s" tests/author/init-slice.ndjson" other stage-read drop
other lf-menv-stage!
T{ s" Nat.add" status -> -1 outcome-unsupported }T
s" tests/front/init-slice.elab.ndjson" other other stage-manifest manifest-digest elab-read drop
T{ s" Nat.add" status other elab-read-against? -> -1 outcome-unsupported true }T
menv-lib lf-menv-stage!
T{ s" Nat.add" status -> -1 outcome-unsupported }T
T{ menv-data menv-lib menv-digest elab-read elab-error-code -> outcome-invalid 24 }T
T{ s" Nat.add" status s" Prod.fst" unfolds -> -1 outcome-unsupported -1 }T
\ The fed input as loading left it, also after the run mode's reset
\ (lfc-empty's) forgot the decoded library and the text list (S1 §1, trust
\ point 3; fault fe-env-intact).
T{ lf-input-intact? lf-menv-reset lf-input-intact? -> true true }T
\ Binder kinds in the fed mode come from the stage named (S1 §4):
\ HAdd.hAdd {α β γ} [self] (a b), none without a stage.
menv-lib lf-menv-stage!
T{ s" HAdd.hAdd" menv-decl lf-menv-kinds nip -> 6 }T
T{ 0 lf-menv-stage! s" HAdd.hAdd" menv-decl lf-menv-kinds nip -> 0 }T

bye
