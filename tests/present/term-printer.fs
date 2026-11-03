\ Unit tests of the presentation side table and the term printer: every
\ public word's success and failure outcomes, stale entries, fuel, visit
\ and pool limits, a busy printer, and the Markdown wrappers. The printed
\ text of many more cases is in print-cases.golden (check_golden.py).
require ./build.fs

variable t1   variable t2   variable t3

\ Side table: binders.
fresh
T{ t-prop dup t1 ! 0 t-var t-lam t2 ! -> }T
T{ t2 @ s" x" nm lf-binder-implicit lf-pres-binder! -> outcome-ok }T
T{ t2 @ lf-pres-binder@ -> s" x" nm lf-binder-implicit true }T
T{ t2 @ s" x" nm 4 lf-pres-binder! -> outcome-invalid }T
T{ t2 @ s" x" nm -1 lf-pres-binder! -> outcome-invalid }T
T{ t2 @ 99 lf-binder-default lf-pres-binder! -> outcome-invalid }T
T{ t1 @ s" x" nm lf-binder-default lf-pres-binder! -> outcome-invalid }T
T{ 63 s" x" nm lf-binder-default lf-pres-binder! -> outcome-invalid }T
T{ t1 @ lf-pres-binder@ -> false }T
\ Side table: sources.
T{ t1 @ 17 lf-pres-source! -> outcome-ok }T
T{ t1 @ lf-pres-source@ -> 17 true }T
T{ t1 @ -1 lf-pres-source! -> outcome-invalid }T
T{ t2 @ lf-pres-source@ -> false }T
T{ t2 @ 0 lf-pres-source! -> outcome-ok }T
T{ t2 @ lf-pres-source@ t2 @ lf-pres-binder@ -> 0 true s" x" nm lf-binder-implicit true }T
T{ 63 5 lf-pres-source! -> outcome-invalid }T
\ A reset of either store makes entries stale; a new term at the same
\ index starts with an empty entry.
lf-term-reset lf-ssession-begin drop
T{ t-prop dup 0 t-var t-lam -> t1 @ t2 @ }T
T{ t2 @ lf-pres-binder@ -> false }T
T{ t1 @ lf-pres-source@ -> false }T
T{ t2 @ s" y" nm lf-binder-strict lf-pres-binder! -> outcome-ok }T
lf-name-reset
T{ t2 @ lf-pres-binder@ -> false }T
\ Binder kinds in Lean's export spelling.
T{ s" default" lf-pres-kind-text -> lf-binder-default true }T
T{ s" implicit" lf-pres-kind-text -> lf-binder-implicit true }T
T{ s" strictImplicit" lf-pres-kind-text -> lf-binder-strict true }T
T{ s" instImplicit" lf-pres-kind-text -> lf-binder-instance true }T
T{ s" explicit" lf-pres-kind-text -> false }T

\ Side table: declarations.
fresh
T{ t-prop t1 ! s" c" nm t1 @ lf-pres-declare -> outcome-ok }T
T{ s" c" nm lf-pres-type@ -> t1 @ true }T
T{ 1 t-sort t2 ! s" c" nm t2 @ lf-pres-declare -> outcome-ok }T
T{ s" c" nm lf-pres-type@ -> t2 @ true }T
T{ s" d" nm lf-pres-type@ -> false }T
T{ s" d" nm 63 lf-pres-declare -> outcome-invalid }T
T{ 99 t1 @ lf-pres-declare -> outcome-invalid }T
: fill-declarations ( -- outcome )
  lf-pres-declaration-capacity 1- 0 ?do s" c" nm i lf-name-num must t1 @ lf-pres-declare
  drop loop
  s" full" nm t1 @ lf-pres-declare ;
T{ fill-declarations -> outcome-exhausted }T
lf-term-reset lf-ssession-begin drop
T{ s" c" nm lf-pres-type@ -> false }T

\ Printing: outcomes and limits.
fresh 0 mode
T{ t-prop 0 t-var 1 t-var t-pi s" proof" ex. t-pi s" P" im. t1 ! -> }T
T{ cap-reset t1 @ fuel lf-print-term -> outcome-ok }T
T{ s" ∀ {P : Prop}, P → P" expect-text -> }T
T{ 63 fuel lf-print-term -> outcome-invalid }T
T{ -1 fuel lf-print-term -> outcome-invalid }T
T{ t1 @ -1 lf-print-term -> outcome-invalid }T
T{ t1 @ 0 lf-print-term -> outcome-exhausted }T
T{ 0 t-var 5 lf-print-term -> outcome-invalid }T
T{ t-prop 3 t-var t-lam 50 lf-print-term -> outcome-invalid }T
\ Fuel: the exact need prints, one unit less is exhausted with none left.
: need ( t -- n ) fuel lf-print-term must-ok fuel lf-print-fuel @ - ;
T{ t1 @ need t2 ! -> }T
T{ t1 @ t2 @ lf-print-term lf-print-fuel @ -> outcome-ok 0 }T
T{ t1 @ t2 @ 1- lf-print-term lf-print-fuel @ -> outcome-exhausted 0 }T
\ Nested visits: a tight limit is exhausted; lf-print-limit! needs >= 1.
T{ 0 lf-print-limit! -> false }T
T{ 2 lf-print-limit! -> true }T
T{ t1 @ fuel lf-print-term -> outcome-exhausted }T
T{ lf-print-default-limit lf-print-limit! -> true }T
T{ t1 @ fuel lf-print-term -> outcome-ok }T
\ A stale constant reference, a corrupted tag and a level parameter that
\ is not a name are invalid.
T{ args{ s" k" t-const t2 ! lf-cref-reset t2 @ fuel lf-print-term -> outcome-invalid }T
T{ t-prop t3 ! 99 t3 @ lf-term-slot node-tag ! t3 @ fuel lf-print-term -> outcome-invalid
  }T
T{ 999 lf-level-param must ssort fuel lf-print-term -> outcome-invalid }T

\ A busy printer refuses a nested print from its sink; afterwards it works.
variable nested   variable nested-result
: nested-sink ( c-addr u -- )
  cap-sink nested @ if exit then true nested ! t1 @ fuel lf-print-term nested-result ! ;
T{ false nested ! ' nested-sink 0 lf-print-setup -> }T
T{ cap-reset t1 @ fuel lf-print-term nested-result @ -> outcome-ok outcome-invalid }T
T{ 0 mode cap-reset t1 @ fuel lf-print-term -> outcome-ok }T

\ Binder names fill the pool: 45 binders of 98 bytes that must all differ
\ (the text goes nowhere).
: long-name ( -- c-addr u )
  s" a-rather-long-binder-name-repeated-in-one-fun-again-and-again-and-again-to-about-a-hundred-bytes" ;
: long-fun ( -- t ) t-prop 0 t-var 45 0 do over swap t-lam long-name ex. loop nip ;
: no-sink ( c-addr u -- ) 2drop ;
T{ fresh ' no-sink 0 lf-print-setup long-fun fuel lf-print-term -> outcome-exhausted }T

\ Levels and names on their own; Markdown math.
fresh 0 mode
T{ cap-reset s" u" lparam s" v" lparam lmax fuel lf-print-level -> outcome-ok }T
T{ s" max u v" expect-text -> }T
T{ 63 fuel lf-print-level -> outcome-invalid }T
T{ cap-reset s" Nat" nm s" add" nm. lf-print-name -> outcome-ok }T
T{ s" Nat.add" expect-text -> }T
T{ 999 lf-print-name -> outcome-invalid }T
T{ t-prop 0 t-var 1 t-var t-pi s" proof" ex. t-pi s" P" im. t1 ! -> }T
T{ cap-reset t1 @ fuel lf-print-inline -> outcome-ok }T
T{ s" $\forall \{P : \mathrm{Prop}\},\ P \to P$" expect-text -> }T
T{ cap-reset t1 @ fuel lf-print-display -> outcome-ok }T
T{ s" $$\forall \{P : \mathrm{Prop}\},\ P \to P$$" expect-text -> }T
\ The wrappers leave the mode as it was.
T{ cap-reset t1 @ fuel lf-print-term -> outcome-ok }T
T{ s" ∀ {P : Prop}, P → P" expect-text -> }T
\ A statement's spine is a proposition even when the quick test cannot
\ tell: c is a constant of unknown type.
T{ t-prop args{ s" c" t-const 0 t-var t-app t-pi s" x" ex. t2 ! -> }T
T{ cap-reset t2 @ fuel lf-print-term -> outcome-ok }T
T{ s" (x : Prop) → c x" expect-text -> }T
T{ cap-reset t2 @ fuel lf-print-statement -> outcome-ok }T
T{ s" ∀ (x : Prop), c x" expect-text -> }T
bye
