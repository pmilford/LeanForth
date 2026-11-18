\ Unit tests of the presentation side table and the term printer: every
\ public word's success and failure outcomes, stale entries, fuel, visit
\ limits, a pool and a scope that grow until the heap refuses, a busy
\ printer, and the Markdown wrappers. The printed text of many more cases
\ is in print-cases.golden (check_golden.py).
include ../support/heap-watch.fs
require ./build.fs
require ../support/store-faults.fs
require ../../src/present/statement-forms.fs

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
\ Reading an entry never grows the slab, only recording one does (Forth
\ review of perf1, finding 2): the slab made again as the module makes it.
: pres-slab-again ( -- )
  lf-pres-terms slab-free  /lf-pterm dup slab-limit-max lf-pres-terms slab-init drop ;
pres-slab-again
T{ t2 @ lf-pres-binder@ t1 @ lf-pres-source@ lf-pres-terms slab-capacity
   -> false false 0 }T
T{ t1 @ 7 lf-pres-source! lf-pres-terms slab-capacity 0> -> outcome-ok true }T
\ An entry the slab cannot hold is refused as full, changing nothing
\ (review rvPF1 4): the slab made again with room for one entry holds
\ t1's, the first unit, not t2's; then made again as the module makes it.
lf-pres-terms slab-free  /lf-pterm 1 lf-pres-terms slab-init drop
T{ t1 @ lf-pres-unit t2 @ lf-pres-unit 0> -> 0 true }T
T{ t2 @ s" x" nm lf-binder-default lf-pres-binder! t2 @ 3 lf-pres-source!
   -> outcome-full outcome-full }T
T{ t2 @ lf-pres-binder@ t2 @ lf-pres-source@ lf-pres-terms slab-capacity
   -> false false 0 }T
T{ t1 @ 5 lf-pres-source! t1 @ lf-pres-source@ -> outcome-ok 5 true }T
T{ t2 @ 3 lf-pres-source! t1 @ s" x" nm lf-binder-default lf-pres-binder!
   -> outcome-full outcome-invalid }T
pres-slab-again
\ The entries the staleness tests below read, recorded again in the new
\ slab (review of pf1-fix M1).
T{ t2 @ s" x" nm lf-binder-implicit lf-pres-binder! t1 @ 17 lf-pres-source!
   -> outcome-ok outcome-ok }T
T{ t2 @ lf-pres-binder@ t1 @ lf-pres-source@
   -> s" x" nm lf-binder-implicit true 17 true }T
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
variable names-room  lf-name-capacity names-room !  100000 lf-name-capacity! must-ok
T{ fill-declarations -> outcome-full }T
lf-name-reset names-room @ lf-name-capacity! must-ok
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
\ Nested visits: a tight limit is full; lf-print-limit! needs >= 1.
T{ 0 lf-print-limit! -> false }T
T{ 2 lf-print-limit! -> true }T
T{ t1 @ fuel lf-print-term -> outcome-full }T
T{ lf-print-default-limit lf-print-limit! -> true }T
T{ t1 @ fuel lf-print-term -> outcome-ok }T
\ A stale constant reference, a corrupted tag and a level parameter that
\ is not a name are invalid.
T{ args{ s" k" t-const t2 ! lf-cref-reset t2 @ fuel lf-print-term -> outcome-invalid }T
T{ t-prop t3 ! 99 t3 @ term-tag! t3 @ fuel lf-print-term -> outcome-invalid
  }T
\ Every tag no step prints, below the printer's table and at its end
\ (refactor-present review L3): 0, a free variable's, a metavariable's,
\ 31 and 32.
: tag-printed ( tag -- outcome ) t-prop t3 ! t3 @ term-tag! t3 @ fuel lf-print-term ;
T{ 0 tag-printed 9 tag-printed 16 tag-printed -> outcome-invalid outcome-invalid outcome-invalid }T
T{ 31 tag-printed 32 tag-printed -1 tag-printed -> outcome-invalid outcome-invalid outcome-invalid }T
T{ 999 lf-level-param must ssort fuel lf-print-term -> outcome-invalid }T
\ A print is refused at its root when a store's seal is broken, the count
\ still sound (compact-store plan step S2: its reads check the index).
T{ t-prop t3 ! term-seal-flip t3 @ fuel lf-print-term term-seal-flip -> outcome-invalid }T
T{ t-prop t3 ! level-seal-flip t3 @ fuel lf-print-term level-seal-flip -> outcome-invalid }T

\ A sink that breaks the rules: sink-calls sets one that runs xt at its
\ n-th call and captures the text.
variable calls   variable trigger   variable trigger-xt
: trigger-sink ( c-addr u -- )
  cap-sink 1 calls +! calls @ trigger @ = if trigger-xt @ execute then ;
: sink-calls ( n xt options -- )
  >r trigger-xt ! trigger ! 0 calls ! ['] trigger-sink r> lf-print-setup ;

\ A busy printer refuses every print from its sink, writing nothing more,
\ and lf-print-limit! too; afterwards it works. The names and levels the
\ nested prints use exist beforehand: a sink must not change a store.
variable nested-result   variable nat-id   variable u-level
: inner-term ( -- ) t1 @ fuel lf-print-term nested-result ! ;
: inner-name ( -- ) nat-id @ lf-print-name nested-result ! ;
: inner-level ( -- ) u-level @ fuel lf-print-level nested-result ! ;
: inner-inline ( -- ) t1 @ fuel lf-print-inline nested-result ! ;
: inner-display ( -- ) t1 @ fuel lf-print-display nested-result ! ;
: inner-statement ( -- ) t1 @ fuel lf-print-statement nested-result ! ;
: inner-limit ( -- )
  5 lf-print-limit! if outcome-ok else outcome-invalid then nested-result ! ;
T{ s" Nat" nm nat-id ! s" u" lparam u-level ! -> }T
: refused-inside ( xt -- outcome )
  1 swap 0 sink-calls cap-reset t1 @ fuel lf-print-term must-ok nested-result @ ;
T{ ' inner-term refused-inside -> outcome-invalid }T
T{ s" ∀ {P : Prop}, P → P" expect-text -> }T
T{ ' inner-name refused-inside ' inner-level refused-inside
  -> outcome-invalid outcome-invalid }T
T{ ' inner-inline refused-inside ' inner-display refused-inside
  -> outcome-invalid outcome-invalid }T
T{ ' inner-statement refused-inside ' inner-limit refused-inside
  -> outcome-invalid outcome-invalid }T
T{ s" ∀ {P : Prop}, P → P" expect-text lf-pjob lf-pjob-limit @
  -> lf-print-default-limit }T
\ lf-print-name, lf-print-level and lf-print-inline are busy too: the
\ name's LaTeX spelling in the pool stays intact. (Markdown math writes
\ its delimiters while no print is in progress, so the nested print here
\ is at the second call, inside the term.)
T{ 1 ' inner-term lf-print-latex sink-calls cap-reset s" Nat" nm s" add" nm. lf-print-name
  nested-result @ -> outcome-ok outcome-invalid }T
T{ s" \mathsf{Nat.add}" expect-text -> }T
T{ 1 ' inner-term 0 sink-calls cap-reset u-level @ fuel lf-print-level nested-result @
  -> outcome-ok outcome-invalid }T
T{ s" u" expect-text -> }T
T{ 2 ' inner-name 0 sink-calls cap-reset t1 @ fuel lf-print-inline nested-result @
  -> outcome-ok outcome-invalid }T
T{ s" $\forall \{P : \mathrm{Prop}\},\ P \to P$" expect-text -> }T
T{ 0 mode cap-reset t1 @ fuel lf-print-term -> outcome-ok }T

\ Binder names fill the pool, which grows: 45 binders of 98 bytes that
\ must all differ, more than the 4,096 bytes it once held (the text goes
\ nowhere). When the heap refuses to grow the pool, the scope or the
\ print's stack, a print that needs more room is full (200 such binders
\ need more than any print before), and the printer is idle again.
: long-name ( -- c-addr u )
  s" a-rather-long-binder-name-repeated-in-one-fun-again-and-again-and-again-to-about-a-hundred-bytes" ;
: long-fun ( n -- t ) t-prop 0 t-var rot 0 do over swap t-lam long-name ex. loop nip ;
: no-sink ( c-addr u -- ) 2drop ;
T{ fresh 512 lf-term-capacity! -> outcome-ok }T
T{ ' no-sink 0 lf-print-setup 45 long-fun fuel lf-print-term -> outcome-ok }T
T{ 200 long-fun 1 heap-refusals ! 100000 lf-print-term heap-refusals @ lf-pp-busy?
  -> outcome-full 0 false }T
T{ fresh lf-term-default lf-term-capacity! -> outcome-ok }T

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
\ A binder with no side-table entry prints as x; the anonymous name 0 as
\ [anonymous].
T{ t-prop 0 t-var t-lam s" fun x ↦ x" shows -> }T
T{ cap-reset 0 lf-print-name -> outcome-ok }T
T{ s" [anonymous]" expect-text -> }T

\ The failure exits of lf-print-level, lf-print-statement, lf-print-inline
\ and lf-print-display, each with the stack as it was. A level index that
\ is no level of the store is invalid, also one whose double would wrap
\ round to a good index (2 * (min-n + i) is 2 * i).
: P ( -- t ) t-prop ;
fresh 0 mode
T{ s" u" lparam s" v" lparam lmax t1 ! P 0 t-var t-pi s" x" ex. t2 ! -> }T
T{ cap-reset t1 @ max-n invert + fuel lf-print-level cap nip -> outcome-invalid 0 }T
T{ -1 fuel lf-print-level lf-level-count @ fuel lf-print-level
  -> outcome-invalid outcome-invalid }T
T{ t1 @ 0 lf-print-level t1 @ -1 lf-print-level -> outcome-exhausted outcome-invalid }T
T{ 1 lf-print-limit! t1 @ fuel lf-print-level -> true outcome-full }T
T{ lf-print-default-limit lf-print-limit! -> true }T
T{ 63 fuel lf-print-statement t2 @ 0 lf-print-statement t2 @ -1 lf-print-statement
  -> outcome-invalid outcome-exhausted outcome-invalid }T
T{ cap-reset 63 fuel lf-print-inline -> outcome-invalid }T
T{ s" $$" expect-text -> }T
T{ t2 @ 0 lf-print-inline t2 @ 0 lf-print-display
  -> outcome-exhausted outcome-exhausted }T
T{ t2 @ -1 lf-print-inline t2 @ -1 lf-print-display -> outcome-invalid outcome-invalid }T

\ A corrupted name store (a count beyond the table, or an entry whose
\ prefix points forward) makes every print invalid. The store's audit
\ reads its header, its root and the entries it has not passed yet; an
\ entry it passed is caught where a name is printed, by its chain's check
\ (lf-name-chain-ok?; ADR 0005 Amendment 1), so the print of a name that
\ does not read it goes on.
variable names-count
: corrupt-count ( -- ) lf-name-count @ names-count ! 99 lf-name-count ! ;
: heal-count ( -- ) names-count @ lf-name-count ! ;
: corrupt-prefix ( id -- ) 50 swap lf-name-slot lf-entry-prefix ! ;
: corrupt-root ( -- ) 50 0 lf-name-slot lf-entry-prefix ! ;
fresh 0 mode
T{ P 0 t-var t-lam t1 ! s" q" nm t2 ! s" u" lparam t3 ! corrupt-count -> }T
T{ t1 @ fuel lf-print-term t2 @ lf-print-name t3 @ fuel lf-print-level
  -> outcome-invalid outcome-invalid outcome-invalid }T
T{ t1 @ fuel lf-print-statement t1 @ fuel lf-print-inline
  -> outcome-invalid outcome-invalid }T
T{ heal-count t1 @ s" fun x ↦ x" shows -> }T
T{ t2 @ corrupt-prefix t2 @ lf-print-name -> outcome-invalid }T
T{ t1 @ s" fun x ↦ x" shows -> }T
\ A binder name with a broken chain is not hygienic: it is refused whole.
T{ t2 @ lf-pp-hygienic? -> false }T
T{ corrupt-root t2 @ lf-print-name t1 @ fuel lf-print-term
  -> outcome-invalid outcome-invalid }T

\ Names print without recursion: one of lf-name-default components prints
\ whole; one more component prints nothing and the print ends full, as a
\ name too long for the pool does (the review's finding M1).
: deep-nm ( n -- id ) 0 swap 0 ?do i lf-name-num must loop ;
fresh 0 mode
T{ 256 lf-name-capacity! -> outcome-ok }T
T{ cap-reset lf-name-default deep-nm lf-print-name cap-len @ -> outcome-ok 181 }T
T{ cap-reset lf-name-default 1+ deep-nm lf-print-name cap-len @ -> outcome-full 0 }T
T{ fresh lf-name-default lf-name-capacity! -> outcome-ok }T

\ Numbers print in decimal whatever BASE is, and BASE is kept: a Sort, a
\ numeric name component, a binder suffix and a LaTeX subscript.
\ (Not in-base, lib/decimal.fs's word, which the library's word list finds
\ first.)
: base-after ( i*x xt n -- j*x n' ) base @ >r base ! execute base @ r> base ! ;
fresh 0 mode
T{ 12 t-sort t1 ! s" x" nm 10 nm# t2 ! -> }T
T{ cap-reset t1 @ fuel ' lf-print-term 16 base-after -> outcome-ok 16 }T
T{ s" Type 11" expect-text -> }T
T{ cap-reset t2 @ ' lf-print-name 16 base-after -> outcome-ok 16 }T
T{ s" x.10" expect-text -> }T
T{ P P P 2 t-var 1 t-var t-app 0 t-var t-app t-pi s" x" ex. t-pi s" x" ex. t-pi s" x" ex.
  t3 ! -> }T
T{ cap-reset t3 @ fuel ' lf-print-term 2 base-after -> outcome-ok 2 }T
T{ s" (x x_1 x_2 : Prop) → @x x_1 x_2" expect-text -> }T
\ Its fuel, the spine's steps included (lf-pp-fuelled, ROUT3): a
\ regression pin of 2026-11-14, 47 units, 39 when a spine spends none.
T{ t3 @ need -> 47 }T
\ Binders grouped over an application domain: F A against F A lifted, the
\ functions and then the arguments compared (lf-pp-seconds-then, ROUT3).
T{ t-prop t-prop t-prop t-pi 0 t-var 1 t-var t-app 1 t-var 2 t-var t-app 1 t-var 0 t-var t-app
   t-pi s" y" ex. t-pi s" x" ex. t-pi s" F" ex. t-pi s" A" ex.
   s" (A : Prop) → (F : Prop → Prop) → (x y : F A) → @x y" shows -> }T
T{ lf-print-latex mode cap-reset s" proof₁₂" ' lf-tex-ident 16 base-after -> 16 }T
T{ s" \mathit{proof}_{12}" expect-text -> }T

\ LaTeX spelling takes a Greek letter or a subscript digit only as a whole
\ UTF-8 character: the bytes B1 CE (the end of α and the start of β) and
\ x 80 E2 82 (a stray byte, then the start of ₀) start no character, so they
\ are written as \backslash{}x\{HH\}: no name can end a line or reorder text.
create odd 4 allot
: odd2 ( -- c-addr u ) $B1 odd c! $CE odd 1+ c! odd 2 ;
: odd4 ( -- c-addr u ) [char] x odd c! $80 odd 1+ c! $E2 odd 2 + c! $82 odd 3 + c! odd 4 ;
create want 16 allot   variable want#
: want+ ( c-addr u -- ) tuck want want# @ + swap move want# +! ;
: mathit ( c-addr u -- c-addr' u' )
  0 want# ! s" \mathit{" want+ want+ s" }" want+ want want# @ ;
T{ cap-reset odd2 lf-tex-ident
   s" \mathit{\backslash{}x\{B1\}\backslash{}x\{CE\}}" expect-text -> }T
T{ cap-reset odd4 lf-tex-ident
   s" \mathit{x\backslash{}x\{80\}\backslash{}x\{E2\}\backslash{}x\{82\}}" expect-text -> }T
\ A line end and a bidirectional control are written out too.
T{ cap-reset s\" a\nb\xe2\x80\xaeC" lf-tex-ident
   s" \mathit{a\backslash{}u\{A\}b\backslash{}u\{202E\}C}" expect-text -> }T
T{ cap-reset s" α" lf-tex-ident s" \alpha" expect-text -> }T
T{ cap-reset s" x₀" lf-tex-ident s" x_{0}" expect-text -> }T

\ A constant's LaTeX spelling goes into the name pool behind the binder
\ names, past the 4,096 bytes the pool once held, and prints; in Unicode
\ the constant takes no pool room.
: long-const ( -- t )   \ the constant long-name.long-name, 197 bytes
  long-name nm long-name nm. lf-name-generation @ cargs 0 lf-cref-new must
  lf-cterm-new must drop ;
: crowded ( n -- t ) t-prop long-const rot 0 do over swap t-lam long-name ex. loop nip ;
T{ fresh ' no-sink 0 lf-print-setup 40 crowded t1 ! -> }T
T{ t1 @ fuel lf-print-term -> outcome-ok }T
T{ ' no-sink lf-print-latex lf-print-setup t1 @ fuel lf-print-term -> outcome-ok }T

\ lf-print-reset from the sink, against the sink rules, ends the print
\ invalid and leaves the printer idle; a THROW leaves it busy, and in a
\ Markdown math print in LaTeX mode, until lf-print-reset.
: throw-7 ( -- ) 7 throw ;
fresh
T{ P 0 t-var 1 t-var t-pi s" h" in. t-pi s" al" im. t1 ! -> }T
T{ s" Nat" nm nat-id ! s" u" lparam u-level ! -> }T
T{ cap-reset 5 ' lf-print-reset 0 sink-calls t1 @ fuel lf-print-term lf-pp-busy?
  -> outcome-invalid false }T
T{ 1 ' lf-print-reset 0 sink-calls nat-id @ lf-print-name -> outcome-invalid }T
T{ 1 ' lf-print-reset 0 sink-calls u-level @ fuel lf-print-level -> outcome-invalid }T
\ Also a binder's name, which prints without a visit (the printer is busy
\ from the start of a print to its end).
create scope-cell 1 cells allot
T{ t1 @ scope-cell ! 1 ' lf-print-reset 0 sink-calls scope-cell 1 fuel lf-print-scope-name
  lf-pp-busy? -> outcome-invalid false }T
T{ 0 mode cap-reset scope-cell 1 fuel lf-print-scope-name -> outcome-ok }T
T{ s" al" expect-text -> }T
T{ 3 ' lf-print-reset 0 sink-calls t1 @ fuel lf-print-inline lf-pp-math?
  -> outcome-invalid false }T
T{ 0 mode t1 @ s" ∀ {al : Prop} [h : al], al" shows -> }T
T{ 2 ' throw-7 0 sink-calls t1 @ fuel ' lf-print-inline catch nip nip -> 7 }T
T{ lf-pp-math? lf-pp-busy? -> true true }T
T{ 0 mode t1 @ fuel lf-print-term -> outcome-invalid }T
T{ lf-print-reset lf-pp-math? lf-pp-busy? -> false false }T
T{ t1 @ s" ∀ {al : Prop} [h : al], al" shows -> }T
\ Defence in depth: counts read from the printer's state are clamped.
T{ t1 @ -1 lf-pp-bodies -> t1 @ }T
T{ -5 lf-pjob lf-pjob-binders ! lf-pp-depth -> 0 }T
T{ lf-pp-scope-table slab-capacity 9 + lf-pjob lf-pjob-binders ! lf-pp-depth
  -> lf-pp-scope-table slab-capacity }T
T{ 0 lf-pjob lf-pjob-binders ! s" x" 5 lf-pp-any? -> false }T
T{ 0 lf-pp-used ! 7 lf-pp-pending nip -> 0 }T
lf-print-reset

\ Known differences from Lean, confirmed with pinned Lean 4.35.0 (see the
\ guide's limits): when Lean's quick test cannot decide, Lean infers the
\ type and prints ∀. Lean prints these as ∀ (x : Prop), (fun y ↦ y) x and
\ ∀ (p : MyProp), p, where def MyProp : Type := Prop.
fresh 0 mode
T{ P P 0 t-var t-lam s" y" ex. 0 t-var t-app t-pi s" x" ex.
  s" (x : Prop) → (fun y ↦ y) x" shows -> }T
T{ args{ s" MyProp" t-const 0 t-var t-pi s" p" ex. s" (p : MyProp) → p" shows -> }T
\ A Sort refers to its level by index alone (a limit of the data model):
\ after a reset of the level store it is invalid, or prints whatever
\ level has that index now.
fresh 0 mode
T{ s" u" lparam ssort t1 ! t1 @ s" Sort u" shows -> }T
T{ lf-level-reset t1 @ fuel lf-print-term -> outcome-invalid }T
T{ s" v" lparam drop t1 @ s" Sort v" shows -> }T

\ String literals (plan task 5.2.3, strings; print-strings.fs): Lean's
\ String.quote, as pinned Lean 4.35.0 prints "a\"b\\c\nd\te\x0d\x01\x7f"
\ and "é😀"; a character text-rule bans as \u (Lean prints U+202E and
\ U+0085 as themselves); in LaTeX inside \texttt, escaped for text mode;
\ bytes that are no UTF-8 character (a corrupted leaf) invalid.
: t-str ( c-addr u -- t ) lf-str-new must-ok drop ;
fresh 0 mode
T{ s" ab" t-str s\" \"ab\"" shows -> }T
T{ s" " t-str s\" \"\"" shows -> }T
T{ s\" a\"b\\c\nd\te\x0d\x01\x7f'" t-str
   s\" \"a\\\"b\\\\c\\nd\\te\\x0d\\x01\\x7f'\"" shows -> }T
T{ s\" \xc3\xa9\xf0\x9f\x98\x80" t-str s\" \"\xc3\xa9\xf0\x9f\x98\x80\"" shows -> }T
T{ s\" a\xe2\x80\xaeb\xc2\x85" t-str s\" \"a\\u202eb\\u0085\"" shows -> }T
\ Above U+FFFF, where Lean's syntax has no escape, as names write it
\ (review F4): U+E0041, a tag character, and U+1D173, a musical format
\ character, as \u{E0041} and \u{1D173}, in plain text and in LaTeX.
T{ s\" a\xf3\xa0\x81\x81b\xf0\x9d\x85\xb3" t-str s\" \"a\\u{E0041}b\\u{1D173}\"" shows -> }T
lf-print-latex mode
T{ s\" a\xf3\xa0\x81\x81b" t-str
   s\" \\texttt{\"a\\textbackslash{}u\\{E0041\\}b\"}" shows -> }T
0 mode
T{ args{ s" f" t-const s" x y" t-str t-app s\" f \"x y\"" shows -> }T
lf-print-latex mode
T{ s\" a_b\\{}~ c" t-str
   s\" \\texttt{\"a\\_b\\textbackslash{}\\textbackslash{}\\{\\}\\textasciitilde{} c\"}"
   shows -> }T
0 mode
T{ s\" \xc3\xa9" t-str t1 ! 1 t1 @ term-second! t1 @ fuel lf-print-term
   -> outcome-invalid }T
\ A number literal (core/literals.fs) prints in decimal; one longer than a
\ cell as its count of limbs.
create lit-seven 7 ,   create lit-wide 1 , 1 ,
: t-lit ( addr n -- t ) lf-hterm-lit must drop ;
T{ lit-seven 1 t-lit s" 7" shows -> }T
T{ lit-wide 2 t-lit s" (literal of 2 limbs)" shows -> }T

\ A projection (core/projections.fs) prints as its leaf, the structure's
\ name and Lean's field number from 1, applied to the projected term, and
\ so does one applied to more arguments (not Lean's syntax yet).
: t-proj ( t c-addr u i -- t' ) >r nm r> lf-proj-of must-ok ;
fresh 0 mode
T{ args{ s" p" t-const s" Prod" 0 t-proj s" Prod.1 p" shows -> }T
T{ args{ s" f" t-const s" Prod" 1 t-proj args{ s" a" t-const t-app s" Prod.2 f a" shows -> }T

\ LaTeX's text mode (statement-forms.fs: a declaration's Lean form in
\ \ttfamily) writes the math mode's escapes of a banned character and of a
\ byte that starts no character (lf-tex-ident above) after
\ \textbackslash{}, as it writes a backslash itself (review reuse-out-2
\ rc3 M1).
: tex-text ( c-addr u -- ) ['] cap-sink 100 lf-lv-setup must cap-reset lf-sf-tex lf-lv-done ;
T{ s\" a\xe2\x80\xaeb\xffc\\" tex-text
   s" a\textbackslash{}u\{202E\}b\textbackslash{}x\{FF\}c\textbackslash{}" expect-text -> }T
\ A print to another sink for a while (lf-print-with, lf-print-to; review
\ s1-elab re-check L5): in Unicode whatever the mode set, the notation
\ flag as given; the sink, the options and the flag given back after,
\ also after a THROW (passed on); lf-print-sink is the sink set.
create other-buf 256 allot   variable other-len
: other-sink ( c-addr u -- ) tuck other-buf other-len @ + swap move other-len +! ;
: other ( -- c-addr u ) other-buf other-len @ ;
: ascii-u ( -- options ) lf-print-ascii lf-print-universes or ;
: lam-id ( -- t ) t-prop 0 t-var t-lam ;
fresh ascii-u mode
T{ lf-print-sink lf-print-settings -> ' cap-sink ' cap-sink ascii-u }T
T{ ' lf-print-settings ' other-sink lf-print-with -> ' other-sink lf-print-unicode }T
T{ ' lf-print-sink ' other-sink lf-print-with lf-print-sink -> ' other-sink ' cap-sink }T
T{ 0 other-len ! cap-reset lam-id ' other-sink false lf-print-to other s" fun x ↦ x" compare
   cap nip -> outcome-ok 0 0 }T
T{ lf-print-settings lf-print-notation? -> ' cap-sink ascii-u false }T
T{ true lf-print-notation! lam-id ' other-sink false lf-print-to lf-print-notation?
   false lf-print-notation! -> outcome-ok true }T
: notation-in ( c-addr u -- ) 2drop lf-print-notation? other-len ! ;
T{ 0 other-len ! lam-id ' notation-in true lf-print-to other-len @ lf-print-notation?
   -> outcome-ok true false }T
: throws ( -- ) 7 throw ;
T{ ' throws ' other-sink ' lf-print-with catch nip nip lf-print-settings
   -> 7 ' cap-sink ascii-u }T
: bad-sink ( c-addr u -- ) 2drop 9 throw ;
T{ lam-id ' bad-sink true ' lf-print-to catch nip nip nip lf-print-reset
   lf-print-notation? lf-print-settings -> 9 false ' cap-sink ascii-u }T
T{ lam-id s" fun x => x" shows -> }T

\ Names as Lean 4.35.0 writes them (review PB1; checked against the pinned
\ Lean's #check and trace_state on 2026-11-18): a component that is no
\ identifier between « », so Foo.«a.b» never prints as Foo.a.b; a root
\ component that is a token of Init's syntax too («fun», but Foo.fun);
\ identifiers, Greek letters and _ bare; a bidirectional control escaped,
\ never raw (Lean writes it raw: a difference kept on purpose).
fresh 0 mode
: foo. ( c-addr u -- t ) s" Foo" nm -rot nm. lf-name-generation @ cargs 0 lf-cref-new must
  lf-cterm-new must drop ;
: one. ( c-addr u -- t ) 0 -rot nm. lf-name-generation @ cargs 0 lf-cref-new must
  lf-cterm-new must drop ;
T{ s" a.b" foo. s" Foo.«a.b»" shows -> }T
T{ s" fun" foo. s" Foo.fun" shows -> }T
T{ s" fun" one. s" «fun»" shows -> }T
T{ s" Type" one. s" «Type»" shows -> }T
T{ s" with space" one. s" «with space»" shows -> }T
T{ s" 1x" one. s" «1x»" shows -> }T
T{ s" αβγ" one. s" αβγ" shows -> }T
T{ s" _" one. s" _" shows -> }T
T{ s" a_b}" one. s" «a_b}»" shows -> }T
T{ s\" a\xe2\x80\xaeb" one. s" «a\u{202E}b»" shows -> }T
\ A part the speller has no room to escape ends the print full, never
\ with the part bare (the speller's text held to 4 bytes, then freed).
: tight ( -- ) nt-free 1 chars 4 nt-out slab-init drop ;
T{ tight s" a.b" foo. fuel lf-print-term nt-free -> outcome-full }T
T{ s" a.b" foo. s" Foo.«a.b»" shows -> }T
\ A binder: its name spelled the same way, in the binder and the body.
: odd-lam ( c-addr u -- t ) 2>r t-prop 0 t-var t-lam 2r> ex. ;
T{ s" a_b}" odd-lam s" fun «a_b}» ↦ «a_b}»" shows -> }T
T{ s" x" odd-lam s" fun x ↦ x" shows -> }T
bye
