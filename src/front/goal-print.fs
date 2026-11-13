\ Goals as text (plan FE1g-1; docs/design/FE1G_TACTICS.md §5.7): Lean
\ 4.35.0's trace_state (Elab/Tactic/BuiltinTactic.lean evalTraceState: the
\ unsolved goals, each by Meta/PPGoal.lean's ppGoal, a blank line between
\ two, Elab/Tactic/Basic.lean goalsToMessageData; the message then ends
\ its line). One goal:
\ - "case TAG" on a line of its own when the goal has a tag;
\ - its hypotheses in the order of its local context, but for those of a
\   kind other than the default (implementation details and auxiliary
\   declarations, which Lean's pp.implementationDetailHyps and
\   pp.auxDecls hide): neighbours of the same type (Lean's ==, after
\   instantiating) on one line, "a b : Nat"; a let whose value is not
\   hidden on a line of its own, "x : Nat := a + b"; a have (nondep) as
\   any hypothesis;
\ - "⊢ " and the goal's type, instantiated.
\ Names as Lean's sanitizeNames gives them: a hypothesis whose name is
\ inaccessible, or shadowed by a newer accessible one of the same name,
\ prints as name✝, the next such of the same name (counting from the
\ newest) as name✝¹, name✝², ... A free variable in a term prints by its
\ hypothesis's name (this file installs the term printer's
\ lf-pp-open-leaf; outside a goal print it names a free variable by the
\ current local context, lf-mctx-view, and one in neither as _fvar.N), a
\ metavariable as ?TAG when tagged, else ?m.N (N: its record's number + 1;
\ Lean counts every metavariable it made, so its N differs). A let's value
\ prints when it is a leaf or, for a synthetic opaque goal, its depth
\ (Lean's Expr.approxDepth) is at most 254; else as ⋯
\ (ppGoal.shouldShowLetValue). Terms print with the term printer
\ (present/), notation on. Where it does not print as Lean does (x.succ
\ for Nat.succ x, ∀ against → where Lean infers the type, lines Lean
\ breaks past its width of 120, a binder Lean renames because its body
\ uses a hypothesis of that name, metavariable numbers and delayed
\ assignments), the text differs: plan 8.6 owns those gaps
\ (tests/front/goals-print.lean lists the ones met).
\ Words: lf-goal-print ( goal -- outcome ), lf-goals-print ( -- outcome )
\ (the proof state's unsolved goals, then the end of the line; FE1g-3
\ runs it for the word .goals), to the term printer's sink (lf-print-setup).
\ Outcomes: ok; invalid for a goal that is no live metavariable; what an
\ instantiation or the printer answers (exhausted, full, unsupported). On
\ a failure part of the text is written. Untrusted presentation.
\ State: the record gp (the goal being printed and its view, the pending
\ group's type, the depth walk) and the slabs gp-codes (each local's name
\ suffix) and gp-names (the pending group's places), in the checker
\ context (ADR 0009). Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../core/let-terms.fs
require ../present/term-printer.fs
require ../present/print-notation.fs
require ./dag-walk.fs
require ./lctx-views.fs
require ./mvars.fs
require ./goals.fs

100000 constant gp-fuel        \ printer fuel for each term
254 constant gp-depth-shown    \ ppGoal's threshold for a tactic goal's let value
255 constant gp-depth-most     \ Lean's approxDepth stops at 255
-1 constant gp-plain           \ the code of a name printed as it is
begin-structure /gp
  field: gp-active    \ true while a goal prints
  field: gp-view      \ that goal's local context
  field: gp-opaque    \ true for a synthetic opaque goal (a tactic goal)
  field: gp-prev      \ the pending group's type, or -1
  field: gp-lines     \ true once a line is written
  field: gp-notation  \ the printer's notation flag before the goal
  /dw +field gp-walk  \ the depth walk
end-structure
/gp context-record: gp
1 cells context-slab: gp-codes    \ per local of the view: gp-plain or k (✝ and k)
1 cells context-slab: gp-names    \ the pending group's places in the view

\ ---- Text.
: gp-emit ( c-addr u -- ) lf-pp-emit ;
: gp-line ( -- ) gp gp-lines @ if s\" \n" gp-emit then true gp gp-lines ! ;
: gp-term ( term -- outcome ) gp-fuel lf-print-term ;
\ Superscript digits, two CASE tables of five.
: gp-super-low ( d -- c-addr u )
  case 0 of s" ⁰" endof 1 of s" ¹" endof 2 of s" ²" endof 3 of s" ³" endof
    s" ⁴" rot endcase ;
: gp-super ( d -- c-addr u )
  dup 5 < if gp-super-low exit then
  case 5 of s" ⁵" endof 6 of s" ⁶" endof 7 of s" ⁷" endof 8 of s" ⁸" endof
    s" ⁹" rot endcase ;
: gp-place ( n -- p ) 1 begin over 9 > while 10 * swap 10 / swap repeat nip ;
: gp-supers ( n -- )
  dup gp-place begin dup while 2dup / 10 mod gp-super gp-emit 10 / repeat 2drop ;
\ Lean's tombstone: ✝ and, after the first, its number in superscript.
: gp-suffix ( code -- ) dup 0< if drop exit then s" ✝" gp-emit ?dup if gp-supers then ;

\ ---- Names (Lean's sanitizeNames), from the newest local to the oldest:
\ a local is renamed when inaccessible or when a newer accessible local
\ has its name; its code is then the number of newer renamed locals of
\ the same name. Quadratic in the hypotheses (Lean keeps a name map).
: gp-view@ ( -- view ) gp gp-view @ ;
: gp-local ( i -- local ) gp-view@ swap lf-view-local ;
: gp-code@ ( i -- code ) gp-codes slab-at @ ;
: gp-same? ( local j -- flag ) gp-local lf-local-name swap lf-local-name lf-name-same? ;
: gp-shadows? ( local j -- flag )
  dup gp-local lf-local-inaccessible? if 2drop false else gp-same? then ;
: gp-renamed-as? ( local j -- flag ) dup gp-code@ 0< if 2drop false else gp-same? then ;
: gp-after ( i -- limit start ) gp-view@ lf-view-count swap 1+ ;
: gp-shadowed? ( i -- flag )
  dup gp-local swap gp-after ?do dup i gp-shadows? if drop true unloop exit then loop
  drop false ;
: gp-like ( i -- n )
  dup gp-local 0 rot gp-after ?do over i gp-renamed-as? if 1+ then loop nip ;
: gp-renamed? ( i -- flag )
  dup gp-local lf-local-inaccessible? if drop true else gp-shadowed? then ;
: gp-code ( i -- code ) dup gp-renamed? if gp-like else drop gp-plain then ;
: gp-codes! ( -- outcome )
  gp-view@ lf-view-count dup gp-codes slab-hold ok-then? 0= if exit then
  begin dup while 1- dup gp-code over gp-codes slab-at ! repeat drop outcome-ok ;

\ A hypothesis's name with its suffix; the printer's hook prints a free
\ variable so, a metavariable by its tag or number.
: gp-hyp ( i -- ) dup gp-local lf-local-name lf-pp-name gp-code@ gp-suffix ;
: gp-current ( -- view ) gp gp-active @ if gp-view@ else lf-mctx-view then ;
: gp-plain-name ( i -- ) gp-current swap lf-view-local lf-local-name lf-pp-name ;
: gp-named ( i -- ) gp gp-active @ if gp-hyp else gp-plain-name then ;
: gp-loose ( fvar -- outcome ) s" _fvar." gp-emit lf-fvar-number lf-pp-number outcome-ok ;
: gp-fvar ( fvar -- outcome )
  gp-current over lf-view-find if nip gp-named outcome-ok else gp-loose then ;
: gp-anonymous ( mvar -- ) s" ?m." gp-emit lf-term-first@ 1+ lf-pp-number ;
: gp-stale ( mvar -- outcome )
  s" ?_mvar." gp-emit lf-term-first@ lf-pp-number outcome-ok ;
: gp-mvar ( mvar -- outcome )
  dup lf-mvar-tag 0= if gp-stale exit then
  ?dup if nip s" ?" gp-emit lf-pp-name else gp-anonymous then outcome-ok ;
: gp-leaf ( term -- outcome ) dup lf-mvar? if gp-mvar else gp-fvar then ;
' gp-leaf is lf-pp-open-leaf

\ ---- A let value's depth: Lean's approxDepth, a leaf 0, a node one more
\ than its deepest part, at most 255; a let (its value, then a lambda of
\ its type and body) counts its type and body at the lambda's depth.
: gp-binary? ( node -- flag ) lf-term-tag@ lf-term-binary-tag? ;
: gp-undone ( child walk -- child true | false )
  over swap dw-done? if drop false else true then ;
: gp-child ( node walk -- child true | false )
  over gp-binary? 0= if 2drop false exit then
  over lf-term-first@ over gp-undone if nip nip true exit then
  swap lf-term-second@ swap gp-undone ;
: gp-images ( node walk -- i1 i2 )
  over lf-term-first@ over dw-image >r swap lf-term-second@ swap dw-image r> swap ;
: gp-deeper ( node walk -- depth )
  over >r gp-images r> lf-let? if 1- 0 max then max 1+ gp-depth-most min ;
: gp-depth-build ( node walk -- depth ) over gp-binary? if gp-deeper else 2drop 0 then ;
: gp-depth ( term -- depth outcome )
  gp gp-walk ['] gp-depth-build over dw-build ! ['] gp-child over dw-pending !
  lf-term-base lf-term-count @ + over dw-size ! dw-run ;
: gp-atomic? ( term -- flag ) gp-binary? 0= ;
: gp-shown? ( value -- flag outcome )
  dup gp-atomic? if drop true outcome-ok exit then
  gp gp-opaque @ 0= if drop false outcome-ok exit then
  gp-depth ok-then? if gp-depth-shown <= outcome-ok else false swap then ;

\ ---- Hypotheses (ppGoal's ppVars and pushPending). A group is the
\ places of neighbours of one type, printed when a hypothesis of another
\ type, a let or the end comes.
: gp-inst ( term -- term' outcome ) lf-instantiate-mvars ;
: gp-fvar-at ( i -- fvar ) gp-local lf-local-fvar ;
: gp-type ( i -- type outcome ) gp-fvar-at lf-fvar-type gp-inst ;
: gp-val ( i -- value outcome ) gp-fvar-at lf-fvar-value gp-inst ;
: gp-group-names ( -- )
  gp-names slab-count 0 ?do i if s"  " gp-emit then i gp-names slab-at @ gp-hyp loop ;
: gp-group-reset ( -- ) gp-names slab-clear -1 gp gp-prev ! ;
: gp-flush ( -- outcome )
  gp-names slab-count 0= if outcome-ok exit then
  gp-line gp-group-names s"  : " gp-emit gp gp-prev @ gp-group-reset gp-term ;
: gp-join ( i -- outcome )
  1 gp-names slab-claim ok-then? if gp-names slab-at ! outcome-ok else nip then ;
: gp-same-type? ( type -- flag outcome )
  gp gp-prev @ dup 0< if 2drop true outcome-ok else gp-fuel lf-print-same? then ;
: gp-grouped ( flag -- outcome ) if outcome-ok else gp-flush then ;
: gp-group ( type -- outcome ) gp-same-type? ok-then? if gp-grouped then ;
: gp-hypothesis ( i type -- outcome )
  dup gp-group ok-then? if gp gp-prev ! gp-join else nip then ;
: gp-cdecl ( i -- outcome ) dup gp-type ok-then? if gp-hypothesis else nip then ;
\ A let, "x : T := v" or "x : T := ⋯".
: gp-elided ( value -- outcome ) drop s" ⋯" gp-emit outcome-ok ;
: gp-shown ( value flag -- outcome ) if gp-term else gp-elided then ;
: gp-value ( value -- outcome )
  s"  := " gp-emit dup gp-shown? ok-then? if gp-shown else nip then ;
: gp-let-head ( i -- outcome )
  gp-line dup gp-hyp s"  : " gp-emit gp-type ok-then? if gp-term then ;
: gp-let-value ( i -- outcome ) gp-val ok-then? if gp-value then ;
: gp-let ( i -- outcome )
  gp-flush dup ok? 0= if nip exit then drop
  dup gp-let-head ok-then? if gp-let-value then ;
: gp-visible? ( i -- flag ) gp-local lf-local-detail? 0= ;
: gp-at ( i -- outcome )
  dup gp-visible? 0= if drop outcome-ok exit then
  dup gp-fvar-at lf-fvar-let? if gp-let else gp-cdecl then ;
: gp-hyps ( -- outcome )
  gp-view@ lf-view-count 0 ?do i gp-at dup ok? 0= if unloop exit then drop loop gp-flush ;

\ ---- A goal: its tag line, its hypotheses, the turnstile and its type.
: gp-case ( goal -- ) lf-mvar-tag drop ?dup if gp-line s" case " gp-emit lf-pp-name then ;
: gp-target ( goal -- outcome )
  gp-line s" ⊢ " gp-emit lf-mvar-type drop gp-inst ok-then? if gp-term then ;
: gp-body ( goal -- outcome ) dup gp-case gp-hyps ok-then? if gp-target then ;
: gp-notation-on ( -- ) lf-print-notation? gp gp-notation ! true lf-print-notation! ;
: gp-open ( goal -- )
  dup lf-mvar-view drop gp gp-view ! lf-mvar-kind drop mv-opaque = gp gp-opaque !
  false gp gp-lines ! gp-group-reset gp-notation-on ;
: gp-close ( outcome -- outcome )
  false gp gp-active ! gp gp-notation @ lf-print-notation! ;
: gp-printed ( goal -- outcome ) true gp gp-active ! gp-body ;
: lf-goal-print ( goal -- outcome )
  dup lf-mvar-live? 0= if drop-invalid exit then
  dup gp-open gp-codes! ok-then? if gp-printed then gp-close ;

\ The unsolved goals, a blank line between two, then the end of the line.
: gp-nth ( list i -- outcome ) dup if s\" \n\n" gp-emit then run@ lf-goal-print ;
: gp-all ( list -- outcome )
  dup run-count 0 ?do dup i gp-nth dup ok? 0= if nip unloop exit then drop loop
  drop s\" \n" gp-emit outcome-ok ;
: lf-goals-print ( -- outcome ) lf-goals-unsolved ok-then? if gp-all then ;
base !   \ the BASE this file was loaded with
