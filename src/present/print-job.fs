\ The term printer's working state and text primitives (plan task 2.4.3):
\ the caller's character sink and options, the print's frames record
\ (lib/frame.fs: its fuel, its nested visits and the explicit stack their
\ steps run on), the binders in scope with their display names, and the
\ pool that holds those names. Untrusted presentation code; the checker
\ never loads it. Requires binder-table.fs and the term and name stores.
\ The sink is an xt ( c-addr u -- ), like TYPE; text, Markdown, LaTeX and
\ later JSON writers reuse the printer by passing their own. Sink rules:
\ - Use the text, or copy it, before returning and before any pictured
\   numeric output (<# ... #>) of the sink's own: the text may lie in the
\   printer's name pool or in the pictured numeric output buffer.
\ - Call no lf-print-* or lf-pres-* word and change no store (terms,
\   levels, names, constant references). A busy printer refuses another
\   print as invalid and lf-print-limit! with false; a print during which
\   the sink called lf-print-reset ends invalid. Store changes are not
\   detected: the printed text is then meaningless.
\ - Do not THROW. After a THROW out of a print, call lf-print-reset, which
\   also ends the LaTeX mode of lf-print-inline and lf-print-display.
\ As defence in depth, every count read from the printer's state is
\ clamped into range, and a reset from the sink only marks the print in
\ progress (lf-print-reset), so a sink that breaks the rules cannot make a
\ print loop without end or address outside the printer's memory.
\ State: one context record, lf-pjob (ADR 0009), whose frames hold a heap
\ block, and two growable arrays of the context (context-slab:), the
\ binders in scope and the name pool; the context's teardown frees all
\ three. Depth (plan task 6.2.0): a print holds a constant number of
\ host-stack cells whatever the depth of its term (see "Visits" below);
\ its stack, its binders and its pool grow on the heap, and a print the
\ heap has no room for is full.

require ../lib/decimal.fs
require ./binder-table.fs

0 constant lf-print-unicode     \ mode: Lean's notation (with pp.unicode.fun)
1 constant lf-print-ascii       \ mode: plain ASCII notation (forall, ->, =>)
2 constant lf-print-latex       \ mode: LaTeX math
3 constant lf-print-mathtext    \ mode: mathematics in Unicode text (ℕ, ·, n²)
3 constant lf-print-mode-mask
4 constant lf-print-universes   \ option bit: show universe arguments, c.{u}
\ No limit of nested visits until the caller sets one (lf-print-limit!).
max-n constant lf-print-default-limit

\ One binder in scope: its domain term and its display name in the pool.
begin-structure /lf-pbind
  field: lf-pbind-domain
  field: lf-pbind-offset
  field: lf-pbind-length
end-structure

\ The frames come first, so a step finds the printer's record at the
\ address of the frames it is given (as mixed-shift.fs does).
begin-structure /lf-pjob
  /frames +field lf-pjob-frames   \ fuel, visits, the steps' stack, a comparison's depth
  2 cells +field lf-pjob-setup  \ the sink, xt ( c-addr u -- ), and the mode and
                                \ option bits: sink options, with 2@ 2!
  field: lf-pjob-limit       \ most nested visits in one print
  field: lf-pjob-binders     \ binders in scope
  field: lf-pjob-chain       \ binders in scope where the current fun began
  field: lf-pjob-used        \ pool bytes in use
  field: lf-pjob-full        \ true once a name did not fit in the pool
  field: lf-pjob-math        \ true while lf-print-inline or -display forces LaTeX
  field: lf-pjob-sinking     \ true while the sink runs
  field: lf-pjob-broken      \ true once the sink reset the print in progress
  field: lf-pjob-printing    \ true from a print's start to its end (or a THROW)
  field: lf-pjob-notation    \ true: print by the notation table (print-notation.fs)
end-structure
0 lf-pjob-frames 0<> [if] .( print-job.fs: frames must come first) cr abort [then]
/lf-pjob context-record: lf-pjob
\ The binders in scope and the name pool, as many as a print needs.
/lf-pbind context-slab: lf-pp-scope-table
1 chars context-slab: lf-pp-pool-bytes

: lf-pp-frames ( -- frames ) lf-pjob lf-pjob-frames ;
: lf-print-fuel ( -- addr ) lf-pp-frames frame-fuel ;
\ Busy while a print is in progress (from lf-pp-start to lf-pp-finish,
\ term-printer.fs, its visits open on the frames meanwhile), or after a
\ THROW out of one.
: lf-pp-printing ( -- addr ) lf-pjob lf-pjob-printing ;
: lf-pp-busy? ( -- flag ) lf-pp-printing @ lf-pp-frames frame-busy? or ;

\ Settings. lf-print-setup takes the sink and the options (a mode plus
\ option bits); lf-print-limit! the most nested visits per print, at least
\ 1 (the default, lf-print-default-limit, is no limit: the heap bounds a
\ print), and refuses while a print is in progress. Every context starts
\ with TYPE, Unicode, no universes and no limit. The frames' visitor is
\ never run: every visit names its own first step (lf-pp-call).
: lf-print-setup ( sink options -- ) lf-pjob lf-pjob-setup 2! ;
\ The settings lf-print-setup made, for a caller that prints elsewhere for
\ a while and then sets them back.
: lf-print-settings ( -- sink options ) lf-pjob lf-pjob-setup 2@ ;
\ The sink alone, for a caller that prints a part of its text through it
\ (a message's term, to the message's sink); the options alone.
: lf-print-sink ( -- sink ) lf-print-settings drop ;
: lf-pp-options ( -- options ) lf-print-settings nip ;
\ Notation (print-notation.fs): off until the caller turns it on; it
\ survives lf-print-setup, which sets only the sink and the options.
: lf-print-notation! ( flag -- ) lf-pjob lf-pjob-notation ! ;
: lf-print-notation? ( -- flag ) lf-pjob lf-pjob-notation @ ;
: lf-print-limit! ( n -- flag )
  dup 0> lf-pp-busy? 0= and if lf-pjob lf-pjob-limit ! true else drop false then ;
: lf-pp-no-visit ( x frames -- -1 outcome frames 0 ) >r drop -1 outcome-invalid r> 0 ;
: lf-print-defaults ( -- )
  ['] lf-pp-no-visit lf-pp-frames frame-init
  ['] type 0 lf-print-setup false lf-print-notation!
  lf-print-default-limit lf-print-limit! drop ;
' lf-print-defaults context-setup
:noname ( -- ) lf-pp-frames frame-free ; context-teardown

\ Text. The sink runs with lf-pjob-sinking set, so that lf-print-reset
\ knows a call from the sink; the flag is restored afterwards, also when
\ the sink THROWs (CATCH only restores it, then the THROW goes on).
: lf-pp-sinking ( -- addr ) lf-pjob lf-pjob-sinking ;
: lf-pp-emit ( c-addr u -- )
  lf-pp-sinking @ >r true lf-pp-sinking ! lf-print-sink catch
  r> lf-pp-sinking ! throw ;
\ The mode: the one set by lf-print-setup, or LaTeX during a Markdown math
\ print, which leaves the options as they are.
: lf-pp-math? ( -- flag ) lf-pjob lf-pjob-math @ ;
: lf-pp-math! ( flag -- ) lf-pjob lf-pjob-math ! ;
: lf-pp-setup-mode ( -- mode ) lf-pp-options lf-print-mode-mask and ;
: lf-pp-mode ( -- mode ) lf-pp-math? if lf-print-latex else lf-pp-setup-mode then ;
: lf-pp-latex? ( -- flag ) lf-pp-mode lf-print-latex = ;
: lf-pp-universes? ( -- flag ) lf-pp-options lf-print-universes and 0<> ;
\ A number's decimal digits, whatever BASE is; BASE is kept. The digits
\ are in the pictured numeric output buffer, so they are used at once.
: lf-pp-number-to ( u xt -- ) >r u>decimal r> execute ;
: lf-pp-number ( u -- ) ['] lf-pp-emit lf-pp-number-to ;

\ Visits (plan task 6.2.0). Every recursive printing word is a chain of
\ steps ( i*x frames -- j*x frames next ) on the print's frames, run by
\ their loop (lib/frame.fs), so a print nests on the host's stacks by a
\ constant whatever its depth. lf-pp-call visits a b with the first step
\ xt ( a b frames -- ... frames next ), charging one unit of fuel and one
\ nested visit, and continues with cont ( outcome frames -- ... frames
\ next ) once the visit has ended with ( outcome frames 0 ). With no fuel,
\ no room on the frames' stack (the heap refuses) or the caller's limit of
\ nested visits reached, it visits nothing and continues at once:
\ exhausted without fuel, otherwise full. Every recursive printing word
\ has that shape, so one record bounds them all. A word ( ... frames cont
\ -- ... frames next ) is a part of a visit: it spends nothing itself and
\ ends by continuing with cont, at once or after the visits it asks for
\ (cont waits on the stack, under the part's own cells, until then).
\ Between two visits a visit's steps save at most lf-pp-spare cells: each
\ visit's admission makes that room. A visit's results go to cont as they
\ are; lf-pp-finish (term-printer.fs) makes the print's own sane. Every
\ step and part carries the protocol's cells (frames, and next or cont)
\ besides its own values, so stack comments of four items are usual here.
12 constant lf-pp-spare
: lf-pp-within? ( frames -- flag ) dup frame-depth @ swap lf-pjob-limit @ < ;
: lf-pp-admit ( frames -- outcome )
  dup frame-admit ok-then? 0= if exit then
  dup lf-pp-within? 0= if drop outcome-full exit then
  lf-pp-spare 2 + swap frame-room? room>outcome ;
: lf-pp-refuse ( a b frames cont outcome -- outcome frames cont ) >r 2swap 2drop r> -rot ;
: lf-pp-call ( a b frames cont xt -- a b frames xt | outcome frames cont )
  2 pick lf-pp-admit dup ok? if drop frame-open else nip lf-pp-refuse then ;
\ A visit run to its end, from the cells the stack holds now: a print's
\ root, or a comparison that a step asks for (print-analysis.fs).
: lf-pp-run ( a b xt -- outcome )
  lf-pp-frames frame-used @ >r >r lf-pp-frames ['] frame-return r> lf-pp-call
  r> frame-loop drop ;
\ Two or three cells kept on the stack across a visit, given back in
\ their order.
: lf-pp-save2 ( x1 x2 frames -- ) tuck frame-save frame-save ;
: lf-pp-restore2 ( frames -- x1 x2 ) dup frame-restore swap frame-restore ;
: lf-pp-save3 ( x1 x2 x3 frames -- ) tuck frame-save lf-pp-save2 ;
: lf-pp-restore3 ( frames -- x1 x2 x3 ) dup >r lf-pp-restore2 r> frame-restore ;
\ A loop over the indexes of a node's parts keeps x, y and the next index.
: lf-pp-keep-next ( x y i frames -- x y i ) >r dup 1+ 2over rot r> lf-pp-save3 ;
\ A part's continuation, after a child's visit, when the part kept n
\ cells: a failed outcome drops them and ends the part with it (true);
\ ok goes (false), the cells still kept.
: lf-pp-failed? ( outcome frames n -- outcome frames true | frames false )
  >r over ok? if nip r> drop false else r> over frame-drop true then ;
\ A continuation that, unless the part failed, restores the three values
\ saved under it and goes on with next ( x1 x2 x3 frames -- ... frames
\ next ): the next of a list's items.
: lf-pp-back3 ( outcome frames next -- ... frames next )
  >r 3 lf-pp-failed? if r> drop 0 exit then dup >r lf-pp-restore3 r> r> execute ;
\ The step of a visit that cannot print its node: invalid.
: lf-pp-invalid-step ( a b frames -- outcome frames 0 ) >r 2drop outcome-invalid r> 0 ;
\ One unit of fuel for a step along a spine or chain, false when none is left.
: lf-pp-spend ( -- flag ) lf-print-fuel cell-spend? ;
\ Steps along a spine or chain from k = 0, one unit of fuel each, while
\ step ( x k -- x' k' true | x k false ) goes on: x and k where it
\ stopped and ok, or exhausted when the fuel ran out first.
: lf-pp-fuelled ( x step -- x' k outcome )
  >r 0 begin lf-pp-spend 0= if r> drop outcome-exhausted exit then r@ execute 0= until
  r> drop outcome-ok ;
\ Close a parenthesis opened when flag is true; the step that does so for
\ the flag saved under it, at the end of a part.
: lf-pp-wrap ( outcome flag -- outcome ) if s" )" lf-pp-emit then ;
\ A continuation that restores the value saved under it and ends with
\ step ( outcome x -- outcome ) on it: closing a parenthesis, leaving a
\ scope (term-printer.fs), ending a part (print-forth.fs).
: lf-pp-restored ( outcome frames step -- outcome frames 0 )
  swap >r r@ frame-restore swap execute r> 0 ;
: lf-pp-wrapped ( outcome frames -- outcome frames 0 ) ['] lf-pp-wrap lf-pp-restored ;
\ A walk (lib/walk.fs) borrows the print's fuel and gives back what is left.
: lf-pp-lend ( walk -- ) lf-print-fuel @ swap walk-budget drop ;
: lf-pp-repay ( walk -- ) walk-fuel @ lf-print-fuel ! ;

\ The name pool, a growable array of bytes. A name the heap has no room
\ for is left out and marks the pool full; the print then ends full. The
\ pool moves when it grows, so nothing keeps an address into it across a
\ put, and the text put never lies in it.
: lf-pp-pool ( -- addr ) lf-pp-pool-bytes slab-base ;
: lf-pp-used ( -- addr ) lf-pjob lf-pjob-used ;
: lf-pp-full? ( -- flag ) lf-pjob lf-pjob-full @ ;
\ The pool full: a name did not fit in it, or could not be printed whole.
: lf-pp-full! ( -- ) true lf-pjob lf-pjob-full ! ;
: lf-pp-room? ( u -- flag ) lf-pp-used @ + lf-pp-pool-bytes slab-hold ok? ;
: lf-pp-put ( c-addr u -- )
  dup lf-pp-room? 0= if 2drop lf-pp-full! exit then
  tuck >r lf-pp-pool lf-pp-used @ + r> move lf-pp-used +! ;
: lf-pp-pool-outcome ( -- outcome )
  lf-pp-full? if outcome-full else outcome-ok then ;
\ Text placed in the pool from offset mark up to the end of what is used;
\ none when less is used (only after a forbidden reset from a sink).
: lf-pp-pending ( mark -- c-addr u ) dup lf-pp-pool + lf-pp-used @ rot - 0 max ;

\ The binders in scope, bottom first, in a growable array; lf-pp-entry
\ counts from the innermost (j = 0), as a bound variable's index does. The
\ count is clamped into the array's range (defence in depth: see the sink
\ rules). A binder the heap has no room for is full (slab-hold's outcome).
: lf-pp-depth ( -- n )
  lf-pjob lf-pjob-binders @ 0 max lf-pp-scope-table slab-capacity min ;
: lf-pp-bind-at ( i -- bind ) lf-pp-scope-table slab-at ;
: lf-pp-entry ( j -- bind ) lf-pp-depth 1- swap - lf-pp-bind-at ;
: lf-pp-text ( bind -- c-addr u )
  dup lf-pbind-offset @ lf-pp-pool + swap lf-pbind-length @ ;
\ Bring a binder into scope: its domain and the name pending at mark.
: lf-pp-bind-set ( domain mark bind -- )
  >r dup r@ lf-pbind-offset ! lf-pp-pending nip r@ lf-pbind-length !
  r> lf-pbind-domain ! ;
: lf-pp-bind ( domain mark -- outcome )
  lf-pp-depth 1+ lf-pp-scope-table slab-hold ok-then2? 0= if exit then
  lf-pp-depth lf-pp-bind-at lf-pp-bind-set 1 lf-pjob lf-pjob-binders +! outcome-ok ;
\ Leave the innermost n binders; their names leave the pool. Nothing is
\ left when none is in scope.
: lf-pp-unbind ( n -- )
  dup 0> lf-pp-depth 0> and 0= if drop exit then
  lf-pp-depth swap - 0 max dup lf-pjob lf-pjob-binders !
  lf-pp-bind-at lf-pbind-offset @ lf-pp-used ! ;

\ A print starts with an empty scope and pool, the given fuel and the
\ visit limit. A busy printer (a sink printing again) and negative fuel
\ are refused.
: lf-pp-broken ( -- addr ) lf-pjob lf-pjob-broken ;
: lf-pp-clear ( -- )
  0 lf-pjob lf-pjob-binders ! 0 lf-pjob lf-pjob-chain ! 0 lf-pp-used ! false lf-pjob
  lf-pjob-full ! ;
: lf-pp-begun ( -- ) lf-pp-clear false lf-pp-broken ! true lf-pp-printing ! ;
: lf-pp-start ( fuel -- flag )
  lf-pp-busy? if drop false exit then
  lf-pp-frames frame-budget dup if lf-pp-begun then ;
\ Recover after a THROW out of a print: idle, with an empty scope and
\ pool, in the mode lf-print-setup set (a Markdown math print forced
\ LaTeX without changing the options). Called by the sink while a print
\ is in progress, against the sink rules, it only marks that print, which
\ goes on to its end, its steps' stack whole, and then ends invalid and
\ resets the printer (lf-pp-reset, at once).
: lf-pp-reset ( -- )
  lf-pp-frames frame-reset lf-pp-clear false lf-pp-math! false lf-pp-broken !
  false lf-pp-printing ! ;
: lf-print-reset ( -- )
  lf-pp-sinking @ lf-pp-busy? and if true lf-pp-broken ! else lf-pp-reset then ;
