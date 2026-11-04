\ The term printer's working state and text primitives (plan task 2.4.3):
\ the caller's character sink and options, the bounded-recursion record,
\ the binders in scope with their display names, and the pool that holds
\ those names. Untrusted presentation code; the checker never loads it.
\ Requires binder-table.fs and the term and name stores.
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
\ clamped into range, so a sink that breaks the rules cannot make a print
\ loop without end or address outside the printer's record.
\ State: one context record, lf-pjob (ADR 0009).

require ./binder-table.fs

0 constant lf-print-unicode     \ mode: Lean's notation (with pp.unicode.fun)
1 constant lf-print-ascii       \ mode: plain ASCII notation (forall, ->, =>)
2 constant lf-print-latex       \ mode: LaTeX math
3 constant lf-print-mode-mask
4 constant lf-print-universes   \ option bit: show universe arguments, c.{u}
lf-depth-limit constant lf-print-binder-capacity
4096 constant lf-print-pool-capacity
lf-depth-limit 2* constant lf-print-default-limit

\ One binder in scope: its domain term and its display name in the pool.
begin-structure /lf-pbind
  field: lf-pbind-domain
  field: lf-pbind-offset
  field: lf-pbind-length
end-structure

begin-structure /lf-pjob
  field: lf-pjob-sink        \ xt ( c-addr u -- )
  field: lf-pjob-options     \ mode and option bits
  field: lf-pjob-limit       \ most nested visits in one print
  field: lf-pjob-binders     \ binders in scope
  field: lf-pjob-chain       \ binders in scope where the current fun began
  field: lf-pjob-used        \ pool bytes in use
  field: lf-pjob-full        \ true once a name did not fit in the pool
  field: lf-pjob-math        \ true while lf-print-inline or -display forces LaTeX
  /frames +field lf-pjob-frames
  lf-print-binder-capacity /lf-pbind * +field lf-pjob-stack
  lf-print-pool-capacity +field lf-pjob-pool
end-structure
/lf-pjob context-record: lf-pjob

: lf-pp-frames ( -- frames ) lf-pjob lf-pjob-frames ;
: lf-print-fuel ( -- addr ) lf-pp-frames frame-fuel ;
\ Busy while a print is in progress, or after a THROW out of one.
: lf-pp-busy? ( -- flag ) lf-pp-frames frame-busy? ;

\ Settings. lf-print-setup takes the sink and the options (a mode plus
\ option bits); lf-print-limit! the most nested visits per print, at least
\ 1, and refuses while a print is in progress. Every context starts with
\ TYPE, Unicode, no universes and the default limit.
: lf-print-setup ( sink options -- ) lf-pjob tuck lf-pjob-options ! lf-pjob-sink ! ;
: lf-print-limit! ( n -- flag )
  dup 0> lf-pp-busy? 0= and if lf-pjob lf-pjob-limit ! true else drop false then ;
: lf-print-defaults ( -- ) ['] type 0 lf-print-setup lf-print-default-limit
  lf-print-limit! drop ;
' lf-print-defaults context-setup

\ Text.
: lf-pp-emit ( c-addr u -- ) lf-pjob lf-pjob-sink @ execute ;
\ The mode: the one set by lf-print-setup, or LaTeX during a Markdown math
\ print, which leaves the options as they are.
: lf-pp-math? ( -- flag ) lf-pjob lf-pjob-math @ ;
: lf-pp-math! ( flag -- ) lf-pjob lf-pjob-math ! ;
: lf-pp-setup-mode ( -- mode ) lf-pjob lf-pjob-options @ lf-print-mode-mask and ;
: lf-pp-mode ( -- mode ) lf-pp-math? if lf-print-latex else lf-pp-setup-mode then ;
: lf-pp-latex? ( -- flag ) lf-pp-mode lf-print-latex = ;
: lf-pp-universes? ( -- flag ) lf-pjob lf-pjob-options @ lf-print-universes and 0<> ;
\ A number's decimal digits, whatever BASE is; BASE is kept. The digits
\ are in the pictured numeric output buffer, so they are used at once.
: lf-pp-digits ( u -- c-addr u ) base @ >r decimal 0 <# #s #> r> base ! ;
: lf-pp-number-to ( u xt -- ) >r lf-pp-digits r> execute ;
: lf-pp-number ( u -- ) ['] lf-pp-emit lf-pp-number-to ;

\ Fuel and bounded recursion. lf-pp-call visits a b with xt ( a b -- outcome
\ ) one level deeper, charging one unit of fuel; with no fuel or no frame
\ left it visits nothing: exhausted without fuel, full without a frame.
\ Every recursive printing word has that shape, so one frames record bounds
\ them all.
: lf-pp-visit ( a b xt frames -- outcome ) drop execute ;
: lf-pp-call ( a b xt -- outcome )
  lf-pp-frames dup frame-room ok-then? if frame-visit else nip nip nip then ;
\ One unit of fuel for a step along a spine or chain, false when none is left.
: lf-pp-spend ( -- flag ) lf-print-fuel dup @ 0> if -1 swap +! true else drop false then ;
\ Close a parenthesis opened when flag is true.
: lf-pp-wrap ( outcome flag -- outcome ) if s" )" lf-pp-emit then ;
\ A walk (lib/walk.fs) borrows the print's fuel and gives back what is left.
: lf-pp-lend ( walk -- ) lf-print-fuel @ swap walk-budget drop ;
: lf-pp-repay ( walk -- ) walk-fuel @ lf-print-fuel ! ;

\ The name pool. A name that does not fit is cut and marks the pool full;
\ the print then ends full.
: lf-pp-pool ( -- addr ) lf-pjob lf-pjob-pool ;
: lf-pp-used ( -- addr ) lf-pjob lf-pjob-used ;
: lf-pp-full? ( -- flag ) lf-pjob lf-pjob-full @ ;
: lf-pp-room? ( u -- flag ) lf-print-pool-capacity lf-pp-used @ - upto? ;
: lf-pp-put ( c-addr u -- )
  dup lf-pp-room? 0= if 2drop true lf-pjob lf-pjob-full ! exit then
  tuck >r lf-pp-pool lf-pp-used @ + r> move lf-pp-used +! ;
: lf-pp-pool-outcome ( -- outcome )
  lf-pp-full? if outcome-full else outcome-ok then ;
\ Text placed in the pool from offset mark up to the end of what is used;
\ none when less is used (only after a forbidden reset from a sink).
: lf-pp-pending ( mark -- c-addr u ) dup lf-pp-pool + lf-pp-used @ rot - 0 max ;

\ The binders in scope, bottom first; lf-pp-entry counts from the
\ innermost (j = 0), as a bound variable's index does. The count is
\ clamped into the stack's range (defence in depth: see the sink rules).
: lf-pp-depth ( -- n ) lf-pjob lf-pjob-binders @ 0 max lf-print-binder-capacity min ;
: lf-pp-bind-at ( i -- bind ) /lf-pbind * lf-pjob lf-pjob-stack + ;
: lf-pp-entry ( j -- bind ) lf-pp-depth 1- swap - lf-pp-bind-at ;
: lf-pp-text ( bind -- c-addr u )
  dup lf-pbind-offset @ lf-pp-pool + swap lf-pbind-length @ ;
\ Bring a binder into scope: its domain and the name pending at mark.
: lf-pp-bind-set ( domain mark bind -- )
  >r dup r@ lf-pbind-offset ! lf-pp-pending nip r@ lf-pbind-length !
  r> lf-pbind-domain ! ;
: lf-pp-bind ( domain mark -- outcome )
  lf-pp-depth lf-print-binder-capacity < 0= if 2drop outcome-full exit then
  lf-pp-depth lf-pp-bind-at lf-pp-bind-set 1 lf-pjob lf-pjob-binders +! outcome-ok ;
\ Leave the innermost n binders; their names leave the pool.
: lf-pp-unbind ( n -- )
  dup 0> 0= if drop exit then
  negate lf-pjob lf-pjob-binders +! lf-pp-depth lf-pp-bind-at lf-pbind-offset @ lf-pp-used
  ! ;

\ A print starts with an empty scope and pool, the given fuel and the
\ visit limit. A busy printer (a sink printing again) is refused.
: lf-pp-clear ( -- )
  0 lf-pjob lf-pjob-binders ! 0 lf-pjob lf-pjob-chain ! 0 lf-pp-used ! false lf-pjob
  lf-pjob-full ! ;
: lf-pp-start ( fuel -- flag )
  lf-pp-busy? over 0< or if drop false exit then
  lf-pjob lf-pjob-limit @ ['] lf-pp-visit lf-pp-frames frame-init
  lf-pp-frames frame-budget dup if lf-pp-clear then ;
\ Recover after a THROW out of a print: idle, with an empty scope and
\ pool, in the mode lf-print-setup set (a Markdown math print forced
\ LaTeX without changing the options).
: lf-print-reset ( -- ) lf-pp-frames frame-reset lf-pp-clear false lf-pp-math! ;
