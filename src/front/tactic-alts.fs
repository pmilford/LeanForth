\ The alternatives of an eliminating tactic (docs/design/TACTIC_PLUGINS.md
\ 2.5; plan 9.4.8l-I, commit C4), Elab glue that drives the runner's
\ blocks, after Lean 4.35.0's Elab/Tactic/Induction.lean (evalAlts :340,
\ checkAltNames :283, getNumExplicitFields :317, evalAlt :83); the
\ eliminator and its alternatives' goals are meta-tactic/elim.fs's:
\   lf-eval-alts ( i info alts target -- )  evalAlts for step i, in its
\       step record (which keeps the four), alts the alternatives' goals
\       (lf-elim-app's run):
\       when i's kind holds alternatives (tactic-run.fs's lf-tactic-alt!),
\       their names checked (lf-alt-names-check) and the block's record
\       opened for them (the caller opens the runner's block after it);
\       else every alternative's goal, its fields introduced with
\       inaccessible names and the target cleared, in order, is the goal
\       list (the caller unfocuses)
\   lf-alt-names-check ( info i -- )  checkAltNames over the alternatives
\       right inside step i, in text order (info kept as the running step
\       record's tal-info, which the messages read): a name written twice 213 at
\       the second (Lean's "Duplicate alternative name"), before a name
\       that is no alternative of info, 206 with the alternatives not
\       written (Lean's orList: "Expected `zero` or `succ`")
\   lf-alt-run ( j -- )  evalAlt, the run word of an alternative (|) step
\       j (lf-tactic-alt!'s xt): the alternative its tag names, in the
\       innermost open block; at most as many names as it has explicit
\       fields (208 at j); its goal alone, its fields introduced (introN
\       with useNamesForExplicitOnly: the names in order for the explicit
\       fields, the binder's own, inaccessible, for the rest; one
\       tactic-core.fs lf-tac-intro1 per field, each through
\       meta-tactic/goal.fs's lf-goal-intro-n), the target cleared
\       (tryClear, meta-tactic/assert.fs's lf-goal-try-clear: a refusal
\       keeps the goal; fuel, room or a gap is thrown,
\       as Lean's <|> never catches a runtime exception), then j runs as a
\       block (unsolved goals at its =>)
\   lf-alts-missing ( i -- )  at block i's end (lf-tactic-end!'s xt): an
\       alternative no | wrote is 207 at i's word (Lean's first message
\       there); the block's record dropped
\ A field's kind is the eliminator's declared type's (elim.fs's
\ lf-elim-alt-kinds), never the goal's node: unknown kinds are 99. A
\ difference from Lean kept from S2 (review tactic-move-c4 L4): Lean
\ 4.35.0's getNumExplicitFields (Induction.lean:317) introduces the
\ fields first and counts the explicit locals, a let-bound one among
\ them (introN names it as explicit); LeanForth counts the declared
\ kinds, which agree for every eliminator a text reaches (recursors and
\ casesOn have no let field).
\ Errors stop the run (author/errors.fs) at the step's word, an
\ alternative's at its |.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: the slab tal-blocks (the open blocks: the eliminator's
\ information, the alternatives' goals and the target), kept in a
\ tactic's saved state on tal-blocks-kept (tac-state:), and tal-js (a
\ block's alternative steps while they are checked), in the checker
\ context (ADR 0009); a step's own fields in its step record (/tal, after
\ tactic-core.fs's tb). Loads in decimal whatever BASE is, then restores
\ it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/find.fs
require ../lib/runs.fs
require ../lib/slab.fs
require ../lib/context.fs
require ../present/binder-table.fs
require ../present/print-job.fs
require ../author/errors.fs
require ./goals.fs
require ./tactic-syntax.fs
require ./tactic-run.fs
require ./tactic-msg.fs
require ./tactic-core.fs
require ./meta-tactic/elim.fs
require ./meta-tactic/assert.fs

\ ---- The open blocks, in a tactic's saved state (tactic-run.fs's
\ tac-state:; review C2 of 2026-11-18: a failed block left them open).
begin-structure /tab
  field: tab-info         \ the eliminator's information
  field: tab-alts         \ the alternatives' goals, a run
  field: tab-target       \ the target
end-structure
/tab context-slab: tal-blocks
/tab context-slab: tal-blocks-kept
: tal-keep ( -- outcome ) tal-blocks tal-blocks-kept slab-keep ;
: tal-kept ( undo? -- outcome ) tal-blocks tal-blocks-kept slab-kept ;
' tal-keep ' tal-kept tac-state:
1 cells context-slab: tal-js   \ a block's alternatives: their steps
\ The step's fields, after tb's.
begin-structure /tal
  /tb +field tal-tb
  field: tal-info         \ the eliminator's information
  field: tal-alts         \ the alternatives' goals (lf-eval-alts), a run
  field: tal-target       \ the target
  field: tal-step         \ the step whose names the fields take
  field: tal-given        \ the names taken so far
  field: tal-k            \ the alternative
end-structure
/tal lf-tac-work-cells cells >
[if] .( tactic-alts.fs: its fields are wider than a step record) cr abort [then]
: tal ( -- addr ) lf-tac-record ;
: tal-info@ ( -- info ) tal tal-info @ ;
: tal-alts@ ( -- alts ) tal tal-alts @ ;
: tal-target@ ( -- target ) tal tal-target @ ;
: tal-i ( -- i ) tal tal-step @ ;
: tal-start ( i info target -- )
  tal tal-target ! tal tal-info ! tal tal-step ! 0 tal tal-given ! ;
: tal-case-name ( k -- name ) tal-info@ swap lf-elim-alt-name ;

\ ---- checkAltNames over block i's alternatives (tal-js: their steps, in
\ text order).
: tal-parent ( j -- i ) lf-tactic-step tac-parent @ ;
: tal-tag ( j -- name ) lf-tactic-step tac-name @ ;
: tal-alts-of ( i -- )
  tal-js slab-clear lf-tactic-count over 1+ ?do dup i tal-parent = if
    i tal-js slab-push lf-tac-must then loop drop ;
: tal-j ( a -- j ) tal-js slab-at @ ;
: tal-tag-at ( a -- name ) tal-j tal-tag ;
: tal-tag=? ( name a -- name flag ) tal-tag-at over = ;
: tal-earlier? ( a -- flag ) dup tal-tag-at swap ['] tal-tag=? any? nip ;
: tal-written? ( name -- flag ) tal-js slab-count ['] tal-tag=? any? nip ;
: tal-named? ( name -- flag ) tal-info@ swap lf-elim-alt-find dup if nip then ;
\ The alternatives no step names, as Lean's orList: x, x or y, x, y, or z.
: tal-unhandled? ( k -- flag ) tal-case-name tal-written? 0= ;
: tal-unhandled# ( -- n ) 0 tal-info@ lf-elim-alts# ['] tal-unhandled? count-index ;
: tal-sep ( m n -- c-addr u )
  over 0= if 2drop s" " exit then dup 2 = if 2drop s"  or " exit then
  1- = if s" , or " else s" , " then ;
: tal-listed ( n m k -- n m' )
  >r 2dup swap tal-sep lf-pp-emit r> tal-case-name lf-tac-.name 1+ ;
: tal-none. ( -- ) s" There are no unhandled alternatives" lf-pp-emit ;
: tal-expected. ( -- )
  tal-unhandled# dup 0= if drop tal-none. exit then s" Expected " lf-pp-emit
  0 tal-info@ lf-elim-alts# 0 ?do i tal-unhandled? if i tal-listed then loop 2drop ;
: tal-name. ( a -- outcome ) s"  " lf-pp-emit tal-tag-at lf-tac-.name outcome-ok ;
: tal-invalid. ( a -- outcome )
  tal-name. drop s" : " lf-pp-emit tal-expected. outcome-ok ;
: tal-refused ( a xt code -- ) >r over swap lf-tac-inline tal-j r> lf-tac-stop-at ;
: tal-twice ( -- )
  tal-js slab-count 0 ?do i tal-earlier? if
    i ['] tal-name. lfa-e-tac-alt-twice tal-refused then loop ;
: tal-unknown ( -- )
  tal-js slab-count 0 ?do i tal-tag-at tal-named? 0= if
    i ['] tal-invalid. lfa-e-tac-alt-name tal-refused then loop ;
: lf-alt-names-check ( info i -- ) swap tal tal-info ! tal-alts-of tal-twice tal-unknown ;

\ ---- An alternative's goal: alone, its fields introduced, the target
\ cleared.
: tal-k@ ( -- k ) tal tal-k @ ;
: tal-kind ( f -- kind )
  tal-info@ tal-k@ lf-elim-alt-kinds rot tuck > 0= if lfa-e-tac-form lf-tac-fail then
  cells + @ ;
: tal-explicit? ( f -- flag ) tal-kind lf-binder-default = ;
: tal-fields ( -- n ) tal-info@ tal-k@ lf-elim-alt-fields ;
: tal-explicit# ( -- n ) 0 tal-fields ['] tal-explicit? count-index ;
: tal-given# ( -- n ) tal-i lf-tac-args# ;
\ introN: the names given for the explicit fields, in order; 0 (the
\ binder's own name, inaccessible) for the others and past the names.
: tal-next-name ( -- name )
  tal-given# tal tal-given @ > 0= if 0 exit then
  tal-i tal tal-given @ lf-tac-arg 1 tal tal-given +! ;
: tal-name-for ( kind -- name ) lf-binder-default = if tal-next-name else 0 then ;
: tal-field ( f -- ) tal-kind dup tal-name-for swap tal-i lf-tac-intro1 ;
: tal-intros ( -- ) tal-fields 0 ?do i tal-field loop ;
: tal-cleared ( -- ) lf-tac-main tal tal-target @ lf-goal-try-clear lf-tac-only ;
: tal-case ( goal -- ) lf-tac-only tal-intros tal-cleared ;

\ ---- evalAlts: with alternatives, the block's record; without, every
\ alternative's goal (the step's arguments counted as names already
\ taken, so none is given), gathered as the goal list.
\ (The step record holds i, info, alts and target from tal-begin on; review
\ tactic-move-c4 M3: no word takes the four cells.)
: tal-begin ( i info alts target -- ) swap tal tal-alts ! tal-start ;
: tal-open ( info alts target -- )
  1 tal-blocks slab-claim lf-tac-must tal-blocks slab-at tuck tab-target ! tuck tab-alts !
  tab-info ! ;
: tal-with ( -- )
  tal-info@ tal-i lf-alt-names-check tal-info@ tal-alts@ tal-target@ tal-open ;
: tal-plain-case ( run k -- run' )
  dup tal tal-k ! tal-alts@ swap run@ tal-case lf-tac-main run-push lf-tac-must ;
: tal-unnamed ( -- ) tal-given# tal tal-given ! ;
: tal-plain ( -- )
  tal-unnamed 0 tal-alts@ run-count 0 ?do i tal-plain-case loop lf-goals! lf-tac-must ;
: tal-holder? ( i -- flag ) lf-tactic-step tac-kind @ lf-tactic-alt@ 0<> ;
: lf-eval-alts ( i info alts target -- )
  tal-begin tal-i tal-holder? if tal-with else tal-plain then ;

\ ---- evalAlt: the alternative step j in its own record, then its block.
: tal-block ( -- addr ) tal-blocks slab-last ;
: tal-case-name@ ( -- name ) tal-k@ tal-case-name ;
: tal-too-many. ( x -- outcome )
  drop s"  " lf-pp-emit tal-case-name@ lf-tac-.name s" : " lf-pp-emit
  tal-given# lf-pp-number s"  provided, but " lf-pp-emit
  tal-explicit# lf-pp-number s"  expected" lf-pp-emit outcome-ok ;
: tal-names-fit ( -- )
  tal-explicit# tal-given# < if 0 ['] tal-too-many. lf-tac-inline
    tal-i lfa-e-tac-alt-names lf-tac-stop-at then ;
: tal-k! ( -- )
  tal-info@ tal-i tal-tag lf-elim-alt-find 0= if
    lfa-e-tac-record lf-tac-stop 0 then tal tal-k ! ;
: tal-goal ( -- goal ) tal-block tab-alts @ tal-k@ run@ ;
: tal-alt ( j -- )
  tal-block dup tab-info @ swap tab-target @ tal-start tal-k! tal-names-fit
  tal-goal tal-case ;
: lf-alt-run ( j -- ) lf-goals over ['] tal-alt lf-tac-in-record lf-tac-block ;

\ ---- At the block's end: an alternative no step wrote (207).
: tal-missing. ( name -- outcome )
  s"  " lf-pp-emit lf-tac-.name s"  has not been provided" lf-pp-emit outcome-ok ;
: tal-unused ( i info k -- i info )
  over swap lf-elim-alt-name dup tal-written? if drop exit then
  ['] tal-missing. lf-tac-inline over lfa-e-tac-alt-missing lf-tac-stop-at ;
: lf-alts-missing ( i -- )
  dup tal-alts-of tal-block tab-info @ dup lf-elim-alts# 0 ?do i tal-unused loop 2drop
  tal-blocks slab-drop ;
base !   \ the BASE this file was loaded with
