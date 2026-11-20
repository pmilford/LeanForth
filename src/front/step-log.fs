\ The step log's writer (plan S2, branch s2-steps; docs/design/
\ S2_INTERFACE.md §6 and appendix C): the steps front/tactic-run.fs
\ recorded while the text ran (lf-steps-record!), written after the
\ verdicts as NDJSON `leanforth-tactic-steps` version 1
\ (schemas/tactic-steps-1.schema.json), for the declarations the kernel
\ accepted only. Per declaration, in the order the text made them, one
\ header line
\   {"tactic_steps":{"axioms":[AXIOM,...],"cut":false,"declaration":NAME,
\    "format":"leanforth-tactic-steps","format_version":1,"open_parts":P,
\    "steps":N}}
\ AXIOM each axiom the declaration depends on (as #print axioms, sorryAx
\ for a by-sorry), P its open parts (by-sorry): a declaration is proved
\ only when P is 0 and every axiom is allowlisted. cut true: the log ran
\ out of room while the text ran (front/tactic-run.fs) before this
\ declaration's end; its steps are left out (N 0). Then one line per
\ step, in the order they took effect:
\   {"goal_before":TEXT|null,"goals_after":[TEXT,...],"parent":P,
\    "source":"LINE:COL","step":K,"tactic":T,"word":W}
\ K counts from 1; P is the step of the block it ran in (an alternative,
\ a case, an induction's with), 0 for the proof's own; T is rfl, exact,
\ intro, induction, alternative, case, rewrite, rw or sorry, W the
\ LeanForth word; TEXT a goal as .goals prints it (goal-print.fs, Lean's
\ trace_state), null before a step with no goal; goals_after the goals in
\ focus once the step took effect. Keys sorted, no whitespace, one line
\ each (lib/json-write.fs). Not built yet of appendix C: each tactic's
\ rule fields, the constants and hypotheses it used and the goals in
\ kernel form (a later version adds them).
\ lf-steps-write ( sink find axioms -- outcome ): sink ( c-addr u -- )
\ takes each piece of a line, then its line feed; find ( c-addr u -- d
\ true | false ) gives the accepted declaration of that full name;
\ axioms ( d xt -- outcome ) calls xt ( c-addr u -- ) with the name of
\ each axiom d depends on; it runs twice, to check that every name can be
\ given, then to write them: a refusal the first time writes "axioms":null
\ (never a short list). ok, or the first refusal (the writer's, full for
\ no room in its key pool, or axioms').
\ Presentation data: nothing reads it to decide; it changes no verdict.
\ Example: ' type ' accepted ' axioms-of lf-steps-write drop
\ State: the record lsl (the sink, the two words, the declaration's first
\ entry, the writer, the text of a position), in the checker context.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/json-write.fs
require ../lib/decimal.fs
require ../author/source.fs
require ./tactic-syntax.fs
require ./tactic-run.fs

4 constant lsl-depth      \ a header: two objects, an array; a step: an object, an array
64 constant lsl-key-room
24 constant lsl-pos-room  \ "LINE:COL"
begin-structure /lsl
  field: lsl-sink
  field: lsl-find
  field: lsl-axioms
  field: lsl-first        \ the declaration's first entry
  field: lsl-pos#
  lsl-pos-room chars +field lsl-pos
  lsl-depth lsl-key-room jw-size +field lsl-writer
end-structure
/lsl context-record: lsl
: lsl-w ( -- writer ) lsl lsl-writer ;
:noname ( -- )
  lsl-depth lsl-key-room lsl-w jw-init drop max-n lsl-w jw-limit !
  true lsl-w jw-sorted ! ; context-setup

\ ---- Lines.
: lsl-begin ( -- ) lsl lsl-sink @ lsl-w jw-start lsl-w jw-open-object ;
: lsl-end ( -- outcome )
  lsl-w jw-close-object lsl-w jw-end dup ok? if s\" \n" lsl lsl-sink @ execute then ;
: lsl-key ( c-addr u -- ) lsl-w jw-key ;
: lsl-text ( c-addr u key-addr key-u -- ) lsl-key lsl-w jw-string ;
: lsl-number ( u key-addr key-u -- ) lsl-key lsl-w jw-u ;
: lsl-span ( first n -- )
  over 0< if 2drop lsl-w jw-null else lf-steps-text lsl-w jw-string then ;

\ ---- The header: the axioms first (their outcome kept), then the rest.
: lsl-name ( decl -- c-addr u ) tld-name 2@ lf-steps-text ;
: lsl-axiom ( c-addr u -- ) lsl-w jw-string ;
: lsl-axioms-of ( d xt -- outcome ) lsl lsl-axioms @ execute ;
: lsl-axiom-list ( d -- outcome )
  s" axioms" lsl-key dup ['] 2drop lsl-axioms-of
  dup ok? 0= if nip lsl-w jw-null exit then
  drop lsl-w jw-open-array ['] lsl-axiom lsl-axioms-of lsl-w jw-close-array ;
: lsl-steps# ( decl -- n ) dup tld-cut @ if drop 0 else tld-count @ then ;
: lsl-rest ( decl -- )
  dup tld-cut @ s" cut" lsl-key lsl-w jw-bool dup lsl-name s" declaration" lsl-text
  s" leanforth-tactic-steps" s" format" lsl-text 1 s" format_version" lsl-number
  dup tld-parts @ s" open_parts" lsl-number lsl-steps# s" steps" lsl-number ;
: lsl-header ( d decl -- outcome )
  lsl-begin s" tactic_steps" lsl-key lsl-w jw-open-object swap lsl-axiom-list
  swap lsl-rest lsl-w jw-close-object lsl-end outcome-and ;

\ ---- A step.
\ The tactic's name, Lean's: its kind's row (tactic-run.fs, lf-tac-lean).
: lsl-tactic ( kind -- c-addr u ) lf-tac-lean ;
\ lsl-pos# and lsl-pos are one cell-counted buffer (lib/bounds.fs).
: lsl-pos+ ( c-addr u -- ) lsl lsl-pos# lsl-pos-room cell-counted+? drop ;
: lsl-source ( pos -- c-addr u )
  0 lsl lsl-pos# ! lfa-pos> swap u>decimal lsl-pos+ s" :" lsl-pos+ u>decimal lsl-pos+
  lsl lsl-pos# cell-count ;
\ An entry's number in its declaration, from 1; one before the first, 0.
: lsl-number-of ( entry -- k ) lsl lsl-first @ - 1+ 0 max ;
: lsl-afters ( entry -- )
  s" goals_after" lsl-key lsl-w jw-open-array
  dup tlg-after @ swap tlg-after# @ over + swap ?do i lf-steps-span lsl-span loop
  lsl-w jw-close-array ;
: lsl-goals ( entry -- )
  s" goal_before" lsl-key dup tlg-before 2@ lsl-span lsl-afters ;
: lsl-kind ( entry -- )
  tlg-kind @ dup lsl-tactic s" tactic" lsl-text lf-tac-word s" word" lsl-text ;
: lsl-step ( k -- outcome )
  lsl-begin dup lf-steps-entry dup lsl-goals
  dup tlg-parent @ lsl-number-of s" parent" lsl-number
  dup tlg-at @ lsl-source s" source" lsl-text
  swap lsl-number-of s" step" lsl-number lsl-kind lsl-end ;

\ ---- A declaration, then the log.
: lsl-steps ( decl -- outcome )
  dup tld-first @ dup lsl lsl-first ! swap lsl-steps# over + swap
  ?do i lsl-step dup ok? 0= if unloop exit then drop loop outcome-ok ;
: lsl-accepted ( decl -- d true | false ) lsl-name lsl lsl-find @ execute ;
: lsl-decl ( k -- outcome )
  lf-steps-decl dup lsl-accepted 0= if drop outcome-ok exit then
  over lsl-header ok-then? if lsl-steps then ;
: lf-steps-write ( sink find axioms -- outcome )
  lsl lsl-sink cell-triple!
  lf-steps-decls 0 ?do i lsl-decl dup ok? 0= if unloop exit then drop loop outcome-ok ;

base !   \ the BASE this file was loaded with
