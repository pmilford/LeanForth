\ by-case: TAG NAMES... => (plan S2, FE1g-5; docs/design/S2_INTERFACE.md
\ 4): the row of its kind in the runner (tactic-run.fs), a port of Lean
\ 4.35.0's case tactic, Elab/Tactic/BuiltinTactic.lean's evalCase (596),
\ getCaseGoals (543) with findTag? (535) and its notFound message, and
\ Elab/Tactic/RenameInaccessibles.lean's renameInaccessibles (11):
\ - The goal: among the unsolved goals, in order, the first whose tag with
\   its macro scopes erased is TAG; else the first of which TAG is a suffix
\   (Name.isSuffixOf: zero finds succ.zero); else a prefix (isPrefixOf:
\   succ finds succ.zero). None is error 210, Lean's "Case tag `TAG` not
\   found." and, after a blank line, its note or hint from the unsolved
\   goals' tags that are not anonymous: "Note: There are no cases to
\   select.", "Hint: The only available case tag is `t`." or "Hint:
\   Available tags:". Lean then previews each tag as an edit of TAG (an
\   editor's character diff, Meta/Hint.lean's readableDiff over
\   Util/Diff.lean's histogram LCS, whose ties follow a hash map's order):
\   not printed (plan 8.6).
\ - Its hypotheses renamed, when a name is given that is not _: from the
\   newest, each local that is no implementation detail and is
\   inaccessible (Lean: macro scopes other than the user's) or shadowed (a
\   newer such local has its name) takes the last name not taken yet (_
\   takes its turn and renames none), until the names run out; names left
\   are error 211 at by-case:, Lean's "too many variable names provided"
\   (Lean logs it and goes on; this stops at it, Lean's first message).
\   The goal is then a new synthetic opaque goal of its type and tag in
\   the renamed context, the old one assigned it (mkFreshExprMVarAt).
\ - The goal's tag made anonymous (setTag), the goal list that goal alone,
\   and the block runs; at its end no goal may be left (error 89 at its =>,
\   Lean's closeUsingOrAdmit under withCaseRef) and the other unsolved
\   goals, in order, are the list (setGoals gs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: the step's own fields in its step record (tactic-run.fs, review
\ fe1g3 M2); no other. Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/runs.fs
require ../lib/find.fs
require ../core/names.fs
require ../core/name-equal.fs
require ../present/print-names.fs
require ../present/print-job.fs
require ../author/errors.fs
require ./mvars.fs
require ./lctx-views.fs
require ./goals.fs
require ./tactic-syntax.fs
require ./tactic-run.fs
require ./tactic-msg.fs
require ./tactic-core.fs
require ./meta-must.fs
require ./meta-tactic/goal.fs

begin-structure /tcs      \ the step's fields
  field: tcs-step         \ the by-case: step
  field: tcs-goals        \ the unsolved goals (Lean's gs)
  field: tcs-goal         \ the goal found, then renamed
  field: tcs-view         \ its context, renamed so far
  field: tcs-left         \ the names not taken yet
end-structure
/tcs lf-tac-work-cells cells >
[if] .( tactic-case.fs: its fields are wider than a step record) cr abort [then]
: tc ( -- addr ) lf-tac-record ;

\ ---- findTag?: the first goal whose tag passes xt ( TAG tag -- flag ).
: tcs-tag ( -- name ) tc tcs-step @ lf-tactic-step tac-name @ ;
: tcs-goal-at ( k -- goal ) tc tcs-goals @ swap run@ ;
: tcs-tag-at ( k -- name ) tcs-goal-at lf-goal-tag ;
: tcs-hit? ( xt k -- xt flag ) tcs-tag swap tcs-tag-at lf-pp-unhygienic 2 pick execute ;
: tcs-first ( xt -- k true | false ) tc tcs-goals @ run-count ['] tcs-hit? find-index ;
: tcs-exact-or-suffix ( -- k true | false )
  ['] lf-name-same? tcs-first ?dup if exit then ['] lf-name-suffix-of? tcs-first ;
: tcs-find ( -- k true | false )
  tcs-exact-or-suffix ?dup if exit then ['] lf-name-prefix-of? tcs-first ;

\ ---- notFound: the message and its note or hint.
: tcs-named? ( x k -- x flag ) tcs-tag-at 0<> ;
: tcs-goals# ( -- n ) tc tcs-goals @ run-count ;
: tcs-named# ( -- n ) 0 tcs-goals# 0 ?do 0 i tcs-named? nip - loop ;
: tcs-only ( -- name ) 0 tcs-goals# ['] tcs-named? find-index drop tcs-tag-at ;
: tcs-only. ( -- ) tcs-only lf-tac-.name s" ." lf-pp-emit ;
: tcs-one. ( -- ) s\" \n\nHint: The only available case tag is " lf-pp-emit tcs-only. ;
: tcs-none. ( -- ) s\" \n\nNote: There are no cases to select." lf-pp-emit ;
: tcs-many. ( -- ) s\" \n\nHint: Available tags:" lf-pp-emit ;
: tcs-hint. ( n -- ) ?dup 0= if tcs-none. exit then 1 = if tcs-one. else tcs-many. then ;
: tcs-not-found. ( -- ) s"  " lf-pp-emit tcs-tag lf-tac-.name s"  not found." lf-pp-emit ;
: tcs-missing. ( x -- outcome ) drop tcs-not-found. tcs-named# tcs-hint. outcome-ok ;
: tcs-not-found ( -- ) 0 ['] tcs-missing. lf-tac-inline lfa-e-tac-case-tag lf-tac-stop ;

\ ---- renameInaccessibles. The names: the step's arguments (0 for _).
: tcs-names ( -- n ) tc tcs-step @ lf-tac-args# ;
: tcs-arg ( k -- name ) tc tcs-step @ swap lf-tac-arg ;
: tcs-ident? ( x k -- x flag ) tcs-arg 0<> ;
: tcs-any? ( -- flag ) 0 tcs-names ['] tcs-ident? find-index dup if nip then ;
: tcs-local ( j -- local ) tc tcs-goal @ lf-goal-view swap lf-view-local ;
: tcs-count ( -- n ) tc tcs-goal @ lf-goal-view lf-view-count ;
: tcs-user? ( local -- flag ) dup lf-local-detail? swap lf-local-inaccessible? or 0= ;
\ Shadowed: a newer local the user can name has local j's name.
: tcs-name-at ( j -- name ) tcs-local lf-local-name ;
: tcs-named-as? ( j local -- j flag ) lf-local-name over tcs-name-at lf-name-same? ;
: tcs-newer ( j k -- j flag )   \ local k, newer than j, the user can name
  tcs-local dup tcs-user? if tcs-named-as? else drop false then ;
: tcs-same? ( j k -- j flag ) 2dup < if tcs-newer else drop false then ;
: tcs-shadowed? ( j -- flag ) tcs-count ['] tcs-same? find-index dup if nip then ;
: tcs-renames? ( j -- flag ) dup tcs-shadowed? swap tcs-local lf-local-inaccessible? or ;
: tcs-view! ( view outcome -- ) lf-tac-must tc tcs-view ! ;
: tcs-renamed ( j name -- )
  swap tcs-local lf-local-fvar swap tc tcs-view @ -rot lf-view-rename tcs-view! ;
: tcs-take ( j -- )
  -1 tc tcs-left +! tc tcs-left @ tcs-arg ?dup if tcs-renamed else drop then ;
: tcs-turn? ( j -- flag )   \ not a detail, and inaccessible or shadowed
  dup tcs-local lf-local-detail? if drop false else tcs-renames? then ;
: tcs-visit ( j -- ) dup tcs-turn? 0= if drop exit then tcs-take ;
: tcs-more? ( j -- j flag ) dup 0> tc tcs-left @ 0> and ;
: tcs-scan ( -- ) tcs-count begin tcs-more? while 1- dup tcs-visit repeat drop ;
: tcs-like ( goal -- goal' )   \ of goal's type and tag, in the renamed context
  dup lf-goal-type swap lf-goal-tag tc tcs-view @ lf-goal-new lf-tac-must ;
: tcs-fresh ( -- )
  tc tcs-goal @ dup tcs-like tuck lf-mvar-assign lf-tac-must tc tcs-goal ! ;
: tcs-start ( -- ) tcs-names tc tcs-left ! tc tcs-goal @ lf-goal-view tc tcs-view ! ;
: tcs-left? ( -- ) tc tcs-left @ if lfa-e-tac-case-names lf-tac-stop then ;
: tcs-renaming ( -- ) tcs-start tcs-scan tcs-left? tcs-fresh ;
: tcs-rename ( -- ) tcs-any? if tcs-renaming then ;

\ ---- evalCase: the goal found and renamed, alone in the list, its tag
\ anonymous; the other unsolved goals (gs.erase g) for the block's end.
: tcs-before ( k -- run ) tc tcs-goals @ swap run-take lf-tac-must ;
: tcs-after ( k -- run ) tc tcs-goals @ swap 1+ run-after lf-tac-must ;
: tcs-rest ( k -- rest ) dup tcs-before swap tcs-after run-cat lf-tac-must ;
: tcs-alone ( -- ) tc tcs-goal @ dup 0 lf-mvar-tag! lf-tac-must lf-tac-only ;
: tcs-found ( -- k ) tcs-find 0= if tcs-not-found then ;
: tcs-gs ( i -- ) tc tcs-step ! lf-goals-unsolved lf-tac-must tc tcs-goals ! ;
: tcs-case ( i -- rest ) tcs-gs
  tcs-found dup tcs-goal-at tc tcs-goal ! tcs-rest tcs-rename tcs-alone ;
: tcs-w-case ( i -- ) dup ['] tcs-case lf-tac-in-record lf-tac-block ;

' tcs-w-case tac-k-case lf-tactic-action!
base !   \ the BASE this file was loaded with
