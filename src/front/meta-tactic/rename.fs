\ renameInaccessibles of the tactic library (docs/design/TACTIC_PLUGINS.md
\ 2.4; plan 9.4.8l-I, commit C4): Lean 4.35.0's Elab/Tactic/
\ RenameInaccessibles.lean (:11, public; used by case, next and rename_i).
\   lf-goal-rename-inaccessibles ( goal names -- goal' )  names a run
\       (lib/runs.fs, Lean's array of binder identifiers: a name, or 0 for
\       _): none, or all _, gives goal itself; else, from the newest, each
\       local of goal's context that is no implementation detail and is
\       inaccessible (Lean: macro scopes other than the user's) or
\       shadowed (a newer local the user can name has its name) takes the
\       last name not taken yet (_ takes its turn and renames none), until
\       the names run out; names left are error 211 at the step running
\       (Lean's "too many variable names provided": Lean logs it and goes
\       on, this stops at it, Lean's first message). goal' is a new
\       synthetic opaque goal of goal's type and tag in the renamed
\       context, goal assigned it (mkFreshExprMVarAt).
\ Errors are thrown as authoring errors at the step running
\ (tactic-run.fs's lf-tac-stop), Meta failures as outcomes (meta-must.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: mrn-frames (a frame per call open, meta-must.fs's lf-with-record,
\ in the checker context, ADR 0009); no other. Loads in decimal whatever
\ BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/slab.fs
require ../../lib/runs.fs
require ../../lib/context.fs
require ../../lib/find.fs
require ../../core/name-equal.fs
require ../../author/errors.fs
require ../mvars.fs
require ../lctx-views.fs
require ../goals.fs
require ../tactic-run.fs
require ../meta-must.fs

begin-structure /mrn
  field: mrn-goal        \ the goal
  field: mrn-names       \ the names, a run
  field: mrn-view        \ its context, renamed so far
  field: mrn-left        \ the names not taken yet
end-structure
/mrn context-slab: mrn-frames
: mrn ( -- frame ) mrn-frames slab-last ;

\ ---- Whether a name is given (Lean's callerScopes: some identifier).
: mrn-ident? ( names k -- names flag ) over swap run@ 0<> ;
: mrn-any? ( names -- flag ) dup run-count ['] mrn-ident? any? nip ;

\ ---- The locals, from the newest: shadowed when a newer local the user
\ can name has local j's name.
: mrn-local ( j -- local ) mrn mrn-goal @ lf-goal-view swap lf-view-local ;
: mrn-count ( -- n ) mrn mrn-goal @ lf-goal-view lf-view-count ;
: mrn-user? ( local -- flag ) dup lf-local-detail? swap lf-local-inaccessible? or 0= ;
: mrn-name-at ( j -- name ) mrn-local lf-local-name ;
: mrn-named-as? ( j local -- j flag ) lf-local-name over mrn-name-at lf-name-same? ;
: mrn-newer ( j k -- j flag )   \ local k, newer than j, the user can name
  mrn-local dup mrn-user? if mrn-named-as? else drop false then ;
: mrn-same? ( j k -- j flag ) 2dup < if mrn-newer else drop false then ;
: mrn-shadowed? ( j -- flag ) mrn-count ['] mrn-same? find-index dup if nip then ;
: mrn-renames? ( j -- flag ) dup mrn-shadowed? swap mrn-local lf-local-inaccessible? or ;

\ ---- A local's turn: the last name left, _ renaming none.
: mrn-view! ( view outcome -- ) lf-must mrn mrn-view ! ;
: mrn-renamed ( j name -- )
  swap mrn-local lf-local-fvar swap mrn mrn-view @ -rot lf-view-rename mrn-view! ;
: mrn-last ( -- name ) -1 mrn mrn-left +! mrn mrn-names @ mrn mrn-left @ run@ ;
: mrn-take ( j -- ) mrn-last ?dup if mrn-renamed else drop then ;
: mrn-turn? ( j -- flag )   \ not a detail, and inaccessible or shadowed
  dup mrn-local lf-local-detail? if drop false else mrn-renames? then ;
: mrn-visit ( j -- ) dup mrn-turn? 0= if drop exit then mrn-take ;
: mrn-more? ( j -- j flag ) dup 0> mrn mrn-left @ 0> and ;
: mrn-scan ( -- ) mrn-count begin mrn-more? while 1- dup mrn-visit repeat drop ;

\ ---- The goal again in the renamed context, the old one assigned it.
: mrn-like ( goal -- goal' )   \ of goal's type and tag, in the renamed context
  dup lf-goal-type swap lf-goal-tag mrn mrn-view @ lf-goal-new lf-must ;
: mrn-fresh ( -- goal' ) mrn mrn-goal @ dup mrn-like tuck lf-mvar-assign lf-must ;
: mrn-left? ( -- ) mrn mrn-left @ if lfa-e-tac-case-names lf-tac-stop then ;
: mrn-run ( goal -- goal' )
  lf-goal-view mrn mrn-view ! mrn mrn-names @ run-count mrn mrn-left !
  mrn-scan mrn-left? mrn-fresh ;
: mrn-framed ( goal names -- goal' ) mrn mrn-names ! dup mrn mrn-goal ! mrn-run ;
: lf-goal-rename-inaccessibles ( goal names -- goal' )
  dup mrn-any? 0= if drop exit then mrn-frames ['] mrn-framed lf-with-record ;
base !   \ the BASE this file was loaded with
