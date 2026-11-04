\ A symbolic term/level session: binds an empty term store to the current
\ level store and parameter context by recording their generations, so any
\ later reset of one of them makes the session stale. Untrusted; not a type
\ checker and cannot authorize a theorem.
\ State: the current session is one /lf-session record, lf-ssession, and
\ the check uses one walk record, lf-ssession-walker; both are members of
\ the checker context (lib/context.fs). Single-threaded within one context.
\ Bare term or level indices reused after a new session are
\ indistinguishable from stale ones; handles (generation-handles.fs) detect
\ that.

require ../lib/lib.fs
require ./diagnostics.fs
require ./level-scope.fs
require ./levels.fs
require ./tagged-sort-boundary.fs
require ./terms.fs

begin-structure /lf-session
  field: lf-session-active
  field: lf-session-terms      \ captured term-store generation
  field: lf-session-levels     \ captured level-store generation
  field: lf-session-context    \ captured parameter-context generation
end-structure
/lf-session context-record: lf-ssession
lf-walk-room context-walk: lf-ssession-walker

: lf-ssession-active ( -- addr ) lf-ssession lf-session-active ;
\ Fuel left after a check; generation-handles continues with it.
: lf-ssession-fuel ( -- addr ) lf-ssession-walker walk-fuel ;

\ The stores a session depends on are all in a valid state.
: lf-ssession-stores-valid? ( -- flag )
  lf-term-count-valid? lf-level-count-valid? and lf-lscope-context-valid? and ;
: lf-ssession-capture ( session -- )
  lf-term-generation @ over lf-session-terms !
  lf-level-generation @ over lf-session-levels !
  lf-lscope-generation @ swap lf-session-context ! ;
: lf-ssession-same? ( session -- flag )
  dup lf-session-terms @ lf-term-generation @ =
  over lf-session-levels @ lf-level-generation @ = and
  swap lf-session-context @ lf-lscope-generation @ = and ;

\ Begin a session on an empty term store. Failure ends any previous session;
\ no store is modified.
: lf-ssession-begin ( -- flag )
  false lf-ssession-active !
  lf-ssession-stores-valid? lf-term-count @ 0= and 0= if false exit then
  lf-ssession lf-ssession-capture true dup lf-ssession-active ! ;

\ The session is active and no store was reset since it began.
: lf-ssession-current? ( -- flag )
  lf-ssession-active @ 0= if false exit then
  lf-ssession-stores-valid? lf-ssession lf-ssession-same? and ;

\ Visiting a node already checked for shape and representation: each
\ symbolic Sort's level is scope-checked with the same budget.
: lf-ssession-sort ( first second walk -- outcome ) nip lf-lscope-walk-check ;
: lf-ssession-dispatch ( first second walk tag -- outcome )
  dup lf-term-binary-tag? if drop walk-push2 exit then
  case lf-tag-symbolic-sort of lf-ssession-sort endof
    lf-tag-bvar of drop 2drop outcome-ok endof walk-bad-tag endcase ;
: lf-ssession-visit ( walk -- outcome ) lf-terms ['] lf-ssession-dispatch walk-visit ;

\ Check one root: representation and shape first, then the level of every
\ reachable Sort. Both passes and every level visit share one budget, and
\ repeated DAG visits are charged repeatedly. Unreachable nodes are ignored.
\ Establishes no binder scope, typing, equality or proof validity.
: lf-ssession-repr ( root -- root outcome )
  dup lf-repr-symbolic lf-ssession-fuel @ lf-repr-check lf-repr-fuel @ lf-ssession-fuel ! ;
: lf-ssession-site ( -- site ) c" symbolic-session lf-ssession-check" ;
: lf-ssession-levels ( root -- outcome )
  ['] lf-ssession-visit lf-ssession-walker walk-run
  lf-ssession-walker lf-ssession-site lf-diag-walk ;
: lf-ssession-ready? ( fuel -- flag ) lf-ssession-walker walk-budget lf-ssession-current? and ;
: lf-ssession-check ( root fuel -- status )
  lf-ssession-ready? if lf-ssession-repr ok-then? if lf-ssession-levels then else drop-invalid then ;
