\ Structural equality of Lean names (ADR 0005): two names are equal when
\ they have the same components in the same order, each a byte string with
\ the same bytes or a number with the same value. The name store interns
\ names, so equal names normally have one ID, but correctness never relies
\ on that (ADR 0012, E5): this compares component by component. Untrusted.
\ No state of its own; reads the name store, which callers must not change
\ during a call.

require ../lib/lib.fs
require ./names.fs

\ Unchecked: one component of two valid entries, without their prefixes
\ (lf-name-payload and lf-name-text are names.fs's).
: lf-name-num= ( a b -- flag ) lf-name-payload swap lf-name-payload = ;
: lf-name-str= ( a b -- flag ) lf-name-text rot lf-name-text compare 0= ;
: lf-name-tags= ( a b -- flag ) lf-name-tag@ swap lf-name-tag@ = ;
: lf-name-part= ( a b -- flag )
  2dup lf-name-tags= 0= if 2drop false exit then
  over lf-name-str? if lf-name-str= else lf-name-num= then ;
: lf-name-prefixes ( a b -- a' b' ) lf-name-prefix@ swap lf-name-prefix@ swap ;

\ Unchecked: a and b are valid IDs of a store that passed
\ lf-name-storage-valid?, whose prefixes point backwards, so the loop ends.
: lf-name-same? ( a b -- flag )
  begin 2dup <> while
    2dup lf-name-part= 0= if 2drop false exit then lf-name-prefixes
  repeat 2drop true ;

\ Checked: false unless both IDs are valid and the whole store passes its
\ audit, which reads every entry.
: lf-name-ids? ( a b -- flag )
  lf-name-valid? swap lf-name-valid? and lf-name-storage-valid? and ;
: lf-name-equal? ( a b -- flag )
  2dup lf-name-ids? if lf-name-same? else 2drop false then ;
