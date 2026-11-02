\ Experimental, untrusted mixed-term inference. Load mixed signature audit,
\ mixed shift, instantiate and convert and their dependencies first. Closed
\ source roots only. Signatures and nested dependencies are unchecked
\ assumptions; no theorem authority. One stable index/session, no raw writes,
\ resets, concurrent calls or reentrancy. Handles are local diagnostics.
\ Fuel is shared by preflight, traversal, specialization and transformations;
\ bounded metadata, identity scans and topological staging are additional work.
\ Only a directly visible Pi is applied; uncertain conversion is unknown.

0 constant lf-minfer-ok
1 constant lf-minfer-invalid
2 constant lf-minfer-exhausted
3 constant lf-minfer-unknown
6 constant lf-minfer-frame-cells
create lf-minfer-frames lf-term-capacity lf-minfer-frame-cells * cells allot
variable lf-minfer-depth
variable lf-minfer-fuel
variable lf-minfer-term-start
variable lf-minfer-level-start
variable lf-minfer-cref-start
variable lf-minfer-token
variable lf-minfer-context-depth
create lf-minfer-context lf-term-capacity cells allot

\ Access fields of the active bounded recursion frame.
: lf-minfer-frame ( depth -- addr )
  lf-minfer-frame-cells * cells lf-minfer-frames + ;
: lf-minfer-current ( -- addr ) lf-minfer-depth @ 1- lf-minfer-frame ;
: lf-minfer@ ( offset -- value ) cells lf-minfer-current + @ ;
: lf-minfer! ( value offset -- ) cells lf-minfer-current + ! ;
: lf-minfer-leave ( result status -- result status ) -1 lf-minfer-depth +! ;

\ Never let a changed or unrecognized helper status become successful inference.
: lf-minfer-repr-status ( status -- status )
  case lf-repr-ok of lf-minfer-ok endof
    lf-repr-invalid of lf-minfer-invalid endof
    lf-repr-exhausted of lf-minfer-exhausted endof
    drop lf-minfer-invalid 0 endcase ;
: lf-minfer-msp-status ( status -- status )
  case lf-msp-ok of lf-minfer-ok endof
    lf-msp-invalid of lf-minfer-invalid endof
    lf-msp-exhausted of lf-minfer-exhausted endof
    lf-msp-unknown of lf-minfer-unknown endof
    drop lf-minfer-invalid 0 endcase ;
: lf-minfer-shift-status ( status -- status )
  case lf-mshift-ok of lf-minfer-ok endof
    lf-mshift-invalid of lf-minfer-invalid endof
    lf-mshift-exhausted of lf-minfer-exhausted endof
    drop lf-minfer-invalid 0 endcase ;
: lf-minfer-inst-status ( status -- status )
  case lf-minst-ok of lf-minfer-ok endof
    lf-minst-invalid of lf-minfer-invalid endof
    lf-minst-exhausted of lf-minfer-exhausted endof
    drop lf-minfer-invalid 0 endcase ;
: lf-minfer-convert-status ( status -- status )
  case lf-mconvert-equal of lf-minfer-ok endof
    lf-mconvert-invalid of lf-minfer-invalid endof
    lf-mconvert-exhausted of lf-minfer-exhausted endof
    lf-mconvert-unknown of lf-minfer-unknown endof
    drop lf-minfer-invalid 0 endcase ;

\ Save a binder domain in the preceding context. Remove it after the body,
\ including when inference fails; the stack has a fixed finite capacity.
: lf-minfer-push ( domain -- flag )
  lf-minfer-context-depth @ lf-term-capacity >= if drop false exit then
  lf-minfer-context-depth @ cells lf-minfer-context + !
  1 lf-minfer-context-depth +! true ;
: lf-minfer-pop ( -- ) -1 lf-minfer-context-depth +! ;

\ Shift a binder's stored type into the current context. Validation, shifting
\ and the outer inference consume one shared remaining visit budget.
: lf-minfer-shift ( node amount -- result status )
  >r dup lf-term-identity 0= if r> drop drop -1 lf-minfer-invalid exit then
  0 r> lf-minfer-fuel @ lf-mixed-shift
  lf-mshift-fuel @ lf-minfer-fuel ! swap drop lf-minfer-shift-status ;

\ Compare two inferred/declared types using conservative beta conversion.
\ Both graphs are validated and compared with the remaining shared budget.
: lf-minfer-compare ( left right -- status )
  dup lf-term-identity 0= if 2drop lf-minfer-invalid exit then >r
  swap dup lf-term-identity 0= if 2drop r> drop lf-minfer-invalid exit then
  rot r> lf-minfer-fuel @ lf-mixed-convert
  lf-mconvert-fuel @ lf-minfer-fuel ! lf-minfer-convert-status ;

\ Substitute the original argument into a Pi body after conversion succeeds.
: lf-minfer-instantiate ( body argument -- result status )
  dup lf-term-identity 0= if 2drop -1 lf-minfer-invalid exit then >r
  swap dup lf-term-identity 0= if 2drop r> drop -1 lf-minfer-invalid exit then
  rot r> lf-minfer-fuel @ lf-mixed-instantiate
  lf-minst-fuel @ lf-minfer-fuel ! swap drop lf-minfer-inst-status ;

\ Make a stamped symbolic Sort from an allocated level. An allocator failure
\ is reported as exhaustion and cannot yield an inferred type.
: lf-minfer-sort ( level -- node status )
  dup lf-level-identity 0= if drop -1 lf-minfer-invalid exit then
  lf-hterm-sort if drop lf-minfer-ok else -1 lf-minfer-exhausted then ;

\ Extract the level from an inferred Sort. An unsupported inferred type is
\ unknown, not a successful judgment or proof of inequality.
: lf-minfer-sort-level ( node -- level status )
  lf-term-read 0= if -1 lf-minfer-invalid exit then
  drop swap lf-tag-symbolic-sort <> if drop -1 lf-minfer-unknown exit then
  lf-minfer-ok ;

\ Specialize a source constant using its audited reference's actual pairs.
\ Copy them out of the reference arena: specialization requires its input
\ array to be disjoint from all mutable arenas and scratch storage.
create lf-minfer-actuals lf-cref-argument-capacity 2 * cells allot
variable lf-minfer-name
variable lf-minfer-actual-count
variable lf-minfer-actual-address
: lf-minfer-constant ( reference -- type status )
  lf-cref-slot dup cell+ @ swap dup 4 cells + swap 3 cells + @
  lf-minfer-actual-count ! lf-minfer-actual-address ! lf-minfer-name !
  lf-minfer-actual-address @ lf-minfer-actuals
  lf-minfer-actual-count @ 2 * cells move
  lf-minfer-token @ lf-minfer-name @ lf-minfer-actuals
  lf-minfer-actual-count @ lf-minfer-fuel @ lf-msp-specialize
  lf-minfer-msp-status ?dup if 0 lf-minfer-fuel ! -1 swap exit then
  lf-mls-fuel @ lf-minfer-fuel ! drop lf-minfer-ok ;

\ Infer an input node, charging one fuel unit per visit. Nodes generated by
\ this operation are output data, never interpreted as fresh source nodes.
: lf-minfer-walk ( node -- type status )
  lf-minfer-fuel @ 0= lf-minfer-depth @ lf-term-capacity >= or if
    drop -1 lf-minfer-exhausted exit
  then
  -1 lf-minfer-fuel +!
  lf-minfer-depth @ lf-minfer-frame ! 1 lf-minfer-depth +!
  0 lf-minfer@ dup 0< swap lf-minfer-term-start @ >= or if
    -1 lf-minfer-invalid lf-minfer-leave exit
  then
  0 lf-minfer@ lf-term-read 0= if -1 lf-minfer-invalid lf-minfer-leave exit then
  3 lf-minfer! 2 lf-minfer! 1 lf-minfer!
  1 lf-minfer@ lf-tag-symbolic-sort = if
    2 lf-minfer@ lf-level-succ 0= if
      -1 lf-minfer-exhausted lf-minfer-leave exit
    then
    lf-minfer-sort lf-minfer-leave exit
  then
  1 lf-minfer@ lf-tag-constant = if
    2 lf-minfer@ lf-minfer-constant lf-minfer-leave exit
  then
  1 lf-minfer@ lf-tag-bvar = if
    2 lf-minfer@ lf-minfer-context-depth @ >= if
      -1 lf-minfer-invalid lf-minfer-leave exit
    then
    lf-minfer-context-depth @ 1- 2 lf-minfer@ - cells lf-minfer-context + @
    2 lf-minfer@ 1+ lf-minfer-shift lf-minfer-leave exit
  then
  1 lf-minfer@ lf-tag-app = if
    2 lf-minfer@ recurse dup if lf-minfer-leave exit then drop
    lf-term-read 0= if -1 lf-minfer-invalid lf-minfer-leave exit then
    5 lf-minfer! 4 lf-minfer!
    lf-tag-pi <> if -1 lf-minfer-unknown lf-minfer-leave exit then
    3 lf-minfer@ recurse dup if lf-minfer-leave exit then drop
    4 lf-minfer@ lf-minfer-compare
    ?dup if -1 swap lf-minfer-leave exit then
    5 lf-minfer@ 3 lf-minfer@ lf-minfer-instantiate lf-minfer-leave exit
  then
  1 lf-minfer@ lf-tag-pi = 1 lf-minfer@ lf-tag-lam = or if
    2 lf-minfer@ recurse dup if lf-minfer-leave exit then drop
    lf-minfer-sort-level dup if lf-minfer-leave exit then drop 4 lf-minfer!
    2 lf-minfer@ lf-minfer-push 0= if
      -1 lf-minfer-exhausted lf-minfer-leave exit
    then
    3 lf-minfer@ recurse lf-minfer-pop
    dup if lf-minfer-leave exit then drop
    1 lf-minfer@ lf-tag-lam = if
      2 lf-minfer@ swap lf-term-pi if
        lf-minfer-ok else -1 lf-minfer-exhausted then
      lf-minfer-leave exit
    then
    lf-minfer-sort-level dup if lf-minfer-leave exit then drop
    dup 0= if drop 0 else
      4 lf-minfer@ swap lf-level-imax 0= if
        -1 lf-minfer-exhausted lf-minfer-leave exit
      then
    then
    lf-minfer-sort lf-minfer-leave exit
  then
  -1 lf-minfer-unknown lf-minfer-leave ;

\ ( token root identity fuel -- type identity status ) Full source and global
\ index preflight precede allocation. All failures restore three arena counts;
\ serials never rewind. Input traversal is limited to original source nodes.
\ Every failure reports zero remaining fuel conservatively.
: lf-mixed-infer ( token root identity fuel -- type identity status )
  dup 0< if 2drop 2drop 0 lf-minfer-fuel ! -1 0 lf-minfer-invalid exit then
  lf-minfer-fuel ! >r >r lf-minfer-token ! r> r>
  2dup 0 lf-minfer-fuel @ lf-constant-term-scope lf-minfer-repr-status ?dup if
    >r 2drop 0 lf-minfer-fuel ! -1 0 r> exit then
  lf-cts-fuel @ lf-minfer-fuel !
  lf-minfer-token @ lf-minfer-fuel @ lf-mixed-signature-audit lf-minfer-msp-status ?dup if
    >r 2drop 0 lf-minfer-fuel ! -1 0 r> exit then
  lf-msa-fuel @ lf-minfer-fuel ! drop
  lf-term-count @ lf-minfer-term-start !
  lf-level-count @ lf-minfer-level-start !
  lf-cref-count @ lf-minfer-cref-start !
  0 lf-minfer-depth ! 0 lf-minfer-context-depth ! lf-minfer-walk
  dup if
    >r drop lf-minfer-term-start @ lf-term-count !
    lf-minfer-level-start @ lf-level-count !
    lf-minfer-cref-start @ lf-cref-count ! 0 lf-minfer-fuel ! -1 0 r> exit
  then
  drop dup lf-term-identity 0= if
    drop lf-minfer-term-start @ lf-term-count !
    lf-minfer-level-start @ lf-level-count !
    lf-minfer-cref-start @ lf-cref-count ! 0 lf-minfer-fuel ! -1 0 lf-minfer-invalid exit
  then lf-minfer-ok ;
