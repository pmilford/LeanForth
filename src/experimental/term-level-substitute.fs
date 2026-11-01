\ Untrusted simultaneous universe substitution in symbolic terms. Load terms,
\ levels, level-scope, tagged-sort-boundary, symbolic-session, generation-handles
\ and level-substitute first. This is not declaration acceptance, type checking,
\ binder-scope checking, level equality, or proof validation. Constants and
\ concrete Sorts are unsupported. Global scratch makes this non-reentrant.
\ The caller owns aligned, accessible arrays disjoint from all arenas, contexts
\ and scratch, and prevents mutation during the call. Handles are forgeable and
\ do not encode arena kind; internal term/level edges rely on immutable arenas.
\ Each formal is one positive ID; each actual is an (index, identity) cell pair.
\ Source parameters must be in the formal list; actuals use the session's caller
\ context, independently of source scope. Replacements are not substituted again.
\ Failure restores both allocation counts, but never rewinds identity serials;
\ scratch and inactive slots may change. No result is issued on failure.

0 constant lf-tlsubst-ok
1 constant lf-tlsubst-invalid
2 constant lf-tlsubst-exhausted
variable lf-tls-root
variable lf-tls-formals
variable lf-tls-actual-handles
variable lf-tls-count
variable lf-tls-fuel
variable lf-tls-terms-before
variable lf-tls-levels-before
variable lf-tls-node
variable lf-tls-tag
variable lf-tls-a
variable lf-tls-b
create lf-tls-actuals lf-level-capacity cells allot
create lf-tls-seen lf-term-capacity cells allot
create lf-tls-results lf-term-capacity cells allot

: lf-tls-rollback ( status -- status )
  lf-tls-terms-before @ lf-term-count !
  lf-tls-levels-before @ lf-level-count ! ;

\ Record reachable nodes; repr validation has already checked backward edges.
: lf-tls-mark ( -- status )
  lf-tls-seen lf-term-capacity cells erase
  0 lf-href-pending !
  lf-tls-root @ lf-href-push 0= if lf-tlsubst-exhausted exit then
  begin lf-href-pending @ 0> while
    lf-tls-fuel @ 0= if lf-tlsubst-exhausted exit then
    -1 lf-tls-fuel +! -1 lf-href-pending +!
    lf-href-pending @ cells lf-href-work + @ lf-tls-node !
    true lf-tls-node @ cells lf-tls-seen + !
    lf-tls-node @ lf-term-read 0= if lf-tlsubst-invalid exit then
    lf-tls-b ! lf-tls-a ! lf-tls-tag !
    lf-tls-tag @ lf-tag-app = lf-tls-tag @ lf-tag-lam = or
    lf-tls-tag @ lf-tag-pi = or if
      lf-tls-a @ lf-href-push 0= if lf-tlsubst-exhausted exit then
      lf-tls-b @ lf-href-push 0= if lf-tlsubst-exhausted exit then
    then
  repeat lf-tlsubst-ok ;

\ Return substituted level or status; lsubst charges its own occurrence fuel.
: lf-tls-level ( root -- result 0 | status )
  lf-tls-formals @ lf-tls-actuals lf-tls-count @ lf-tls-fuel @ lf-lsubst
  lf-lsubst-fuel @ lf-tls-fuel ! ;

\ Build in topological order. Reuse unchanged nodes and their original stamps.
: lf-tls-build ( -- status )
  lf-tls-root @ 1+ 0 ?do
    i cells lf-tls-seen + @ if
      i lf-term-read 0= if lf-tlsubst-invalid unloop exit then
      lf-tls-b ! lf-tls-a ! lf-tls-tag !
      lf-tls-tag @ lf-tag-symbolic-sort = if
        lf-tls-a @ lf-tls-level ?dup if unloop exit then
        dup lf-tls-a @ = if drop i else
          dup lf-level-identity 0= if drop lf-tlsubst-invalid unloop exit then
          lf-hterm-sort 0= if lf-tlsubst-exhausted unloop exit then drop
        then
      else lf-tls-tag @ lf-tag-bvar = if i else
        lf-tls-a @ cells lf-tls-results + @
        lf-tls-b @ cells lf-tls-results + @
        2dup lf-tls-b @ = swap lf-tls-a @ = and if
          2drop i
        else
          lf-tls-tag @ lf-term-binary 0= if lf-tlsubst-exhausted unloop exit then
        then
      then then
      i cells lf-tls-results + !
    then
  loop lf-tlsubst-ok ;

\ ( term-index term-id formal-addr actual-handles-addr count fuel
\   -- result-index result-id lf-tlsubst-ok | status )
\ Fuel is shared by syntax, stamp, reachability and level occurrence walks;
\ repeated actual validation and DAG occurrences consume fuel independently.
\ Invalid syntax, identity, scope or input returns invalid; resource limits
\ return exhausted. Accessible array storage is the caller's responsibility.
: lf-tlsubst ( term-index term-id formal-addr actual-handles-addr count fuel
                -- result-index result-id 0 | status )
  dup 0< if 2drop 2drop 2drop lf-tlsubst-invalid exit then lf-tls-fuel !
  dup 0< over lf-level-capacity > or if
    2drop 2drop drop lf-tlsubst-invalid exit
  then
  lf-tls-count ! lf-tls-actual-handles ! lf-tls-formals !
  2dup lf-hterm-valid? 0= if 2drop lf-tlsubst-invalid exit then
  drop lf-tls-root !
  lf-term-serial @ 0< lf-level-serial @ 0< or if lf-tlsubst-invalid exit then
  lf-term-count @ lf-tls-terms-before ! lf-level-count @ lf-tls-levels-before !
  lf-tls-count @ 0 ?do
    i 2 * cells lf-tls-actual-handles @ + dup @ swap cell+ @
    2dup lf-hlevel-valid? 0= if 2drop lf-tlsubst-invalid unloop exit then
    drop i cells lf-tls-actuals + !
  loop
  \ Validate the formal list and every actual even if no Sort is reachable.
  0 lf-tls-level ?dup if lf-tls-rollback exit then drop
  lf-tls-root @ lf-repr-symbolic lf-tls-fuel @ lf-repr-check
  lf-repr-fuel @ lf-tls-fuel ! ?dup if lf-tls-rollback exit then
  lf-tls-root @ lf-tls-fuel @ lf-href-check
  lf-href-fuel @ lf-tls-fuel ! ?dup if lf-tls-rollback exit then
  lf-tls-mark ?dup if lf-tls-rollback exit then
  lf-tls-build ?dup if lf-tls-rollback exit then
  lf-tls-root @ cells lf-tls-results + @ dup lf-term-identity 0= if
    drop lf-tlsubst-invalid lf-tls-rollback exit
  then lf-tlsubst-ok ;
