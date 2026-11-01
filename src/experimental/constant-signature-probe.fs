\ Untrusted bridge from constant-reference syntax to candidate specialization.
\ Load constant-references.fs and raw-signature-specialize.fs and dependencies.
\ Single-threaded and non-reentrant. Owners must not mutate raw storage,
\ counts, identities, index, metadata, or scratch during a call; lifecycle
\ operations must follow the dependencies' contracts. Handles and tokens are
\ forgeable, session-local diagnostics, not capabilities. No type, declaration,
\ scope beyond dependency checks, theorem or proof validity is established.
\ The scratch array is private to this adapter and must not be mutated by callers.
create lf-csig-actuals lf-cref-argument-capacity 2 * cells allot
variable lf-csig-token
variable lf-csig-index
variable lf-csig-identity
variable lf-csig-fuel
variable lf-csig-name
variable lf-csig-count

\ ( token cref-index cref-identity fuel -- term identity lf-rspec-ok | status )
\ Requires a current index/metadata token and a live reference with live name
\ and ordered level identities. Exact arity is enforced by specialization.
\ Unknown candidate, invalid input and exhaustion use lf-rspec status codes.
\ Specialization may allocate; its rollback and fuel rules apply unchanged.
: lf-csig-probe ( token index identity fuel -- term identity 0 | status )
  lf-csig-fuel ! lf-csig-identity ! lf-csig-index ! lf-csig-token !
  lf-csig-token @ lf-rspec-current? 0= if lf-rspec-invalid exit then
  lf-csig-fuel @ 0< if lf-rspec-invalid exit then
  lf-csig-index @ lf-csig-identity @ lf-cref-read 0= if
    lf-rspec-invalid exit
  then
  lf-csig-count ! drop lf-csig-name !
  lf-csig-count @ 0 ?do
    lf-csig-index @ lf-csig-identity @ i lf-cref-level 0= if
      lf-rspec-invalid unloop exit
    then
    lf-csig-actuals i 2 * cells + dup >r cell+ ! r> !
  loop
  lf-csig-token @ lf-csig-name @ lf-csig-actuals lf-csig-count @
  lf-csig-fuel @ lf-rspec-specialize ;
