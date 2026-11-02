\ Untrusted constant-node candidate-type diagnostic. Load constant-term-boundary
\ and constant-signature-probe and their dependencies first. Single-threaded,
\ non-reentrant; exclude raw mutation, reloads and lifecycle changes during a
\ call. Handles and index tokens are forgeable session-local diagnostics.
\ No declaration, typing judgment, theorem or proof is established.
variable lf-cttype-token
variable lf-cttype-root
variable lf-cttype-id
variable lf-cttype-boundary-fuel
variable lf-cttype-signature-fuel

\ ( token root identity boundary-fuel signature-fuel -- term identity 0 | status )
\ The full handle and constant level scopes are checked before reading the
\ root's reference. Only a constant root is supported. Boundary fuel is shared
\ across its term and level visits; signature fuel is independently supplied
\ to each of lookup and substitution, per lf-rspec-specialize. Both must be
\ nonnegative. Boundary failure maps explicitly to lf-rspec statuses; unknown
\ means no candidate metadata. Specialization restores arena counts on failure,
\ but not identity serials or scratch. Success can allocate. Internal scratch
\ belongs to the dependencies and must not be accessed or aliased by callers.
: lf-cttype-probe ( token root identity boundary-fuel signature-fuel -- term identity 0 | status )
  lf-cttype-signature-fuel ! lf-cttype-boundary-fuel ! lf-cttype-id !
  lf-cttype-root ! lf-cttype-token !
  lf-cttype-signature-fuel @ 0< lf-cttype-boundary-fuel @ 0< or if
    lf-rspec-invalid exit
  then
  lf-cttype-root @ lf-cttype-id @ lf-cttype-boundary-fuel @ lf-cterm-check
  case
    lf-repr-ok of endof
    lf-repr-invalid of lf-rspec-invalid exit endof
    lf-repr-exhausted of lf-rspec-exhausted exit endof
    drop lf-rspec-invalid exit
  endcase
  lf-cttype-root @ lf-term-read 0= if lf-rspec-invalid exit then
  rot lf-tag-constant <> if 2drop lf-rspec-invalid exit then
  lf-cttype-token @ -rot lf-cttype-signature-fuel @ lf-csig-probe ;
