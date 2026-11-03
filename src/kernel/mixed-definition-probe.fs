\ UNTRUSTED mixed type/value diagnostic; load mixed-infer.fs and dependencies.
\ Signatures, including nested dependencies, are unchecked assumptions. This
\ registers nothing, proves no theorem, and returns no term or certificate.
\ One stable session/index, suffix-only rollback and no raw mutation are
\ assumed. Unsupported inference/conversion is unknown.
\ It checks a definition, or a theorem, in Lean's order (ADR 0011, fact 1):
\ the claim's type is a Sort (S1 rejects a rigid non-Sort: typeExpected);
\ for a theorem that Sort is a proposition (S3: thmTypeIsNotProp); the
\ value's type converts to the claim (D1-D5 reject: declTypeMismatch).
\ Inference rejects by F1, S2 and D1-D5 inside the terms. Rejection is
\ [kernel] code, not yet through the review gate.
\ State: one request record, lf-mdefinition-request: the claim, the value,
\ whether it is a theorem, the index token, the fuel and the arena marks of
\ the current call; a member of the checker context (lib/context.fs). The
\ inference itself runs on mixed-infer's state, as a job this module starts
\ with lf-minfer-start. Single-threaded within one context.

require ../lib/lib.fs
require ../core/constant-references.fs
require ../core/constant-term-scope.fs
require ../core/levels.fs
require ../core/terms.fs
require ./mixed-infer.fs
require ./mixed-signature-audit.fs

begin-structure /lf-mdreq
  field: lf-mdreq-token     \ signature index token
  field: lf-mdreq-claim-root  \ claimed type: root and identity
  field: lf-mdreq-claim-id
  field: lf-mdreq-value-root  \ value: root and identity
  field: lf-mdreq-value-id
  field: lf-mdreq-fuel        \ fuel left; the result once a call returns
  field: lf-mdreq-theorem     \ true for a theorem: its type must be a proposition
  field: lf-mdreq-terms       \ arena counts when the call began
  field: lf-mdreq-levels
  field: lf-mdreq-crefs
end-structure
/lf-mdreq context-record: lf-mdefinition-request

\ Fuel left by the last probe: what inference left on success, zero after
\ any failure.
: lf-mdefinition-fuel ( -- addr ) lf-mdefinition-request lf-mdreq-fuel ;

: lf-mdreq-claim! ( type tid req -- ) tuck lf-mdreq-claim-id ! lf-mdreq-claim-root ! ;
: lf-mdreq-value! ( value vid req -- ) tuck lf-mdreq-value-id ! lf-mdreq-value-root ! ;
: lf-mdreq-claim@ ( req -- type tid ) dup lf-mdreq-claim-root @ swap lf-mdreq-claim-id @ ;
: lf-mdreq-value@ ( req -- value id ) dup lf-mdreq-value-root @ swap lf-mdreq-value-id @ ;

\ Arena counts when the check begins; inference restores them.
: lf-mdreq-mark ( req -- )
  lf-term-count @ over lf-mdreq-terms ! lf-level-count @ over lf-mdreq-levels !
  lf-cref-count @ swap lf-mdreq-crefs ! ;
: lf-mdreq-rewind ( req -- )
  dup lf-mdreq-terms @ lf-term-count ! dup lf-mdreq-levels @ lf-level-count !
  lf-mdreq-crefs @ lf-cref-count ! ;

\ Both closed source graphs and the entire index must be audited before any
\ allocation: otherwise a stale second root or index handle could revive.
\ Each check spends the request's fuel. lf-constant-term-scope and
\ lf-mixed-signature-audit report only ok, invalid, exhausted or full.
: lf-mdefinition-scope ( root id req -- status )
  dup >r lf-mdreq-fuel @ 0 swap lf-constant-term-scope lf-cts-fuel @ r> lf-mdreq-fuel !
  outcome-sane ;
: lf-mdefinition-audit ( req -- status )
  dup >r lf-mdreq-token @ r@ lf-mdreq-fuel @ lf-mixed-signature-audit lf-msa-fuel @
  r> lf-mdreq-fuel ! outcome-sane ;
: lf-mdefinition-claim-scope ( req -- status )
  dup lf-mdreq-claim@ rot lf-mdefinition-scope ;
: lf-mdefinition-value-scope ( req -- status )
  dup lf-mdreq-value@ rot lf-mdefinition-scope ;
: lf-mdefinition-preflight ( req -- status )
  dup lf-mdefinition-claim-scope ok-then?
  if dup lf-mdefinition-value-scope ok-then? if lf-mdefinition-audit then then ;

\ Internal inference consumes the original preflighted roots only. One
\ mixed-infer job, started once with the fuel the preflight left, covers
\ the pair; the preflight allocated nothing, so the job's arena marks are
\ the request's.
: lf-mdefinition-start ( req -- )
  dup lf-mdreq-token @ swap lf-mdreq-fuel @ lf-minfer-start ;
\ The claim's own type must be a Sort (S1); for a theorem its level must be
\ zero under every assignment (S3, Lean's is_prop); the value's inferred
\ type must then convert to the claim (D1-D5). Inference reports ok,
\ invalid, exhausted, full, unknown or rejected.
: lf-mdefinition-site ( -- site ) c" mixed-definition-probe lf-mixed-definition-probe" ;
: lf-mdefinition-claim-level ( type -- level status )
  lf-minfer-walk ok-then? 0= if no-result exit then
  lf-mdefinition-site lf-diag-type-expected lf-minfer-sort-rule ;
: lf-mdefinition-not-prop ( level -- status )
  lf-mdefinition-site lf-diag-not-proposition lf-minfer-reject ;
: lf-mdefinition-prop ( level -- status )
  dup lf-minfer-zero? ok-then? if if drop outcome-ok else lf-mdefinition-not-prop then
  else nip then ;
: lf-mdefinition-claim-sort ( req type -- status )
  lf-mdefinition-claim-level ok-then? 0= if nip exit then
  swap lf-mdreq-theorem @ if lf-mdefinition-prop else drop outcome-ok then ;
: lf-mdefinition-value-type ( value type -- status )
  swap lf-minfer-walk ok-then? 0= if nip exit then
  swap lf-minfer-agree lf-mdefinition-site lf-diag-value-apart lf-minfer-verdict ;
: lf-mdefinition-claim ( req -- status )
  dup lf-mdreq-claim-root @ lf-mdefinition-claim-sort ;
: lf-mdefinition-pair ( req -- status )
  dup lf-mdefinition-claim ok-then?
  if dup lf-mdreq-value-root @ swap lf-mdreq-claim-root @ lf-mdefinition-value-type then ;
: lf-mdefinition-walk ( req -- status )
  dup lf-mdefinition-start lf-mdefinition-pair outcome-sane ;

\ Infer, keep the fuel inference left, and restore the arena counts.
: lf-mdefinition-infer ( req -- status )
  dup lf-mdefinition-walk lf-minfer-fuel @ rot tuck lf-mdreq-fuel ! lf-mdreq-rewind ;
: lf-mdefinition-check ( req -- status )
  dup lf-mdreq-mark dup lf-mdefinition-preflight ok-then? if lf-mdefinition-infer then ;
: lf-mdefinition-ready? ( req -- flag )
  lf-mdreq-fuel @ 0< 0= lf-term-count-valid? and lf-level-count-valid? and
  lf-cref-state-valid? and ;
: lf-mdefinition-run ( req -- status )
  dup lf-mdefinition-ready? if dup lf-mdefinition-check else outcome-invalid then
  dup ok? if nip else 0 rot lf-mdreq-fuel ! then ;

\ One shared visit fuel; all failures conservatively report zero in
\ lf-mdefinition-fuel. Success reports the remaining fuel. Every result
\ leaves all three arena counts as they were; allocation serials never
\ rewind. No generated handles escape this word. The definition probe
\ allows a claim in any Sort; the theorem probe also requires the claim to
\ be a proposition (rule S3).
: lf-mdefinition-probe ( token type tid value vid fuel theorem -- status )
  lf-mdefinition-request >r r@ lf-mdreq-theorem ! r@ lf-mdreq-fuel ! r@ lf-mdreq-value!
  r@ lf-mdreq-claim! r@ lf-mdreq-token ! r> lf-mdefinition-run ;
: lf-mixed-definition-probe ( token type tid value vid fuel -- status )
  false lf-mdefinition-probe ;
: lf-mixed-theorem-probe ( token type tid value vid fuel -- status )
  true lf-mdefinition-probe ;
