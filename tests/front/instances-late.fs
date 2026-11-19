\ A wrong instance record met by a later query (plan slice MF2+DT;
\ docs/design/MATHLIB_FRONT.md §3; src/front/instances.fs):
\ tests/front/mul-wrong.elab.ndjson is tests/front/whnf-slice.elab.ndjson
\ with one change, instMulNat recorded as an instance of Add (still filed
\ under Mul's root), and its header's records_sha256 recomputed (the
\ SHA-256 of every line after the header), so the reader accepts it.
\ Each record is checked when first needed: the first query, of Add's
\ root, whose records are right, answers in full; the second, of Mul's
\ root, meets instMulNat: refused (115), the record named
\ (lf-inst-refused-decl), and every later query by each word, the
\ refusal kept (not found again: its code stays when the last error is
\ cleared), until a reset. Every T{ }T checks the data stack's depth.
include ../support/tester.fs
\ Every module first: a context member declared after menv-load would
\ move the context under the loaded slice.
require ../../src/front/instances.fs
require ./menv-slice.fs
:noname ( -- c-addr u ) s" tests/front/mul-wrong.elab.ndjson" ; is menv-data
require ./whnf-cases.fs

: add-nat ( -- t ) l0 1 s" Add" cn nat app ;
: mul-nat ( -- t ) l0 1 s" Mul" cn nat app ;
: decl-named ( c-addr u -- d ) menv-name elab-decl-of drop ;
: class-defaults ( c-addr u -- n outcome ) decl-named lf-default-instances rot drop ;
T{ add-nat lf-inst-candidates rot drop lf-inst-error lf-inst-refusal -> 3 outcome-ok 0 0 }T
T{ mul-nat lf-inst-candidates nip nip lf-inst-error lf-inst-refusal
   lf-inst-refused-decl s" instMulNat" decl-named =
   -> outcome-invalid 115 115 true }T
T{ 0 it it-error ! add-nat lf-inst-unify nip nip lf-inst-error -> outcome-invalid 115 }T
T{ 0 it it-error ! s" HAdd" class-defaults nip lf-inst-error -> outcome-invalid 115 }T
T{ lf-inst-classes lf-mctx-depth lf-mctx-marks -> outcome-invalid 0 0 }T
\ A reset (as a new read) forgets the refusal: Add answers again.
T{ lf-inst-reset add-nat lf-inst-candidates rot drop lf-inst-refusal -> 3 outcome-ok 0 }T
bye
