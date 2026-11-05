\ Term forms the first checker does not support (ADR 0011, rule U2): a
\ let, a natural-number or string literal, a metadata node and, for the
\ first checker's own importer (import/checker-input.fs) only, a
\ projection; the feed stages a projection as such since plan task 5.2.2
\ (core/projections.fs), a natural-number literal since plan task 5.2.3
\ (core/literals.fs) and a let since plan task 4.2.3 (core/let-terms.fs),
\ so only checker-input.fs still makes a let's leaf. An importer that
\ meets one in a declaration stages it as a
\ leaf of its own tag that records only which form it was, so that the
\ declaration audit (kernel/check-declaration.fs) finds it and answers
\ unsupported before any typing. The leaf keeps nothing of the form's
\ contents: nothing checks them, so nothing may depend on them. Every
\ other pass treats the tag as unknown (a walk reports invalid, inference
\ unknown), so such a leaf must never reach one: the audit runs first.
\ Free variables and metavariables are not forms of this kind: an export
\ cannot hold them, and an importer refuses them as invalid input (V1).
\ Untrusted [import] data.
\ State: none of its own; the leaves go into the term store (terms.fs).

require ../lib/lib.fs
require ./generation-handles.fs
require ./terms.fs

8 constant lf-tag-unsupported
\ The forms, numbered in the order of Lean's Expr constructors.
1 constant lf-form-let
2 constant lf-form-nat
3 constant lf-form-string
4 constant lf-form-mdata
5 constant lf-form-proj

: lf-form? ( form -- flag ) lf-form-let lf-form-proj between? ;
\ A leaf for one form, as a handle: (index identity true), or false for a
\ number that names no form, a full store or a spent serial (which the
\ store records as a diagnostic).
: lf-hterm-unsupported ( form -- index identity true | false )
  dup lf-form? 0= if drop false exit then
  lf-tag-unsupported swap 0 lf-term-add lf-hterm-result ;
