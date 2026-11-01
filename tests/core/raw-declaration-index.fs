\ Untrusted candidate-signature index tests. Entries do not assert or check
\ declarations and cannot be used as theorem handles or axioms.
include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/experimental/names.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/tagged-sort-boundary.fs
include ../../src/experimental/symbolic-session.fs
include ../../src/experimental/generation-handles.fs
include ../../src/experimental/raw-declaration-index.fs

variable alpha-name
variable beta-name
variable signature-id
lf-name-reset lf-term-reset lf-level-reset lf-lscope-context-reset
T{ 0 s" alpha" lf-name-str -> 1 true }T
1 alpha-name !
T{ 0 s" beta" lf-name-str -> 2 true }T
2 beta-name !
T{ lf-ssession-begin -> true }T
T{ lf-rawdecl-begin -> true }T
T{ 0 lf-level-identities @ lf-hterm-sort -> 0 lf-term-serial @ true }T
lf-term-serial @ signature-id !
T{ alpha-name @ 0 signature-id @ 1000 lf-rawdecl-put -> lf-rawdecl-ok }T
T{ alpha-name @ 1000 lf-rawdecl-find -> 0 signature-id @ lf-rawdecl-ok }T
T{ beta-name @ 1000 lf-rawdecl-find -> -1 0 lf-rawdecl-unknown }T
T{ alpha-name @ 0 signature-id @ 1000 lf-rawdecl-put -> lf-rawdecl-invalid }T
T{ 0 0 signature-id @ 1000 lf-rawdecl-put -> lf-rawdecl-invalid }T
T{ beta-name @ 0 0 1000 lf-rawdecl-put -> lf-rawdecl-invalid }T
T{ beta-name @ 0 signature-id @ 0 lf-rawdecl-put -> lf-rawdecl-exhausted }T
T{ alpha-name @ -1 lf-rawdecl-find -> -1 0 lf-rawdecl-invalid }T
T{ beta-name @ 0 signature-id @ -1 lf-rawdecl-put -> lf-rawdecl-invalid }T
T{ lf-rawdecl-count @ -> 1 }T
T{ alpha-name @ 1000 lf-rawdecl-find -> 0 signature-id @ lf-rawdecl-ok }T
\ Name aliases within the same live interner resolve to the same record.
T{ 0 s" alpha" lf-name-str -> 1 true }T
T{ 1 1000 lf-rawdecl-find -> 0 signature-id @ lf-rawdecl-ok }T
\ A new term session must not silently rebind an existing index, even after
\ its term slot has been reused. Old allocation identities also fail closed.
lf-term-reset
T{ lf-ssession-begin -> true }T
T{ 0 lf-level-identities @ lf-hterm-sort -> 0 lf-term-serial @ true }T
T{ alpha-name @ 1000 lf-rawdecl-find -> -1 0 lf-rawdecl-invalid }T
T{ beta-name @ 0 lf-term-serial @ 1000 lf-rawdecl-put -> lf-rawdecl-invalid }T
\ Resetting names invalidates the entire index rather than recycling it.
lf-name-reset
T{ alpha-name @ 1000 lf-rawdecl-find -> -1 0 lf-rawdecl-invalid }T
T{ beta-name @ 0 signature-id @ 1000 lf-rawdecl-put -> lf-rawdecl-invalid }T
T{ lf-rawdecl-count @ -> 1 }T
\ Isolate name invalidation while the term session remains current, and
\ reuse the same numeric name slot for a different name.
T{ lf-rawdecl-begin -> true }T
T{ 0 s" first" lf-name-str -> 1 true }T
T{ 1 0 lf-term-serial @ 1000 lf-rawdecl-put -> lf-rawdecl-ok }T
lf-name-reset
T{ 0 s" second" lf-name-str -> 1 true }T
T{ lf-ssession-current? -> true }T
T{ 1 1000 lf-rawdecl-find -> -1 0 lf-rawdecl-invalid }T
\ A fresh index uses the current meaning of ID 1; callers must preserve the
\ name generation separately when carrying IDs across index lifetimes.
T{ lf-rawdecl-begin -> true }T
T{ 1 0 lf-term-serial @ 1000 lf-rawdecl-put -> lf-rawdecl-ok }T
T{ 1 1000 lf-rawdecl-find -> 0 lf-term-serial @ lf-rawdecl-ok }T
bye
