\ Layer entry: everything that checks an export, without the command line,
\ the front end, the authoring words, the term printer's proof outlines or
\ the verified-program track: the kernel (src/load/kernel.fs), the
\ importer (src/load/import.fs), and the checked environment saved and
\ loaded with a snapshot, its verdict version (ADR 0020, plan step SN3),
\ which a fresh check without --save-snapshot never runs. The import pass
\ reads run records (import/run-record.fs), whose names it prints with
\ the presentation's name text (present/name-text.fs and the few modules
\ it requires); nothing else of present/ is loaded.
\ The kernel's and the importer's tests and pinned-Lean comparisons load
\ this file (or src/load/kernel.fs), not src/main.fs. src/main.fs loads
\ it first, so the order of every definition is the full load's.
require ./kernel.fs
require ./import.fs
require ../kernel/verdict-version.fs
require ../kernel/env-snapshot.fs
require ../kernel/env-import.fs
