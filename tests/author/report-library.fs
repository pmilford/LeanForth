\ report.fs for a text that names the constants of a library (plan task
\ 8.2.1d): the library export is read as `leanforth check --env EXPORT`
\ reads it (cli/check-lf.fs, its manifest checked), the text runs with its
\ finder, also in the round trip's new context, and only the text's own
\ declarations are reported.
\ Usage: gforth tests/author/report-library.fs -e 's" EXPORT" s" FILE" report-with bye'
\ Test-only; not a public interface.
require ./report.fs
require ../../src/cli/check-lf.fs

: report-with ( lib-addr lib-u file-addr file-u -- )
  2swap true lfc-library-open dup ok? 0= abort" report: the library does not load" drop
  ['] lfc-find trip-finder ! report 0 trip-finder ! lfc-library-close ;
