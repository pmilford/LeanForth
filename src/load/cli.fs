\ Layer entry: the whole command line, LeanForth text included, for
\ src/main.fs after every other layer. cli/leanforth.fs is the command line
\ of exports and snapshots (src/load/cli-checker.fs loads it alone);
\ cli/leanforth-text.fs adds a text's check, on the front end
\ (cli/check-lf.fs). The modules before cli/leanforth.fs are the ones it
\ required itself until 2026-11-19, in that order, check-lf.fs among them
\ where it stood: so every word of the full load comes in the same order as
\ before but the text words cli/leanforth-text.fs took over, which come
\ last (docs/development/forth-reviews, branch layered-loads).
require ../cli/print.fs
require ../import/run-replay.fs
require ../import/ndjson-count.fs
require ../import/ndjson-emit.fs
require ../cli/print-lf.fs
require ../cli/check-lf.fs
require ../cli/check-json.fs
require ../cli/leanforth.fs
require ../cli/leanforth-text.fs
