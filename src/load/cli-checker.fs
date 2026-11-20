\ Layer entry: the command line of exports and snapshots, on the checker
\ (src/load/checker.fs) and the presentation its print uses, without the
\ front end, the authoring words or the verified-program track: check,
\ replay, print (with --lf), count and reexport of an EXPORT, check and
\ print with --snapshot or --save-snapshot, version, capabilities, help.
\ It is cli/leanforth.fs without cli/leanforth-text.fs: a LeanForth text
\ (FILE.lf) is refused here (exit 4) and is checked by bin/leanforth,
\ which loads src/main.fs. bin/leanforth-checker runs this entry, so the
\ tests and the pinned-Lean comparisons that check only exports depend on
\ the checker's files alone (scripts/tested-tree.py); for those commands
\ its output is bin/leanforth's, byte for byte.
require ./checker.fs
require ../cli/print.fs
require ../cli/leanforth.fs
