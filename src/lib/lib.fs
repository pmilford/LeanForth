\ Loads the general Forth library in dependency order. Modules elsewhere
\ load it with `require ../lib/lib.fs`; the marker word below also keeps it
\ from loading twice on a Forth whose REQUIRE sees two different relative
\ paths as two files. Nothing in lib/ knows about Lean.
[undefined] lf-lib-loaded [if]
: lf-lib-loaded ( -- ) ;
include ./portability.fs
include ./bounds.fs
include ./store.fs
include ./node.fs
include ./outcome.fs
include ./walk.fs
include ./frame.fs
include ./context.fs
[then]
