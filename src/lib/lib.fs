\ Loads the whole general Forth library; each file requires its own
\ dependencies, so the order below only groups them. Modules elsewhere
\ load it with `require ../lib/lib.fs`; the marker word below also keeps it
\ from loading twice on a Forth whose REQUIRE sees two different relative
\ paths as two files. Nothing in lib/ knows about Lean.
[undefined] lf-lib-loaded [if]
: lf-lib-loaded ( -- ) ;
require ./portability.fs
require ./bounds.fs
require ./store.fs
require ./node.fs
require ./outcome.fs
require ./walk.fs
require ./frame.fs
require ./context.fs
[then]
