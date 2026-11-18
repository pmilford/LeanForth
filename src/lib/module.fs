\ Wordlists and module boundaries (ADR 0010, accepted 2026-11-03): the
\ library's public and private wordlists and the four words a module uses
\ to keep its helpers private. A module that uses them, after its header
\ and its REQUIREs:
\
\   lf-lib-private module-open      \ helpers by default
\   : helper ( -- ) ... ;
\   lf-lib set-current
\   : public-word ( -- ) ... helper ... ;
\   lf-lib-private set-current
\   ...
\   module-close
\
\ The previous compilation wordlist waits on the data stack between
\ module-open and module-close, so nested loading balances. A file that
\ keeps BASE on the stack opens after saving it and closes before
\ restoring it. lf-lib is pushed onto the search order once, when this file
\ loads, so the library's public words are visible to everything loaded
\ afterwards; lf-lib-private is searched only between module-open and
\ module-close, and by tests that ask for it with
\ `lf-lib-private order+`. Only Forth-2012 Search-Order words.
\
\ Wordlists are a code-quality tool, not a trust boundary (ADR 0010,
\ decision 9). So far only the libraries written after the ADR use them;
\ the other groups' wordlists (lf-core, lf-kernel, ...) come with their
\ migration steps.
\ State: the two wordlists and the search-order entry, made once while
\ loading.
\ Example: a helper kept private, a public word that uses it.
\   lf-lib-private module-open
\   : twice ( n -- 2n ) 2* ;
\   lf-lib set-current
\   : quadruple ( n -- 4n ) twice twice ;
\   module-close
\   5 quadruple .  s" twice" find-name 0= .   \ prints: 20 -1

[undefined] lf-lib [if]
wordlist constant lf-lib
wordlist constant lf-lib-private
\ Push wid onto the search order, first searched; pop the first entry.
: order+ ( wid -- ) >r get-order r> swap 1+ set-order ;
: order- ( -- ) get-order nip 1- set-order ;
\ Search a module's private wordlist and compile into it, keeping the
\ previous compilation wordlist; then give that back and stop searching it.
: module-open ( private -- previous ) dup order+ get-current swap set-current ;
: module-close ( previous -- ) set-current order- ;
lf-lib order+
[then]
