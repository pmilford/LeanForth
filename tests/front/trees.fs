\ Prints the syntax tree the natural reader builds for a statement, in
\ Lean's syntax after macro expansion (binop%, binrel%, application),
\ for tests/front/check_front.py, which compares it with pinned Lean's
\ expansion of the same statement. Test-only. Usage, after
\ src/load/checker.fs, src/load/front.fs and src/cli/check-lf.fs:
\   s" 0 n + n =" tree   \ prints binrel% Eq (binop% HAdd.hAdd 0 n) n
\ The statement runs in a theorem with the variables n and m of type Nat,
\ against the Init slice's constants (tests/author/init-slice.ndjson).

: tree-library ( -- )
  s" tests/author/init-slice.ndjson" true lfc-library-open ok? 0= abort" trees: no library" ;
tree-library
' type lf-print-unicode lf-print-setup
\ Only the reader runs: end t stops before the elaborator (error 71, the
\ hand-over's default; front/elab-decl.fs is tested in tests/front/elab.fs).
' lfh-later is lf-front-elaborate   ' lfr-unelaborated is lf-front-by-statement
create tree-text 512 allot  variable tree-text#
: tree+ ( c-addr u -- ) tuck tree-text tree-text# @ + swap move tree-text# +! ;
: tree-run ( c-addr u -- )
  0 tree-text# ! s" theorem t Nat explicit: n Nat explicit: m " tree+ tree+
  s"  := n end t" tree+ lf-author-begin tree-text tree-text# @ lf-author-text drop
  lf-author-code 71 <> abort" trees: the statement did not read" ;
: .var ( slot -- ) if ." m" else ." n" then ;
: .const ( decl -- ) lfa-decl-name lf-print-name drop ;
defer .tree ( node -- )
: compound? ( node -- flag )
  syn-kind@ dup syn-k-app syn-k-rightact one-of2? swap syn-k-binop syn-k-binrel 1+ within or ;
: .arg ( node -- ) space dup compound? if ." (" .tree ." )" else .tree then ;
: .op ( node -- ) dup syn-a@ lf-print-name drop dup syn-b@ .arg syn-c@ .arg ;
: .args ( app -- ) dup syn-b@ 0 ?do dup i syn-arg .arg loop drop ;
: .node ( node -- )
  dup syn-kind@ case
    syn-k-num of syn-a@ 0 .r endof
    syn-k-var of syn-a@ .var endof
    syn-k-const of syn-a@ .const endof
    syn-k-binop of ." binop% " .op endof
    syn-k-binrel of ." binrel% " .op endof
    syn-k-rightact of ." rightact% " .op endof
    syn-k-app of dup syn-a@ .tree .args endof
  endcase ;
' .node is .tree
: tree ( c-addr u -- ) tree-run lf-front-statement .tree cr ;
