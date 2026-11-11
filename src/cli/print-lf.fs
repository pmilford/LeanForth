\ A Lean export written out as one LeanForth text (plan task 8.6.3, ADR 0017
\ Amendment 1, A2): the words behind `leanforth print --lf` (cli/leanforth.fs).
\ Every declaration of the export fed into the checker's input, in file
\ order, is written by the term printer's Forth mode (present/print-forth.fs)
\ as the theorem, def or axiom words that build it, statement and value, so
\ that src/author's runner reads the text back to identical terms.
\
\ What the words cannot write is never dropped and never written wrongly. A
\ declaration that is not a safe theorem, definition or axiom (an inductive
\ type, a constructor, a recursor, a quotient constant, an opaque constant,
\ an unsafe or partial declaration), has more universe parameters than
\ lf-decl-universe-capacity, or does not print (a name or literal the words
\ cannot spell, a form such as let, fuel or room that ran out) is replaced
\ by a comment line `\ not written: NAME (reason)` and, so that later
\ declarations that use the constant still read back, an `import-stub` of
\ the same name, universe parameters and, when it prints, type: the stub the
\ authoring words already use for a constant Lean's library provides
\ (tests/author/07-add-comm.lf). Each skipped declaration is also listed on
\ stderr with its reason, and a summary of the counts ends the run. A
\ declaration is printed twice, once into the void to learn that it prints
\ and once for real, so no half-written declaration ever reaches the output.
\ The export is not checked and the text proves nothing: it is untrusted
\ presentation, and a stub is an assumption, not a proof.
\
\ Known gaps (plan task 8.6.3 follow-ups): a constant that the export uses
\ but no declaration of it defines (not a valid export) gets no stub; the
\ definition's reducibility hint, safety and protected status are not in the
\ text (the authoring words make a regular, safe, unprotected definition).
\
\ Public word: lf-file-write ( fuel -- skipped ) writes to the standard
\ output, the skipped declarations' lines and the summary to stderr; skipped
\ is how many declarations were replaced.
\ State: one context record, lf-fl (the counts and the declaration record
\ handed to the printer).

require ../lib/lib.fs
require ../core/input.fs
require ../present/print-forth.fs
require ./name-text.fs

\ Why a declaration is not written, one counter each (lf-fl-counts).
0 constant fl-inductive
1 constant fl-constructor
2 constant fl-recursor
3 constant fl-quotient
4 constant fl-block
5 constant fl-opaque
6 constant fl-unsafe
7 constant fl-arity
8 constant fl-unsupported
9 constant fl-invalid
10 constant fl-fuel
11 constant fl-none           \ not skipped
11 constant fl-reasons

begin-structure /lf-fl
  field: lf-fl-any              \ true once something was written
  field: lf-fl-written          \ declarations written whole
  field: lf-fl-fuel             \ the printer's fuel for each declaration
  fl-reasons cells +field lf-fl-counts   \ skipped declarations by reason
  /lf-fdecl +field lf-fl-decl   \ the declaration record the printer reads
end-structure
/lf-fl context-record: lf-fl

: fl-reason-text ( reason -- c-addr u )
  case fl-inductive of s" an inductive type" endof
    fl-constructor of s" an inductive type's constructor" endof
    fl-recursor of s" a recursor" endof
    fl-quotient of s" a quotient constant" endof
    fl-block of s" an inductive block's header" endof
    fl-opaque of s" an opaque constant" endof
    fl-unsafe of s" an unsafe or partial declaration" endof
    fl-arity of s" more than 8 universe parameters" endof
    fl-unsupported of s" a name, literal or term form the words cannot write" endof
    fl-invalid of s" a term the input does not hold (let, metadata) or malformed" endof
    fl-fuel of s" the printer ran out of fuel or room" endof
    s" ?" rot endcase ;

\ The standard error, for the list of what was skipped.
: fl-err ( c-addr u -- ) stderr write-file drop ;
: fl-err-line ( c-addr u -- ) fl-err s\" \n" fl-err ;
: fl-out ( c-addr u -- ) type ;
: fl-both ( c-addr u -- ) 2dup fl-out fl-err ;

\ The name of the input declaration idecl as display text, escaped by name-text.fs.
: fl-name ( idecl -- c-addr u ) lf-idecl-name @ nt-name 0= if 2drop s" ?" then ;

\ Why the declaration cannot be written whole, by its kind, safety and arity;
\ fl-none when it can.
: fl-kind-why ( kind -- reason )
  case lf-kind-inductive of fl-inductive endof lf-kind-constructor of fl-constructor endof
    lf-kind-recursor of fl-recursor endof lf-kind-quotient of fl-quotient endof
    lf-kind-block of fl-block endof lf-kind-opaque of fl-opaque endof fl-none swap endcase ;
: fl-safe-why ( idecl -- reason )
  lf-idecl-safety @ lf-safety-safe = if fl-none else fl-unsafe then ;
: fl-why ( idecl -- reason )
  dup lf-idecl-kind @ fl-kind-why dup fl-none <> if nip exit then drop fl-safe-why ;
: fl-fits? ( idecl -- flag ) lf-idecl-arity @ lf-decl-universe-capacity > 0= ;

\ The printer's record for idecl: kind, name, type and value (-1 for none) and
\ the universe parameters.
: fl-decl ( -- fdecl ) lf-fl lf-fl-decl ;
: fl-universes! ( idecl -- )
  fl-decl lf-fdecl-universe swap lf-idecl-params@ lf-decl-universe-capacity min
  dup fl-decl lf-fdecl-universes ! 0 ?do dup i lf-param@ 2 pick i cells + ! loop 2drop ;
: fl-kind ( idecl -- kind )
  lf-idecl-kind @ case lf-kind-theorem of lf-decl-theorem endof
    lf-kind-definition of lf-decl-def endof lf-decl-axiom swap endcase ;
: fl-fill ( idecl kind type value -- fdecl )
  fl-decl /lf-fdecl erase fl-decl lf-fdecl-value ! fl-decl lf-fdecl-type !
  fl-decl lf-fdecl-kind ! dup lf-idecl-name @ fl-decl lf-fdecl-name !
  fl-universes! fl-decl ;
: fl-whole ( idecl -- fdecl ) dup fl-kind over lf-idecl-type @ 2 pick lf-idecl-value @ fl-fill ;
: fl-typed-stub ( idecl -- fdecl ) lf-decl-stub over lf-idecl-type @ -1 fl-fill ;
: fl-bare-stub ( idecl -- fdecl ) lf-decl-stub -1 -1 fl-fill ;

\ Print fdecl to sink: the printer's outcome; the text before a failure is
\ incomplete, so a caller first prints into the void.
: fl-run ( fdecl sink -- outcome ) 0 lf-print-setup lf-fl lf-fl-fuel @ lf-print-forth-decl ;
: fl-prints ( fdecl -- outcome ) ['] 2drop fl-run ;
: fl-write ( fdecl -- ) ['] fl-out fl-run drop ;
: fl-separate ( -- ) lf-fl lf-fl-any @ if s\" \n" fl-out then true lf-fl lf-fl-any ! ;

\ The reason a printer outcome stands for.
: fl-outcome-why ( outcome -- reason )
  case outcome-unsupported of fl-unsupported endof outcome-invalid of fl-invalid endof
    drop fl-fuel 0 endcase ;
: fl-count! ( reason -- ) cells lf-fl lf-fl-counts + 1 swap +! ;

\ Which stub stands in for idecl: 1 typed, 2 bare, 0 none.
: fl-stub-kind ( idecl -- n )
  dup fl-fits? 0= if drop 0 exit then
  dup fl-typed-stub fl-prints ok? if drop 1 exit then
  fl-bare-stub fl-prints ok? if 2 else 0 then ;
: fl-stub-text ( n -- c-addr u )
  case 1 of s" ; an import-stub with its type stands in" endof
    2 of s" ; an import-stub without its type stands in" endof
    s" ; no import-stub could be written either" rot endcase ;
\ The comment line, also on stderr (without its comment mark).
: fl-note ( idecl reason n -- )
  s" \ " fl-out s" not written: " fl-both rot fl-name fl-both s"  (" fl-both
  swap fl-reason-text fl-both fl-stub-text fl-both s" )" fl-both
  s\" \n" fl-out s\" \n" fl-err ;
: fl-stub ( idecl n -- )
  case 1 of fl-typed-stub fl-write endof 2 of fl-bare-stub fl-write endof 2drop 0 endcase ;
: fl-skip ( idecl reason -- )
  dup fl-count! over fl-stub-kind >r
  fl-separate over swap r@ fl-note r> fl-stub ;
: fl-one ( idecl -- )
  dup fl-why dup fl-none <> if fl-skip exit then drop
  dup fl-fits? 0= if fl-arity fl-skip exit then
  dup fl-whole fl-prints dup ok? if drop fl-separate fl-whole fl-write
    1 lf-fl lf-fl-written +! exit then
  fl-outcome-why fl-skip ;

: fl-count@ ( reason -- n ) cells lf-fl lf-fl-counts + @ ;
: fl-skipped ( -- n ) 0 fl-reasons 0 ?do i fl-count@ + loop ;
: fl-num ( n -- c-addr u ) 0 <# #s #> ;
: fl-reason-line ( reason -- )
  dup fl-count@ ?dup 0= if drop exit then
  s"   " fl-err fl-num fl-err s"  " fl-err fl-reason-text fl-err-line ;
\ The counts, on stderr.
: fl-summary ( -- )
  lf-fl lf-fl-written @ fl-num fl-err s"  declarations written, " fl-err
  fl-skipped fl-num fl-err s"  not written" fl-err-line
  fl-reasons 0 ?do i fl-reason-line loop ;

: lf-file-write ( fuel -- skipped )
  lf-fl /lf-fl erase lf-fl lf-fl-fuel !
  lf-input-count 0 ?do i lf-input-decl fl-one loop fl-summary fl-skipped ;
