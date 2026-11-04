\ A declaration's statement in three forms (plan task 8.6.2; owner,
\ 2026-11-04): in Lean's notation (the term printer, Unicode, or ASCII in
\ LaTeX style), in mathematical notation (the term printer's LaTeX mode,
\ between $ and $) and in LeanForth words (the printer's Forth mode,
\ print-forth.fs). The proof outline's header prints them; the words here
\ are its only users, and a program that wants the three lines for some
\ other declaration may call lf-print-forms the same way.
\
\ The LeanForth form is the declaration's type written as the axiom of the
\ same name states a type: `axiom NAME`, one line for each parameter, the
\ rest of the type, `end NAME`, with a line for each universe parameter
\ first. It is the one form of LeanForth words that states a type with no
\ proof, and the authoring words (src/author/) run it to the identical type
\ (tests/author/ checks that for the pinned examples). Running it asserts
\ nothing: the axiom exists only in the authoring program's stores, and
\ the checker's verdict for the declaration is the one printed above it.
\ A declaration with more than 8 universe parameters, or a name or label
\ the words cannot spell, prints the words' reason instead (print-forth.fs).
\
\ Every form is printed straight to the outline's output sink, not through
\ its line buffer, so no statement is cut at the buffer's size. In LaTeX
\ style (lf-lv-latex!) the Lean form is the ASCII notation in the
\ typewriter font and the LeanForth form is a typewriter block, both
\ escaped for LaTeX; the mathematics is inline math.
\ Untrusted presentation code: the checker never loads it, and nothing it
\ prints is evidence of anything. Requires log-view.fs for its sink, fuel
\ and style, and print-forth.fs.
\ State: one context record: which forms are hidden, whether the LeanForth
\ block is at the start of a line, and the declaration record handed to
\ print-forth.fs.
\
\ Public words:
\   lf-forms! ( mask -- )   the forms to print: lf-form-lean, -mathematics,
\     -leanforth added up (the default is all three, lf-forms-all)
\   lf-forms ( -- mask )
\   lf-print-forms ( decl kind-c-addr u -- )   the lines of the forms
\     selected for the input declaration decl, after the line before: kind
\     is "Statement" or "Type", the word its labels start with; each line
\     ends with the style's end of line

require ./log-view.fs
require ./print-forth.fs

1 constant lf-form-lean
2 constant lf-form-mathematics
4 constant lf-form-leanforth
7 constant lf-forms-all

begin-structure /lf-sf
  field: lf-sf-hidden            \ the forms not printed
  field: lf-sf-bol               \ true at the start of a line of the block
  /lf-fdecl +field lf-sf-decl    \ the declaration print-forth.fs prints
end-structure
/lf-sf context-record: lf-sf

: lf-forms! ( mask -- ) lf-forms-all and lf-forms-all xor lf-sf lf-sf-hidden ! ;
: lf-forms ( -- mask ) lf-sf lf-sf-hidden @ lf-forms-all xor ;
: lf-forms-has? ( bit -- flag ) lf-forms and 0<> ;

\ Sinks. The Lean form is one line: its text as it is, or escaped for the
\ typewriter font. The LeanForth block goes four columns in (two ems in
\ LaTeX), a new line after each of the printer's line ends.
: lf-sf-newline ( -- c-addr u ) s\"  \\\\\n" ;
: lf-sf-tex-form ( char -- c-addr u true | false )
  case 32 of s" ~" true endof 10 of lf-sf-newline true endof
    [char] \ of s" \textbackslash{}" true endof [char] ^ of s" \^{}" true endof
    [char] ~ of s" \textasciitilde{}" true endof [char] _ of s" \_" true endof
    [char] # of s" \#" true endof [char] % of s" \%" true endof
    [char] & of s" \&" true endof [char] { of s" \{" true endof
    [char] } of s" \}" true endof [char] $ of s" \$" true endof
    >r false r> endcase ;
: lf-sf-tex-byte ( c-addr -- )
  dup c@ lf-sf-tex-form if rot drop lf-lv-out else 1 lf-lv-out then ;
: lf-sf-tex ( c-addr u -- ) 0 ?do dup i + lf-sf-tex-byte loop drop ;
: lf-sf-line-sink ( c-addr u -- ) lf-lv-tex? if lf-sf-tex else lf-lv-out then ;
\ The block: indentation is written before the first byte of a line.
: lf-sf-bol! ( flag -- ) lf-sf lf-sf-bol ! ;
: lf-sf-indent ( -- ) lf-sf lf-sf-bol @ 0= if exit then false lf-sf-bol!
  lf-lv-tex? if s" \hspace*{2em}" lf-lv-out else 4 lf-lv-blank-run then ;
: lf-sf-plain-byte ( c-addr -- )
  dup c@ 10 = if drop s\" \n" lf-lv-out true lf-sf-bol! exit then
  lf-sf-indent 1 lf-lv-out ;
: lf-sf-tex-block-byte ( c-addr -- )
  dup c@ 10 = if drop lf-sf-newline lf-lv-out true lf-sf-bol! exit then
  lf-sf-indent lf-sf-tex-byte ;
: lf-sf-block-sink ( c-addr u -- )
  lf-lv-tex? 0= if 0 ?do dup i + lf-sf-plain-byte loop drop exit then
  0 ?do dup i + lf-sf-tex-block-byte loop drop ;

\ The three printers, each to its sink and mode.
: lf-sf-printer ( xt mode -- ) lf-print-setup ;
: lf-sf-theorem? ( decl -- flag ) lf-idecl-kind @ lf-kind-theorem = ;
: lf-sf-lean-mode ( -- mode ) lf-lv-tex? if lf-print-ascii else lf-print-unicode then ;
\ The type of a theorem prints as a proposition (its Pi spine as ∀), the
\ type of anything else as a term.
: lf-sf-type ( decl -- )
  dup lf-idecl-type @ lf-lv lf-lv-fuel @ rot lf-sf-theorem?
  if lf-print-statement else lf-print-term then lf-lv-printed ;
: lf-sf-lean ( decl -- )
  ['] lf-sf-line-sink lf-sf-lean-mode lf-sf-printer
  lf-lv-tex? if s" {\ttfamily " lf-lv-out then lf-sf-type
  lf-lv-tex? if s" }" lf-lv-out then ;
: lf-sf-mathematics ( decl -- )
  s" $" lf-lv-out ['] lf-lv-out lf-print-latex lf-sf-printer lf-sf-type s" $" lf-lv-out ;

\ The LeanForth block: the declaration as an axiom of its own name.
: lf-sf-universes ( decl -- )
  lf-sf lf-sf-decl lf-fdecl-universe swap lf-idecl-params@ dup
  lf-sf lf-sf-decl lf-fdecl-universes ! 0 ?do
    dup i lf-param@ 2 pick i cells + ! loop 2drop ;
: lf-sf-fdecl ( decl -- fdecl )
  lf-sf lf-sf-decl /lf-fdecl erase
  lf-decl-axiom lf-sf lf-sf-decl lf-fdecl-kind !
  dup lf-idecl-name @ lf-sf lf-sf-decl lf-fdecl-name !
  dup lf-idecl-type @ lf-sf lf-sf-decl lf-fdecl-type !
  -1 lf-sf lf-sf-decl lf-fdecl-value ! lf-sf-universes lf-sf lf-sf-decl ;
: lf-sf-fits? ( decl -- flag ) lf-idecl-arity @ lf-decl-universe-capacity > 0= ;
: lf-sf-unspelled ( outcome -- )
  s\" (not complete: " lf-sf-block-sink outcome-text lf-sf-block-sink
  s\" )\n" lf-sf-block-sink ;
: lf-sf-forth ( decl -- )
  true lf-sf-bol! ['] lf-sf-block-sink lf-print-unicode lf-sf-printer
  lf-lv-tex? if s" {\ttfamily " lf-lv-out then
  dup lf-sf-fits? 0= if drop outcome-unsupported else
    lf-sf-fdecl lf-lv lf-lv-fuel @ lf-print-forth-decl then
  dup ok? 0= if lf-sf-unspelled else drop then
  lf-lv-tex? if s\" }\n" lf-lv-out then ;

\ The lines. A label is the kind word and what the line shows.
: lf-sf-label ( kind-c-addr u c-addr u -- )
  2>r lf-lv-tex? 0= if s"   " lf-lv-put then lf-lv-put 2r> lf-lv-put
  lf-lv-tex? if 0 lf-lv-flush s"  " lf-lv-out else 28 lf-lv-flush then ;
: lf-sf-end ( -- ) lf-lv-printer lf-lv-tex? if s"  \\" lf-lv-out then lf-lv-cr ;
: lf-sf-lean-line ( decl kind u -- )
  lf-lv-tex? if s"  in Lean (ASCII):" else s"  in Lean:" then lf-sf-label
  lf-sf-lean 0 lf-lv-flush lf-sf-end ;
: lf-sf-math-line ( decl kind u -- )
  s"  in mathematics:" lf-sf-label lf-sf-mathematics 0 lf-lv-flush lf-sf-end ;
: lf-sf-forth-line ( decl kind u -- )
  s"  in LeanForth (as an axiom states a type; this assumes nothing):" lf-sf-label
  lf-lv-tex? if s" \\" lf-lv-out lf-lv-cr else lf-lv-cr then lf-sf-forth lf-lv-printer ;
: lf-sf-copy ( d k u -- d k u d k u ) 2 pick 2 pick 2 pick ;
: lf-print-forms ( decl kind-c-addr u -- )
  lf-form-lean lf-forms-has? if lf-sf-copy lf-sf-lean-line then
  lf-form-mathematics lf-forms-has? if lf-sf-copy lf-sf-math-line then
  lf-form-leanforth lf-forms-has? if lf-sf-copy lf-sf-forth-line then
  2drop drop ;
