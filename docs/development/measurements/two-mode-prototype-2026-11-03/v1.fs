\ Throwaway prototype for ADR 0019's section on defining words and loops:
\ the words a draft IR v1 needs, given to BOTH designs at once, the alias
\ vocabulary (cv.fs: new entries in cv-words) and the mode shift (ms.fs:
\ new verification semantics of Forth's own words). Writes a draft IR v1
\ text, not a format anyone reads yet:
\   do / ?do ... loop / +loop, i, j, leave, unloop   counted loops
\   begin ... until, begin ... again                  loops ending at the end
\   call NAME for RECURSE                             the definition being made
\   create, prim ",", does                            in a defining word
\   created NAME / cell n / cell undefined / does W / end   declared data
\   addr NAME                                          a created word's address
\   prim @, prim !, prim cells                         memory (IR v1)
\ At the top level a user-written defining word RUNS: its create part
\ (the instructions before DOES>, here only literals, CREATE and ,) is
\ executed on a model of data space, as Forth runs it while loading, and
\ declares the new word with its data. Load after cv.fs and ms.fs.

\ ---------------------------------------------------------------- frames
5 constant f-do
: do-frames ( -- n ) 0 cv-ctl# @ 0 ?do cv-ctl i cells + @ f-do = - loop ;
: v1-need-do ( n -- ) do-frames > if why-unbalanced cv-invalid! then ;
: v1-word ( c-addr u -- ) cv-start cv+ cv-here cv-done ;
: v1-do ( -- ) cv-inside s" do" f-do cv-open ;
: v1-?do ( -- ) cv-inside s" ?do" f-do cv-open ;
: v1-close-do ( c-addr u -- )
  cv-inside f-do cv-top? 0= if 2drop why-unbalanced cv-invalid! then cv-close ;
: v1-loop ( -- ) s" loop" v1-close-do ;
: v1-+loop ( -- ) s" +loop" v1-close-do ;
: v1-i ( -- ) cv-inside 1 v1-need-do s" i" v1-word ;
: v1-j ( -- ) cv-inside 2 v1-need-do s" j" v1-word ;
: v1-leave ( -- ) cv-inside 1 v1-need-do s" leave" v1-word ;
: v1-unloop ( -- ) cv-inside 1 v1-need-do s" unloop" v1-word ;
: v1-close-begin ( c-addr u -- )
  cv-inside f-begin cv-top? 0= if 2drop why-unbalanced cv-invalid! then cv-close ;
: v1-until ( -- ) s" until" v1-close-begin ;
: v1-again ( -- ) s" again" v1-close-begin ;
: v1-recurse ( -- ) cv-inside cv-start s" call " cv+ cv-def @ pw-name cv+ cv-here cv-done ;

\ ---------------------------------------------------------------- data
\ Per definition (pw-id): the create part recorded as (kind, value) ops,
\ and whether the word is a defining word that can run at the top level.
\ Per created word: its DOES> word (body) or 0.
0 constant op-lit  1 constant op-create  2 constant op-comma
2 constant k-created
16 constant ops-max  41 constant ids
create ops ids ops-max * 2* cells allot  create ops# ids cells allot
create runnable ids cells allot           create does-of ids cells allot
create defining ids cells allot
variable v1-does?  variable v1-mark
: cur-id ( -- id ) cv-def @ pw-id @ ;
: op-addr ( id i -- a ) swap ops-max * + 2* cells ops + ;
: rec-op ( kind value -- )
  cv-in-def @ 0= v1-does? @ or if 2drop exit then
  cur-id cells ops# + dup @ ops-max = if drop 2drop exit then
  >r cur-id r@ @ op-addr 2! 1 r> +! ;
\ The concrete stack of top-level literals, mirroring the kept tokens.
create kv 16 cells allot  variable kv#
: kv-push ( n -- ) kv# @ 16 < if kv kv# @ cells + ! 1 kv# +! else drop then ;
: kv-pop ( -- n ) -1 kv# +! kv kv# @ cells + @ ;
: v1-lit ( n -- )
  op-lit over rec-op cv-in-def @ 0= if dup kv-push then cv-lit ;
\ An open top-level CREATE region: cells follow as "," are seen.
variable region
: v1-close-region ( -- ) region @ if s" end" cv+ cv-line false region ! then ;
: v1-colon ( -- )
  v1-close-region cv-colon false v1-does? ! cv-lines# @ v1-mark !
  0 cur-id cells ops# + ! false cur-id cells runnable + ! false cur-id cells defining + ! ;
: v1-semicolon ( -- ) cv-semicolon false v1-does? ! ;
: v1-constant ( -- ) v1-close-region cv-constant 0 kv# ! ;
\ A name after CREATE or VARIABLE at the top level, or after a defining
\ word's CREATE: a created word of the file.
: v1-created ( does -- body )
  cv-kept# @ if drop why-left-over cv-unsupported! then
  cv-name k-created swap cv-define dup >r pw-id @ cells does-of + ! cv-read
  true r@ pw-done ! s" created " cv+ r@ pw-name cv+ cv-here cv-at+ cv-line r> ;
: v1-create ( -- )
  cv-in-def @ if s" create" v1-word op-create 0 rec-op exit then
  v1-close-region 0 v1-created drop true region ! ;
: v1-variable ( -- )
  cv-in-def @ if why-inside cv-unsupported! then
  v1-close-region 0 v1-created drop s"   cell undefined" cv+ cv-line s" end" cv+ cv-line ;
\ "," in a definition is a memory instruction; at the top level it adds
\ the one kept literal to the open region.
: v1-comma ( -- )
  cv-in-def @ if s" prim ," v1-word op-comma 0 rec-op exit then
  region @ 0= cv-kept# @ 1 <> or kv# @ 1 <> or if why-not-ir cv-unsupported! then
  0 cv-kept# ! 0 cv-values ! s"   cell " cv+ kv-pop cv-n+ cv-here cv-at+ cv-line ;
\ DOES>: the rest of the definition is each created word's behaviour. The
\ word can run at the top level if its create part was only literals,
\ CREATE and "," (every line written since its "word" line was recorded).
: v1-does ( -- )
  cv-inside cv-ctl# @ if why-unbalanced cv-invalid! then
  cv-lines# @ v1-mark @ - cur-id cells ops# + @ = cur-id cells runnable + !
  true cur-id cells defining + ! true v1-does? ! s" does" cv+ cv-here cv-at+ cv-line ;
: v1-mem ( c-addr u -- ) cv-in-def @ 0= if 2drop why-not-ir cv-unsupported! then v1-word ;
: v1-fetch ( -- ) s" prim @" v1-mem ;
: v1-store ( -- ) s" prim !" v1-mem ;
: v1-cells ( -- ) s" prim cells" v1-mem ;

\ ---------------------------------------------------------------- calls
\ Run a defining word's create part on the kept literals: CREATE reads the
\ next name, as Forth's CREATE does when the word runs while loading.
create cs 16 cells allot  variable cs#  variable child
: cs-push ( n -- ) cs cs# @ cells + ! 1 cs# +! ;
: cs-pop ( -- n ) cs# @ 0= if why-borrowed cv-unsupported! then -1 cs# +! cs cs# @ cells + @ ;
: run-op ( kind value -- )
  swap case
    op-lit of cs-push endof
    op-create of drop child @ if why-not-ir cv-unsupported! then
      cv-def @ v1-created child ! endof
    op-comma of drop child @ 0= if why-not-ir cv-unsupported! then
      s"   cell " cv+ cs-pop cv-n+ cv-line endof
  endcase ;
: run-defining ( body -- )
  cv-kept# @ kv# @ <> if drop why-left-over cv-unsupported! then
  kv cs kv# @ cells move kv# @ cs# ! 0 kv# ! 0 cv-kept# ! 0 cv-values ! 0 child !
  dup cv-def ! pw-id @ dup cells ops# + @ 0 ?do dup i op-addr 2@ run-op loop drop
  cs# @ child @ 0= or if why-one-value cv-unsupported! then
  s"   does " cv+ child @ pw-id @ cells does-of + @ pw-name cv+ cv-line s" end" cv+ cv-line ;
: v1-call ( body -- )
  dup pw-kind @ k-created = if
    cv-in-def @ 0= if drop why-outside cv-unsupported! then
    dup pw-id @ cells does-of + @ if s" call " else s" addr " then
    cv-start cv+ pw-name cv+ cv-here cv-done exit then
  dup pw-id @ cells defining + @ if
    \ Creating words while the program runs changes the dictionary at run
    \ time: unsupported inside verified words (plan).
    cv-in-def @ if drop why-not-ir cv-unsupported! then
    dup pw-id @ cells runnable + @ 0= if drop why-not-ir cv-unsupported! then
    v1-close-region run-defining exit then
  cv-call ;

\ ---------------------------------------------------------------- both designs
\ Alias: entries in the vocabulary (shadowing the reserved ones).
' v1-colon cv-entry :         ' v1-semicolon cv-entry ;     ' v1-constant cv-entry constant
' v1-do cv-entry do           ' v1-?do cv-entry ?do         ' v1-loop cv-entry loop
' v1-+loop cv-entry +loop     ' v1-i cv-entry i             ' v1-j cv-entry j
' v1-leave cv-entry leave     ' v1-unloop cv-entry unloop   ' v1-until cv-entry until
' v1-again cv-entry again     ' v1-recurse cv-entry recurse ' v1-create cv-entry create
' v1-variable cv-entry variable  ' v1-comma cv-entry ,       ' v1-does cv-entry does>
' v1-fetch cv-entry @         ' v1-store cv-entry !         ' v1-cells cv-entry cells
\ Mode shift: verification semantics of Forth's own words.
' v1-colon verifies :         ' v1-semicolon verifies ;     ' v1-constant verifies constant
' v1-do verifies do           ' v1-?do verifies ?do         ' v1-loop verifies loop
' v1-+loop verifies +loop     ' v1-i verifies i             ' v1-j verifies j
' v1-leave verifies leave     ' v1-unloop verifies unloop   ' v1-until verifies until
' v1-again verifies again     ' v1-recurse verifies-name recurse ' v1-create verifies create
' v1-variable verifies variable  ' v1-comma verifies ,       ' v1-does verifies does>
' v1-fetch verifies @         ' v1-store verifies !         ' v1-cells verifies cells
' v1-lit cv-lit-xt !  ' v1-call cv-call-xt !
\ The end of the text also ends an open region.
: v1-run-file ( c-addr u -- outcome ) false region ! 0 kv# ! cv-run-file ;
: v1-ms-run-file ( c-addr u -- outcome ) false region ! 0 kv# ! ms-run-file ;
