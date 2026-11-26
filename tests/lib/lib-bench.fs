\ Speed of the src/lib libraries at a small and a large size (plan task 1.1.8;
\ report only, not part of make test): `make lib-bench` runs it on gforth-fast
\ and gforth and prints one Markdown table per engine, the figures of
\ docs/development/FORTH_LIBRARY.md's "Measured profiles". Each row times one
\ operation of one library on n items, repeating it until a run takes at least
\ 0.2 s, best of two runs, and prints the time per item (an item is a byte, a
\ value, a call or an operation, as the row says). Writes two scratch files,
\ build/lib-bench-lines.tmp and build/lib-bench.sect, and deletes them. Uses
\ Gforth's utime; meant for 64-bit cells.
require ../../src/lib/sha256.fs
require ../../src/lib/json.fs
require ../../src/lib/json-write.fs
require ../../src/lib/bigint.fs
require ../../src/lib/memo.fs
require ../../src/lib/sort.fs
require ../../src/lib/pqueue.fs
require ../../src/lib/sections.fs
require ../../src/lib/pools.fs
require ../../src/lib/runs.fs
require ../../src/lib/text-rule.fs
require ../../src/lib/text-run.fs
require ../../src/lib/xt-table.fs
require ../../src/lib/task.fs
decimal

\ ---- Timing: a case is ( n -- ), n items of work; prep ( n -- ) runs before it.
variable items        \ items a case does, when its prep sets it; else n
: run-once ( n xt reps -- us ) utime 2>r 0 ?do 2dup execute loop 2drop utime 2r> d- d>s ;
\ The clock of a WSL host now and then steps back: a run that reads no time
\ or less is run again.
: timed ( n xt reps -- us )
  begin 2 pick 2 pick 2 pick run-once dup 0<= while drop repeat >r 2drop drop r> ;
: enough ( n xt -- reps ) 1 begin >r 2dup r@ timed 200000 < r@ 1 30 lshift < and
  while r> 2* repeat 2drop r> ;
: best ( n xt reps -- us ) >r 2dup r@ timed -rot r> timed min ;
: per-item ( us reps n -- tenths-ns ) items @ ?dup if nip then * >r 10000 * r> / ;
: .1 ( tenths -- ) 0 <# # [char] . hold #s #> type ;
: .time ( tenths-ns -- )
  dup 100000 < if .1 ."  ns" exit then
  1000 / dup 100000 < if .1 ."  µs" exit then 1000 / .1 ."  ms" ;
: cell. ( n prep go -- ) 0 items ! >r ?dup if over swap execute then
  dup 0 .r ." : " dup dup r@ enough tuck r> swap best swap rot per-item .time ;
: row { small large prep go c-addr u -- }
  ." | " c-addr u type ."  | " small prep go cell. ."  | " large prep go cell. ."  |" cr ;

\ ---- Shared data: 4 MiB of random bytes, of UTF-8 text, and 1 Mi random cells.
4 1024 * 1024 * constant big-bytes
1024 1024 * constant big-cells
variable seed  12345 seed !
: random ( -- u ) seed @ 6364136223846793005 * 1442695040888963407 + dup seed ! 33 rshift ;
: buffer ( u -- addr ) allocate throw ;
big-bytes buffer constant raw         big-bytes buffer constant raw2
big-bytes buffer constant utext       big-cells cells buffer constant cells-in
big-cells cells buffer constant cells-work
: fill-raw ( -- ) big-bytes 0 do random raw i + c! loop ;
: fill-utext ( -- ) big-bytes 0 do s\" abc\xe2\x9c\x93" i 6 mod /string drop c@ utext i + c! loop ;
: fill-cells ( -- ) big-cells 0 do random cells-in i cells + ! loop ;
fill-raw fill-utext fill-cells

\ ---- sha256: init, update with n bytes, final.
sha256: hasher  create digest 32 allot
: sha-go ( n -- ) hasher sha256-init raw swap hasher sha256-update digest hasher sha256-final ;

\ ---- json: parse an array of objects of about n bytes; json-write: an array of n integers.
json: view  8 view json-init drop
variable jlen
: j+ ( c-addr u -- ) tuck raw2 jlen @ + swap move jlen +! ;
: json-prep ( n -- ) 0 jlen ! s" [" j+
  begin s\" {\"id\":12345,\"name\":\"ab\\u00e9\",\"ok\":true,\"xs\":[1,2]}" j+ dup jlen @ 2 + >
  while s" ," j+ repeat drop s" ]" j+ jlen @ items ! ;
: json-go ( n -- ) drop raw2 jlen @ view json-parse drop ;
4 64 json-writer: writer
: jw-go ( n -- ) ['] 2drop writer jw-start writer jw-open-array
  0 ?do i writer jw-n loop writer jw-close-array writer jw-end drop ;

\ ---- bignum and bigint: operands of about n limbs (19 decimal digits a limb).
create arena /big-arena allot   16 1024 * 1024 * buffer 16 1024 * 1024 * arena big-arena-init
variable na  variable nb  variable np  variable bmark
: digits ( n char -- c-addr u ) swap 19 * >r raw2 r@ rot fill raw2 r> ;
arena big-mark constant arena-empty
: big-prep ( n -- ) arena-empty arena big-release drop  1 items !
  dup [char] 9 digits arena decimal>big drop na !  [char] 7 digits arena decimal>big drop nb !
  na @ nb @ arena big* drop np !  arena big-mark bmark ! ;
: big*-go ( n -- ) drop na @ nb @ arena big* 2drop bmark @ arena big-release drop ;
: big/-go ( n -- ) drop np @ nb @ arena big/ 2drop bmark @ arena big-release drop ;
: int-prep ( n -- ) big-prep  np @ arena nat>bigint drop arena bigint-negate drop na !
  nb @ arena nat>bigint drop nb !  arena big-mark bmark ! ;
: ediv-go ( n -- ) drop na @ nb @ arena bigint-ediv 2drop bmark @ arena big-release drop ;

\ ---- htab: n distinct 32-bit values inserted, then each found (2n operations).
create htable /htab allot   create hooks /htab-hooks allot
: hval ( i -- x ) 2654435761 * $ffffffff and ;
: h-rehash ( n htab -- h ) drop hval hash-fmix ;
: h-same ( n key htab -- flag ) drop swap hval = ;
' h-rehash ' h-same hooks htab-hooks!
: h-add ( i -- ) htable htab-ready drop dup hval dup hash-fmix htable htab-find
  if 2drop else over hval hash-fmix htable htab-put then ;
: h-find ( i -- ) hval dup hash-fmix htable htab-find 0= abort" htab lost a value" drop ;
: two-n ( n -- ) 2* items ! ;
: htab-go ( n -- ) 4 hooks htable htab-init drop
  dup 0 ?do i h-add loop 0 ?do i h-find loop htable htab-free ;

\ ---- memo: n keys of two cells put, then each found; slab: n pushes, n pops;
\ pqueue: n random cells pushed, then popped.
create memo /memo allot
: memo-go ( n -- ) 2 1 memo memo-init drop
  dup 0 ?do i i 0 memo memo! drop loop 0 ?do i 0 memo memo@ 2drop loop memo memo-free ;
create slab /slab allot
: slab-go ( n -- ) 1 cells dup slab-limit-max slab slab-init drop
  dup 0 ?do i slab slab-push drop loop 0 ?do slab slab-pop drop loop slab slab-free ;
create queue /pqueue allot   ' sort-signed queue pq-init drop
: pq-go ( n -- ) dup 0 ?do cells-in i cells + @ queue pq-push drop loop
  0 ?do queue pq-pop drop loop ;

\ ---- sort: n random cells copied, then sorted by value.
create sorter /sorter allot   ' sort-signed sorter sorter-cells drop
: sort-go ( n -- ) cells-in cells-work 2 pick cells move cells-work swap sorter sort-records drop ;

\ ---- bytes: UTF-8 validation of n bytes; the reader over n lines of 80 bytes.
: utf8-go ( n -- ) utext swap utf8-valid? drop ;
: lines-file ( -- c-addr u ) s" build/lib-bench-lines.tmp" ;
reader: lines  4096 65536 lines reader-init drop
: lines-prep ( n -- ) dup 80 * items !  lines-file w/o create-file throw
  swap 0 ?do utext 79 2 pick write-line throw loop close-file throw ;
: lines-go ( n -- ) drop lines-file lines reader-open drop
  begin lines reader-more? while lines reader-line drop 2drop repeat lines reader-close drop ;

\ ---- decimal: an n-digit number written, and read back.
variable dnum
: dec-prep ( n -- ) 1 swap 1 ?do 10 * loop 7 + dnum ! 1 items ! ;
: u>dec-go ( n -- ) drop dnum @ u>decimal 2drop ;
: dec>u-go ( n -- ) drop dnum @ u>decimal digits>u if drop then ;

\ ---- sections: one section of n bytes written to a file, opened and read back.
sections: sf
: sect-file ( -- c-addr u ) s" build/lib-bench.sect" ;
: sect-go ( n -- ) sf sections-init raw 1 2 pick 1 sf sections-add drop
  sect-file sf sections-write drop sf sections-init sect-file sf sections-open drop
  raw2 swap 0 sf sections-read drop sf sections-close drop ;

\ ---- task: n empty jobs, at most 8 in flight, each in its own context.
8 constant in-flight
create job-contexts in-flight cells allot   create jobs in-flight cells allot
: job-ctx ( k -- context ) cells job-contexts + @ ;
: contexts-new ( -- ) in-flight 0 do context-new throw job-contexts i cells + ! loop ;
: submit ( k -- ) dup job-ctx ['] noop job-submit throw swap cells jobs + ! ;
: batch ( k -- ) dup 0 ?do i submit loop 0 ?do jobs i cells + @ job-wait throw loop ;
: task-go ( n -- ) begin dup 0> while dup in-flight min dup batch - repeat drop ;

\ ---- hash32, bounds, bits, u32: n bytes hashed; an absent cell sought among n;
\ 1000 binary searches over n sorted cells; n fields written, then read.
: hash-go ( n -- ) raw swap hash-bytes drop ;
: index-go ( n -- ) -1 cells-in rot cells-index drop ;
: sorted-prep ( n -- ) 0 ?do i 2* cells-work i cells + ! loop 1000 items ! ;
: below? ( x k -- x flag ) cells cells-work + @ over < ;
: bound-go ( n -- ) 1000 0 do i 7919 * over 2* mod 0 2 pick ['] below? lower-bound 2drop loop drop ;
: u32-go ( n -- ) dup 0 ?do i raw i u32s + u32! loop 0 swap 0 ?do raw i u32s + u32@ + loop drop ;

\ ---- cons and pools: n distinct texts of a cell interned; n pairs as tuples.
create texts /cons allot   create tuples /cons allot   create tkey 1 cells allot
: text-go ( n -- ) 4 text-class texts cons-init drop
  0 ?do i tkey ! tkey 1 cells texts text-intern 2drop loop texts cons-free ;
: pair ( a b -- ) tuples tuple-start drop swap tuples tuple-add drop
  tuples tuple-add drop tuples tuple-end 2drop ;
: tuple-go ( n -- ) 4 tuple-class tuples cons-init drop
  0 ?do i i 7 + pair loop tuples cons-free ;

\ ---- runs: one run grown by n cells; store and node: n nodes in a heap store.
: runs-go ( n -- ) runs-reset 0 swap 0 ?do i run-push drop loop drop ;
create nodes store-header allot
: node+ ( -- ) 1 2 3 nodes node-new if drop exit then
  nodes store-grow drop 1 2 3 nodes node-new 0= abort" store full" drop ;
: node-go ( n -- ) 16 /node 0 nodes store-heap-init drop dup 16 + nodes store-limit! drop
  0 ?do node+ loop nodes store-heap-free ;

\ ---- walk: a chain of n nodes; frame: the leaves of a tree of n levels (header example).
8 walk: chain
: chain-visit ( walk -- outcome )
  dup walk-node @ ?dup if 1- swap walk-push room>outcome else drop outcome-ok then ;
: walk-go ( n -- ) dup 1+ chain walk-budget drop ['] chain-visit chain walk-run drop ;
: leaves-sum ( b outcome frames -- n outcome frames 0 )
  >r r@ frame-restore over ok? if rot + swap else drop then r> 0 ;
: leaves-second ( a outcome frames -- x frames next | -1 outcome frames 0 )
  >r dup ok? 0= if r@ frame-restore drop r> 0 exit then drop
  r@ frame-restore 2 - swap r@ frame-save r> ['] leaves-sum frame-call ;
: leaves-visit ( n frames -- x frames next | n outcome frames 0 )
  over 2 < if >r drop 1 outcome-ok r> 0 exit then
  2dup frame-save swap 1- swap ['] leaves-second frame-call ;
' leaves-visit frames: tree
: fib-visits ( n -- visits ) 1 1 rot 0 ?do tuck + loop drop 2* 1- ;
: tree-prep ( n -- ) fib-visits items ! ;
: tree-go ( n -- ) max-n tree frame-budget drop 0 tree frame-run 2drop ;

\ ---- context: n contexts made, then freed.
create made 100 cells allot
: context-go ( n -- ) dup 0 ?do context-new throw made i cells + ! loop
  0 ?do made i cells + @ context-free throw loop ;

\ ---- text-rule, text-run: n bytes of UTF-8 text checked; scanned for an absent '~'.
: rule-go ( n -- ) utext swap tr-rule? drop ;
: tilde? ( c -- flag ) [char] ~ = ;
: scan-go ( n -- ) utext swap ['] tilde? text-any? drop ;

\ ---- xt-table: 1000 lookups in a htable of n entries; blocks: n bytes zeroed and freed;
\ outcome: n steps of ok-each.
16 ' noop xt-table: xts-small   4096 ' noop xt-table: xts-large
variable xts
: xts-prep ( n -- ) 16 = if ['] xts-small else ['] xts-large then >body xts ! 1000 items ! ;
: xts-go ( n -- ) drop 1000 0 do i 4095 and xts @ xt-table@ drop loop ;
: one ( n -- ) drop 1 items ! ;
: block-go ( n -- ) allocate0 throw free throw ;
: ok-step ( k -- outcome ) drop outcome-ok ;
: each-go ( n -- ) ['] ok-step ok-each drop ;

: lib-bench ( -- ) cr
  ." | Library: operation (time per item) | small n: time | large n: time |" cr
  ." | --- | --- | --- |" cr
  64 1048576 0 ['] sha-go s" sha256: hash a message (a byte)" row
  64 1048576 ['] json-prep ['] json-go s" json: parse (a byte)" row
  8 100000 0 ['] jw-go s" json-write: an array of integers (a value)" row
  2 1000 ['] big-prep ['] big*-go s" bignum: multiply, n limbs (a call)" row
  2 1000 ['] big-prep ['] big/-go s" bignum: divide 2n by n limbs (a call)" row
  2 1000 ['] int-prep ['] ediv-go s" bigint: ediv, -2n by n limbs (a call)" row
  1000 1000000 ['] two-n ['] htab-go s" htab: insert, then find (an operation)" row
  1000 1000000 ['] two-n ['] memo-go s" memo: put, then find (an operation)" row
  1000 1000000 ['] two-n ['] slab-go s" slab: push, then pop (an operation)" row
  16 1000000 0 ['] sort-go s" sort: random cells, with their copy (a cell)" row
  1000 1000000 ['] two-n ['] pq-go s" pqueue: push, then pop (an operation)" row
  64 1048576 0 ['] utf8-go s" bytes: utf8-valid? (a byte)" row
  10 50000 ['] lines-prep ['] lines-go s" bytes: reader, 80-byte lines (a byte)" row
  2 20 ['] dec-prep ['] u>dec-go s" decimal: u>decimal, n digits (a call)" row
  2 20 ['] dec-prep ['] dec>u-go s" decimal: u>decimal then digits>u (a call)" row
  1024 4194304 0 ['] sect-go s" sections: write, open, read one section (a byte)" row
  64 1048576 0 ['] hash-go s" hash32: hash-bytes (a byte)" row
  16 1000000 0 ['] index-go s" bounds: cells-index, absent (a cell)" row
  16 1000000 ['] sorted-prep ['] bound-go s" bits: lower-bound over n cells (a search)" row
  1000 1000000 ['] two-n ['] u32-go s" u32: u32! then u32@ (a field)" row
  1000 1000000 0 ['] text-go s" pools: text-intern, distinct texts (a text)" row
  1000 1000000 0 ['] tuple-go s" pools: tuples of two (a tuple)" row
  1000 1000000 0 ['] runs-go s" runs: run-push (a cell)" row
  1000 1000000 0 ['] node-go s" store, node: node-new with growth (a node)" row
  1000 1000000 0 ['] walk-go s" walk: a chain of n nodes (a visit)" row
  10 25 ['] tree-prep ['] tree-go s" frame: leaves of a tree, n levels (a visit)" row
  1 100 0 ['] context-go s" context: new, then free (a context)" row
  64 1048576 0 ['] rule-go s" text-rule: tr-rule? (a byte)" row
  10 1048576 0 ['] scan-go s" text-run: text-any?, no match (a byte)" row
  16 4096 ['] xts-prep ['] xts-go s" xt-table: xt-table@ in n entries (a lookup)" row
  64 1048576 ['] one ['] block-go s" blocks: allocate0 and free, n bytes (a call)" row
  16 1000000 0 ['] each-go s" outcome: ok-each (a step)" row
  pool-start throw contexts-new
  1 1000 0 ['] task-go s" task: empty jobs, 8 in flight (a job)" row
  pool-stop  lines-file delete-file drop  sect-file delete-file drop ;
