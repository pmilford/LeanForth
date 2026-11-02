\ Throughput sketch: stream an NDJSON export line by line, pull out the
\ integers outside strings, and hash-cons every expression record.
\ Benchmark only; not a parser.
65536 constant /lbuf
create line-buf /lbuf 2 + allot
variable fid
variable nlines variable nexpr variable nnew variable nbytes variable probes
create ints 16 cells allot
variable nints variable instr variable acc variable indig

: push-int ( -- )
  indig @ if nints @ 15 < if acc @ nints @ cells ints + ! 1 nints +! then
  0 acc ! 0 indig ! then ;
: scan-ints ( addr u -- )
  0 nints ! 0 instr ! 0 acc ! 0 indig !
  over + swap
  begin 2dup > while
    dup c@
    instr @ if
      dup [char] \ = if drop 1+ else [char] " = if 0 instr ! then then
    else
      dup [char] " = if drop push-int -1 instr ! else
      dup [char] 0 - 10 u< if [char] 0 - acc @ 10 * + acc ! -1 indig ! else drop push-int then then
    then 1+
  repeat 2drop push-int ;

\ Node store: kind and up to four integer fields per expression.
5 constant /nodec
8000000 constant max-nodes
max-nodes /nodec * cells allocate throw constant nodes
variable nnodes
24 constant hbits
1 hbits lshift constant hslots
hslots 1- constant hmask
hslots cells allocate throw constant htab
htab hslots cells erase

variable kind
: int@ ( i -- n ) cells ints + @ ;
\ key = kind, then up to 4 ints (excluding the "ie" index).
create key 5 cells allot
variable nkey
: build-key ( first-int-index count -- )
  kind @ key ! 4 min dup nkey ! 0 ?do dup i + int@ key i 1+ cells + ! loop drop
  nkey @ 1+ 5 swap ?do 0 key i cells + ! loop ;
: mix ( h x -- h' ) xor $9E3779B97F4A7C15 * dup 29 rshift xor ;
: key-hash ( -- h ) 0 5 0 do key i cells + @ mix loop ;
: node ( idx -- addr ) /nodec * cells nodes + ;
: key= ( idx -- f ) node key 5 cells tuck compare 0= ;
: hcons ( -- idx )
  key-hash hmask and
  begin
    1 probes +!
    dup cells htab + @ ?dup
  while
    1- dup key= if nip exit then drop
    1+ hmask and
  repeat
  nnodes @ >r key r@ node 5 cells move
  r@ 1+ swap cells htab + ! 1 nnodes +! 1 nnew +! r> ;

: classify ( addr u -- )
  \ first key starts at offset 2; "ie" first means kind from the second key
  drop dup 2 + c@ 8 lshift over 3 + c@ or
  dup [char] i 8 lshift [char] e or = if
    drop dup 2 + begin dup c@ [char] , <> while 1+ repeat 2 + c@ $10000 +
  then kind ! drop ;

: expr? ( -- f ) kind @ dup [char] i 8 lshift [char] n or <> swap [char] i 8 lshift [char] l or <> and ;
: ie-first? ( -- f ) kind @ $FFFF > ;
: line ( addr u -- )
  2dup classify 2dup scan-ints nip nbytes +!
  kind @ [char] { = if exit then   \ meta
  expr? 0= if exit then
  kind @ dup [char] a 8 lshift [char] p or = swap [char] f 8 lshift [char] o or = or
  kind @ [char] b 8 lshift [char] v or = or kind @ [char] c 8 lshift [char] o or = or
  0= if exit then  \ declarations are skipped; only expressions are hash-consed
  1 nexpr +!
  ie-first? if 1 nints @ 1- else 0 nints @ 1- then build-key hcons drop ;
: line2 ( addr u -- )
  2dup classify kind @ $FFFF > if 2dup scan-ints nip nbytes +! 1 nexpr +! 1 nints @ 1- build-key hcons drop exit then
  line ;

: run ( c-addr u -- )
  r/o open-file throw fid !
  begin line-buf /lbuf fid @ read-line throw while
    1 nlines +! line-buf swap line2
  repeat drop fid @ close-file throw ;

utime
next-arg run depth ." depth=" . cr
utime 2swap d- d>f 1e6 f/
." lines " nlines ? ." exprs " nexpr ? ." new-nodes " nnew ? ." probes " probes ? ." bytes " nbytes ? cr
." seconds " f. cr
bye
