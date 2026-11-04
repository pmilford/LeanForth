\ Interned lists of 32-bit numbers and interned texts (ADR 0016 C2): two
\ classes of hash-consed sets (cons.fs), so that equal lists, and equal
\ texts, get one number, in one tier or across an input tier and a scratch
\ tier over it. A general tool with no Lean knowledge; untrusted. The Lean
\ store uses them for universe-argument and parameter lists and for
\ literals.
\
\ Tuples. A tuple is a list of numbers 0 .. 2^32-1 of any length, kept as
\ consecutive 32-bit fields [n] [item 1] .. [item n]; its number is the
\ position of [n] among the set's fields. There is no fixed limit on its
\ length (plan task 6.2.0) beyond the set's room. A tuple is built in
\ steps at the set's free end: tuple-start, then tuple-add per item, then
\ tuple-end, which gives an equal tuple's number or keeps the new one.
\ Only one tuple of a set is built at a time; any other change to the set
\ in between (a rollback or reset) abandons it, and tuple-add or
\ tuple-end then give invalid.
\
\ Texts. A text is any byte string of at most 2^32-1 bytes, kept once in
\ the set's byte slab; a record of two fields gives its offset and length.
\
\ Outcomes: ok; full when a limit is reached or the heap has no room;
\ invalid for a sealed or corrupted set, a tuple step out of order, or an
\ item beyond 32 bits. Accessors are unchecked: give them numbers this
\ module gave, or check them with cons-entry?.
\
\ Example: two equal lists get one number.
\   create lists /cons allot   4 tuple-class lists cons-init drop
\   : pair ( a b -- t ) lists tuple-start drop swap lists tuple-add drop
\     lists tuple-add drop lists tuple-end drop ;
\   7 9 pair 7 9 pair = .                 \ -1, true
\   7 9 pair dup lists tuple-length . 1 swap lists tuple-item .   \ 2 9
\
\ Interface: tuple-class tuple-start tuple-add tuple-end tuple-length
\ tuple-item text-class text-intern text@. State: the two classes, made
\ while loading and read-only afterwards. Loads in decimal whatever BASE
\ is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./portability.fs
require ./outcome.fs
require ./u32.fs
require ./hash32.fs
require ./cons.fs
require ./module.fs

lf-lib-private module-open

\ Tuples: one unit is one 32-bit field.
lf-lib set-current
1 u32s cons-numbers-max cons-class: tuple-class
\ Unchecked: the length of tuple t, and its item i (from 0).
: tuple-length ( t cons -- n ) cons-at u32@ ;
: tuple-item ( i t cons -- u ) cons-at swap 1+ u32s + u32@ ;
lf-lib-private set-current
: tuple-hash ( addr -- h )
  dup u32@ dup hash-fmix swap 0 ?do over i 1+ u32s + u32@ hash-step loop nip ;
\ Two tuples are equal when their fields are: COMPARE of the characters is
\ exact, since the same u32! wrote both, whatever its byte order.
: tuple= ( addr1 addr2 -- flag )
  over u32@ over u32@ <> if 2drop false exit then over u32@ 1+ u32s tuck compare 0= ;
: tuple-rehash ( n cons -- h ) cons-at tuple-hash ;
: tuple-same ( n key cons -- flag ) rot swap cons-at swap cons-top tuple= ;
\ The fields of the tuple at local: its length plus one, saturating at
\ u32-mask, so that a corrupted length never wraps on a 32-bit host.
: tuple-span ( local cons -- units )
  cons-records slab-at u32@ dup u32-mask <> if 1+ then ;
' tuple-rehash ' tuple-same ' tuple-span tuple-class cons-hooks!

\ The candidate's length so far, and its next item.
: tuple-count ( cons -- n ) cons-top u32@ ;
: tuple-item! ( u cons -- ) cons-top dup u32@ 1+ 2dup swap u32! u32s + u32! ;
: tuple-step? ( cons -- flag ) cons-building @ ;
: tuple-wide? ( u -- flag ) u32-mask u> ;
lf-lib set-current
\ Start a tuple: ok, or the outcome of cons-room.
: tuple-start ( cons -- outcome )
  >r 1 0 r@ cons-room dup ok? if 0 r@ cons-top u32! true r@ cons-building ! then r> drop ;
\ Add an item: ok, full, or invalid out of order or for u beyond 32 bits.
: tuple-add ( u cons -- outcome )
  dup tuple-step? 0= if 2drop outcome-invalid exit then
  over tuple-wide? if 2drop outcome-invalid exit then
  >r r@ tuple-count 2 + 0 r@ cons-room ok-then? if r@ tuple-item! outcome-ok then
  r> drop ;
lf-lib-private set-current
: tuple-keep ( i cons -- t outcome ) >r r@ tuple-count 1+ swap r> cons-commit ;
lf-lib set-current
\ End the tuple: its number (an equal tuple's, which may be the under
\ set's) and ok; or -1 and full, or invalid out of order. The tuple is
\ ended either way, except when cons-room fails, which leaves it open.
: tuple-end ( cons -- t outcome )
  dup tuple-step? 0= if drop outcome-invalid no-result exit then
  >r 1 0 r@ cons-room dup ok? 0= if r> drop no-result exit then drop
  false r@ cons-building ! r@ cons-top tuple-hash true r@ cons-find
  if r> drop outcome-ok else r> tuple-keep then ;
lf-lib-private set-current

\ Texts: one unit is two 32-bit fields, offset and length.
lf-lib set-current
2 u32s cons-numbers-max cons-class: text-class
\ Unchecked: the bytes of text t.
: text@ ( t cons -- addr u )
  2dup cons-at dup u32@ swap 1 u32s + u32@ >r -rot cons-text-at r> ;
lf-lib-private set-current
: text-rehash ( n cons -- h ) text@ hash-bytes ;
: text-same ( n key cons -- flag ) rot swap text@ rot cons-key 2@ compare 0= ;
: text-span ( local cons -- units ) 2drop 1 ;
' text-rehash ' text-same ' text-span text-class cons-hooks!
: text-record! ( offset length addr -- ) tuck 1 u32s + u32! u32! ;
\ Keep the key's text as a new text: the record first (at the class's
\ limit it is full), then the bytes, whose offset goes into the record.
: text-place ( t cons -- )
  >r r@ cons-key 2@ r@ cons-text, r@ cons-key @ rot r> cons-at text-record! ;
: text-keep ( i cons -- t outcome )
  >r 1 swap r@ cons-commit dup ok? if drop dup r@ text-place outcome-ok then r> drop ;
lf-lib set-current
\ The number of the text addr u (an equal text's, which may be the under
\ set's) and ok; or -1 and full or invalid. The text may lie anywhere,
\ even in the set's own byte slab, which may move while room is made: its
\ address is found again (cons-room-key).
: text-intern ( addr u cons -- t outcome )
  >r r@ cons-key! 1 r@ cons-room-key dup ok? 0= if r> drop no-result exit then drop
  r@ cons-key 2@ hash-bytes true r@ cons-find
  if r> drop outcome-ok else r> text-keep then ;

module-close
base !   \ the BASE this file was loaded with
