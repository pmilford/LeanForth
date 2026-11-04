\ Unit tests of src/import/ndjson-emit.fs, the re-exporter. Lines fed one
\ at a time to the reader (export-line) come back as lean4export 3.1.0
\ writes them: lines in its bytes unchanged, for every record kind and
\ enumeration word; other spellings of the same records (white space, key
\ order, escapes) in its form. Every failure gives an outcome other than
\ ok and leaves no line. Every NDJSON export of the repository is then
\ re-exported in memory and must equal its file byte for byte, also with
\ BASE hexadecimal; and two planted faults, one member of one record kind
\ written with the wrong value or in the wrong order, are caught by those
\ files. tests/core/test_ndjson_emit.py does the same through files and
\ the command line, and reads every copy back. The module is loaded under
\ HEX, with the heap watched.
include ../support/tester.fs
include ../support/checks.fs
include ../support/heap-watch.fs
hex require ../../src/import/ndjson-emit.fs base @ decimal constant base-after-load

T{ base-after-load -> 16 }T
live-blocks @ constant blocks-at-start

\ Lines are fed from a writable copy; the output stays in memory (fid 0).
create line 4096 allot
: feed ( c-addr u -- outcome ) tuck line swap move line swap reexported export-line ;
variable mark
: marked ( -- ) reexport-pending nip mark ! ;
: since ( -- c-addr u ) reexport-pending mark @ /string ;
\ The output since the mark is c-addr u and a line feed.
: wrote? ( c-addr u -- flag )
  since dup 0= if 2drop 2drop false exit then
  2dup + 1- c@ 10 = >r 1- compare 0= r> and ;
: nothing? ( -- flag ) since nip 0= ;
\ Feed a line: whether it came back as itself, or as c-addr u.
: same ( c-addr u -- outcome flag ) 2dup marked feed >r wrote? r> swap ;
: becomes ( in-addr in-u out-addr out-u -- outcome flag ) 2swap marked feed >r wrote? r> swap ;
\ A line that fails: its outcome, and whether it left nothing behind.
: refused ( c-addr u -- outcome flag ) marked feed nothing? ;

: meta ( -- c-addr u )
  s\" {\"meta\":{\"exporter\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"},\"format\":{\"version\":\"3.1.0\"},\"lean\":{\"githash\":\"eb6cafb7290e8bd5f2937522d8d804f58f02bafc\",\"version\":\"4.35.0\"}}}" ;
: begun ( -- outcome )
  0 reexport-begin dup ok? if drop meta same swap ok? and flag>outcome then ;

\ Every kind of record, as the exporter writes it, comes back unchanged.
T{ begun reexport-lines@ -> outcome-ok 1 }T
T{ s\" {\"in\":1,\"str\":{\"pre\":0,\"str\":\"a\"}}" same -> outcome-ok true }T
T{ s\" {\"in\":2,\"num\":{\"i\":18446744073709551616,\"pre\":1}}" same -> outcome-ok true }T
T{ s\" {\"in\":3,\"str\":{\"pre\":1,\"str\":\"t\\u0009q\\\"b\\\\n\\nr\\r\\u0000\\u0008\\u000c\\u001f\x7f/ \xc3\xa9\xe2\x82\xac\xf0\x9f\x98\x80\"}}"
   same -> outcome-ok true }T
T{ s\" {\"il\":1,\"succ\":0}" same s\" {\"il\":2,\"param\":1}" same -> outcome-ok true outcome-ok true }T
T{ s\" {\"il\":3,\"max\":[1,2]}" same s\" {\"il\":4,\"imax\":[2,3]}" same
   -> outcome-ok true outcome-ok true }T
T{ s\" {\"ie\":0,\"sort\":4}" same s\" {\"bvar\":0,\"ie\":1}" same -> outcome-ok true outcome-ok true }T
T{ s\" {\"const\":{\"name\":1,\"us\":[1,2]},\"ie\":2}" same -> outcome-ok true }T
T{ s\" {\"const\":{\"name\":3,\"us\":[]},\"ie\":3}" same -> outcome-ok true }T
T{ s\" {\"app\":{\"arg\":1,\"fn\":2},\"ie\":4}" same -> outcome-ok true }T
T{ s\" {\"ie\":5,\"lam\":{\"binderInfo\":\"default\",\"body\":1,\"name\":1,\"type\":0}}" same
   -> outcome-ok true }T
T{ s\" {\"forallE\":{\"binderInfo\":\"implicit\",\"body\":1,\"name\":0,\"type\":0},\"ie\":6}" same
   -> outcome-ok true }T
T{ s\" {\"ie\":7,\"lam\":{\"binderInfo\":\"strictImplicit\",\"body\":1,\"name\":2,\"type\":0}}" same
   -> outcome-ok true }T
T{ s\" {\"forallE\":{\"binderInfo\":\"instImplicit\",\"body\":1,\"name\":3,\"type\":0},\"ie\":8}"
   same -> outcome-ok true }T
T{ s\" {\"ie\":9,\"letE\":{\"body\":1,\"name\":1,\"nondep\":true,\"type\":0,\"value\":4}}" same
   -> outcome-ok true }T
T{ s\" {\"ie\":10,\"letE\":{\"body\":1,\"name\":0,\"nondep\":false,\"type\":0,\"value\":4}}" same
   -> outcome-ok true }T
T{ s\" {\"ie\":11,\"proj\":{\"idx\":1,\"struct\":4,\"typeName\":1}}" same -> outcome-ok true }T
T{ s\" {\"ie\":12,\"natVal\":\"123456789012345678901234567890\"}" same -> outcome-ok true }T
T{ s\" {\"ie\":13,\"strVal\":\"tab\\u0009 nl\\n cr\\r esc\\u001b \\\"\\\\ \xf0\x9d\x94\xbd\"}" same
   -> outcome-ok true }T
T{ s\" {\"ie\":14,\"mdata\":{\"data\":{\"a\":\"Lean.DataValue.ofBool true\",\"b\":{\"x\":[1,true,null,false,\"\\u0009\"]}},\"expr\":4}}"
   same -> outcome-ok true }T
T{ s\" {\"axiom\":{\"isUnsafe\":true,\"levelParams\":[1],\"name\":1,\"type\":0}}" same
   -> outcome-ok true }T
T{ s\" {\"def\":{\"all\":[1],\"hints\":\"opaque\",\"levelParams\":[],\"name\":1,\"safety\":\"partial\",\"type\":0,\"value\":4}}"
   same -> outcome-ok true }T
T{ s\" {\"def\":{\"all\":[1,3],\"hints\":\"abbrev\",\"levelParams\":[1,3],\"name\":3,\"safety\":\"unsafe\",\"type\":0,\"value\":4}}"
   same -> outcome-ok true }T
T{ s\" {\"def\":{\"all\":[],\"hints\":{\"regular\":4294967295},\"levelParams\":[],\"name\":1,\"safety\":\"safe\",\"type\":0,\"value\":4}}"
   same -> outcome-ok true }T
T{ s\" {\"thm\":{\"all\":[1],\"levelParams\":[],\"name\":1,\"type\":0,\"value\":4}}" same
   -> outcome-ok true }T
T{ s\" {\"opaque\":{\"all\":[1],\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0,\"value\":4}}"
   same -> outcome-ok true }T
T{ s\" {\"quot\":{\"kind\":\"type\",\"levelParams\":[1],\"name\":1,\"type\":0}}" same
   -> outcome-ok true }T
T{ s\" {\"quot\":{\"kind\":\"ctor\",\"levelParams\":[1],\"name\":1,\"type\":0}}" same
   -> outcome-ok true }T
T{ s\" {\"quot\":{\"kind\":\"lift\",\"levelParams\":[1,3],\"name\":1,\"type\":0}}" same
   -> outcome-ok true }T
T{ s\" {\"quot\":{\"kind\":\"ind\",\"levelParams\":[1],\"name\":1,\"type\":0}}" same
   -> outcome-ok true }T
\ Inductive blocks: two types, two constructors and a recursor of two
\ rules; then a block without recursors, one without constructors, one
\ with neither.
: two-types ( -- c-addr u )
  s\" {\"inductive\":{\"ctors\":[{\"cidx\":0,\"induct\":1,\"isUnsafe\":false,\"levelParams\":[],\"name\":2,\"numFields\":0,\"numParams\":0,\"type\":0},{\"cidx\":1,\"induct\":3,\"isUnsafe\":true,\"levelParams\":[1],\"name\":3,\"numFields\":2,\"numParams\":1,\"type\":1}],\"recs\":[{\"all\":[1,3],\"isUnsafe\":false,\"k\":true,\"levelParams\":[1],\"name\":2,\"numIndices\":1,\"numMinors\":2,\"numMotives\":2,\"numParams\":0,\"rules\":[{\"ctor\":2,\"nfields\":0,\"rhs\":4},{\"ctor\":3,\"nfields\":2,\"rhs\":5}],\"type\":0}],\"types\":[{\"all\":[1,3],\"ctors\":[2],\"isRec\":false,\"isReflexive\":true,\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"numIndices\":0,\"numNested\":1,\"numParams\":0,\"type\":0},{\"all\":[1,3],\"ctors\":[3],\"isRec\":true,\"isReflexive\":false,\"isUnsafe\":true,\"levelParams\":[1],\"name\":3,\"numIndices\":2,\"numNested\":0,\"numParams\":1,\"type\":1}]}}" ;
T{ two-types same reexport-lines@ -> outcome-ok true 34 }T
T{ s\" {\"inductive\":{\"ctors\":[{\"cidx\":0,\"induct\":1,\"isUnsafe\":false,\"levelParams\":[],\"name\":2,\"numFields\":0,\"numParams\":0,\"type\":0}],\"recs\":[],\"types\":[{\"all\":[1],\"ctors\":[2],\"isRec\":false,\"isReflexive\":false,\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"numIndices\":0,\"numNested\":0,\"numParams\":0,\"type\":0}]}}"
   same -> outcome-ok true }T
T{ s\" {\"inductive\":{\"ctors\":[],\"recs\":[{\"all\":[1],\"isUnsafe\":false,\"k\":false,\"levelParams\":[],\"name\":2,\"numIndices\":0,\"numMinors\":0,\"numMotives\":1,\"numParams\":0,\"rules\":[],\"type\":0}],\"types\":[{\"all\":[1],\"ctors\":[],\"isRec\":false,\"isReflexive\":false,\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"numIndices\":0,\"numNested\":0,\"numParams\":0,\"type\":0}]}}"
   same -> outcome-ok true }T
T{ s\" {\"inductive\":{\"ctors\":[],\"recs\":[],\"types\":[{\"all\":[1],\"ctors\":[],\"isRec\":false,\"isReflexive\":false,\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"numIndices\":0,\"numNested\":0,\"numParams\":0,\"type\":0}]}}"
   same -> outcome-ok true }T

\ Other spellings of the same records come back in the exporter's form:
\ no white space, keys in order, Lean's escapes, the same numbers.
T{ s\" { \"in\" : 4 , \"str\" : { \"str\" : \"x\" , \"pre\" : 0 } }"
   s\" {\"in\":4,\"str\":{\"pre\":0,\"str\":\"x\"}}" becomes -> outcome-ok true }T
T{ s\" {\"ie\":15,\"app\":{\"fn\":2,\"arg\":1}}" s\" {\"app\":{\"arg\":1,\"fn\":2},\"ie\":15}"
   becomes -> outcome-ok true }T
T{ s\" {\"ie\":16,\"strVal\":\"\\t\\b\\f\\/\\u00e9\\u20AC\\ud83d\\ude00\\u007f\\u0041\"}"
   s\" {\"ie\":16,\"strVal\":\"\\u0009\\u0008\\u000c/\xc3\xa9\xe2\x82\xac\xf0\x9f\x98\x80\x7fA\"}"
   becomes -> outcome-ok true }T
T{ s\" {\"il\":5,\"max\":[ 1 , 4 ]}" s\" {\"il\":5,\"max\":[1,4]}" becomes -> outcome-ok true }T
T{ s\" {\"thm\":{\"value\":4,\"type\":0,\"name\":1,\"levelParams\":[],\"all\":[1]}}"
   s\" {\"thm\":{\"all\":[1],\"levelParams\":[],\"name\":1,\"type\":0,\"value\":4}}"
   becomes -> outcome-ok true }T
T{ s\" {\"ie\":17,\"mdata\":{\"expr\":4,\"data\":{\"k\":[ 1, -0, {} ]}}}"
   s\" {\"ie\":17,\"mdata\":{\"data\":{\"k\":[1,0,{}]},\"expr\":4}}" becomes -> outcome-ok true }T
T{ reexport-end reexport-lines@ -> outcome-ok 43 }T

\ Failures never give ok and leave nothing behind; the first one stays,
\ and every later record is refused. mdata's data with keys out of order
\ cannot be written in the exporter's form (it cannot have written it).
: sorted-in ( -- outcome ) s\" {\"ie\":0,\"sort\":0}" feed ;
T{ begun sorted-in -> outcome-ok outcome-ok }T
T{ s\" {\"ie\":1,\"mdata\":{\"data\":{\"b\":1,\"a\":2},\"expr\":0}}" refused
   -> outcome-invalid true }T
T{ s\" {\"ie\":1,\"sort\":0}" refused emit-status -> outcome-invalid true outcome-invalid }T
T{ reexport-end reexport-lines@ -> outcome-invalid 2 }T
\ A key longer than the writer's key pool is full.
create long-line 5100 allot
: long-start ( -- c-addr u ) s\" {\"ie\":1,\"mdata\":{\"data\":{\"" ;
: long-end ( -- c-addr u ) s\" \":0},\"expr\":0}}" ;
: long-key ( -- c-addr u )
  long-start tuck long-line swap move  long-line over + 5000 [char] k fill
  5000 + long-end rot long-line + swap dup >r move long-line r> 5000 + long-start nip + ;
: feed-long ( c-addr u -- outcome ) marked reexported export-line ;
T{ begun sorted-in long-key feed-long nothing? -> outcome-ok outcome-ok outcome-full true }T
\ A malformed line is the reader's failure; nothing is written for it.
T{ begun s\" {\"ie\":0,\"sort\":1}" refused -> outcome-ok outcome-invalid true }T
\ A code outside an enumeration, given by a handler that changes its
\ record first, is invalid: binder information, safety, quotient kind and
\ hints in turn.
: wrong ( record field-xt -- record ) over swap execute 9 swap ! ;
: bad-binder ( record -- outcome ) ['] binder-info wrong emit-record ;
: bad-safety ( record -- outcome ) ['] decl-safety wrong emit-record ;
: bad-quot ( record -- outcome ) ['] decl-quot-kind wrong emit-record ;
: bad-hints ( record -- outcome ) ['] decl-hints wrong emit-record ;
: with-handler ( xt kind -- ) reexported export-handler ! ;
: lam-in ( -- c-addr u ) s\" {\"ie\":1,\"lam\":{\"binderInfo\":\"default\",\"body\":0,\"name\":0,\"type\":0}}" ;
T{ begun sorted-in ' bad-binder kind-lam with-handler lam-in refused
   -> outcome-ok outcome-ok outcome-invalid true }T
: def-in ( -- c-addr u ) s\" {\"def\":{\"all\":[],\"hints\":\"abbrev\",\"levelParams\":[],\"name\":0,\"safety\":\"safe\",\"type\":0,\"value\":0}}" ;
T{ begun sorted-in ' bad-safety kind-def with-handler def-in refused
   -> outcome-ok outcome-ok outcome-invalid true }T
T{ begun sorted-in ' bad-hints kind-def with-handler def-in refused
   -> outcome-ok outcome-ok outcome-invalid true }T
T{ begun sorted-in ' bad-quot kind-quot with-handler
   s\" {\"quot\":{\"kind\":\"ind\",\"levelParams\":[],\"name\":0,\"type\":0}}" refused
   -> outcome-ok outcome-ok outcome-invalid true }T
\ No line may start while a block is unfinished, no element may come
\ outside a block, and no re-export may end inside one.
T{ begun 1 reexporter reexport-left ! sorted-in -> outcome-ok outcome-invalid }T
T{ begun reexported export-record ctor-line -> outcome-ok outcome-invalid }T
T{ begun 1 reexporter reexport-left ! reexport-end -> outcome-ok outcome-invalid }T
\ A file that cannot be read, and one that cannot be written (a file
\ opened read-only): no output, and full.
T{ s" tests/core/no-such-export.ndjson" 0 reexport-file -> outcome-invalid }T
s" tests/reference/identity.ndjson" r/o bin open-file throw constant read-only
T{ s" tests/reference/identity.ndjson" read-only reexport-file -> outcome-full }T
T{ read-only close-file -> 0 }T

\ Buffers grow by doubling, and refuse to pass their limit, unchanged.
create spare /buffer allot  spare /buffer erase
T{ s" abc" spare buffer-append spare buffer-size @ spare buffer-text s" abc" compare
   -> true reexport-buffer-start 0 }T
T{ reexport-buffer-limit spare buffer-grow spare buffer-size @ spare buffer-used @
   -> false reexport-buffer-start 3 }T
T{ reexport-buffer-start spare buffer-grow spare buffer-size @ spare buffer-used @
   -> true reexport-buffer-start 2* 3 }T
T{ spare buffer-release spare buffer-addr @ spare buffer-size @ -> 0 0 }T

\ Every NDJSON export of the repository comes back byte for byte, in
\ memory, and the same with BASE hexadecimal.
: file-bytes ( c-addr u -- addr u )
  r/o bin open-file throw >r r@ file-size throw drop dup allocate throw swap
  2dup r@ read-file throw over <> abort" short read" r> close-file throw ;
: same-file? ( c-addr u -- outcome flag )
  2dup 0 reexport-file >r file-bytes 2dup reexport-pending compare 0= >r drop free throw
  r> r> swap ;
T{ s" tests/reference/composition.ndjson" same-file? -> outcome-ok true }T
T{ s" tests/reference/constant-fixture.ndjson" same-file? -> outcome-ok true }T
T{ s" tests/reference/identity.ndjson" same-file? -> outcome-ok true }T
T{ s" tests/reference/poly-identity.ndjson" same-file? -> outcome-ok true }T
T{ s" tests/reference/type-identity.ndjson" same-file? -> outcome-ok true }T
T{ s" tests/core/ndjson-block.ndjson" same-file? -> outcome-ok true }T
T{ s" tests/core/check-declaration-cases/composition-literal.ndjson" same-file?
   -> outcome-ok true }T
T{ s" tests/core/check-declaration-cases/composition-loose.ndjson" same-file?
   -> outcome-ok true }T
T{ s" tests/core/check-declaration-cases/composition-postulate.ndjson" same-file?
   -> outcome-ok true }T
T{ s" tests/core/check-declaration-cases/composition-wrong-argument.ndjson" same-file?
   -> outcome-ok true }T
T{ s" tests/core/reexport/kinds.ndjson" same-file? reexport-lines@ -> outcome-ok true 1390 }T
T{ hex s" tests/core/reexport/kinds.ndjson" same-file? decimal -> outcome-ok true }T

\ Planted faults, each in one member of one record kind, are caught: an
\ application's arguments swapped (the bytes differ, first at the
\ composition's line 27) and its keys in the wrong order (the writer's
\ order check refuses the line).
' app-line >body constant app-form
app-form form-value @ constant app-writer
: swapped-app ( record -- )
  emit-open dup app-fn s" arg" u-member app-arg s" fn" u-member emit-close ;
: misordered-app ( record -- )
  emit-open dup app-fn s" fn" u-member app-arg s" arg" u-member emit-close ;
: plant ( xt -- ) app-form form-value ! ;
\ The line of the first byte where the output differs from c-addr u.
: first-line ( c-addr u -- n )
  1 -rot reexport-pending rot min 0 ?do
    over i + c@ over i + c@ 2dup <> if 2drop 2drop unloop exit then
    drop 10 = if rot 1+ -rot then
  loop 2drop ;
: composition ( -- c-addr u ) s" tests/reference/composition.ndjson" ;
T{ ' swapped-app plant composition same-file? -> outcome-ok false }T
T{ composition file-bytes 2dup first-line >r drop free throw r> -> 27 }T
T{ ' misordered-app plant composition 0 reexport-file reexported export-at @ -> outcome-invalid 27 }T
T{ app-writer plant composition same-file? -> outcome-ok true }T

T{ reexport-free live-blocks @ blocks-at-start - -> 0 }T
cases-done
bye
