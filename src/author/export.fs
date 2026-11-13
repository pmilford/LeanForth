\ LeanForth text to the kernel (plan task 8.2.1c; ADR 0017 Amendment 1,
\ A1 and A3, and its Amendment 2): the theorems, definitions and axioms an
\ authoring run made (runner.fs), written as the records of a Lean export
\ in lean4export's format 3.1.0, one line at a time, to a sink. The
\ command line's sink hands each line to the importer stage
\ (import/stage.fs, stage-produce), which reads it as it reads Lean's own
\ exports, so the terms the words built reach the kernel by the path every
\ export takes: staged, fed and checked by check-declaration, the verdicts
\ printed from the published slots (cli/check-lf.fs). Untrusted, like the
\ words: a wrong record is a different claim, which the checker checks as
\ it is, and the stage checks every record's shape.
\
\ The lines: a metadata record naming LeanForth as the exporter (the stage
\ takes it only when asked to read other exporters, stage-any-version!);
\ every name of the run's name store but the anonymous one, in ID order, a
\ name's export index its ID; every level but zero and every term node but
\ a projection's leaf, in store order, numbered from 1 and from 0 (the
\ stores only append, so a node's parts come before it and every record
\ names earlier ones only); then each theorem, definition and axiom in the
\ order it ended, with its universe parameters, type and value. A
\ definition's hints are regular with Lean's height (getMaxHeight): one
\ more than the greatest height of a definition its value names, the
\ file's own or the library's (lfa-decl-height). Import stubs and library
\ constants are not written: a checked run refuses stubs (library.fs), and
\ the library's declarations are in its own export. Binder names and kinds
\ come from the presentation side table, as the words recorded them; Lean's
\ kernel ignores them. Each line is one JSON text of lib/json-write.fs,
\ which refuses bytes that are not UTF-8, with each object's keys in
\ Lean's order (sorted; the writer's sorted mode refuses any other) and
\ the names' strings escaped as Lean's Json.compress escapes them.
\
\ Same format, not the same bytes (review L1; ADR 0017 Amendment 2): each
\ record has the form and key order of the pinned exporter's, but the
\ numbering differs. lean4export writes names, levels and expressions as
\ it first meets them, declaration by declaration, one record for equal
\ nodes; here they come store by store, and nodes the term store keeps
\ apart (binders are never shared) get records of their own. The metadata
\ names LeanForth as the exporter and no Lean build ("githash": "none").
\ So a declaration means exactly what Lean's export of the same source
\ means (tests/author/check_author.py compares every fixture's records
\ with pinned Lean's export, record for record), but the file differs.
\
\ lf-author-export ( sink -- outcome ): sink ( c-addr u -- outcome ) is
\ given each line, without its line feed. The first outcome that is not ok
\ stops the writing and is returned: the sink's; the JSON writer's (full
\ for a line longer than lfx-line-capacity, invalid for a name that is not
\ UTF-8); full for no heap for the numbering tables; unsupported for a node
\ no record holds (none the words build). Example, with a sink that types:
\   : show ( c-addr u -- outcome ) type cr outcome-ok ;
\   lf-author-begin s" theorem t Prop explicit: p p := p end t" lf-author-text drop
\   ' show lf-author-export .   \ the export's lines, then 0 (ok)
\ State: one context record, lfx (the sink, the outcome so far, the JSON
\ writer, the line being built and the addresses of the numbering tables,
\ heap blocks freed before lf-author-export returns).

require ../lib/lib.fs
require ../lib/bytes.fs
require ../lib/json-write.fs
require ../core/terms.fs
require ../core/levels.fs
require ../core/names.fs
require ../core/literals.fs
require ../core/projections.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/tagged-sort-boundary.fs
require ../present/binder-table.fs
require ./constants.fs

4096 constant lfx-line-capacity
4 constant lfx-depth   \ objects and arrays open at once: {"thm":{"all":[...]}}
64 constant lfx-key-room   \ the open objects' last keys, for the sorted mode

begin-structure /lfx
  field: lfx-sink           \ xt ( c-addr u -- outcome )
  field: lfx-outcome        \ ok, or the first refusal
  field: lfx-expr-table     \ heap: per term node, its expression number, or -1
  field: lfx-level-table    \ heap: per level, its level number
  field: lfx-height-table   \ heap: per declaration, a definition's height
  field: lfx-mark-table     \ heap: per term node, a cell: reached from a value
  field: lfx-length         \ bytes of the line built so far
  lfx-depth lfx-key-room jw-size +field lfx-writer
  lfx-line-capacity +field lfx-line
end-structure
/lfx context-record: lfx
: lfx-w ( -- writer ) lfx lfx-writer ;
\ Lean's key order and string escapes (review S7); a line's limit.
: lfx-setup ( -- )
  lfx-depth lfx-key-room lfx-w jw-init drop lfx-line-capacity lfx-w jw-limit !
  true lfx-w jw-sorted ! true lfx-w jw-lean ! ;
' lfx-setup context-setup

\ The outcome so far: the first refusal stays.
: lfx-ok? ( -- flag ) lfx lfx-outcome @ ok? ;
: lfx-refuse ( outcome -- ) lfx-ok? if lfx lfx-outcome ! else drop then ;

\ A line: one JSON text into the line buffer (the writer's limit keeps it
\ inside), then to the sink, unless something was refused.
: lfx-append ( c-addr u -- )
  tuck lfx lfx-line lfx lfx-length @ + swap move lfx lfx-length +! ;
: lfx-begin ( -- ) 0 lfx lfx-length ! ['] lfx-append lfx-w jw-start ;
: lfx-sent ( -- outcome ) lfx lfx-line lfx lfx-length @ lfx lfx-sink @ execute ;
: lfx-emit ( -- ) lfx-w jw-end lfx-refuse lfx-ok? if lfx-sent lfx-refuse then ;
\ JSON values: objects, keys, numbers, strings, number members.
: lfx-open ( -- ) lfx-w jw-open-object ;
: lfx-close ( -- ) lfx-w jw-close-object ;
: lfx-key ( c-addr u -- ) lfx-w jw-key ;
: lfx-u ( u -- ) lfx-w jw-u ;
: lfx-member ( u c-addr u -- ) lfx-key lfx-u ;
: lfx-inner ( c-addr u -- ) lfx-key lfx-open ;
: lfx-record ( u c-addr u -- ) lfx-begin lfx-open lfx-member ;

\ The numbering tables: a cell per term node, level and declaration.
: lfx-cell ( i table -- addr ) @ swap cells + ;
: lfx-expr# ( term -- n ) lfx lfx-expr-table lfx-cell @ ;
: lfx-expr! ( n term -- ) lfx lfx-expr-table lfx-cell ! ;
: lfx-level# ( level -- n ) lfx lfx-level-table lfx-cell @ ;
: lfx-level! ( n level -- ) lfx lfx-level-table lfx-cell ! ;
: lfx-height@ ( i -- h ) lfx lfx-height-table lfx-cell @ ;
: lfx-height! ( h i -- ) lfx lfx-height-table lfx-cell ! ;
: lfx-block ( u addr -- flag ) swap 1 max allocate if drop 0 then dup rot ! 0<> ;
: lfx-tables ( -- flag )
  lf-term-count @ cells dup lfx lfx-expr-table lfx-block
  lf-level-count @ cells lfx lfx-level-table lfx-block and
  lfa-decl-count cells lfx lfx-height-table lfx-block and
  swap lfx lfx-mark-table lfx-block and ;
: lfx-free ( -- )
  lfx lfx-expr-table heap-release lfx lfx-level-table heap-release
  lfx lfx-height-table heap-release lfx lfx-mark-table heap-release ;

\ The metadata: LeanForth's words wrote the records, in format 3.1.0, by
\ the rules of the pinned Lean.
: lfx-text ( c-addr u key-addr key-u -- ) lfx-key lfx-w jw-string ;
: lfx-version ( c-addr u -- ) s" version" lfx-text ;
: lfx-exporter ( -- )
  s" exporter" lfx-inner s" leanforth" s" name" lfx-text s" 0.1.0-dev" lfx-version
  lfx-close ;
: lfx-lean ( -- )
  s" lean" lfx-inner s" none" s" githash" lfx-text s" 4.35.0" lfx-version lfx-close ;
: lfx-meta ( -- )
  lfx-begin lfx-open s" meta" lfx-inner lfx-exporter
  s" format" lfx-inner s" 3.1.0" lfx-version lfx-close lfx-lean lfx-close lfx-close
  lfx-emit ;

\ Names: {"in":ID,"str":{"pre":P,"str":"text"}} or {"in":ID,"num":{"i":N,"pre":P}}.
: lfx-name-str ( id -- )
  s" str" lfx-inner dup lf-name-prefix@ s" pre" lfx-member lf-name-text s" str" lfx-text ;
: lfx-name-num ( id -- )
  s" num" lfx-inner dup lf-name-payload s" i" lfx-member
  lf-name-prefix@ s" pre" lfx-member ;
: lfx-name ( id -- )
  dup s" in" lfx-record
  dup lf-name-tag@ lf-name-tag-num = if lfx-name-num else lfx-name-str then
  lfx-close lfx-close lfx-emit ;
: lfx-names ( -- ) lf-name-count @ 1 ?do i lfx-name loop ;

\ Levels: {"il":N,"succ":L}, "max":[A,B], "imax":[A,B] or "param":NAME.
\ Every zero is level 0, which the format never writes.
: lfx-pair ( slot c-addr u -- )
  lfx-key lfx-w jw-open-array dup node-first @ lfx-level# lfx-u
  node-second @ lfx-level# lfx-u lfx-w jw-close-array ;
\ Two CASEs, one arm per tag written (zero never is); any other tag is
\ refused (unsupported), never written as another level (review S6).
: lfx-binary-level ( slot -- )
  dup node-tag @ case lf-level-tag-max of s" max" lfx-pair endof
    lf-level-tag-imax of s" imax" lfx-pair endof
    nip outcome-unsupported lfx-refuse endcase ;
: lfx-level-body ( slot -- )
  dup node-tag @ case
    lf-level-tag-succ of node-first @ lfx-level# s" succ" lfx-member endof
    lf-level-tag-param of node-first @ s" param" lfx-member endof
    >r lfx-binary-level r> endcase ;
: lfx-zero? ( level -- flag ) lf-level-slot node-tag @ lf-level-tag-zero = ;
: lfx-level-line ( n slot -- ) swap s" il" lfx-record lfx-level-body lfx-close lfx-emit ;
: lfx-level ( next level -- next' )
  dup lfx-zero? if 0 swap lfx-level! exit then
  2dup lfx-level! lf-level-slot over swap lfx-level-line 1+ ;
: lfx-levels ( -- ) 1 lf-level-count @ 0 ?do i lfx-level loop drop ;

\ Expressions: {"ie":N, then the node's own member}. A reference to a
\ projection's leaf, which no record holds, is refused (unsupported; the
\ words never make one, values.fs), never written as a number.
: lfx-expr-ref ( term -- n ) lfx-expr# dup 0< if outcome-unsupported lfx-refuse then ;
: lfx-ref ( term c-addr u -- ) rot lfx-expr-ref 0 max -rot lfx-member ;
: lfx-sort ( term -- ) lf-term-first@ lfx-level# s" sort" lfx-member ;
: lfx-bvar ( term -- ) lf-term-first@ s" bvar" lfx-member ;
: lfx-app ( term -- )
  s" app" lfx-inner dup lf-term-second@ s" arg" lfx-ref lf-term-first@ s" fn" lfx-ref
  lfx-close ;
: lfx-info ( kind -- c-addr u )
  case lf-binder-implicit of s" implicit" endof
    lf-binder-strict of s" strictImplicit" endof
    lf-binder-instance of s" instImplicit" endof s" default" rot endcase ;
: lfx-naming ( term -- name kind ) lf-pres-binder@ 0= if 0 lf-binder-default then ;
: lfx-binder ( term c-addr u -- )
  lfx-inner dup lfx-naming lfx-info s" binderInfo" lfx-text
  over lf-term-second@ s" body" lfx-ref s" name" lfx-member
  lf-term-first@ s" type" lfx-ref lfx-close ;
: lfx-levels-of ( addr count -- )
  s" us" lfx-key lfx-w jw-open-array
  0 ?do dup i lf-cref-pair@ drop lfx-level# lfx-u loop drop lfx-w jw-close-array ;
: lfx-const ( term -- )
  s" const" lfx-inner lf-term-first@ lf-cref-slot
  dup lf-cref-name@ drop s" name" lfx-member lf-cref-pairs lfx-levels-of lfx-close ;
: lfx-digits ( u -- c-addr u ) base @ >r decimal 0 <# #s #> r> base ! ;
: lfx-lit ( term -- ) lf-lit-cell lfx-digits s" natVal" lfx-text ;
: lfx-proj ( term -- )
  s" proj" lfx-inner dup lf-proj-leaf lf-proj-idx s" idx" lfx-member
  dup lf-proj-struct s" struct" lfx-ref lf-proj-leaf lf-proj-name s" typeName" lfx-member
  lfx-close ;
\ Two CASEs, one arm per tag the words build.
: lfx-other ( term tag -- )
  case lf-tag-constant of lfx-const endof lf-tag-lit of lfx-lit endof
    lf-tag-projection of lfx-proj endof
    >r drop outcome-unsupported lfx-refuse r> endcase ;
: lfx-body ( term -- )
  dup lf-term-tag@ case
    lf-tag-symbolic-sort of lfx-sort endof lf-tag-bvar of lfx-bvar endof
    lf-tag-app of lfx-app endof lf-tag-lam of s" lam" lfx-binder endof
    lf-tag-pi of s" forallE" lfx-binder endof  dup >r lfx-other r> endcase ;
\ Lean's key order: the members app, bvar, const and forallE come before
\ "ie", the others after it.
lf-tag-app lf-tag-bit lf-tag-bvar lf-tag-bit or lf-tag-constant lf-tag-bit or
  lf-tag-pi lf-tag-bit or constant lfx-before-ie
: lfx-ie-last? ( term -- flag ) lf-term-tag@ lf-tag-bit lfx-before-ie and 0<> ;
: lfx-ie ( n -- ) s" ie" lfx-member ;
: lfx-expr-members ( n term -- )
  dup lfx-ie-last? if lfx-body lfx-ie else swap lfx-ie lfx-body then ;
: lfx-expr-line ( n term -- ) lfx-begin lfx-open lfx-expr-members lfx-close lfx-emit ;
\ A projection's leaf is no expression of its own: the projection holds it.
: lfx-expr ( next term -- next' )
  dup lf-term-tag@ lf-tag-proj = if -1 swap lfx-expr! exit then
  2dup lfx-expr! over swap lfx-expr-line 1+ ;
: lfx-exprs ( -- ) 0 lf-term-count @ 0 ?do i lfx-expr loop drop ;

\ Heights (Lean's getMaxHeight): the nodes a value reaches are marked in
\ one sweep down from it, as a node's parts come before it; each constant
\ reached brings the height of the definition it names.
: lfx-mark ( term -- ) true swap lfx lfx-mark-table lfx-cell ! ;
: lfx-marked? ( term -- flag ) lfx lfx-mark-table lfx-cell @ ;
: lfx-unmark ( -- ) lfx lfx-mark-table @ lf-term-count @ cells erase ;
: lfx-decl-height ( i -- h )
  dup lfa-library? if lfa-decl lfa-decl-height @ exit then
  dup lfa-decl-kind lf-decl-def = if lfx-height@ else drop 0 then ;
: lfx-named-height ( name -- h ) lfa-decl-find if lfx-decl-height else 0 then ;
: lfx-const-height ( term -- h )
  lf-term-first@ lf-cref-slot lf-cref-name@ drop lfx-named-height ;
: lfx-binary? ( term -- flag ) lf-term-tag@ lf-tag-bit lf-binary-tags and 0<> ;
: lfx-visit ( h term -- h' )
  dup lfx-binary? if dup lf-term-first@ lfx-mark lf-term-second@ lfx-mark exit then
  dup lf-term-tag@ lf-tag-constant = if lfx-const-height max else drop then ;
: lfx-reached ( h term -- h' ) dup lfx-marked? if lfx-visit else drop then ;
: lfx-sweep ( h top -- h' ) 0 swap do i lfx-reached -1 +loop ;
: lfx-value-height ( value -- h ) lfx-unmark dup lfx-mark 0 swap lfx-sweep 1+ ;

\ Declarations: {"thm":{...}}, {"def":{...}}, {"axiom":{...}}.
: lfx-params ( decl -- )
  s" levelParams" lfx-key lfx-w jw-open-array dup lf-fdecl-universe
  swap lf-fdecl-universes @ 0 ?do dup i cells + @ lfx-u loop drop lfx-w jw-close-array ;
: lfx-all ( decl -- )
  s" all" lfx-key lfx-w jw-open-array lf-fdecl-name @ lfx-u lfx-w jw-close-array ;
: lfx-head ( decl -- ) dup lfx-params lf-fdecl-name @ s" name" lfx-member ;
: lfx-typed ( decl -- ) lf-fdecl-type @ s" type" lfx-ref ;
: lfx-valued ( decl -- ) lf-fdecl-value @ s" value" lfx-ref ;
: lfx-decl-open ( c-addr u -- ) lfx-begin lfx-open lfx-inner ;
: lfx-decl-close ( -- ) lfx-close lfx-close lfx-emit ;
: lfx-thm ( decl -- )
  s" thm" lfx-decl-open dup lfx-all dup lfx-head dup lfx-typed lfx-valued lfx-decl-close ;
: lfx-axiom ( decl -- )
  s" axiom" lfx-decl-open false s" isUnsafe" lfx-key lfx-w jw-bool dup lfx-head lfx-typed
  lfx-decl-close ;
: lfx-hints ( height -- ) s" hints" lfx-inner s" regular" lfx-member lfx-close ;
: lfx-def ( height decl -- )
  s" def" lfx-decl-open dup lfx-all swap lfx-hints dup lfx-head
  s" safe" s" safety" lfx-text dup lfx-typed lfx-valued lfx-decl-close ;
: lfx-definition ( i -- )
  dup lfa-decl lf-fdecl-value @ lfx-value-height 2dup swap lfx-height!
  swap lfa-decl lfx-def ;
\ A CASE with one arm per kind written; stubs and library constants are not.
: lfx-declaration ( i -- )
  dup lfa-decl-kind case lf-decl-theorem of lfa-decl lfx-thm endof
    lf-decl-def of lfx-definition endof lf-decl-axiom of lfa-decl lfx-axiom endof
    nip endcase ;
: lfx-declarations ( -- ) lfa-decl-count 0 ?do i lfx-declaration loop ;

\ Public word; see the header.
: lfx-start ( sink -- ) lfx lfx-sink ! outcome-ok lfx lfx-outcome ! ;
: lfx-records ( -- ) lfx-meta lfx-names lfx-levels lfx-exprs lfx-declarations ;
: lf-author-export ( sink -- outcome )
  lfx-start lfx-tables if lfx-records else outcome-full lfx-refuse then
  lfx-free lfx lfx-outcome @ ;
