\ Test-only reading of the printer transport (present_transport.py) from
\ stdin, which is data, never code: it interns the names, builds the
\ levels and terms, fills the presentation side table (binder names and
\ kinds, source record IDs, declared types) and keeps the declarations.
\ Malformed or truncated input aborts. Shared by fixture-reader.fs and
\ tests/author/corpus-lean.fs; defines words only.
require ./build.fs

create cb 1 allot
: byte-in ( -- u ) cb 1 stdin read-file throw 1 <> abort" fixture: truncated" cb c@ ;
: u32 ( -- u ) byte-in byte-in 8 lshift or byte-in 16 lshift or byte-in 24 lshift or ;
: u32< ( limit -- u ) u32 tuck u> 0= abort" fixture: field out of range" ;

\ Stream index -> store index, for names, levels and terms.
64 constant slots
create name-map slots cells allot
create level-map slots cells allot
create term-map slots cells allot
variable names#   variable levels#   variable terms#
: name-check ( i -- ) names# @ 1+ u< 0= abort" fixture: bad name" ;
: name-id ( i -- id ) dup name-check cells name-map + @ ;
: level-id ( i -- l )
  dup levels# @ 1+ u< 0= abort" fixture: bad level" cells level-map + @ ;
: term-id ( i -- t ) dup terms# @ u< 0= abort" fixture: bad term" cells term-map + @ ;

\ Names.
create str-buf 256 allot
: read-str ( prefix -- id )
  257 u32< dup >r 0 ?do byte-in str-buf i + c! loop str-buf r> lf-name-str must ;
: read-name ( i -- )
  u32 u32 name-id swap case 1 of read-str endof 2 of u32 nm# endof true
  abort" fixture: name kind" endcase
  swap cells name-map + ! ;
: read-names ( -- )
  0 name-map ! slots u32< dup names# ! 0 ?do i 1+ read-name i 1+ names# ! loop ;

\ Levels; index 0 is zero.
: two-levels ( first second -- l1 l2 ) swap level-id swap level-id ;
: read-level ( i -- )
  u32 u32 u32 rot case
    1 of drop level-id lsucc endof
    2 of two-levels lmax endof
    3 of two-levels limax endof
    4 of drop name-id lf-level-param must endof
    true abort" fixture: level tag" endcase
  swap cells level-map + ! ;
: read-levels ( -- )
  0 level-map ! 0 levels# ! slots u32< 0 ?do i 1+ read-level i 1+ levels# ! loop ;

\ Terms, each recorded with its stream index as source ID.
: record-binder ( t name kind -- t ) >r name-id over swap r> lf-pres-binder! must-ok ;
: read-binder ( tag -- t )
  u32 term-id u32 term-id rot 4 = if t-lam else t-pi then u32 4 u32< record-binder ;
: id-const ( id -- t )
  lf-name-generation @ cargs cargc @ lf-cref-new must lf-cterm-new must drop ;
: read-const ( -- t ) u32 name-id args{ 9 u32< 0 ?do u32 level-id uarg loop id-const ;
: read-term ( -- t )
  u32 case
    1 of u32 level-id ssort endof
    2 of u32 t-var endof
    3 of u32 term-id u32 term-id t-app endof
    4 of 4 read-binder endof
    5 of 5 read-binder endof
    7 of read-const endof
    true abort" fixture: term tag" endcase ;
: read-terms ( -- )
  0 terms# ! slots 1+ u32< 0 ?do
    read-term dup i lf-pres-source! must-ok i cells term-map + ! i 1+ terms# ! loop ;

\ Declarations: kind, name, universe parameter names, type and value.
begin-structure /decl
  field: decl-kind
  field: decl-name
  field: decl-params#
  4 cells +field decl-params
  field: decl-type
  field: decl-value
end-structure
create decls slots /decl * allot
variable decls#
: decl ( i -- addr ) /decl * decls + ;
: read-params ( d -- ) 5 u32< 2dup swap decl-params# ! 0 ?do u32 name-id over decl-params
  i cells + ! loop drop ;
: read-decl ( d -- )
  2 u32< over decl-kind ! u32 name-id over decl-name ! dup read-params
  u32 term-id over decl-type ! u32 term-id over decl-value !
  dup decl-type @ swap decl-name @ swap lf-pres-declare must-ok ;
: read-decls ( -- ) slots u32< dup decls# ! 0 ?do i decl read-decl loop ;
: at-end ( -- ) cb 1 stdin read-file throw 0<> abort" fixture: trailing data" ;

