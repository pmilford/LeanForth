\ Test support: a tree dump of a declaration, written without the term
\ printer, so that the round trip compares terms by an independent path:
\ every node, de Bruijn index, level, constant name and universe argument,
\ binder name and kind, and every label and note with its kind. Source
\ positions are not dumped (the printed layout differs from the input).
\ Three things that are the same Lean term dump the same: a binder with no
\ entry in the side table and an explicit, anonymous one; a concrete Sort n
\ and the symbolic Sort of the level n (ADR 0007); and the name of a Pi
\ binder that prints as -> (explicit, unused, anonymous or hygienic), the
\ round trip's one stated exception (ADR 0017 section 13).
\ Output goes to dump-out ( c-addr u -- ), which the caller sets; labels
\ and notes are dumped while dump-notes? holds true (the comparison with
\ Lean's export, lean_terms.py, writes the same format without them).
\ Test-only; not a public interface.
require ../../src/author/runner.fs

defer dump-out ( c-addr u -- )
variable dump-notes?  true dump-notes? !
: d ( c-addr u -- ) dump-out ;
: d# ( n -- ) base @ >r decimal dup abs 0 <# #s rot sign #> r> base ! d ;

\ Names: parts joined by dots, a numeric part as #n.
: dump-part ( id -- )
  dup lf-name-tag@ lf-name-tag-str = if lf-name-text d else s" #" d lf-name-payload d# then ;
: dump-name ( id -- )
  dup 0= if drop s" [anonymous]" d exit then
  dup lf-name-prefix@ ?dup if recurse s" ." d then dump-part ;

: dump-level ( l -- )
  dup lf-level-tag@ case
    lf-level-tag-zero of drop s" 0" d endof
    lf-level-tag-succ of s" (succ " d lf-level-first@ recurse s" )" d endof
    lf-level-tag-max of s" (max " d dup lf-level-first@ recurse s"  " d lf-level-second@
      recurse s" )" d endof
    lf-level-tag-imax of s" (imax " d dup lf-level-first@ recurse s"  " d lf-level-second@
      recurse s" )" d endof
    lf-level-tag-param of s" (param " d lf-level-first@ dump-name s" )" d endof
    s" (bad level)" d nip endcase ;
: dump-number-level ( n -- ) dup 0 ?do s" (succ " d loop s" 0" d 0 ?do s" )" d loop ;

\ Does term mention variable k of its context? (independent of the printer)
: uses? ( term k -- flag )
  over lf-term-tag@ case
    lf-tag-bvar of swap lf-term-first@ = endof
    lf-tag-app of 2dup swap lf-term-first@ swap recurse >r swap lf-term-second@ swap recurse
      r> or endof
    lf-tag-lam of 2dup swap lf-term-first@ swap recurse >r 1+ swap lf-term-second@ swap
      recurse r> or endof
    lf-tag-pi of 2dup swap lf-term-first@ swap recurse >r 1+ swap lf-term-second@ swap
      recurse r> or endof
    >r 2drop false r> endcase ;
: hygienic? ( name -- flag )
  begin dup lf-name-tag@ lf-name-tag-num = while lf-name-prefix@ repeat
  dup lf-name-tag@ lf-name-tag-str = if lf-name-text s" _hyg" compare 0= else drop false then ;
: arrow? ( pi -- flag )
  dup lf-pres-binder@ 0= if 0 lf-binder-default then
  lf-binder-default = swap dup 0= swap hygienic? or and
  swap lf-term-second@ 0 uses? 0= and ;

: dump-note ( i -- )
  s"  [" d dup lf-note-kind@ d# s" :" d lf-note-text@ d s" ]" d ;
: dump-notes ( term -- )
  lf-note-count 0 ?do dup i lf-note-on? if i dump-note then loop drop ;
: dump-binder ( term -- )
  lf-pres-binder@ 0= if 0 lf-binder-default then s"  " d swap dump-name s"  " d d# ;
: dump-pi-binder ( pi -- )
  dup arrow? if drop s"  [arrow] 0" d else dump-binder then ;
: dump-levels ( addr n -- ) 0 ?do s"  " d dup i lf-cref-pair@ drop dump-level loop drop ;
: dump-const ( term -- )
  s" (const " d dup lf-term-first@ swap lf-term-second@ 2dup lf-cref-read
  0= abort" dump: stale reference" 2drop dump-name lf-cref-levels drop dump-levels s" )" d ;
defer dump-sub ( term -- )
: dump-node ( term -- )
  dup lf-term-tag@ case
    lf-tag-bvar of s" #" d lf-term-first@ d# endof
    lf-tag-sort of s" (Sort " d lf-term-first@ dump-number-level s" )" d endof
    lf-tag-symbolic-sort of s" (Sort " d lf-term-first@ dump-level s" )" d endof
    lf-tag-constant of dump-const endof
    lf-tag-app of s" (app " d dup lf-term-first@ dump-sub s"  " d lf-term-second@ dump-sub
      s" )" d endof
    lf-tag-lam of s" (lam" d dup dump-binder s"  " d dup lf-term-first@ dump-sub s"  " d
      lf-term-second@ dump-sub s" )" d endof
    lf-tag-pi of s" (pi" d dup dump-pi-binder s"  " d dup lf-term-first@ dump-sub s"  " d
      lf-term-second@ dump-sub s" )" d endof
    s" (bad term)" d nip endcase ;
: dump-term ( term -- )
  dup 0< if drop s" none" d exit then dup dump-node dump-notes? @ if dump-notes else drop then ;
' dump-term is dump-sub

create dump-eol 10 c,
: dump-decl ( decl -- )
  dup lf-fdecl-kind @ d# s"  " d dup lf-fdecl-name @ dump-name
  dup lf-fdecl-universes @ 0 ?do s"  u:" d dup lf-fdecl-universe i cells + @ dump-name loop
  dump-eol 1 d s"   type " d dup lf-fdecl-type @ dump-term dump-eol 1 d
  s"   value " d lf-fdecl-value @ dump-term dump-eol 1 d ;
