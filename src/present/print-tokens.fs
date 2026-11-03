\ The printer's notation in its three modes: Unicode (Lean's own notation,
\ as Lean prints with pp.unicode.fun), ASCII (forall, ->, fun ... =>) and
\ LaTeX math. Every symbol and every identifier the printer writes goes
\ through this file, so a mode changes only the spelling, never the
\ structure or the binder names. Untrusted presentation code.
\ Requires print-names.fs. No state.

require ./print-names.fs
require ./latex-text.fs

\ One token word per symbol: the mode selects the spelling.
: lf-pp-forall ( -- )
  lf-pp-mode case lf-print-ascii of s" forall " endof lf-print-latex of s" \forall " endof
  s" ∀ " rot endcase lf-pp-emit ;
: lf-pp-arrow ( -- )
  lf-pp-mode case lf-print-ascii of s"  -> " endof lf-print-latex of s"  \to " endof
  s"  → " rot endcase lf-pp-emit ;
: lf-pp-fun ( -- )
  lf-pp-latex? if s" \lambda" else s" fun" then lf-pp-emit ;
: lf-pp-mapsto ( -- )
  lf-pp-mode case lf-print-ascii of s"  => " endof lf-print-latex of s"  \mapsto " endof
  s"  ↦ " rot endcase lf-pp-emit ;
\ The comma after a run of ∀ binders, and the space between words.
: lf-pp-comma ( -- ) lf-pp-latex? if s" ,\ " else s" , " then lf-pp-emit ;
: lf-pp-space ( -- ) lf-pp-latex? if s" \ " else s"  " then lf-pp-emit ;
: lf-pp-colon ( -- ) s"  : " lf-pp-emit ;
: lf-pp-paren ( -- ) s" (" lf-pp-emit ;
: lf-pp-unparen ( -- ) s" )" lf-pp-emit ;
: lf-pp-explicit ( -- ) s" @" lf-pp-emit ;

\ Binder brackets by binder kind (binder-table.fs): ( ), { }, strict
\ implicit, [ ].
: lf-pp-strict-open ( -- c-addr u )
  lf-pp-mode case lf-print-ascii of s" {{" endof lf-print-latex of s" \{\{" endof
  s" ⦃" rot endcase ;
: lf-pp-strict-close ( -- c-addr u )
  lf-pp-mode case lf-print-ascii of s" }}" endof lf-print-latex of s" \}\}" endof
  s" ⦄" rot endcase ;
: lf-pp-brace-open ( -- c-addr u ) lf-pp-latex? if s" \{" else s" {" then ;
: lf-pp-brace-close ( -- c-addr u ) lf-pp-latex? if s" \}" else s" }" then ;
: lf-pp-open ( kind -- )
  case lf-binder-implicit of lf-pp-brace-open endof lf-binder-strict of lf-pp-strict-open
  endof
  lf-binder-instance of s" [" endof s" (" rot endcase lf-pp-emit ;
: lf-pp-close ( kind -- )
  case lf-binder-implicit of lf-pp-brace-close endof lf-binder-strict of
  lf-pp-strict-close endof
  lf-binder-instance of s" ]" endof s" )" rot endcase lf-pp-emit ;

\ Sorts and universe levels.
: lf-pp-word ( c-addr u -- )
  lf-pp-latex? 0=
  if lf-pp-emit exit then s" \mathrm{" lf-pp-emit lf-pp-emit s" }" lf-pp-emit ;
: lf-pp-prop ( -- ) s" Prop" lf-pp-word ;
: lf-pp-type ( -- ) s" Type" lf-pp-word ;
: lf-pp-sort ( -- ) s" Sort" lf-pp-word ;
: lf-pp-max ( -- ) lf-pp-latex? if s" \max" else s" max" then lf-pp-emit ;
: lf-pp-imax ( -- )
  lf-pp-latex? if s" \operatorname{imax}" else s" imax" then lf-pp-emit ;
: lf-pp-plus ( -- ) s"  + " lf-pp-emit ;
: lf-pp-universes-open ( -- ) lf-pp-latex? if s" .\{" else s" .{" then lf-pp-emit ;
: lf-pp-universes-close ( -- ) lf-pp-brace-close lf-pp-emit ;
: lf-pp-list-comma ( -- ) lf-pp-latex? if s" ,\ " else s" , " then lf-pp-emit ;

\ Identifiers: a bound variable's display name; a universe parameter's
\ name, spelled like a variable; a constant's name. In LaTeX a structured
\ name is first spelled out in the name pool, then styled.
: lf-pp-ident ( c-addr u -- ) lf-pp-latex? if lf-tex-ident else lf-pp-emit then ;
: lf-pp-spell ( id xt -- )
  lf-pp-used @ >r >r ['] lf-pp-put lf-pp-name-to r> r@ lf-pp-pending rot execute r>
  lf-pp-used ! ;
: lf-pp-anonymous ( -- ) s" [anonymous]" lf-pp-word ;
: lf-pp-name ( id -- )
  ?dup 0= if lf-pp-anonymous exit then
  lf-pp-latex? if ['] lf-tex-ident lf-pp-spell else ['] lf-pp-emit lf-pp-name-to then ;
: lf-pp-constant ( id -- )
  ?dup 0= if lf-pp-anonymous exit then
  lf-pp-latex? if ['] lf-tex-constant lf-pp-spell else ['] lf-pp-emit lf-pp-name-to then ;
