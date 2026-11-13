\ The notation table (plan task 4.4.3, version 1): versioned data that says
\ how the term printer writes an application of a Lean constant as mathematics.
\ One row per constant: its name, the number of arguments the application
\ must have (implicit and instance arguments included), the notation's kind,
\ which arguments are its operands, its precedences and four spellings, one
\ for each printer mode (lf-print-unicode, -ascii, -latex, -mathtext). A row
\ whose spelling in a mode is empty does not apply in that mode: the term
\ prints as the kernel's term does. The precedences are Lean's own
\ (Init/Notation.lean in the pinned toolchain), so the parentheses are
\ Lean's. Untrusted presentation code: a row changes only how a term is
\ spelled, never what it is, and the checker never loads it.
\ Standalone: requires only lib/lib.fs; print-notation.fs uses it.
\ No state: the rows and their texts are data of the dictionary, written
\ once while the table loads.
\
\ Kinds (the printing of each is in print-notation.fs):
\   atom     a constant with no argument:       Nat     written ℕ in mathematics
\   numeral  OfNat.ofNat _ 3 _                  written 3 (a literal that fits a cell)
\   infix    a OP b                             operands a, b at lprec and rprec
\   power    a ^ b                              b a superscript in mathematics
\   prefix   OP a                               operand at rprec
\   suffix   a OP                               Nat.succ n written n + 1
\   exists   ∃ x y, p                           Exists, binders merged
\ Row layout: arity, a and b (the argument indexes of the operands, from 0),
\ prec (the notation's own precedence), lprec and rprec (the least precedence
\ allowed for operand a and operand b), props (true: the operands are
\ propositions, so a Pi among them prints as ∀), mprec, four spellings.
\
\ Defining words. Each makes one whole row, from the numbers before it and
\ the constant's name and its four quoted spellings after it:
\   infix:  ( arity a b prec "Const" "s0" "s1" "s2" "s3" -- )  operands at prec + 1
\   infixl: ( same )  left operand at prec    infix-at: ( same )  both at prec
\   power: ( same )  right operand at prec, b a superscript in mathematics
\   prefix: ( arity a prec rprec ... )   suffix: ( arity a prec ... )
\   atom: ( "Const" "s0" "s1" "s2" "s3" -- )   numeral: ( "Const" -- )
\ and for the connectives, whose operands are propositions:
\   prop-infix: ( as infix: )   prop-infixr: ( same, right operand at prec )
\   exists: ( as atom: )
\   prop-prefix: ( as prefix: ), whose operand in LaTeX and mathematical text
\     is tight: parenthesized unless an atom or an application (¬(a = b),
\     where Lean writes ¬a = b)
\ Example: 6 4 5 65 infixl: HAdd.hAdd " + " " + " " + " " + "
\ A row's texts follow it in the dictionary; its first field says how far
\ the next row starts (lf-nt-after).

require ../lib/lib.fs

1 constant lf-notation-version

0 constant lf-nt-atom
1 constant lf-nt-numeral
2 constant lf-nt-infix
3 constant lf-nt-power
4 constant lf-nt-prefix
5 constant lf-nt-suffix
6 constant lf-nt-exists

begin-structure /lf-nt
  field: lf-nt-next       \ address units from the row to the next one
  2 cells +field lf-nt-name   \ the constant's name: c-addr u, after the row
  field: lf-nt-kind
  field: lf-nt-arity
  field: lf-nt-a
  field: lf-nt-b
  field: lf-nt-prec
  field: lf-nt-lprec
  field: lf-nt-rprec
  field: lf-nt-props
  field: lf-nt-mprec      \ the operand's precedence in the mathematical modes, or 0
  8 cells +field lf-nt-syms   \ four spellings, c-addr u each, after the row
end-structure
1023 constant lf-nt-tight-prec

\ Making a row: a zeroed record, its numbers, then its texts copied after
\ it as the table is read (a load-time word: it allots).
: lf-nt-blank ( -- row ) here /lf-nt dup allot over swap erase ;
: lf-nt-precs! ( prec row -- )
  2dup lf-nt-prec ! >r 1+ dup r@ lf-nt-lprec ! r> lf-nt-rprec ! ;
: lf-nt-places! ( arity a b row -- ) tuck lf-nt-b ! tuck lf-nt-a ! lf-nt-arity ! ;
: lf-nt-new ( arity a b prec kind -- row )
  lf-nt-blank tuck lf-nt-kind ! tuck lf-nt-precs! dup >r lf-nt-places! r> ;
: lf-nt-keep ( c-addr u -- c-addr' u ) here >r dup allot tuck r@ swap move r> swap ;
: lf-nt-quoted ( "text" -- c-addr u ) [char] " parse 2drop [char] " parse ;
: lf-nt-spelling ( row i -- addr ) 2* cells swap lf-nt-syms + ;
: lf-nt-spell ( row i -- ) lf-nt-spelling >r lf-nt-quoted lf-nt-keep r> 2! ;
: lf-nt-named ( row "Const" -- row ) dup lf-nt-name >r parse-name lf-nt-keep r> 2! ;
: lf-nt-spells ( row "s0" "s1" "s2" "s3" -- row ) 4 0 do dup i lf-nt-spell loop ;
: lf-nt-end ( row -- ) align here over - swap lf-nt-next ! ;
: lf-nt-row ( arity a b prec kind "Const" "s0" "s1" "s2" "s3" -- row )
  lf-nt-new lf-nt-named lf-nt-spells ;
\ Changes to a row before it ends: an operand at the notation's own
\ precedence, operands that are propositions, a tight operand.
: lf-nt-left-at ( row -- row ) dup lf-nt-prec @ over lf-nt-lprec ! ;
: lf-nt-right-at ( row -- row ) dup lf-nt-prec @ over lf-nt-rprec ! ;
: lf-nt-prop ( row -- row ) true over lf-nt-props ! ;
: lf-nt-tight ( row -- row ) lf-nt-tight-prec over lf-nt-mprec ! ;
: lf-nt-prefix-row ( arity a prec rprec "Const" "s0" "s1" "s2" "s3" -- row )
  >r 0 swap lf-nt-prefix lf-nt-row r> over lf-nt-rprec ! ;

: atom: ( "Const" "s0" "s1" "s2" "s3" -- ) 0 0 0 0 lf-nt-atom lf-nt-row lf-nt-end ;
: numeral: ( "Const" -- ) 3 1 0 0 lf-nt-numeral lf-nt-new lf-nt-named lf-nt-end ;
: infix: ( arity a b prec "Const" "s0" "s1" "s2" "s3" -- )
  lf-nt-infix lf-nt-row lf-nt-end ;
: infixl: ( arity a b prec "Const" "s0" "s1" "s2" "s3" -- )
  lf-nt-infix lf-nt-row lf-nt-left-at lf-nt-end ;
: infix-at: ( arity a b prec "Const" "s0" "s1" "s2" "s3" -- )
  lf-nt-infix lf-nt-row lf-nt-left-at lf-nt-right-at lf-nt-end ;
: power: ( arity a b prec "Const" "s0" "s1" "s2" "s3" -- )
  lf-nt-power lf-nt-row lf-nt-right-at lf-nt-end ;
\ OP a: the notation has precedence prec, its operand rprec.
: prefix: ( arity a prec rprec "Const" "s0" "s1" "s2" "s3" -- )
  lf-nt-prefix-row lf-nt-end ;
\ a OP: the operand is the argument a, at prec.
: suffix: ( arity a prec "Const" "s0" "s1" "s2" "s3" -- )
  0 swap lf-nt-suffix lf-nt-row lf-nt-left-at lf-nt-end ;
: prop-infix: ( arity a b prec "Const" "s0" "s1" "s2" "s3" -- )
  lf-nt-infix lf-nt-row lf-nt-prop lf-nt-end ;
: prop-infixr: ( arity a b prec "Const" "s0" "s1" "s2" "s3" -- )
  lf-nt-infix lf-nt-row lf-nt-right-at lf-nt-prop lf-nt-end ;
: prop-prefix: ( arity a prec rprec "Const" "s0" "s1" "s2" "s3" -- )
  lf-nt-prefix-row lf-nt-prop lf-nt-tight lf-nt-end ;
: exists: ( "Const" "s0" "s1" "s2" "s3" -- )
  2 1 0 0 lf-nt-exists lf-nt-row lf-nt-prop lf-nt-end ;

\ ---- Version 1 of the table ----------------------------------------------
\ The rows follow in the dictionary, one after the other, from lf-nt-rows to
\ lf-nt-rows-end.
create lf-nt-rows
\ Types of numbers, in mathematics.
atom: Nat        ""           ""           "\mathbb{N}"      "ℕ"
atom: Int        ""           ""           "\mathbb{Z}"      "ℤ"
atom: Rat        ""           ""           "\mathbb{Q}"      "ℚ"
atom: Real       ""           ""           "\mathbb{R}"      "ℝ"
numeral: OfNat.ofNat
\ Relations (Lean: infix:50). Ne, Dvd.dvd and Membership.mem have no ASCII spelling.
3 1 2 50 infix: Eq          " = "  " = "  " = "         " = "
3 1 2 50 infix: Ne          " ≠ "  ""      " \ne "      " ≠ "
4 2 3 50 infix: LT.lt       " < "  " < "  " < "        " < "
4 2 3 50 infix: LE.le       " ≤ "  " <= " " \le "      " ≤ "
4 2 3 50 infix: GT.gt       " > "  " > "  " > "        " > "
4 2 3 50 infix: GE.ge       " ≥ "  " >= " " \ge "      " ≥ "
4 2 3 50 infix: Dvd.dvd     " ∣ "  ""      " \mid "     " ∣ "
\ a ∈ b is notation:50 a:50 " ∈ " b:50 => Membership.mem b a.
5 4 3 50 infix-at: Membership.mem " ∈ " "" " \in "      " ∈ "
\ Arithmetic (Lean: infixl:65, infixl:70, infixr:80, prefix:75).
6 4 5 65 infixl: HAdd.hAdd   " + "  " + "  " + "        " + "
6 4 5 65 infixl: HSub.hSub   " - "  " - "  " - "        " - "
6 4 5 70 infixl: HMul.hMul   " * "  " * "  " \cdot "    " · "
6 4 5 70 infixl: HDiv.hDiv   " / "  " / "  " / "        " / "
6 4 5 70 infixl: HMod.hMod   " % "  " % "  " \bmod "    " mod "
6 4 5 80 power: HPow.hPow   " ^ "  " ^ "  "^"          "^"
3 2 75 75 prefix: Neg.neg     "-"    "-"    "-"           "-"
1 0 65 suffix: Nat.succ    ""     ""     " + 1"        " + 1"
\ Logic (Lean: infix:20, infixr:35, infixr:30, notation:max "¬" p:40).
2 0 1 20 prop-infix: Iff     " ↔ "  " <-> " " \leftrightarrow " " ↔ "
2 0 1 35 prop-infixr: And    " ∧ "  " /\ " " \wedge "   " ∧ "
2 0 1 30 prop-infixr: Or     " ∨ "  " \/ " " \vee "     " ∨ "
1 0 1024 40 prop-prefix: Not "¬"    ""     "\neg "       "¬"
exists: Exists                       "∃ "   "exists " "\exists " "∃ "
here constant lf-nt-rows-end

\ The row for the constant named c-addr u, or 0: the first such row.
: lf-nt-after ( row -- row' ) dup lf-nt-next @ + ;
: lf-nt-named? ( c-addr u row -- flag ) lf-nt-name 2@ compare 0= ;
: lf-nt-find ( c-addr u -- row | 0 )
  lf-nt-rows begin dup lf-nt-rows-end u< while
    >r 2dup r@ lf-nt-named? if 2drop r> exit then r> lf-nt-after repeat
  drop 2drop 0 ;
\ A row's spelling for a printer mode (0 to 3), empty when it has none.
: lf-nt-sym ( row mode -- c-addr u ) lf-nt-spelling 2@ ;
