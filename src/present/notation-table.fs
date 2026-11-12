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
\ No state: the rows are constants of the dictionary.
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
\ propositions, so a Pi among them prints as ∀), four spellings.
\
\ Defining words, written after the numbers they take and reading the
\ constant's name and its four quoted spellings from the text that follows:
\   infix:  ( arity a b prec "Const" "s0" "s1" "s2" "s3" -- )  operands at prec + 1
\   infixl: ( same )  left operand at prec    infixr: ( same )  right operand at prec
\   power: ( same as infixr: )   prefix: ( arity a prec rprec ... )
\   suffix: ( arity a prec ... )   atom: ( ... )   numeral: ( "Const" )   exists: ( ... )
\   props   ( -- )  marks the row just defined as one of propositions
\ Example: 6 4 5 65 infixl: HAdd.hAdd " + " " + " " + " " + "
\ The texts of all rows must fit the 4096-byte pool (lf-nt-pool).

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
  2 cells +field lf-nt-name   \ the constant's name: c-addr u in lf-nt-pool
  field: lf-nt-kind
  field: lf-nt-arity
  field: lf-nt-a
  field: lf-nt-b
  field: lf-nt-prec
  field: lf-nt-lprec
  field: lf-nt-rprec
  field: lf-nt-props
  field: lf-nt-mprec      \ the operand's precedence in the mathematical modes, or 0
  8 cells +field lf-nt-syms   \ four spellings, c-addr u each, in lf-nt-pool
end-structure

\ The texts of the rows, copied here as the table is read (a cursor of the
\ load, not of any print): the pool is full at 4096 bytes.
4096 constant lf-nt-pool-size
create lf-nt-pool lf-nt-pool-size allot
variable lf-nt-fill
: lf-nt-keep ( c-addr u -- c-addr' u )
  dup lf-nt-fill @ + lf-nt-pool-size > abort" notation text area full"
  dup >r lf-nt-pool lf-nt-fill @ + dup >r swap move r> r> dup lf-nt-fill +! ;
: lf-nt-quoted ( "text" -- c-addr u ) [char] " parse 2drop [char] " parse ;

: lf-nt-new ( arity a b prec kind "Const" -- row )
  here /lf-nt allot >r r@ /lf-nt erase r@ lf-nt-kind !
  dup r@ lf-nt-prec ! 1+ dup r@ lf-nt-lprec ! r@ lf-nt-rprec !
  r@ lf-nt-b ! r@ lf-nt-a ! r@ lf-nt-arity !
  parse-name lf-nt-keep r@ lf-nt-name 2! r> ;
: lf-nt-spelling ( row i -- addr ) 2* cells swap lf-nt-syms + ;
: lf-nt-spell ( row -- row ) 4 0 do
    lf-nt-quoted lf-nt-keep 2 pick i lf-nt-spelling 2! loop ;
: lf-nt-lprec! ( row n -- ) over lf-nt-lprec ! drop ;
: lf-nt-rprec! ( row n -- ) over lf-nt-rprec ! drop ;
: lf-nt-last ( -- row ) here /lf-nt - ;

: atom: ( "Const" "s0" "s1" "s2" "s3" -- ) 0 0 0 0 lf-nt-atom lf-nt-new lf-nt-spell drop ;
: numeral: ( "Const" -- ) 3 1 0 0 lf-nt-numeral lf-nt-new drop ;
: infix: ( arity a b prec "Const" "s0" "s1" "s2" "s3" -- )
  lf-nt-infix lf-nt-new lf-nt-spell drop ;
: infixl: ( arity a b prec "Const" "s0" "s1" "s2" "s3" -- )
  lf-nt-infix lf-nt-new lf-nt-spell dup lf-nt-prec @ lf-nt-lprec! ;
: infixr: ( arity a b prec "Const" "s0" "s1" "s2" "s3" -- )
  lf-nt-infix lf-nt-new lf-nt-spell dup lf-nt-prec @ lf-nt-rprec! ;
: power: ( arity a b prec "Const" "s0" "s1" "s2" "s3" -- )
  lf-nt-power lf-nt-new lf-nt-spell dup lf-nt-prec @ lf-nt-rprec! ;
\ OP a: the notation has precedence prec, its operand rprec.
: prefix: ( arity a prec rprec "Const" "s0" "s1" "s2" "s3" -- )
  >r 0 swap lf-nt-prefix lf-nt-new lf-nt-spell r> lf-nt-rprec! ;
\ a OP: the operand is the argument a, at prec.
: suffix: ( arity a prec "Const" "s0" "s1" "s2" "s3" -- )
  0 swap lf-nt-suffix lf-nt-new lf-nt-spell dup lf-nt-prec @ lf-nt-lprec! ;
: exists: ( "Const" "s0" "s1" "s2" "s3" -- ) 2 1 0 0 lf-nt-exists lf-nt-new
  lf-nt-spell drop ;
: props ( -- ) true lf-nt-last lf-nt-props ! ;
\ In LaTeX and mathematical text the operand needs parentheses unless it is
\ an atom or an application (¬(a = b), where Lean writes ¬a = b).
: tight ( -- ) 1023 lf-nt-last lf-nt-mprec ! ;

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
5 4 3 50 infix: Membership.mem " ∈ " "" " \in "         " ∈ "
  lf-nt-last 50 lf-nt-lprec!  lf-nt-last 50 lf-nt-rprec!
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
2 0 1 20 infix: Iff         " ↔ "  " <-> " " \leftrightarrow " " ↔ "
  props
2 0 1 35 infixr: And         " ∧ "  " /\ " " \wedge "   " ∧ "
  props
2 0 1 30 infixr: Or          " ∨ "  " \/ " " \vee "     " ∨ "
  props
1 0 1024 40 prefix: Not         "¬"    ""     "\neg "       "¬"
  props tight
exists: Exists                       "∃ "   "exists " "\exists " "∃ "
  props
here constant lf-nt-rows-end

\ The row for the constant named c-addr u, or 0.
: lf-nt-row? ( row c-addr u -- flag )
  rot lf-nt-name 2@ compare 0= ;
: lf-nt-find ( c-addr u -- row | 0 )
  lf-nt-rows begin dup lf-nt-rows-end u< while
    >r 2dup r@ -rot lf-nt-row? if 2drop r> exit then
    r> /lf-nt + repeat
  drop 2drop 0 ;
\ A row's spelling for a printer mode (0 to 3), empty when it has none.
: lf-nt-sym ( row mode -- c-addr u ) lf-nt-spelling 2@ ;
