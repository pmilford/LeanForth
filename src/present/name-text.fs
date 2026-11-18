\ The one name speller (review R9, 2026-11-18): a name as display text,
\ for the command line's text and JSON reports (cli/leanforth.fs,
\ cli/check-json.fs) and, a component at a time (nt-part), for the term
\ printer (print-names.fs, so goals and print too): Lean's own
\ Name.toString (Lean 4.35.0, Init/Data/ToString/Name.lean), its
\ components joined by dots from the root, numeric ones in decimal, a
\ component that is not an identifier between « and » (an empty one as
\ «»), the anonymous name as [anonymous]; names of any depth. As Lean's
\ formatter writes an identifier (Name.toString with isToken), a root
\ component that is a token of Init's syntax (nt-tokens: fun, let, Type,
\ ...) is between « » too: «fun», but Foo.fun; the tokens a file's own
\ imports add (Mathlib's notation) are not known here. Three
\ differences make the text show exactly what the name holds, so that no
\ name can start a line of its own, look like the start of another line
\ or reorder what follows it:
\ 1. a component that is not an identifier is always between « and »:
\    Lean leaves out « » for a component that holds », and for a whole
\    name with macro scopes (x._@._hyg), an inaccessible one (holding ✝)
\    or pseudo-syntax (_, or a root that starts with # or ?), so spaces
\    and colons would pass through and a line could begin with
\    "fake: accepted"; here x._@._hyg shows as x.«_@»._hyg;
\ 2. inside « », every character the run records' text rule bans (C0 and
\    C1 controls, format characters such as bidirectional controls, line
\    and paragraph separators; lib/text-rule.fs's tr-banned?) and » itself
\    show as \u{X}, the code point in hexadecimal, so the component ends
\    at the first »; a byte that does not start UTF-8 as \x{X};
\ 3. a backslash shows as \\, so that the text of an escape in a name is
\    never read as an escape.
\ An identifier is as Lean's isIdFirst and isIdRest have it
\ (Init/Meta/Defs.lean). The components are gathered in a heap block,
\ from the name up to the root, so there is no fixed limit but the heap's.
\ Untrusted presentation; LeanForth-specific (Lean's names and identifier
\ rules).
\
\ nt-name ( id -- c-addr u flag ) the display text of name id; flag false
\ when the heap had no room for it (the text must then not be shown).
\ nt-part ( id -- c-addr u flag ) the string component id (the last of
\ name id) as it shows: its text itself when it is shown bare, else
\ between « » and escaped (flag false: no room).
\ nt-text ( c-addr u -- c-addr' u' flag ) any bytes with the escapes of 2
\ and 3, without « » (an export's file name), in a block of its own. Never
\ give it text that is already escaped (a name's, the term printer's): it
\ would escape it twice; its own last result it refuses (flag false). A
\ text of nt-name or nt-part stays valid until the next call of either,
\ one of nt-text until the next nt-text. nt-free frees the heap blocks; the command line does not
\ call it: one process runs one command, the blocks are as large as the
\ longest name shown, and the host takes them back when the process
\ leaves. A Forth session that wants the memory back calls it; the next
\ call makes them again.
\ State: one shared record, nt-state (/nt): three slabs (a name's text,
\ other text escaped, the name's components), which of the first two is
\ being written, whether a byte found no room, and the table of Init's
\ tokens, laid while loading. One text at
\ a time, in any context. It reads bytes (c@) to decode UTF-8. Loads in
\ decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/slab.fs
require ../lib/bytes.fs
require ../lib/decimal.fs
require ../lib/text-rule.fs
require ../lib/name-table.fs
require ../core/names.fs

begin-structure /nt
  /slab +field nts-names     \ a name's text (nt-name, nt-part)
  /slab +field nts-raw       \ other text escaped (nt-text), never the text it reads
  /slab +field nts-parts     \ the name's component IDs, from the name to the root
  field: nts-into            \ the slab the text being built goes to
  field: nts-short           \ true once a byte found no room
  2 cells +field nts-tokens  \ Init's tokens (lib/name-table.fs), laid while loading
end-structure
create nt-state /nt allot  nt-state /nt erase
: nt-names ( -- slab ) nt-state nts-names ;
: nt-raw ( -- slab ) nt-state nts-raw ;
: nt-out ( -- slab ) nt-state nts-into @ ;
: nt-parts ( -- slab ) nt-state nts-parts ;
: nt-short ( -- addr ) nt-state nts-short ;
\ The slabs, made when first used, freed by nt-free.
: nt-make ( unit slab -- )
  dup slab-live? if 2drop exit then over slab-limit-max swap slab-init drop ;
: nt-unmade ( slab -- ) dup slab-free /slab erase ;
: nt-free ( -- ) nt-names nt-unmade nt-raw nt-unmade nt-parts nt-unmade ;
\ A new text, built in slab (nt-names or nt-raw).
: nt-start ( slab -- )
  dup nt-state nts-into ! 1 chars swap nt-make 1 cells nt-parts nt-make
  nt-out slab-clear false nt-short ! ;

\ ---- The text being built: bytes added, a refused one marks it short.
: nt-put ( c-addr u -- )
  dup nt-out slab-claim ok? if nt-out slab-at swap move exit then
  drop 2drop true nt-short ! ;
: nt-text@ ( -- c-addr u flag ) 0 nt-out slab-at nt-out slab-count nt-short @ 0= ;
: nt-decimal ( u -- ) u>decimal nt-put ;
\ An escape: its prefix, the number in hexadecimal, then }.
: nt-escape ( u c-addr u -- ) nt-put u>hex nt-put s" }" nt-put ;

\ ---- Characters. The first character of a text: its code point and
\ length, or the byte and 0 when it does not start a UTF-8 sequence.
: nt-char ( c-addr u -- code n )
  over swap utf8-length ?dup if tuck utf8-decode swap else c@ 0 then ;
\ Ranges ( lo , hi , ) of code points. Lean's isIdFirst: ASCII letters,
\ _ and isLetterLike (Greek but λ, Π and Σ, Coptic, Greek Extended, the
\ letterlike block, Latin-1 letters but × and ÷, Latin Extended-A,
\ mathematical Latin).
create nt-first
  $41 , $5a ,  $5f , $5f ,  $61 , $7a ,  $c0 , $d6 ,  $d8 , $f6 ,  $f8 , $17f ,
  $391 , $39f ,  $3a1 , $3a2 ,  $3a4 , $3a9 ,  $3b1 , $3ba ,  $3bc , $3fb ,
  $1f00 , $1ffe ,  $2100 , $214f ,  $1d49c , $1d59f ,
here nt-first - 2 cells / constant nt-first#
\ isIdRest adds digits, ' ! ? and isSubScriptAlnum: subscript digits
\ ₀-₉, letters ₐ-ₜ and ᵢ-ᵪ, and ⱼ (not the subscript signs ₊ ₋ ₌ ₍ ₎).
create nt-rest
  $21 , $21 ,  $27 , $27 ,  $30 , $39 ,  $3f , $3f ,
  $2080 , $2089 ,  $2090 , $209c ,  $1d62 , $1d6a ,  $2c7c , $2c7c ,
here nt-rest - 2 cells / constant nt-rest#
: nt-first? ( code -- flag ) nt-first nt-first# in-ranges? ;
: nt-rest? ( code -- flag )
  dup nt-first? if drop true else nt-rest nt-rest# in-ranges? then ;
\ Whether every character of c-addr u is valid UTF-8 and satisfies xt
\ ( code -- flag ).
: nt-all? ( c-addr u xt -- flag )
  >r begin dup while
    2dup nt-char dup 0= if 2drop 2drop r> drop false exit then
    swap r@ execute 0= if drop 2drop r> drop false exit then /string
  repeat 2drop r> drop true ;
\ An identifier: not empty, its first character isIdFirst, the rest isIdRest.
: nt-ident? ( c-addr u -- flag )
  dup 0= if 2drop false exit then 2dup nt-char dup 0= if 2drop 2drop false exit then
  >r nt-first? 0= if r> drop 2drop false exit then r> /string ['] nt-rest? nt-all? ;

\ ---- Escaped text, one character at a time (see the header).
: nt-escaped? ( code -- flag ) dup tr-banned? swap $bb = or ;
\ The character code, n bytes at the start of c-addr u: escaped, a
\ backslash doubled, or as it is; then the rest.
: nt-shown ( c-addr u code n -- c-addr' u' )
  >r dup nt-escaped? if s" \u{" nt-escape r> /string exit then
  [char] \ = if s" \\" nt-put else over r@ nt-put then r> /string ;
: nt-out-char ( c-addr u -- c-addr' u' )
  2dup nt-char ?dup if nt-shown else s" \x{" nt-escape 1 /string then ;
: nt-escaped ( c-addr u -- ) begin dup while nt-out-char repeat 2drop ;

\ ---- The tokens of Init's syntax that are identifiers, which Lean's
\ formatter puts between « » as a root component: Lean 4.35.0's token
\ table after importing Init (Lean.Parser.getTokenTable), its entries that
\ pass isIdFirst and isIdRest, but _ (Lean never escapes the pseudo-syntax
\ _). Regenerate them when the pinned Lean changes.
: nt-tokens ( -- table ) nt-state nts-tokens ;
: nt-token, ( c-addr u -- ) nt-tokens name-entry ;
s" Prop" nt-token, s" Sort" nt-token, s" StateRefT" nt-token, s" Type" nt-token,
s" abbrev" nt-token, s" add_decl_doc" nt-token, s" assert!" nt-token,
s" assert_not_exists" nt-token, s" assert_not_imported" nt-token,
s" attribute" nt-token, s" axiom" nt-token, s" binder_predicate" nt-token,
s" break" nt-token, s" builtin_initialize" nt-token, s" by" nt-token,
s" catch" nt-token, s" class" nt-token, s" coinductive" nt-token,
s" coinductive_fixpoint" nt-token, s" continue" nt-token, s" dbg_trace" nt-token,
s" debug_assert!" nt-token, s" declare_syntax_cat" nt-token, s" decreasing_by" nt-token,
s" def" nt-token, s" deprecated_module" nt-token, s" deprecated_syntax" nt-token,
s" deriving" nt-token, s" do" nt-token, s" docs_to_verso" nt-token, s" elab" nt-token,
s" elab_rules" nt-token, s" else" nt-token, s" end" nt-token, s" example" nt-token,
s" export" nt-token, s" extends" nt-token, s" finally" nt-token, s" for" nt-token,
s" forall" nt-token, s" from" nt-token, s" fun" nt-token, s" grind_pattern" nt-token,
s" have" nt-token, s" haveI" nt-token, s" hiding" nt-token, s" idbg" nt-token,
s" if" nt-token, s" import" nt-token, s" in" nt-token, s" include" nt-token,
s" inductive" nt-token, s" inductive_fixpoint" nt-token, s" inferInstanceAs" nt-token,
s" infix" nt-token, s" infixl" nt-token, s" infixr" nt-token,
s" init_grind_norm" nt-token, s" init_quot" nt-token, s" initialize" nt-token,
s" instance" nt-token, s" leading_parser" nt-token, s" let" nt-token, s" letI" nt-token,
s" let_delayed" nt-token, s" let_expr" nt-token, s" let_fun" nt-token,
s" let_tmp" nt-token, s" local" nt-token, s" logNamedError" nt-token,
s" logNamedErrorAt" nt-token, s" logNamedWarning" nt-token,
s" logNamedWarningAt" nt-token, s" macro" nt-token, s" macro_rules" nt-token,
s" match" nt-token, s" match_expr" nt-token, s" meta" nt-token,
s" monotonicity_by" nt-token, s" mut" nt-token, s" mutual" nt-token,
s" namespace" nt-token, s" no_index" nt-token, s" nofun" nt-token, s" nomatch" nt-token,
s" noncomputable" nt-token, s" nonrec" nt-token, s" notation" nt-token,
s" omit" nt-token, s" opaque" nt-token, s" open" nt-token, s" panic!" nt-token,
s" partial" nt-token, s" partial_fixpoint" nt-token, s" postfix" nt-token,
s" prefix" nt-token, s" private" nt-token, s" protected" nt-token, s" public" nt-token,
s" recall" nt-token, s" recall?" nt-token, s" recommended_spelling" nt-token,
s" register_error_explanation" nt-token, s" register_tactic_tag" nt-token,
s" renaming" nt-token, s" repeat" nt-token, s" return" nt-token, s" scoped" nt-token,
s" section" nt-token, s" set_option" nt-token, s" show" nt-token,
s" show_term_elab" nt-token, s" sorry" nt-token, s" structure" nt-token,
s" suffices" nt-token, s" syntax" nt-token, s" tactic_alt" nt-token,
s" tactic_extension" nt-token, s" tactic_name" nt-token, s" tactic_tag" nt-token,
s" termination_by" nt-token, s" termination_by?" nt-token, s" then" nt-token,
s" theorem" nt-token, s" throwNamedError" nt-token, s" throwNamedErrorAt" nt-token,
s" trailing_parser" nt-token, s" try" nt-token, s" universe" nt-token,
s" unless" nt-token, s" unlock_limits" nt-token, s" unreachable!" nt-token,
s" unsafe" nt-token, s" until" nt-token, s" variable" nt-token, s" where" nt-token,
s" while" nt-token, s" with" nt-token, s" with_weak_namespace" nt-token,
: nt-token? ( c-addr u -- flag ) nt-tokens name-table-find 0<> ;

\ ---- Components: a string one as it is when an identifier (and, as the
\ root, no token), else escaped between « and »; a numeric one in decimal.
: nt-root? ( id -- flag ) lf-name-prefix@ 0= ;
: nt-token-root? ( id -- flag )
  dup nt-root? if lf-name-text nt-token? else drop false then ;
: nt-plain? ( id -- flag ) dup lf-name-text nt-ident? swap nt-token-root? 0= and ;
: nt-quoted ( c-addr u -- ) s" «" nt-put nt-escaped s" »" nt-put ;
: nt-str ( id -- ) dup nt-plain? if lf-name-text nt-put else lf-name-text nt-quoted then ;
: nt-component ( id -- )
  dup lf-name-str? if nt-str else lf-name-payload nt-decimal then ;
: nt-part ( id -- c-addr u flag )
  dup nt-plain? if lf-name-text true exit then
  lf-name-text nt-names nt-start nt-quoted nt-text@ ;

\ The name's components, from the name up to the root (k = 0 the last);
\ full when the heap has no room for them.
: nt-gather ( id -- outcome )
  nt-parts slab-clear begin dup while
    dup nt-parts slab-push ok? 0= if drop outcome-full exit then lf-name-prefix@
  repeat drop outcome-ok ;
: nt-count ( -- n ) nt-parts slab-count ;
: nt-part-id ( k -- id ) nt-parts slab-at @ ;
\ Root first, joined by dots.
: nt-dot ( k -- ) nt-count 1- <> if s" ." nt-put then ;
: nt-components ( -- ) 0 nt-count 1- do i nt-dot i nt-part-id nt-component -1 +loop ;
: nt-name ( id -- c-addr u flag )
  nt-names nt-start ?dup 0= if s" [anonymous]" true exit then
  nt-gather ok? 0= if nt-text@ drop false exit then nt-components nt-text@ ;
\ Other text, escaped into a slab of its own (nt-raw): a name's text
\ (nt-name, nt-part) given to it is read from another slab; text inside
\ nt-raw, its own last result, is refused (flag false), never read while
\ it is rewritten (review F1).
: nt-own? ( c-addr -- flag ) nt-raw slab-offset 0< 0= ;
: nt-text ( c-addr u -- c-addr' u' flag )
  over nt-own? if false exit then nt-raw nt-start nt-escaped nt-text@ ;

base !   \ the BASE this file was loaded with
