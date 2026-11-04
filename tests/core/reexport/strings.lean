/-
A string literal with every class of byte Lean's JSON printer writes
differently, for the re-export check against pinned Lean
(tests/core/reexport/lean-check.sh, `make reference-reexport`). Its
export is made afresh and not kept: with the definitions every string
literal depends on (String.ofList, Char.ofNat) it has about 11,000 lines.
-/
namespace ReexportStrings

/-- The quote, the backslash, line feed and carriage return, which the
printer writes by letter; tab, backspace, form feed, escape and the other
bytes below 32, which it writes as \u00xx; DEL, the slash and characters
of two, three and four bytes, which it writes as themselves. -/
def text : String :=
  "tab\t nl\n cr\r bs\x08 ff\x0c nul\x00 us\x1f esc\x1b del\x7f q\" bsl\\ sl/ é € 😀 𝔽"

end ReexportStrings
