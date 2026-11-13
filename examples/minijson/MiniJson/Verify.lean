/-
  File: MiniJson/Verify.lean
  Purpose: Every claim of Spec.lean restated with `recall`. `recall` fails to compile
  when the statement written here differs from the one proved, so the ordinary build
  checks that the proofs prove what the spec states. Each `#print axioms` line reports
  the axioms a claim rests on, for reading; the check that fails on an axiom outside
  the allowed list is the axiom assertion in the test package.

  Written by `claims sync` from Spec.lean. Not edited by hand.
  Created: 2026-11-14
-/

import MiniJson.Proofs

/-! ## Claim 1. A text parses to a value exactly when the text's tokens are the value's tokens. -/

namespace MiniJson.Proofs

open MiniJson

recall parseChars_iff (text : List Char) (value : Json) :
    parseChars text = some value ↔ tokenize text = some (tokensOf value)
#print axioms parseChars_iff

end MiniJson.Proofs

/-! ## Claim 2. The text the renderer writes for a value has exactly that value's tokens. -/

namespace MiniJson.Proofs

open MiniJson

recall tokenize_renderChars (value : Json) : tokenize (renderChars value) = some (tokensOf value)
#print axioms tokenize_renderChars

end MiniJson.Proofs

/-! ## Claim 3. Parsing the text rendered for a value gives the value back. -/

namespace MiniJson.Proofs

open MiniJson

recall parseChars_renderChars (value : Json) : parseChars (renderChars value) = some value
#print axioms parseChars_renderChars

recall parse_render (value : Json) : parse (render value) = some value
#print axioms parse_render

end MiniJson.Proofs

/-! ## Claim 4. Two values with the same rendered text are the same value. -/

namespace MiniJson.Proofs

open MiniJson

recall renderChars_injective (first second : Json) (sameText : renderChars first = renderChars second) :
    first = second
#print axioms renderChars_injective

end MiniJson.Proofs

/-! ## Claim 5. The functions on strings are the functions on lists of characters. -/

namespace MiniJson.Proofs

open MiniJson

recall parse_eq_parseChars (text : String) : parse text = parseChars text.toList
#print axioms parse_eq_parseChars

recall render_toList (value : Json) : (render value).toList = renderChars value
#print axioms render_toList

end MiniJson.Proofs

/-! ## Claim 6. A text that parses to a value is that value's rendered text with white space added. -/

namespace MiniJson.Proofs

open MiniJson

recall parseChars_text (text : List Char) (value : Json) (parsed : parseChars text = some value) :
    text.filter (fun character => !isSpace character) = renderChars value
#print axioms parseChars_text

end MiniJson.Proofs

/-! ## Claim 7. A text parses to a value exactly when it is the value's tokens written out. -/

namespace MiniJson.Proofs

open MiniJson

recall parseChars_iff_writes (text : List Char) (value : Json) :
    parseChars text = some value ↔ writes (tokensOf value) text = true
#print axioms parseChars_iff_writes

end MiniJson.Proofs
