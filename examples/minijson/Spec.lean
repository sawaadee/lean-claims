/-
  File: Spec.lean
  Purpose: Every guarantee this project makes, stated with the proofs left out. A reviewer
  who reads this file, and the definitions it mentions, knows what is guaranteed. Each
  theorem is proved under the same name in `MiniJson/Proofs/`, and `lake comparator` checks
  that what is proved there is exactly what is stated here.

  The claims are about a subset of JSON: `null`, `true`, `false`, natural numbers and
  arrays. They are stated on lists of characters. Claim 5 says the functions on `String`
  are the same functions.

  To read the claims a reviewer needs three definitions: `Json`, the values; `tokensOf`,
  the tokens that stand for a value; and `writes`, which says what it is for a text to be
  a sequence of tokens written out. Claims 1 and 2 are stated against the tokenizer, and
  claim 7 says the same of the parser without it, so the tokenizer does not have to be
  taken on trust. `TRUST.md` lists everything the claims are built from.

  This file is written by hand and no tool writes to it. `spec.lock` records a hash of
  every claim, and every lean-claims command stops when the two differ. After a change to
  a claim that is meant, run `claims lock --update`.

  The module is its own library, `Spec`. It is not a default target and nothing imports
  it, so its `sorry`s never reach `lake build`.
  Created: 2026-11-14
-/

import MiniJson

/-! ## Claim 1. A text parses to a value exactly when the text's tokens are the value's tokens.

This says everything about what the parser accepts and what it returns. A text that is
not made of tokens parses to nothing. A text whose tokens are not those of any value
parses to nothing. White space between tokens changes nothing, because it is not a
token. -/

namespace MiniJson.Proofs

open MiniJson

/-- There is no hypothesis. The left side is the parser returning `value` for `text`. The
    right side is `tokenize` succeeding on `text` with exactly the tokens `tokensOf` gives
    for `value`. -/
theorem parseChars_iff (text : List Char) (value : Json) :
    parseChars text = some value ↔ tokenize text = some (tokensOf value) := by
  sorry

end MiniJson.Proofs

/-! ## Claim 2. The text the renderer writes for a value has exactly that value's tokens.

The renderer writes nothing that is not a token of the value, leaves none out, and writes
them in order. -/

namespace MiniJson.Proofs

open MiniJson

/-- There is no hypothesis. `tokenize` succeeds on the rendered text, and its result is
    what `tokensOf` gives for the value. -/
theorem tokenize_renderChars (value : Json) : tokenize (renderChars value) = some (tokensOf value) := by
  sorry

end MiniJson.Proofs

/-! ## Claim 3. Parsing the text rendered for a value gives the value back.

This is the property a caller relies on: nothing is lost or changed by writing a value
out and reading it in. It follows from claims 1 and 2 and is stated for both forms of the
two functions. -/

namespace MiniJson.Proofs

open MiniJson

/-- On lists of characters. There is no hypothesis: it holds for every value. -/
theorem parseChars_renderChars (value : Json) : parseChars (renderChars value) = some value := by
  sorry

/-- On strings. There is no hypothesis: it holds for every value. -/
theorem parse_render (value : Json) : parse (render value) = some value := by
  sorry

end MiniJson.Proofs

/-! ## Claim 4. Two values with the same rendered text are the same value.

No two different values are written the same way, so a rendered text can stand for a
value wherever the value is wanted, as a key or in a comparison. -/

namespace MiniJson.Proofs

open MiniJson

/-- `sameText` says the two values are rendered to the same characters. The conclusion is
    that they are one value. -/
theorem renderChars_injective (first second : Json) (sameText : renderChars first = renderChars second) :
    first = second := by
  sorry

end MiniJson.Proofs

/-! ## Claim 5. The functions on strings are the functions on lists of characters.

`parse` and `render` add nothing of their own: one hands the string's characters to
`parseChars`, and the other makes a string of the characters `renderChars` gives. Every
claim about the two functions on lists of characters is therefore a claim about these. -/

namespace MiniJson.Proofs

open MiniJson

/-- There is no hypothesis. Parsing a string is parsing its list of characters. -/
theorem parse_eq_parseChars (text : String) : parse text = parseChars text.toList := by
  sorry

/-- There is no hypothesis. The characters of a rendered string are the rendered
    characters. -/
theorem render_toList (value : Json) : (render value).toList = renderChars value := by
  sorry

end MiniJson.Proofs

/-! ## Claim 6. A text that parses to a value is that value's rendered text with white space added.

Taking the white space out of any accepted text leaves exactly the characters the renderer
writes for the value. So the parser accepts no other way of writing a value: no leading
zero on a number, no other spelling of a word, nothing extra. Claim 1 says a text is
accepted by its tokens; this claim says what a text with those tokens can look like. -/

namespace MiniJson.Proofs

open MiniJson

/-- `parsed` says the parser returns `value` for `text`. The conclusion compares two lists
    of characters: `text` with every white space character filtered out, and the text
    `renderChars` writes for `value`. -/
theorem parseChars_text (text : List Char) (value : Json) (parsed : parseChars text = some value) :
    text.filter (fun character => !isSpace character) = renderChars value := by
  sorry

end MiniJson.Proofs

/-! ## Claim 7. A text parses to a value exactly when it is the value's tokens written out.

"Written out" is `writes`: any white space, then the first token's characters, then any
white space, then the next token's characters, and so on, with only white space after the
last. This says which texts the parser accepts and what it returns for each, and it says
so without the tokenizer. Claim 1 holds the parser to the tokenizer; this claim holds both
to a definition short enough to check by reading. White space inside a word or a number
is refused, a leading zero is refused, and white space between tokens is always allowed. -/

namespace MiniJson.Proofs

open MiniJson

/-- There is no hypothesis. The left side is the parser returning `value` for `text`. The
    right side is `writes` answering yes for the tokens `tokensOf` gives for `value` and
    the same `text`. -/
theorem parseChars_iff_writes (text : List Char) (value : Json) :
    parseChars text = some value ↔ writes (tokensOf value) text = true := by
  sorry

end MiniJson.Proofs
