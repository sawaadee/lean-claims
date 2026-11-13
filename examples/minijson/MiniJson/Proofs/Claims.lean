/-
  File: MiniJson/Proofs/Claims.lean
  Purpose: The proofs of the claims in `Spec.lean`, each under the name and with the
  statement the spec gives it. They rest on the exactness of the parser on tokens
  (`MiniJson/Proofs/Tokens.lean`) and on the tokenizer reading back the renderer's text
  (`MiniJson/Proofs/Text.lean`), and claim 6 on an accepted text being its tokens' text with
  white space added (`MiniJson/Proofs/Stripped.lean`), and claim 7 on the tokenizer accepting
  exactly the texts that are tokens written out (`MiniJson/Proofs/Written.lean`).
  Created: 2026-11-14
-/

import MiniJson
import MiniJson.Proofs.Tokens
import MiniJson.Proofs.Text
import MiniJson.Proofs.Stripped
import MiniJson.Proofs.Written

namespace MiniJson.Proofs

open MiniJson

theorem parseChars_iff (text : List Char) (value : Json) :
    parseChars text = some value ↔ tokenize text = some (tokensOf value) := by
  unfold parseChars
  cases tokenize text with
  | none => simp
  | some tokens => simp [parseTokens_iff]

theorem tokenize_renderChars (value : Json) : tokenize (renderChars value) = some (tokensOf value) :=
  tokenize_renderChars_tokens value

theorem parseChars_renderChars (value : Json) : parseChars (renderChars value) = some value :=
  (parseChars_iff (renderChars value) value).mpr (tokenize_renderChars value)

theorem parse_render (value : Json) : parse (render value) = some value := by
  simp [parse, render, parseChars_renderChars]

theorem renderChars_injective (first second : Json) (sameText : renderChars first = renderChars second) :
    first = second := by
  have parsedFirst := parseChars_renderChars first
  rw [sameText, parseChars_renderChars second] at parsedFirst
  exact (Option.some.inj parsedFirst).symm

theorem parse_eq_parseChars (text : String) : parse text = parseChars text.toList := rfl

theorem render_toList (value : Json) : (render value).toList = renderChars value := by
  simp [render]

mutual

/-- The text of a value's tokens is the value's rendered text. -/
theorem tokensText_tokensOf (value : Json) : tokensText (tokensOf value) = renderChars value := by
  match value with
  | .null => rfl
  | .bool true => rfl
  | .bool false => rfl
  | .number amount => simp [tokensText, tokensOf, tokenText, renderChars]
  | .array [] => rfl
  | .array (first :: others) =>
    have firstText := tokensText_tokensOf first
    have othersText := tokensText_tokensAfterFirst others
    simp only [tokensText] at firstText othersText ⊢
    simp [tokensOf, renderChars, tokenText, firstText, othersText]

theorem tokensText_tokensAfterFirst (items : List Json) :
    tokensText (tokensAfterFirst items) = renderAfterFirst items := by
  match items with
  | [] => rfl
  | item :: others =>
    have itemText := tokensText_tokensOf item
    have othersText := tokensText_tokensAfterFirst others
    simp only [tokensText] at itemText othersText ⊢
    simp [tokensAfterFirst, renderAfterFirst, tokenText, itemText, othersText]

end

theorem parseChars_text (text : List Char) (value : Json) (parsed : parseChars text = some value) :
    text.filter (fun character => !isSpace character) = renderChars value := by
  have tokens := (parseChars_iff text value).mp parsed
  have stripped := tokenizeWith_text _ text _ tokens
  rw [tokensText_tokensOf] at stripped
  exact stripped

theorem parseChars_iff_writes (text : List Char) (value : Json) :
    parseChars text = some value ↔ writes (tokensOf value) text = true :=
  (parseChars_iff text value).trans (tokenize_iff_writes text value)

end MiniJson.Proofs
