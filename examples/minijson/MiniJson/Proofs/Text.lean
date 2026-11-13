/-
  File: MiniJson/Proofs/Text.lean
  Purpose: The tokenizer reads back what the renderer writes: the tokens of a value's
  text are the value's tokens. The facts on the way are that a number's digits are read
  as one number token when no digit follows them, and that a value's text has at least as
  many characters as the value has tokens, so the fuel `tokenize` gives is enough.
  Created: 2026-11-14
-/

import MiniJson
import MiniJson.Proofs.Digits

namespace MiniJson.Proofs

open MiniJson

/-- A text that does not begin with a digit: it is empty or its first character is none. -/
def NoDigitFirst (text : List Char) : Prop :=
  ∀ first more, text = first :: more → first.isDigit = false

theorem noDigitFirst_nil : NoDigitFirst [] := by
  intro first more impossible
  contradiction

theorem noDigitFirst_cons (first : Char) (more : List Char) (notDigit : first.isDigit = false) :
    NoDigitFirst (first :: more) := by
  intro head tail same
  injection same with sameHead _
  rw [← sameHead]
  exact notDigit

/-- A digit is not white space. -/
theorem isSpace_of_isDigit (character : Char) (isDigit : character.isDigit = true) : isSpace character = false := by
  cases spaceOrNot : isSpace character with
  | false => rfl
  | true =>
    simp [isSpace] at spaceOrNot
    rcases spaceOrNot with ((same | same) | same) | same <;> rw [same] at isDigit <;> contradiction

theorem takeWhile_digits (digits rest : List Char) (allDigits : ∀ character ∈ digits, character.isDigit = true)
    (noDigitNext : NoDigitFirst rest) : (digits ++ rest).takeWhile Char.isDigit = digits := by
  induction digits with
  | nil =>
    cases rest with
    | nil => rfl
    | cons first more => simp [noDigitNext first more rfl]
  | cons first more hypothesis =>
    simp [allDigits first (by simp), hypothesis (fun character member => allDigits character (by simp [member]))]

theorem dropWhile_digits (digits rest : List Char) (allDigits : ∀ character ∈ digits, character.isDigit = true)
    (noDigitNext : NoDigitFirst rest) : (digits ++ rest).dropWhile Char.isDigit = rest := by
  induction digits with
  | nil =>
    cases rest with
    | nil => rfl
    | cons first more => simp [noDigitNext first more rfl]
  | cons first more hypothesis =>
    simp [allDigits first (by simp), hypothesis (fun character member => allDigits character (by simp [member]))]

/-- The digits of a number, with no digit after them, are read as that number's token. -/
theorem tokenizeWith_digitsOf (number fuel : Nat) (rest : List Char) (noDigitNext : NoDigitFirst rest) :
    tokenizeWith (fuel + 1) (digitsOf number ++ rest) =
      (tokenizeWith fuel rest).map (Token.number number :: ·) := by
  obtain ⟨first, more, shape, firstNotZero, moreMeansLarge⟩ := digitsOf_shape number
  have allDigits := digitsOf_all_digits number
  have readBack := natOfDigits_digitsOf number
  rw [shape] at allDigits readBack
  have firstIsDigit : first.isDigit = true := allDigits first (by simp)
  have moreAreDigits : ∀ character ∈ more, character.isDigit = true :=
    fun character member => allDigits character (by simp [member])
  have noLeadingZero : (first == '0' && !more.isEmpty) = false := by
    cases more with
    | nil => simp
    | cons second others =>
      have notZero := firstNotZero (by have := moreMeansLarge (by simp); omega)
      simp [notZero]
  rw [shape]
  show tokenizeWith (fuel + 1) (first :: (more ++ rest)) = _
  conv => lhs; unfold tokenizeWith
  split
  case h_9 =>
    injection ‹first :: (more ++ rest) = _› with sameFirst sameRest
    injection ‹fuel + 1 = _› with sameFuel
    subst sameFirst sameRest sameFuel
    simp [isSpace_of_isDigit first firstIsDigit, firstIsDigit, takeWhile_digits more rest moreAreDigits noDigitNext,
      dropWhile_digits more rest moreAreDigits noDigitNext, readBack]
    intro isZero moreDigits
    simp [isZero] at noLeadingZero
    exact absurd noLeadingZero moreDigits
  -- Every other case is no fuel, no character, or a first character that is no digit.
  all_goals first
    | omega
    | contradiction
    | (injection ‹first :: (more ++ rest) = _› with sameFirst _
       rw [sameFirst] at firstIsDigit
       exact absurd firstIsDigit (by decide))

/-- What follows the first item of an array does not begin with a digit: it begins with a
    comma or the closing bracket. -/
theorem noDigitFirst_renderAfterFirst (items : List Json) (rest : List Char) :
    NoDigitFirst (renderAfterFirst items ++ rest) := by
  cases items with
  | nil => exact noDigitFirst_cons _ _ (by decide)
  | cons item others => exact noDigitFirst_cons _ _ (by decide)

/-- The tokenizer reads `rest` as `restTokens` whenever it has at least `needed` units of
    fuel. Stating it for every such amount, and not for one, is what lets the facts below
    be put together without a separate argument that more fuel changes nothing. -/
def ReadsWith (needed : Nat) (rest : List Char) (restTokens : List Token) : Prop :=
  ∀ fuel, needed ≤ fuel → tokenizeWith fuel rest = some restTokens

mutual

/-- The tokenizer reads a value's text as the value's tokens, then goes on with what
    follows, provided no digit follows. It needs one unit of fuel for each token. -/
theorem tokenizeWith_renderChars (value : Json) (needed : Nat) (rest : List Char) (restTokens : List Token)
    (noDigitNext : NoDigitFirst rest) (readRest : ReadsWith needed rest restTokens) :
    ReadsWith ((tokensOf value).length + needed) (renderChars value ++ rest) (tokensOf value ++ restTokens) := by
  intro fuel enough
  match value with
  | .null =>
    obtain ⟨fuel, rfl⟩ : ∃ less, fuel = less + 1 := ⟨fuel - 1, by simp [tokensOf] at enough; omega⟩
    simp [tokensOf, renderChars, tokenizeWith, readRest fuel (by simp [tokensOf] at enough; omega)]
  | .bool true =>
    obtain ⟨fuel, rfl⟩ : ∃ less, fuel = less + 1 := ⟨fuel - 1, by simp [tokensOf] at enough; omega⟩
    simp [tokensOf, renderChars, tokenizeWith, readRest fuel (by simp [tokensOf] at enough; omega)]
  | .bool false =>
    obtain ⟨fuel, rfl⟩ : ∃ less, fuel = less + 1 := ⟨fuel - 1, by simp [tokensOf] at enough; omega⟩
    simp [tokensOf, renderChars, tokenizeWith, readRest fuel (by simp [tokensOf] at enough; omega)]
  | .number amount =>
    obtain ⟨fuel, rfl⟩ : ∃ less, fuel = less + 1 := ⟨fuel - 1, by simp [tokensOf] at enough; omega⟩
    simp only [tokensOf, renderChars]
    rw [tokenizeWith_digitsOf amount fuel rest noDigitNext, readRest fuel (by simp [tokensOf] at enough; omega)]
    rfl
  | .array [] =>
    obtain ⟨fuel, rfl⟩ : ∃ less, fuel = (less + 1) + 1 := ⟨fuel - 2, by simp [tokensOf] at enough; omega⟩
    simp [tokensOf, renderChars, tokenizeWith, readRest fuel (by simp [tokensOf] at enough; omega)]
  | .array (first :: others) =>
    have lengths : 1 + (tokensOf first).length + (tokensAfterFirst others).length + needed ≤ fuel := by
      simp [tokensOf] at enough
      omega
    obtain ⟨fuel, rfl⟩ : ∃ less, fuel = less + 1 := ⟨fuel - 1, by omega⟩
    have readOthers := tokenizeWith_renderAfterFirst others needed rest restTokens noDigitNext readRest
    have readFirst := tokenizeWith_renderChars first ((tokensAfterFirst others).length + needed)
      (renderAfterFirst others ++ rest) (tokensAfterFirst others ++ restTokens)
      (noDigitFirst_renderAfterFirst others rest) readOthers fuel (by omega)
    simp [tokensOf, renderChars, tokenizeWith, readFirst]

theorem tokenizeWith_renderAfterFirst (items : List Json) (needed : Nat) (rest : List Char)
    (restTokens : List Token) (noDigitNext : NoDigitFirst rest) (readRest : ReadsWith needed rest restTokens) :
    ReadsWith ((tokensAfterFirst items).length + needed) (renderAfterFirst items ++ rest)
      (tokensAfterFirst items ++ restTokens) := by
  intro fuel enough
  match items with
  | [] =>
    obtain ⟨fuel, rfl⟩ : ∃ less, fuel = less + 1 := ⟨fuel - 1, by simp [tokensAfterFirst] at enough; omega⟩
    simp [tokensAfterFirst, renderAfterFirst, tokenizeWith, readRest fuel (by simp [tokensAfterFirst] at enough; omega)]
  | item :: others =>
    have lengths : 1 + (tokensOf item).length + (tokensAfterFirst others).length + needed ≤ fuel := by
      simp [tokensAfterFirst] at enough
      omega
    obtain ⟨fuel, rfl⟩ : ∃ less, fuel = less + 1 := ⟨fuel - 1, by omega⟩
    have readOthers := tokenizeWith_renderAfterFirst others needed rest restTokens noDigitNext readRest
    have readItem := tokenizeWith_renderChars item ((tokensAfterFirst others).length + needed)
      (renderAfterFirst others ++ rest) (tokensAfterFirst others ++ restTokens)
      (noDigitFirst_renderAfterFirst others rest) readOthers fuel (by omega)
    simp [tokensAfterFirst, renderAfterFirst, tokenizeWith, readItem]

end

mutual

/-- A value's text has at least one character for each of its tokens. -/
theorem tokens_le_chars (value : Json) : (tokensOf value).length ≤ (renderChars value).length := by
  match value with
  | .null => simp [tokensOf, renderChars]
  | .bool true => simp [tokensOf, renderChars]
  | .bool false => simp [tokensOf, renderChars]
  | .number amount =>
    obtain ⟨first, more, shape, _, _⟩ := digitsOf_shape amount
    simp [tokensOf, renderChars, shape]
  | .array [] => simp [tokensOf, renderChars]
  | .array (first :: others) =>
    have firstBound := tokens_le_chars first
    have othersBound := tokensAfterFirst_le_chars others
    simp [tokensOf, renderChars]
    omega

theorem tokensAfterFirst_le_chars (items : List Json) :
    (tokensAfterFirst items).length ≤ (renderAfterFirst items).length := by
  match items with
  | [] => simp [tokensAfterFirst, renderAfterFirst]
  | item :: others =>
    have itemBound := tokens_le_chars item
    have othersBound := tokensAfterFirst_le_chars others
    simp [tokensAfterFirst, renderAfterFirst]
    omega

end

/-- The tokens of a value's text are the value's tokens. -/
theorem tokenize_renderChars_tokens (value : Json) : tokenize (renderChars value) = some (tokensOf value) := by
  have nothingLeft : ReadsWith 1 [] [] := by
    intro fuel enough
    obtain ⟨fuel, rfl⟩ : ∃ less, fuel = less + 1 := ⟨fuel - 1, by omega⟩
    simp [tokenizeWith]
  have read := tokenizeWith_renderChars value 1 [] [] noDigitFirst_nil nothingLeft
    ((renderChars value).length + 1) (by have bound := tokens_le_chars value; omega)
  simpa [tokenize] using read

end MiniJson.Proofs
