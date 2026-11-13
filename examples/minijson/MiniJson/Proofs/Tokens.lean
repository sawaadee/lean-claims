/-
  File: MiniJson/Proofs/Tokens.lean
  Purpose: The parser on tokens is exact: it reads a value from a sequence of tokens
  precisely when the sequence is that value's tokens. One direction says the parser
  accepts every value's tokens (it is complete). The other says that whatever it accepts
  was some value's tokens (it is sound).
  Created: 2026-11-14
-/

import MiniJson

namespace MiniJson.Proofs

open MiniJson

/-- A value's tokens start with a token that is not a closing bracket. -/
theorem tokensOf_starts (value : Json) :
    ∃ first more, tokensOf value = first :: more ∧ first ≠ Token.closeBracket := by
  cases value with
  | null => exact ⟨_, _, rfl, by decide⟩
  | bool flag => cases flag <;> exact ⟨_, _, rfl, by decide⟩
  | number amount => exact ⟨_, _, rfl, by simp⟩
  | array items => cases items <;> exact ⟨_, _, rfl, by decide⟩

mutual

/-- Complete: with enough fuel, the parser reads a value back from its tokens and leaves
    what follows them. -/
theorem parseValue_tokensOf (value : Json) (fuel : Nat) (rest : List Token)
    (enough : (tokensOf value).length ≤ fuel) :
    parseValue fuel (tokensOf value ++ rest) = some (value, rest) := by
  match value, fuel with
  | .null, fuel + 1 => simp [tokensOf, parseValue]
  | .bool true, fuel + 1 => simp [tokensOf, parseValue]
  | .bool false, fuel + 1 => simp [tokensOf, parseValue]
  | .number amount, fuel + 1 => simp [tokensOf, parseValue]
  | .array [], fuel + 1 => simp [tokensOf, parseValue]
  | .array (first :: others), fuel + 1 =>
    have lengths : (tokensOf first).length + (tokensAfterFirst others).length ≤ fuel := by
      simp [tokensOf] at enough
      omega
    have readFirst := parseValue_tokensOf first fuel (tokensAfterFirst others ++ rest) (by omega)
    have readOthers := parseAfterFirst_tokensAfterFirst others fuel rest (by omega)
    obtain ⟨firstToken, moreTokens, shape, notClose⟩ := tokensOf_starts first
    rw [shape] at readFirst
    cases firstToken <;> simp_all [tokensOf, parseValue]
  | value, 0 =>
    obtain ⟨firstToken, moreTokens, shape, _⟩ := tokensOf_starts value
    simp [shape] at enough

theorem parseAfterFirst_tokensAfterFirst (items : List Json) (fuel : Nat) (rest : List Token)
    (enough : (tokensAfterFirst items).length ≤ fuel) :
    parseAfterFirst fuel (tokensAfterFirst items ++ rest) = some (items, rest) := by
  match items, fuel with
  | [], fuel + 1 => simp [tokensAfterFirst, parseAfterFirst]
  | item :: others, fuel + 1 =>
    have lengths : (tokensOf item).length + (tokensAfterFirst others).length ≤ fuel := by
      simp [tokensAfterFirst] at enough
      omega
    have readItem := parseValue_tokensOf item fuel (tokensAfterFirst others ++ rest) (by omega)
    have readOthers := parseAfterFirst_tokensAfterFirst others fuel rest (by omega)
    simp [tokensAfterFirst, parseAfterFirst, readItem, readOthers]
  | [], 0 => simp [tokensAfterFirst] at enough
  | _ :: _, 0 => simp [tokensAfterFirst] at enough

end

/-- Sound: whatever the parser reads was the tokens of the value it returns, followed by
    the tokens it leaves. Both parsers are treated at once, by the fuel. -/
theorem parse_sound (fuel : Nat) :
    (∀ tokens value rest, parseValue fuel tokens = some (value, rest) → tokens = tokensOf value ++ rest) ∧
    (∀ tokens items rest, parseAfterFirst fuel tokens = some (items, rest) →
      tokens = tokensAfterFirst items ++ rest) := by
  induction fuel with
  | zero => constructor <;> intro tokens _ _ parsed <;> simp [parseValue, parseAfterFirst] at parsed
  | succ fuel hypothesis =>
    obtain ⟨valueSound, afterFirstSound⟩ := hypothesis
    constructor
    · intro tokens value rest parsed
      unfold parseValue at parsed
      split at parsed
      all_goals try (simp at parsed; obtain ⟨rfl, rfl⟩ := parsed; simp [tokensOf])
      · contradiction
      · split at parsed
        · rename_i first afterFirst readFirst
          split at parsed
          · rename_i others afterArray readOthers
            simp at parsed
            obtain ⟨rfl, rfl⟩ := parsed
            injection ‹fuel + 1 = _› with sameFuel
            subst sameFuel
            rw [valueSound _ _ _ readFirst, afterFirstSound _ _ _ readOthers]
            simp [tokensOf]
          · contradiction
        · contradiction
      · contradiction
    · intro tokens items rest parsed
      unfold parseAfterFirst at parsed
      split at parsed
      · contradiction
      · simp at parsed
        obtain ⟨rfl, rfl⟩ := parsed
        simp [tokensAfterFirst]
      · split at parsed
        · rename_i item afterItem readItem
          split at parsed
          · rename_i others afterArray readOthers
            simp at parsed
            obtain ⟨rfl, rfl⟩ := parsed
            injection ‹fuel + 1 = _› with sameFuel
            subst sameFuel
            rw [valueSound _ _ _ readItem, afterFirstSound _ _ _ readOthers]
            simp [tokensAfterFirst]
          · contradiction
        · contradiction
      · contradiction

/-- The parser on tokens is exact: a sequence of tokens parses to a value exactly when
    it is that value's tokens. -/
theorem parseTokens_iff (tokens : List Token) (value : Json) :
    parseTokens tokens = some value ↔ tokens = tokensOf value := by
  constructor
  · intro parsed
    unfold parseTokens at parsed
    split at parsed
    · rename_i parsedValue readValue
      simp at parsed
      rw [← parsed]
      simpa using (parse_sound _).1 _ _ _ readValue
    · contradiction
  · intro isTokens
    rw [isTokens]
    unfold parseTokens
    have readValue := parseValue_tokensOf value ((tokensOf value).length + 1) [] (by omega)
    simp at readValue
    simp [readValue]

end MiniJson.Proofs
