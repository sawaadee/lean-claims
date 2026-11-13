/-
  File: MiniJson/Proofs/Digits.lean
  Purpose: Facts about writing a number in decimal and reading it back, which the proofs
  about the tokenizer and the renderer rest on: `digitsOf` gives digits only, gives no
  leading zero, and `natOfDigits` reads its result back as the number.
  Created: 2026-11-14
-/

import MiniJson

namespace MiniJson.Proofs

open MiniJson

/-- The character of a digit has the code of `0` plus the digit. The facts about digit
    characters below follow from this by arithmetic, so that no kernel has to compute with
    characters to check them. -/
theorem digitChar_toNat (digit : Nat) (isDigit : digit < 10) : (digitChar digit).toNat = 48 + digit := by
  unfold digitChar
  have zero : '0'.toNat = 48 := rfl
  rw [zero]
  simp [Char.toNat, Char.ofNat, Nat.isValidChar, show 48 + digit < 55296 by omega, Char.ofNatAux]
  omega

theorem digitChar_isDigit (digit : Nat) (isDigit : digit < 10) : (digitChar digit).isDigit = true := by
  have code : (digitChar digit).val.toNat = 48 + digit := digitChar_toNat digit isDigit
  simp [Char.isDigit, UInt32.le_iff_toNat_le, code]
  omega

theorem digitChar_value (digit : Nat) (isDigit : digit < 10) : (digitChar digit).toNat - '0'.toNat = digit := by
  have zero : '0'.toNat = 48 := rfl
  rw [digitChar_toNat digit isDigit, zero]
  omega

theorem digitChar_ne_zero (digit : Nat) (isDigit : digit < 10) (notZero : digit ≠ 0) : digitChar digit ≠ '0' := by
  intro same
  have code := digitChar_toNat digit isDigit
  rw [same] at code
  have zero : '0'.toNat = 48 := rfl
  omega

/-- Reading one more digit multiplies what was read by ten and adds the digit. -/
theorem natOfDigits_append_single (digits : List Char) (last : Char) :
    natOfDigits (digits ++ [last]) = natOfDigits digits * 10 + (last.toNat - '0'.toNat) := by
  simp [natOfDigits, List.foldl_append]

/-- What `digitsOf` writes, `natOfDigits` reads back. -/
theorem natOfDigits_digitsOf (number : Nat) : natOfDigits (digitsOf number) = number := by
  induction number using Nat.strongRecOn with
  | _ number hypothesis =>
    unfold digitsOf
    split
    · rename_i small
      simpa [natOfDigits] using digitChar_value number small
    · rename_i large
      rw [natOfDigits_append_single, hypothesis (number / 10) (by omega),
        digitChar_value (number % 10) (by omega)]
      omega

/-- Every character `digitsOf` writes is a decimal digit. -/
theorem digitsOf_all_digits (number : Nat) : ∀ character ∈ digitsOf number, character.isDigit = true := by
  induction number using Nat.strongRecOn with
  | _ number hypothesis =>
    unfold digitsOf
    split
    · rename_i small
      intro character member
      simp at member
      rw [member]
      exact digitChar_isDigit number small
    · intro character member
      rcases List.mem_append.mp member with inFront | isLast
      · exact hypothesis (number / 10) (by omega) character inFront
      · simp at isLast
        rw [isLast]
        exact digitChar_isDigit (number % 10) (by omega)

/-- `digitsOf` writes a first digit, which is `0` only for the number 0, and writes
    further digits only for a number of 10 or more. -/
theorem digitsOf_shape (number : Nat) :
    ∃ first more, digitsOf number = first :: more ∧ (number ≠ 0 → first ≠ '0') ∧ (more ≠ [] → 10 ≤ number) := by
  induction number using Nat.strongRecOn with
  | _ number hypothesis =>
    unfold digitsOf
    split
    · rename_i small
      exact ⟨digitChar number, [], rfl, fun notZero => digitChar_ne_zero number small notZero, fun notEmpty => absurd rfl notEmpty⟩
    · rename_i large
      obtain ⟨first, more, shape, firstNotZero, _⟩ := hypothesis (number / 10) (by omega)
      refine ⟨first, more ++ [digitChar (number % 10)], by simp [shape], fun _ => firstNotZero (by omega), fun _ => by omega⟩

end MiniJson.Proofs
