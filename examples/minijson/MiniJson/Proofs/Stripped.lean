/-
  File: MiniJson/Proofs/Stripped.lean
  Purpose: Whatever the tokenizer accepts is the text of its tokens with white space
  added: taking the white space out of an accepted text leaves exactly the characters the
  tokens are written with. This is what rules out a tokenizer that accepts too much, such
  as a number with a leading zero. The fact about numbers it rests on is that a run of
  digits with no leading zero is the decimal form of the number it writes.
  Created: 2026-11-14
-/

import MiniJson
import MiniJson.Proofs.Digits
import MiniJson.Proofs.Text

namespace MiniJson.Proofs

open MiniJson

/-- The characters a sequence of tokens is written with, nothing between them. -/
def tokensText (tokens : List Token) : List Char :=
  tokens.flatMap tokenText

/-- A text with its white space taken out. -/
def withoutSpaces (text : List Char) : List Char :=
  text.filter fun character => !isSpace character

theorem digit_bounds (character : Char) (isDigit : character.isDigit = true) :
    48 ≤ character.toNat ∧ character.toNat ≤ 57 := by
  simp [Char.isDigit, UInt32.le_iff_toNat_le] at isDigit
  exact isDigit

theorem digitChar_of_digit (character : Char) (isDigit : character.isDigit = true) :
    digitChar (character.toNat - '0'.toNat) = character := by
  have bounds := digit_bounds character isDigit
  have zero : '0'.toNat = 48 := rfl
  unfold digitChar
  rw [show '0'.toNat + (character.toNat - '0'.toNat) = character.toNat by omega]
  exact Char.ofNat_toNat character

theorem digit_value_lt (character : Char) (isDigit : character.isDigit = true) :
    character.toNat - '0'.toNat < 10 := by
  have bounds := digit_bounds character isDigit
  have zero : '0'.toNat = 48 := rfl
  omega

theorem digit_value_pos (character : Char) (isDigit : character.isDigit = true) (notZero : character ≠ '0') :
    1 ≤ character.toNat - '0'.toNat := by
  have bounds := digit_bounds character isDigit
  have zero : '0'.toNat = 48 := rfl
  have notFortyEight : character.toNat ≠ 48 := by
    intro same
    apply notZero
    have back := Char.ofNat_toNat character
    rw [same] at back
    exact back.symm
  omega

theorem foldl_digits_ge (digits : List Char) (start : Nat) :
    start ≤ digits.foldl (fun soFar digit => soFar * 10 + (digit.toNat - '0'.toNat)) start := by
  induction digits generalizing start with
  | nil => exact Nat.le_refl start
  | cons digit more hypothesis =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (by omega) (hypothesis _)

/-- A run of digits that does not start with `0` writes a number of at least 1. -/
theorem natOfDigits_pos (first : Char) (more : List Char) (isDigit : first.isDigit = true) (notZero : first ≠ '0') :
    1 ≤ natOfDigits (first :: more) := by
  have firstValue := digit_value_pos first isDigit notZero
  unfold natOfDigits
  simp only [List.foldl_cons]
  exact Nat.le_trans (by omega) (foldl_digits_ge more _)

/-- A run of digits with no leading zero is the decimal form of the number it writes.
    `count` is one less than the length of the run. -/
theorem digitsOf_natOfDigits (count : Nat) : ∀ digits : List Char, digits.length = count + 1 →
    (∀ character ∈ digits, character.isDigit = true) →
    (count ≠ 0 → ∀ first more, digits = first :: more → first ≠ '0') →
    digitsOf (natOfDigits digits) = digits := by
  induction count with
  | zero =>
    intro digits length allDigits _
    match digits, length with
    | [only], _ =>
      have isDigit := allDigits only (by simp)
      have small := digit_value_lt only isDigit
      have value : natOfDigits [only] = only.toNat - '0'.toNat := by simp [natOfDigits]
      rw [value]
      unfold digitsOf
      simp only [small, ↓reduceIte]
      rw [digitChar_of_digit only isDigit]
  | succ count hypothesis =>
    intro digits length allDigits noLeadingZero
    have notEmpty : digits ≠ [] := by
      intro empty
      simp [empty] at length
    obtain ⟨front, last, rfl⟩ : ∃ front last, digits = front ++ [last] :=
      ⟨digits.dropLast, digits.getLast notEmpty, (List.dropLast_concat_getLast notEmpty).symm⟩
    have frontLength : front.length = count + 1 := by
      simp at length
      omega
    have lastIsDigit := allDigits last (by simp)
    match front, frontLength with
    | first :: more, frontLength =>
      have frontDigits : ∀ character ∈ first :: more, character.isDigit = true :=
        fun character member => allDigits character (List.mem_append_left _ member)
      have firstNotZero : first ≠ '0' := noLeadingZero (by omega) first (more ++ [last]) rfl
      have frontPositive := natOfDigits_pos first more (frontDigits first (by simp)) firstNotZero
      have lastSmall := digit_value_lt last lastIsDigit
      have written := hypothesis (first :: more) frontLength frontDigits
        (fun _ head tail same => by injection same with sameHead _; rw [← sameHead]; exact firstNotZero)
      rw [natOfDigits_append_single]
      unfold digitsOf
      have large : ¬ natOfDigits (first :: more) * 10 + (last.toNat - '0'.toNat) < 10 := by omega
      simp only [large, ↓reduceIte]
      rw [show (natOfDigits (first :: more) * 10 + (last.toNat - '0'.toNat)) / 10 = natOfDigits (first :: more) by omega,
        show (natOfDigits (first :: more) * 10 + (last.toNat - '0'.toNat)) % 10 = last.toNat - '0'.toNat by omega,
        written, digitChar_of_digit last lastIsDigit]

/-- Every character `takeWhile` keeps passes the test it was kept by. -/
theorem takeWhile_all (test : Char → Bool) (text : List Char) :
    ∀ character ∈ text.takeWhile test, test character = true := by
  induction text with
  | nil => intro character member; simp at member
  | cons first rest hypothesis =>
    intro character member
    cases passes : test first with
    | false => simp [List.takeWhile, passes] at member
    | true =>
      simp only [List.takeWhile, passes, List.mem_cons] at member
      rcases member with same | inRest
      · rw [same]; exact passes
      · exact hypothesis character inRest

/-- Characters that are not white space stay when the white space is taken out. -/
theorem withoutSpaces_append (kept rest : List Char) (noSpaces : ∀ character ∈ kept, isSpace character = false) :
    withoutSpaces (kept ++ rest) = kept ++ withoutSpaces rest := by
  unfold withoutSpaces
  rw [List.filter_append, List.filter_eq_self.mpr (fun character member => by simp [noSpaces character member])]

/-- Whatever the tokenizer accepts, with its white space taken out, is the text of the
    tokens it returns. -/
theorem tokenizeWith_text (fuel : Nat) :
    ∀ text tokens, tokenizeWith fuel text = some tokens → withoutSpaces text = tokensText tokens := by
  induction fuel with
  | zero => intro text tokens read; simp [tokenizeWith] at read
  | succ fuel hypothesis =>
    intro text tokens read
    have step : ∀ (token : Token) (kept rest : List Char),
        (tokenizeWith fuel rest).map (token :: ·) = some tokens →
        (∀ character ∈ kept, isSpace character = false) → kept = tokenText token →
        withoutSpaces (kept ++ rest) = tokensText tokens := by
      intro token kept rest mapped noSpaces isText
      obtain ⟨after, readAfter, rfl⟩ := Option.map_eq_some_iff.mp mapped
      rw [withoutSpaces_append kept rest noSpaces, hypothesis rest after readAfter, isText]
      simp [tokensText]
    unfold tokenizeWith at read
    split at read
    case h_1 => omega
    case h_2 =>
      injection read with empty
      rw [← empty]
      rfl
    case h_3 => injection ‹fuel + 1 = _› with sameFuel; subst sameFuel; exact step _ ['['] _ read (by decide) rfl
    case h_4 => injection ‹fuel + 1 = _› with sameFuel; subst sameFuel; exact step _ [']'] _ read (by decide) rfl
    case h_5 => injection ‹fuel + 1 = _› with sameFuel; subst sameFuel; exact step _ [','] _ read (by decide) rfl
    case h_6 =>
      injection ‹fuel + 1 = _› with sameFuel; subst sameFuel
      exact step _ ['n', 'u', 'l', 'l'] _ read (by decide) rfl
    case h_7 =>
      injection ‹fuel + 1 = _› with sameFuel; subst sameFuel
      exact step _ ['t', 'r', 'u', 'e'] _ read (by decide) rfl
    case h_8 =>
      injection ‹fuel + 1 = _› with sameFuel; subst sameFuel
      exact step _ ['f', 'a', 'l', 's', 'e'] _ read (by decide) rfl
    case h_9 =>
      injection ‹fuel + 1 = _› with sameFuel; subst sameFuel
      rename_i first rest _ _ _ _ _ _
      split at read
      · rename_i isSpaceCharacter
        have dropped : withoutSpaces (first :: rest) = withoutSpaces rest := by
          simp [withoutSpaces, isSpaceCharacter]
        rw [dropped]
        exact hypothesis _ _ read
      · rename_i notSpace
        split at read
        · rename_i isDigitCharacter
          simp only at read
          split at read
          · contradiction
          · rename_i noLeadingZero
            have moreDigits : ∀ character ∈ rest.takeWhile Char.isDigit, character.isDigit = true :=
              takeWhile_all Char.isDigit rest
            have runDigits : ∀ character ∈ first :: rest.takeWhile Char.isDigit, character.isDigit = true := by
              intro character member
              rcases List.mem_cons.mp member with same | inMore
              · rw [same]; exact isDigitCharacter
              · exact moreDigits character inMore
            have canonical := digitsOf_natOfDigits (rest.takeWhile Char.isDigit).length
              (first :: rest.takeWhile Char.isDigit) (by simp) runDigits (by
                intro someMore head tail same isZero
                injection same with sameHead _
                apply noLeadingZero
                have notEmpty : (rest.takeWhile Char.isDigit).isEmpty = false := by
                  cases shape : rest.takeWhile Char.isDigit with
                  | nil => simp [shape] at someMore
                  | cons _ _ => rfl
                simp [sameHead, isZero, notEmpty])
            have whole : first :: rest = (first :: rest.takeWhile Char.isDigit) ++ rest.dropWhile Char.isDigit := by
              simp [List.takeWhile_append_dropWhile]
            rw [whole]
            exact step _ _ _ read
              (fun character member => isSpace_of_isDigit character (runDigits character member)) canonical.symm
        · contradiction

end MiniJson.Proofs
