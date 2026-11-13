/-
  File: MiniJson/Proofs/Written.lean
  Purpose: The tokenizer accepts exactly the texts that are tokens written out, in the
  sense of `writes`: it returns a sequence of tokens for a text precisely when the text is
  those tokens with white space only between them. One direction says the tokenizer
  accepts nothing else. The other says it refuses nothing of that form, for sequences in
  which no two numbers stand side by side, which the tokens of a value never do.
  Created: 2026-11-14
-/

import MiniJson
import MiniJson.Proofs.Digits
import MiniJson.Proofs.Text
import MiniJson.Proofs.Tokens
import MiniJson.Proofs.Stripped

namespace MiniJson.Proofs

open MiniJson

theorem dropSpaces_space (first : Char) (rest : List Char) (isSpaceCharacter : isSpace first = true) :
    dropSpaces (first :: rest) = dropSpaces rest := by
  simp [dropSpaces, List.dropWhile, isSpaceCharacter]

theorem dropSpaces_not_space (first : Char) (rest : List Char) (notSpace : isSpace first = false) :
    dropSpaces (first :: rest) = first :: rest := by
  simp [dropSpaces, List.dropWhile, notSpace]

/-- White space in front of a text does not change which tokens it writes. -/
theorem writes_space (tokens : List Token) (first : Char) (rest : List Char) (isSpaceCharacter : isSpace first = true) :
    writes tokens (first :: rest) = writes tokens rest := by
  cases tokens <;> simp [writes, dropSpaces_space first rest isSpaceCharacter]

/-- Every token's text starts with a character that is not white space. -/
theorem tokenText_starts (token : Token) :
    ∃ first more, tokenText token = first :: more ∧ isSpace first = false := by
  cases token with
  | number value =>
    obtain ⟨first, more, shape, _, _⟩ := digitsOf_shape value
    have firstIsDigit : first.isDigit = true := digitsOf_all_digits value first (by simp [shape])
    exact ⟨first, more, shape, isSpace_of_isDigit first firstIsDigit⟩
  | _ => exact ⟨_, _, rfl, by decide⟩

/-- A token's text followed by a text writes that token and then whatever the text writes. -/
theorem writes_token (token : Token) (more : List Token) (rest : List Char) :
    writes (token :: more) (tokenText token ++ rest) = writes more rest := by
  obtain ⟨first, tail, shape, notSpace⟩ := tokenText_starts token
  have atFront : dropSpaces (tokenText token ++ rest) = tokenText token ++ rest := by
    rw [shape]
    exact dropSpaces_not_space first (tail ++ rest) notSpace
  simp [writes, atFront, List.isPrefixOf_iff_prefix.mpr (List.prefix_append _ _)]

/-- The tokenizer accepts nothing else: whatever it returns for a text, the text is those
    tokens written out. -/
theorem tokenizeWith_writes (fuel : Nat) :
    ∀ text tokens, tokenizeWith fuel text = some tokens → writes tokens text = true := by
  induction fuel with
  | zero => intro text tokens read; simp [tokenizeWith] at read
  | succ fuel hypothesis =>
    intro text tokens read
    have step : ∀ (token : Token) (kept rest : List Char),
        (tokenizeWith fuel rest).map (token :: ·) = some tokens → kept = tokenText token →
        writes tokens (kept ++ rest) = true := by
      intro token kept rest mapped isText
      obtain ⟨after, readAfter, rfl⟩ := Option.map_eq_some_iff.mp mapped
      rw [isText, writes_token]
      exact hypothesis rest after readAfter
    unfold tokenizeWith at read
    split at read
    case h_1 => omega
    case h_2 =>
      injection read with empty
      rw [← empty]
      rfl
    case h_3 => injection ‹fuel + 1 = _› with sameFuel; subst sameFuel; exact step _ ['['] _ read rfl
    case h_4 => injection ‹fuel + 1 = _› with sameFuel; subst sameFuel; exact step _ [']'] _ read rfl
    case h_5 => injection ‹fuel + 1 = _› with sameFuel; subst sameFuel; exact step _ [','] _ read rfl
    case h_6 => injection ‹fuel + 1 = _› with sameFuel; subst sameFuel; exact step _ ['n', 'u', 'l', 'l'] _ read rfl
    case h_7 => injection ‹fuel + 1 = _› with sameFuel; subst sameFuel; exact step _ ['t', 'r', 'u', 'e'] _ read rfl
    case h_8 =>
      injection ‹fuel + 1 = _› with sameFuel; subst sameFuel
      exact step _ ['f', 'a', 'l', 's', 'e'] _ read rfl
    case h_9 =>
      injection ‹fuel + 1 = _› with sameFuel; subst sameFuel
      rename_i first rest _ _ _ _ _ _
      split at read
      · rename_i isSpaceCharacter
        rw [writes_space tokens first rest isSpaceCharacter]
        exact hypothesis _ _ read
      · split at read
        · rename_i isDigitCharacter
          simp only at read
          split at read
          · contradiction
          · rename_i noLeadingZero
            have runDigits : ∀ character ∈ first :: rest.takeWhile Char.isDigit, character.isDigit = true := by
              intro character member
              rcases List.mem_cons.mp member with same | inMore
              · rw [same]; exact isDigitCharacter
              · exact takeWhile_all Char.isDigit rest character inMore
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
            exact step _ _ _ read canonical.symm
        · contradiction

/-! ## The other direction: the tokenizer refuses nothing of that form -/

/-- Whether a token is a number. -/
def isNumber : Token → Bool
  | .number _ => true
  | _ => false

/-- Whether no two numbers stand side by side in a sequence of tokens. Two numbers side by
    side cannot be written without white space between them, and with it or without it the
    tokenizer is right to read their text differently, so the direction below is about
    sequences where it does not happen. -/
def separated : List Token → Bool
  | first :: second :: rest => !(isNumber first && isNumber second) && separated (second :: rest)
  | _ => true

theorem separated_tail (first : Token) (more : List Token) (apart : separated (first :: more) = true) :
    separated more = true := by
  cases more with
  | nil => rfl
  | cons second rest =>
    simp only [separated, Bool.and_eq_true] at apart
    exact apart.2

theorem separated_after_number (value : Nat) (second : Token) (rest : List Token)
    (apart : separated (Token.number value :: second :: rest) = true) : isNumber second = false := by
  simp only [separated, isNumber, Bool.and_eq_true, Bool.true_and, Bool.not_eq_true'] at apart
  exact apart.1

/-- A token that is not a number starts with a character that is not a digit. -/
theorem tokenText_first_not_digit (token : Token) (notNumber : isNumber token = false) :
    ∃ first more, tokenText token = first :: more ∧ first.isDigit = false := by
  cases token with
  | number value => simp [isNumber] at notNumber
  | _ => exact ⟨_, _, rfl, by decide⟩

/-- White space at the front of a text is skipped at the cost of one unit of fuel. -/
theorem tokenizeWith_space (first : Char) (rest : List Char) (fuel : Nat) (isSpaceCharacter : isSpace first = true) :
    tokenizeWith (fuel + 1) (first :: rest) = tokenizeWith fuel rest := by
  conv => lhs; unfold tokenizeWith
  split
  case h_9 =>
    injection ‹first :: rest = _› with sameFirst sameRest
    injection ‹fuel + 1 = _› with sameFuel
    subst sameFirst sameRest sameFuel
    simp [isSpaceCharacter]
  -- Every other case is no fuel, no character, or a first character that is no white space.
  all_goals first
    | omega
    | contradiction
    | (injection ‹first :: rest = _› with sameFirst _
       rw [sameFirst] at isSpaceCharacter
       exact absurd isSpaceCharacter (by decide))

/-- What is left after a number's digits does not begin with a digit, when what follows
    the number is written out and is not itself a number. -/
theorem noDigitFirst_after_number (more : List Token) (rest : List Char) (written : writes more rest = true)
    (nextNotNumber : ∀ second others, more = second :: others → isNumber second = false) : NoDigitFirst rest := by
  intro first tail shape
  cases spaceOrNot : isSpace first with
  | true =>
    cases digitOrNot : first.isDigit with
    | false => rfl
    | true => rw [isSpace_of_isDigit first digitOrNot] at spaceOrNot; contradiction
  | false =>
    rw [shape] at written
    cases more with
    | nil => simp [writes, dropSpaces_not_space first tail spaceOrNot] at written
    | cons second others =>
      obtain ⟨head, textTail, textShape, notDigit⟩ :=
        tokenText_first_not_digit second (nextNotNumber second others rfl)
      simp only [writes, dropSpaces_not_space first tail spaceOrNot, textShape, Bool.and_eq_true] at written
      have isPrefix := List.isPrefixOf_iff_prefix.mp written.1
      obtain ⟨_, sameText⟩ := isPrefix
      injection sameText with sameHead _
      rw [← sameHead]
      exact notDigit

/-- The tokenizer refuses nothing of that form: a text that writes a sequence of tokens,
    no two numbers side by side, is read as that sequence, given more fuel than the text
    has characters. -/
theorem writes_tokenizeWith (fuel : Nat) :
    ∀ text tokens, text.length < fuel → writes tokens text = true → separated tokens = true →
      tokenizeWith fuel text = some tokens := by
  induction fuel with
  | zero => intro text tokens enough; omega
  | succ fuel hypothesis =>
    intro text tokens enough written apart
    cases text with
    | nil =>
      cases tokens with
      | nil => simp [tokenizeWith]
      | cons token more =>
        obtain ⟨first, tail, shape, _⟩ := tokenText_starts token
        simp [writes, dropSpaces, shape] at written
    | cons first rest =>
      cases spaceOrNot : isSpace first with
      | true =>
        rw [tokenizeWith_space first rest fuel spaceOrNot]
        rw [writes_space tokens first rest spaceOrNot] at written
        exact hypothesis rest tokens (by simp at enough; omega) written apart
      | false =>
        cases tokens with
        | nil => simp [writes, dropSpaces_not_space first rest spaceOrNot] at written
        | cons token more =>
          simp only [writes, dropSpaces_not_space first rest spaceOrNot, Bool.and_eq_true] at written
          obtain ⟨isPrefix, writtenMore⟩ := written
          have whole := List.prefix_iff_eq_append.mp (List.isPrefixOf_iff_prefix.mp isPrefix)
          generalize List.drop (tokenText token).length (first :: rest) = after at whole writtenMore
          obtain ⟨textFirst, textTail, textShape, _⟩ := tokenText_starts token
          have shorter : after.length < fuel := by
            have lengths := congrArg List.length whole
            simp [textShape] at lengths enough
            omega
          have readAfter := hypothesis after more shorter writtenMore (separated_tail token more apart)
          rw [← whole]
          cases token with
          | number value =>
            have noDigitNext : NoDigitFirst after := noDigitFirst_after_number more after writtenMore
              (fun second others shape => separated_after_number value second others (shape ▸ apart))
            show tokenizeWith (fuel + 1) (digitsOf value ++ after) = _
            rw [tokenizeWith_digitsOf value fuel after noDigitNext, readAfter]
            rfl
          | _ => simp [tokenText, tokenizeWith, readAfter]

/-- A token that is not a number can stand in front of any separated sequence. -/
theorem separated_cons_other (first : Token) (rest : List Token) (notNumber : isNumber first = false)
    (restApart : separated rest = true) : separated (first :: rest) = true := by
  cases rest <;> simp_all [separated]

/-- Any token can stand in front of a separated sequence that does not begin with a number. -/
theorem separated_cons_before_other (first : Token) (rest : List Token)
    (restNotNumber : ∀ second more, rest = second :: more → isNumber second = false)
    (restApart : separated rest = true) : separated (first :: rest) = true := by
  cases rest with
  | nil => rfl
  | cons second more => simp [separated, restNotNumber second more rfl, restApart]

/-- What follows the first item of an array does not begin with a number. -/
theorem tokensAfterFirst_not_number (items : List Json) (rest : List Token) :
    ∀ head tail, tokensAfterFirst items ++ rest = head :: tail → isNumber head = false := by
  intro head tail shape
  cases items with
  | nil =>
    simp only [tokensAfterFirst, List.cons_append] at shape
    injection shape with sameHead _
    rw [← sameHead]; rfl
  | cons item others =>
    simp only [tokensAfterFirst, List.cons_append] at shape
    injection shape with sameHead _
    rw [← sameHead]; rfl

mutual

/-- No two numbers stand side by side in a value's tokens, whatever follows them, as long
    as what follows does not begin with a number. -/
theorem separated_tokensOf (value : Json) (rest : List Token) (restApart : separated rest = true)
    (restNotNumber : ∀ first more, rest = first :: more → isNumber first = false) :
    separated (tokensOf value ++ rest) = true := by
  match value with
  | .null => exact separated_cons_other _ rest rfl restApart
  | .bool true => exact separated_cons_other _ rest rfl restApart
  | .bool false => exact separated_cons_other _ rest rfl restApart
  | .number amount => exact separated_cons_before_other _ rest restNotNumber restApart
  | .array [] => exact separated_cons_other _ _ rfl (separated_cons_other _ rest rfl restApart)
  | .array (first :: others) =>
    have othersApart := separated_tokensAfterFirst others rest restApart restNotNumber
    have firstApart := separated_tokensOf first (tokensAfterFirst others ++ rest) othersApart
      (tokensAfterFirst_not_number others rest)
    have unfolded : tokensOf (Json.array (first :: others)) ++ rest =
        Token.openBracket :: (tokensOf first ++ (tokensAfterFirst others ++ rest)) := by
      simp [tokensOf]
    rw [unfolded]
    exact separated_cons_other _ _ rfl firstApart

theorem separated_tokensAfterFirst (items : List Json) (rest : List Token) (restApart : separated rest = true)
    (restNotNumber : ∀ first more, rest = first :: more → isNumber first = false) :
    separated (tokensAfterFirst items ++ rest) = true := by
  match items with
  | [] => exact separated_cons_other _ rest rfl restApart
  | item :: others =>
    have othersApart := separated_tokensAfterFirst others rest restApart restNotNumber
    have itemApart := separated_tokensOf item (tokensAfterFirst others ++ rest) othersApart
      (tokensAfterFirst_not_number others rest)
    have unfolded : tokensAfterFirst (item :: others) ++ rest =
        Token.comma :: (tokensOf item ++ (tokensAfterFirst others ++ rest)) := by
      simp [tokensAfterFirst]
    rw [unfolded]
    exact separated_cons_other _ _ rfl itemApart

end

/-- The tokenizer is exact for a value's tokens: it returns them for a text precisely when
    the text is those tokens written out. -/
theorem tokenize_iff_writes (text : List Char) (value : Json) :
    tokenize text = some (tokensOf value) ↔ writes (tokensOf value) text = true := by
  constructor
  · exact tokenizeWith_writes _ text _
  · intro written
    have apart := separated_tokensOf value [] rfl (fun _ _ impossible => by contradiction)
    rw [List.append_nil] at apart
    exact writes_tokenizeWith _ text _ (by omega) written apart

end MiniJson.Proofs
