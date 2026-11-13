/-
  File: MiniJson/Value.lean
  Purpose: The values this library reads and writes, and the tokens their text is made of.
  The values are a subset of JSON: `null`, `true`, `false`, natural numbers and arrays.
  Strings, objects, negative numbers and fractions are not part of it.

  `tokensOf` gives the one sequence of tokens that stands for a value. It is the
  specification the parser is held to: a text stands for a value exactly when the text's
  tokens are the value's tokens.
  Created: 2026-11-14
-/

namespace MiniJson

/-- A value: `null`, a boolean, a natural number, or an array of values. -/
inductive Json where
  | null
  | bool (value : Bool)
  | number (value : Nat)
  | array (items : List Json)

/-- A token: one of the three words, a number, a bracket or a comma. White space between
    tokens is not a token. -/
inductive Token where
  | nullWord
  | trueWord
  | falseWord
  | number (value : Nat)
  | openBracket
  | closeBracket
  | comma
deriving DecidableEq, Repr

mutual

/-- The tokens of a value. An array is an opening bracket, its items separated by commas,
    and a closing bracket. -/
def tokensOf : Json → List Token
  | .null => [.nullWord]
  | .bool true => [.trueWord]
  | .bool false => [.falseWord]
  | .number value => [.number value]
  | .array [] => [.openBracket, .closeBracket]
  | .array (first :: others) => .openBracket :: (tokensOf first ++ tokensAfterFirst others)

/-- The tokens of an array after its first item: each further item with a comma in front,
    then the closing bracket. -/
def tokensAfterFirst : List Json → List Token
  | [] => [.closeBracket]
  | item :: others => .comma :: (tokensOf item ++ tokensAfterFirst others)

end

end MiniJson
