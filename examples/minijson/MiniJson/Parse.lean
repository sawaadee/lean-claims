/-
  File: MiniJson/Parse.lean
  Purpose: The parser: from tokens to a value, and from text to a value by way of the
  tokens. `parseChars` works on a list of characters and is what the claims are about.
  `parse` is the same function on a `String`.
  Created: 2026-11-14
-/

import MiniJson.Tokenize

namespace MiniJson

mutual

/-- Read one value from the front of the tokens and return it with the tokens after it.
    `fuel` bounds the depth of the reading; `parseTokens` gives enough. -/
def parseValue : Nat → List Token → Option (Json × List Token)
  | 0, _ => none
  | _ + 1, .nullWord :: rest => some (.null, rest)
  | _ + 1, .trueWord :: rest => some (.bool true, rest)
  | _ + 1, .falseWord :: rest => some (.bool false, rest)
  | _ + 1, .number value :: rest => some (.number value, rest)
  | _ + 1, .openBracket :: .closeBracket :: rest => some (.array [], rest)
  | fuel + 1, .openBracket :: rest =>
    match parseValue fuel rest with
    | some (first, afterFirst) =>
      match parseAfterFirst fuel afterFirst with
      | some (others, afterArray) => some (.array (first :: others), afterArray)
      | none => none
    | none => none
  | _ + 1, _ => none

/-- Read the rest of an array after its first item: further items, each after a comma,
    up to the closing bracket. -/
def parseAfterFirst : Nat → List Token → Option (List Json × List Token)
  | 0, _ => none
  | _ + 1, .closeBracket :: rest => some ([], rest)
  | fuel + 1, .comma :: rest =>
    match parseValue fuel rest with
    | some (item, afterItem) =>
      match parseAfterFirst fuel afterItem with
      | some (others, afterArray) => some (item :: others, afterArray)
      | none => none
    | none => none
  | _ + 1, _ => none

end

/-- The value a sequence of tokens stands for: one value, with no token left over. -/
def parseTokens (tokens : List Token) : Option Json :=
  match parseValue (tokens.length + 1) tokens with
  | some (value, []) => some value
  | _ => none

/-- The value a text stands for, or `none` when it stands for none. -/
def parseChars (text : List Char) : Option Json :=
  (tokenize text).bind parseTokens

/-- The value a string stands for, or `none` when it stands for none. -/
def parse (text : String) : Option Json :=
  parseChars text.toList

end MiniJson
