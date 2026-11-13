/-
  File: MiniJson/Render.lean
  Purpose: The renderer: from a value to its text, with no white space. `renderChars`
  gives a list of characters and is what the claims are about. `render` is the same
  function to a `String`.
  Created: 2026-11-14
-/

import MiniJson.Value

namespace MiniJson

/-- The character that writes a digit from 0 to 9. -/
def digitChar (digit : Nat) : Char :=
  Char.ofNat ('0'.toNat + digit)

/-- A number in decimal, with no leading zero. -/
def digitsOf (number : Nat) : List Char :=
  if number < 10 then
    [digitChar number]
  else
    digitsOf (number / 10) ++ [digitChar (number % 10)]
decreasing_by omega

mutual

/-- The text of a value. An array is written `[`, its items separated by `,`, and `]`. -/
def renderChars : Json → List Char
  | .null => ['n', 'u', 'l', 'l']
  | .bool true => ['t', 'r', 'u', 'e']
  | .bool false => ['f', 'a', 'l', 's', 'e']
  | .number value => digitsOf value
  | .array [] => ['[', ']']
  | .array (first :: others) => '[' :: (renderChars first ++ renderAfterFirst others)

/-- The text of an array after its first item. -/
def renderAfterFirst : List Json → List Char
  | [] => [']']
  | item :: others => ',' :: (renderChars item ++ renderAfterFirst others)

end

/-- The text of a value as a string. -/
def render (value : Json) : String :=
  String.ofList (renderChars value)

end MiniJson
