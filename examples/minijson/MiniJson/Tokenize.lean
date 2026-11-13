/-
  File: MiniJson/Tokenize.lean
  Purpose: Splits text into tokens. Claims 1 and 2 are stated against this function, and
  claim 7 holds it to `writes` in `MiniJson/Written.lean`, which says what a text of
  tokens is without it. So a reviewer does not have to take this file on trust: a
  tokenizer that accepted too much or too little would make claim 7 false.

  A number is a run of decimal digits, taken as long as it goes. A run of more than one
  digit that starts with `0` is refused, as JSON refuses it. White space is a space, a
  line feed, a tab or a carriage return, and may stand between any two tokens. Anything
  else, and any word other than `null`, `true` and `false`, is refused.
  Created: 2026-11-14
-/

import MiniJson.Value

namespace MiniJson

/-- The four characters JSON counts as white space. -/
def isSpace (character : Char) : Bool :=
  character == ' ' || character == '\n' || character == '\t' || character == '\r'

/-- The number a run of decimal digits writes, read left to right. -/
def natOfDigits (digits : List Char) : Nat :=
  digits.foldl (fun soFar digit => soFar * 10 + (digit.toNat - '0'.toNat)) 0

/-- The tokens of a text, or `none` when some part of it is no token. `fuel` bounds the
    number of tokens and white space characters read; `tokenize` gives enough. -/
def tokenizeWith : Nat → List Char → Option (List Token)
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, '[' :: rest => (tokenizeWith fuel rest).map (Token.openBracket :: ·)
  | fuel + 1, ']' :: rest => (tokenizeWith fuel rest).map (Token.closeBracket :: ·)
  | fuel + 1, ',' :: rest => (tokenizeWith fuel rest).map (Token.comma :: ·)
  | fuel + 1, 'n' :: 'u' :: 'l' :: 'l' :: rest => (tokenizeWith fuel rest).map (Token.nullWord :: ·)
  | fuel + 1, 't' :: 'r' :: 'u' :: 'e' :: rest => (tokenizeWith fuel rest).map (Token.trueWord :: ·)
  | fuel + 1, 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest => (tokenizeWith fuel rest).map (Token.falseWord :: ·)
  | fuel + 1, first :: rest =>
    if isSpace first then
      tokenizeWith fuel rest
    else if first.isDigit then
      let moreDigits := rest.takeWhile Char.isDigit
      if first == '0' && !moreDigits.isEmpty then
        none
      else
        (tokenizeWith fuel (rest.dropWhile Char.isDigit)).map (Token.number (natOfDigits (first :: moreDigits)) :: ·)
    else
      none

/-- The tokens of a text, or `none` when the text is not made of tokens and white space. -/
def tokenize (text : List Char) : Option (List Token) :=
  tokenizeWith (text.length + 1) text

end MiniJson
