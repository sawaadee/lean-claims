/-
  File: MiniJson/Written.lean
  Purpose: Says, without the tokenizer, what it is for a text to be a sequence of tokens
  written out: white space, then the first token's characters, then white space, then the
  next token's characters, and so on, with only white space after the last.

  `writes` is the specification claim 7 holds the parser to. It is a few lines, it calls
  nothing but `isSpace`, `tokenText` and list functions, and it can be read without
  reading the tokenizer. That is its purpose: with claim 7 the tokenizer is no longer
  something a reviewer has to take on trust.
  Created: 2026-11-14
-/

import MiniJson.Tokenize
import MiniJson.Render

namespace MiniJson

/-- The characters a token is written with. A number is written in decimal with no leading
    zero. -/
def tokenText : Token → List Char
  | .nullWord => ['n', 'u', 'l', 'l']
  | .trueWord => ['t', 'r', 'u', 'e']
  | .falseWord => ['f', 'a', 'l', 's', 'e']
  | .number value => digitsOf value
  | .openBracket => ['[']
  | .closeBracket => [']']
  | .comma => [',']

/-- A text without the white space at its front. -/
def dropSpaces (text : List Char) : List Char :=
  text.dropWhile isSpace

/-- Whether `text` is `tokens` written out in order: before each token any white space,
    then exactly that token's characters, and after the last token nothing but white
    space. White space inside a token's characters is not allowed, because the characters
    must follow one another. -/
def writes : List Token → List Char → Bool
  | [], text => (dropSpaces text).isEmpty
  | token :: more, text =>
    (tokenText token).isPrefixOf (dropSpaces text) &&
      writes more ((dropSpaces text).drop (tokenText token).length)

end MiniJson
