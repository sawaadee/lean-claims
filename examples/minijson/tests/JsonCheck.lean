/-
  File: tests/JsonCheck.lean
  Purpose: The program the differential test runs. It reads texts from standard input, one
  to a line, and for each writes one line: `ok` and the text the value renders back as
  when the text parses, and `refused` when it does not. `tests/differential.py` compares
  those lines with what another JSON library says of the same texts.

  The proofs are about the definitions of `parse` and `render`. What runs here is the code
  the compiler made from them, and that the two agree is not proved. This program is how
  that part is tested.
  Created: 2026-11-14
-/

import MiniJson

open MiniJson

/-- The verdict on one text: `ok` with the rendering of its value, or `refused`. -/
def verdict (text : String) : String :=
  match parse text with
  | some value => s!"ok {render value}"
  | none => "refused"

/-- Read lines until the input ends, writing the verdict on each. A line's own line feed
    is not part of its text. -/
partial def answerLines (input : IO.FS.Stream) (output : IO.FS.Stream) : IO Unit := do
  let line ← input.getLine
  if line.isEmpty then
    return
  let text := if line.endsWith "\n" then (line.dropEnd 1).toString else line
  output.putStrLn (verdict text)
  answerLines input output

def main : IO Unit := do
  answerLines (← IO.getStdin) (← IO.getStdout)
