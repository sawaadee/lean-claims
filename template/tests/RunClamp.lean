/-
  File: tests/RunClamp.lean
  Purpose: Runs the compiled `clamp` on a table of inputs and compares each result with
  the expected value. The proofs are about the definition of `clamp`. What runs is the
  code the compiler made from it, and that the two agree is not proved. This program is
  the test `claims.toml` names for that part of the surface, and `faults.toml` holds the
  bug it must be seen to catch.

  It exits with status 0 when every case passes and 1 otherwise, naming each failing case.
  Created: 2026-11-13
-/

import Example

open Example

/-- One case: a lower bound, an upper bound, an input and the result `clamp` must give. -/
structure ClampCase where
  low : Nat
  high : Nat
  value : Nat
  expected : Nat

/-- An input below, inside and above a range, both ends of it, a range of one number, and
    an empty range. -/
def clampCases : List ClampCase := [
  { low := 5, high := 10, value := 3, expected := 5 },
  { low := 5, high := 10, value := 5, expected := 5 },
  { low := 5, high := 10, value := 7, expected := 7 },
  { low := 5, high := 10, value := 10, expected := 10 },
  { low := 5, high := 10, value := 12, expected := 10 },
  { low := 4, high := 4, value := 9, expected := 4 },
  { low := 10, high := 5, value := 7, expected := 10 }]

def main : IO UInt32 := do
  let mut failures := 0
  for clampCase in clampCases do
    let result := clamp clampCase.low clampCase.high clampCase.value
    if result != clampCase.expected then
      IO.eprintln s!"clamp {clampCase.low} {clampCase.high} {clampCase.value} returned {result}, expected {clampCase.expected}"
      failures := failures + 1
  if failures == 0 then
    IO.println s!"the compiled clamp returned the expected value in all {clampCases.length} cases"
    return 0
  IO.eprintln s!"{failures} of {clampCases.length} cases failed"
  return 1
