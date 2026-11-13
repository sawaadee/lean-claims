/-
  File: Example/Clamp.lean
  Purpose: The starter library's one function, `clamp`, which brings a number into a
  range. It is here so that the starter project has something real to make claims about.
  Created: 2026-11-13
-/

namespace Example

/-- `clamp low high value` is `value` when it lies from `low` to `high`, `low` when it is
    below, and `high` when it is above. When `high < low` the range is empty and the
    result is `low`. -/
def clamp (low high value : Nat) : Nat :=
  max low (min high value)

end Example
