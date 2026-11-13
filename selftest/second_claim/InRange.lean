/-
  File: RangeTools/InRange.lean
  Purpose: `inRange`, which says whether a number lies in a range.
  Created: 2026-11-13
-/

namespace RangeTools

/-- `inRange low high value` is `true` exactly when `value` lies from `low` to `high`,
    both ends included. -/
def inRange (low high value : Nat) : Bool :=
  decide (low ≤ value ∧ value ≤ high)

end RangeTools
