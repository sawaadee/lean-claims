/-
  File: Example/Proofs/Clamp.lean
  Purpose: The proofs of the six claims about `clamp`: its result is never below the lower
  bound and, for a range that is not empty, never above the upper bound; and what the
  result is for an input in the range, below it, above it, and for an empty range.
  Created: 2026-11-13
-/

import Example.Clamp

namespace Example.Proofs

open Example

/-- The result is at least the lower bound, for every range and every input. -/
theorem clamp_ge_low (low high value : Nat) : low ≤ clamp low high value := by
  unfold clamp
  omega

/-- The result is at most the upper bound. `rangeNotEmpty` is needed: when `high < low`
    the result is `low`, which is above `high`. -/
theorem clamp_le_high (low high value : Nat) (rangeNotEmpty : low ≤ high) :
    clamp low high value ≤ high := by
  unfold clamp
  omega

/-- A value already in range is returned unchanged. -/
theorem clamp_eq_self (low high value : Nat) (atLeastLow : low ≤ value) (atMostHigh : value ≤ high) :
    clamp low high value = value := by
  unfold clamp
  omega

/-- A value at or below the lower bound becomes the lower bound, for every range. -/
theorem clamp_of_below (low high value : Nat) (atMostLow : value ≤ low) :
    clamp low high value = low := by
  unfold clamp
  omega

/-- A value at or above the upper bound becomes the upper bound, when the range is not
    empty. -/
theorem clamp_of_above (low high value : Nat) (rangeNotEmpty : low ≤ high) (atLeastHigh : high ≤ value) :
    clamp low high value = high := by
  unfold clamp
  omega

/-- For an empty range the result is the lower bound, whatever the input. -/
theorem clamp_of_empty (low high value : Nat) (rangeEmpty : high < low) :
    clamp low high value = low := by
  unfold clamp
  omega

end Example.Proofs
