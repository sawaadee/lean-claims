/-
  File: Spec.lean
  Purpose: Every guarantee this project makes, stated with the proofs left out. A reviewer
  who reads this file, and the definitions it mentions, knows what is guaranteed. Each
  theorem is proved under the same name in `Example/Proofs/`, and `lake comparator` checks
  that what is proved there is exactly what is stated here.

  This file is written by hand and no tool writes to it. `spec.lock` records a hash of
  every claim, and every lean-claims command stops when the two differ. After a change to
  a claim that is meant, run `claims lock --update`.

  The module is its own library, `Spec`. It is not a default target and nothing imports
  it, so its `sorry`s never reach `lake build`.
  Created: 2026-11-13
-/

import Example

/-! ## Claim 1. The result is never below the lower bound.

Whatever the range and whatever the input, `clamp` returns a number that is at least
`low`. -/

namespace Example.Proofs

open Example

/-- There is no hypothesis. The statement holds even for an empty range, `high < low`,
    where the result is `low` itself. -/
theorem clamp_ge_low (low high value : Nat) : low ≤ clamp low high value := by
  sorry

end Example.Proofs

/-! ## Claim 2. The result is never above the upper bound, when the range is not empty.

A caller who passes a sensible range gets a number inside it: with claim 1, the result
lies from `low` to `high`. -/

namespace Example.Proofs

open Example

/-- `rangeNotEmpty : low ≤ high` says the range holds at least one number. It is needed:
    for an empty range the result is `low`, which is above `high`. -/
theorem clamp_le_high (low high value : Nat) (rangeNotEmpty : low ≤ high) :
    clamp low high value ≤ high := by
  sorry

end Example.Proofs

/-! ## Claim 3. A number already in the range is returned unchanged.

`clamp` only moves numbers that are outside the range. Claims 1 and 2 alone would allow
a function that always returns `low`; this claim rules that out. -/

namespace Example.Proofs

open Example

/-- `atLeastLow` and `atMostHigh` say that `value` lies from `low` to `high`. The
    conclusion is that the result is `value` itself. -/
theorem clamp_eq_self (low high value : Nat) (atLeastLow : low ≤ value) (atMostHigh : value ≤ high) :
    clamp low high value = value := by
  sorry

end Example.Proofs

/-! ## Claim 4. A number at or below the lower bound becomes the lower bound.

This holds for every range, an empty one included. -/

namespace Example.Proofs

open Example

/-- `atMostLow : value ≤ low` says the input is not above the lower bound. The conclusion
    is that the result is `low` itself. -/
theorem clamp_of_below (low high value : Nat) (atMostLow : value ≤ low) :
    clamp low high value = low := by
  sorry

end Example.Proofs

/-! ## Claim 5. A number at or above the upper bound becomes the upper bound, when the range is not empty.

With claims 3 and 4 this covers every input for a range that holds at least one number. -/

namespace Example.Proofs

open Example

/-- `rangeNotEmpty : low ≤ high` says the range holds at least one number, and
    `atLeastHigh : high ≤ value` that the input is not below the upper bound. The
    conclusion is that the result is `high` itself. -/
theorem clamp_of_above (low high value : Nat) (rangeNotEmpty : low ≤ high) (atLeastHigh : high ≤ value) :
    clamp low high value = high := by
  sorry

end Example.Proofs

/-! ## Claim 6. For an empty range the result is the lower bound.

A caller who passes the bounds the wrong way round gets a defined answer, and this claim
says which. Without it the claims would say nothing about such a call beyond claim 1. -/

namespace Example.Proofs

open Example

/-- `rangeEmpty : high < low` says no number lies from `low` to `high`. The conclusion is
    that the result is `low`, whatever the input. -/
theorem clamp_of_empty (low high value : Nat) (rangeEmpty : high < low) :
    clamp low high value = low := by
  sorry

end Example.Proofs
