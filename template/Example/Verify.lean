/-
  File: Example/Verify.lean
  Purpose: Every claim of Spec.lean restated with `recall`. `recall` fails to compile
  when the statement written here differs from the one proved, so the ordinary build
  checks that the proofs prove what the spec states. Each `#print axioms` line reports
  the axioms a claim rests on, for reading; the check that fails on an axiom outside
  the allowed list is the axiom assertion in the test package.

  Written by `claims sync` from Spec.lean. Not edited by hand.
  Created: 2026-11-13
-/

import Example.Proofs

/-! ## Claim 1. The result is never below the lower bound. -/

namespace Example.Proofs

open Example

recall clamp_ge_low (low high value : Nat) : low ≤ clamp low high value
#print axioms clamp_ge_low

end Example.Proofs

/-! ## Claim 2. The result is never above the upper bound, when the range is not empty. -/

namespace Example.Proofs

open Example

recall clamp_le_high (low high value : Nat) (rangeNotEmpty : low ≤ high) :
    clamp low high value ≤ high
#print axioms clamp_le_high

end Example.Proofs

/-! ## Claim 3. A number already in the range is returned unchanged. -/

namespace Example.Proofs

open Example

recall clamp_eq_self (low high value : Nat) (atLeastLow : low ≤ value) (atMostHigh : value ≤ high) :
    clamp low high value = value
#print axioms clamp_eq_self

end Example.Proofs

/-! ## Claim 4. A number at or below the lower bound becomes the lower bound. -/

namespace Example.Proofs

open Example

recall clamp_of_below (low high value : Nat) (atMostLow : value ≤ low) :
    clamp low high value = low
#print axioms clamp_of_below

end Example.Proofs

/-! ## Claim 5. A number at or above the upper bound becomes the upper bound, when the range is not empty. -/

namespace Example.Proofs

open Example

recall clamp_of_above (low high value : Nat) (rangeNotEmpty : low ≤ high) (atLeastHigh : high ≤ value) :
    clamp low high value = high
#print axioms clamp_of_above

end Example.Proofs

/-! ## Claim 6. For an empty range the result is the lower bound. -/

namespace Example.Proofs

open Example

recall clamp_of_empty (low high value : Nat) (rangeEmpty : high < low) :
    clamp low high value = low
#print axioms clamp_of_empty

end Example.Proofs
