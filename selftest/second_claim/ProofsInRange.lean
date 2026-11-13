/-
  File: RangeTools/Proofs/InRange.lean
  Purpose: The proof of claim 7, about `inRange`, under the name the spec gives it.
  Created: 2026-11-13
-/

import RangeTools.InRange

namespace RangeTools.Proofs

open RangeTools

theorem inRange_iff (low high value : Nat) :
    inRange low high value = true ↔ low ≤ value ∧ value ≤ high := by
  unfold inRange
  exact decide_eq_true_iff

end RangeTools.Proofs
