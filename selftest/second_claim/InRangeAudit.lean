/-
  File: tests/InRangeAudit.lean
  Purpose: The audit of claim 7, about `inRange`: a wrong implementation that fails it,
  and that any function meeting it is `inRange`. The claim has no hypothesis.
  Created: 2026-11-13
-/

import LeanClaims
import RangeTools.Proofs

namespace InRangeAudit

open RangeTools

/-- A function with the shape of `inRange`. -/
abbrev Candidate := Nat → Nat → Nat → Bool

/-- Claim 7 asked of a candidate. -/
def MeetsClaim7 (candidate : Candidate) : Prop :=
  ∀ low high value, candidate low high value = true ↔ low ≤ value ∧ value ≤ high

/-- `inRange` has the property, by the proved claim. -/
theorem inRange_meets_claim7 : MeetsClaim7 inRange := Proofs.inRange_iff

/-- Audit: fails claim 7. A candidate that forgets the upper bound answers yes for 12 in
    the range 5 to 10. -/
theorem forgetsUpperBound_fails_claim7 : ¬ MeetsClaim7 (fun low _ value => decide (low ≤ value)) :=
  fun meets => absurd ((meets 5 10 12).mp (by decide)).2 (by decide)

/-- Audit: determines claim 7. Any candidate that meets claim 7 is `inRange`: the claim
    fixes the answer for every input. -/
theorem claim_determines_inRange (candidate : Candidate) (meets : MeetsClaim7 candidate) :
    candidate = inRange :=
  funext fun low => funext fun high => funext fun value =>
    Bool.eq_iff_iff.mpr ((meets low high value).trans (Proofs.inRange_iff low high value).symm)

end InRangeAudit
