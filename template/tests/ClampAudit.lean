/-
  File: tests/ClampAudit.lean
  Purpose: The audit of the six claims about `clamp`. The proofs show the claims are true
  of `clamp`. The theorems here show the claims are worth having: for each claim a wrong
  implementation that fails it, that the hypotheses of the claims can hold, and that any
  function meeting claims 3 to 6 is `clamp`, so those four leave nothing unsaid.

  Each claim is written here as a property of an arbitrary candidate function, so that
  it can be asked of wrong implementations. `clamp_meets_every_claim` ties those
  properties to the proved claims: each property, asked of `clamp`, is its claim's
  statement.

  A theorem whose doc comment starts with `Audit:` says which claims it audits, and
  `claims audit` has Lean confirm that from the theorem's statement. A theorem failing a
  claim must be `¬ P wrong` for the claim's property `P`. The theorem that the claims
  determine `clamp` must take the claims' properties of a candidate as hypotheses. A
  theorem that hypotheses can hold must be `hypotheses_can_hold% T` for the claim's
  theorem `T`, which Lean builds from `T` itself. An `Audit:` line that Lean does not
  confirm is an error.
  Created: 2026-11-13
-/

import LeanClaims
import Example.Proofs

namespace ClampAudit

open Example

/-- A function with the shape of `clamp`: a lower bound, an upper bound and an input. -/
abbrev Candidate := Nat → Nat → Nat → Nat

/-- Claim 1 asked of a candidate: the result is never below the lower bound. -/
def MeetsClaim1 (candidate : Candidate) : Prop :=
  ∀ low high value, low ≤ candidate low high value

/-- Claim 2 asked of a candidate: for a range that is not empty, the result is never above
    the upper bound. -/
def MeetsClaim2 (candidate : Candidate) : Prop :=
  ∀ low high value, low ≤ high → candidate low high value ≤ high

/-- Claim 3 asked of a candidate: an input in the range is returned unchanged. -/
def MeetsClaim3 (candidate : Candidate) : Prop :=
  ∀ low high value, low ≤ value → value ≤ high → candidate low high value = value

/-- Claim 4 asked of a candidate: an input at or below the lower bound becomes the lower
    bound. -/
def MeetsClaim4 (candidate : Candidate) : Prop :=
  ∀ low high value, value ≤ low → candidate low high value = low

/-- Claim 5 asked of a candidate: for a range that is not empty, an input at or above the
    upper bound becomes the upper bound. -/
def MeetsClaim5 (candidate : Candidate) : Prop :=
  ∀ low high value, low ≤ high → high ≤ value → candidate low high value = high

/-- Claim 6 asked of a candidate: for an empty range the result is the lower bound. -/
def MeetsClaim6 (candidate : Candidate) : Prop :=
  ∀ low high value, high < low → candidate low high value = low

/-- `clamp` meets all six properties, by the six proved claims. So each property here asks
    no more of a candidate than the claim it stands for asks of `clamp`. -/
theorem clamp_meets_every_claim :
    MeetsClaim1 clamp ∧ MeetsClaim2 clamp ∧ MeetsClaim3 clamp ∧ MeetsClaim4 clamp ∧ MeetsClaim5 clamp ∧
      MeetsClaim6 clamp :=
  ⟨Proofs.clamp_ge_low, Proofs.clamp_le_high, Proofs.clamp_eq_self, Proofs.clamp_of_below,
    Proofs.clamp_of_above, Proofs.clamp_of_empty⟩

/-! ## A wrong implementation for each claim -/

/-- Audit: fails claim 1. A candidate that forgets the lower bound returns 3 for the range
    5 to 10 and the input 3. -/
theorem forgetsLowerBound_fails_claim1 : ¬ MeetsClaim1 (fun _ high value => min high value) :=
  fun meets => absurd (meets 5 10 3) (by decide)

/-- Audit: fails claim 2. A candidate that forgets the upper bound returns 12 for the range
    5 to 10 and the input 12. -/
theorem forgetsUpperBound_fails_claim2 : ¬ MeetsClaim2 (fun low _ value => max low value) :=
  fun meets => absurd (meets 5 10 12 (by decide)) (by decide)

/-- Audit: fails claim 3. A candidate that always returns the lower bound meets claims 1
    and 2, and returns 5 for the input 7 in the range 5 to 10. -/
theorem alwaysLowerBound_fails_claim3 : ¬ MeetsClaim3 (fun low _ _ => low) :=
  fun meets => absurd (meets 5 10 7 (by decide) (by decide)) (by decide)

/-- Audit: fails claim 4. A candidate that lets an input below the range through returns 3
    for the range 5 to 10 and the input 3. -/
theorem passesLowInput_fails_claim4 :
    ¬ MeetsClaim4 (fun low high value => max (min low value) (min high value)) :=
  fun meets => absurd (meets 5 10 3 (by decide)) (by decide)

/-- Audit: fails claim 5. A candidate that is one short at the top returns 9 for the range
    5 to 10 and the input 10. -/
theorem oneShortAtTop_fails_claim5 : ¬ MeetsClaim5 (fun low high value => max low (min high (value - 1))) :=
  fun meets => absurd (meets 5 10 10 (by decide) (by decide)) (by decide)

/-- Audit: fails claim 6. A candidate that applies the bounds in the other order agrees
    with `clamp` on every range that is not empty, and returns 5 for the empty range 10 to
    5 and the input 7. -/
theorem boundsInOtherOrder_fails_claim6 : ¬ MeetsClaim6 (fun low high value => min high (max low value)) :=
  fun meets => absurd (meets 10 5 7 (by decide)) (by decide)

/-! ## The hypotheses of the claims can hold -/

/-- Audit: hypotheses of claim 2 can hold. The range 5 to 10 is not empty. -/
theorem claim2_hypotheses_can_hold : hypotheses_can_hold% Proofs.clamp_le_high :=
  ⟨5, 10, 7, by decide, trivial⟩

/-- Audit: hypotheses of claim 3 can hold. The number 7 lies in the range 5 to 10. -/
theorem claim3_hypotheses_can_hold : hypotheses_can_hold% Proofs.clamp_eq_self :=
  ⟨5, 10, 7, by decide, by decide, trivial⟩

/-- Audit: hypotheses of claim 4 can hold. The number 3 is at or below the lower bound 5. -/
theorem claim4_hypotheses_can_hold : hypotheses_can_hold% Proofs.clamp_of_below :=
  ⟨5, 10, 3, by decide, trivial⟩

/-- Audit: hypotheses of claim 5 can hold. The range 5 to 10 is not empty and 12 is at or
    above its upper bound. -/
theorem claim5_hypotheses_can_hold : hypotheses_can_hold% Proofs.clamp_of_above :=
  ⟨5, 10, 12, by decide, by decide, trivial⟩

/-- Audit: hypotheses of claim 6 can hold. The range 10 to 5 is empty. -/
theorem claim6_hypotheses_can_hold : hypotheses_can_hold% Proofs.clamp_of_empty :=
  ⟨10, 5, 7, by decide, trivial⟩

/-! ## The claims determine `clamp` -/

/-- Audit: determines claims 3 to 6. Any candidate that meets claims 3, 4, 5 and 6 is
    `clamp`: the four cases (an empty range, an input at or below the lower bound, at or
    above the upper bound, and strictly between) cover every call, and each claim fixes
    the result in its case. Claims 1 and 2 are not needed for this; they follow from the
    other four. -/
theorem claims_determine_clamp (candidate : Candidate) (meets3 : MeetsClaim3 candidate)
    (meets4 : MeetsClaim4 candidate) (meets5 : MeetsClaim5 candidate) (meets6 : MeetsClaim6 candidate) :
    candidate = clamp := by
  funext low high value
  unfold clamp
  by_cases rangeEmpty : high < low
  · rw [meets6 low high value rangeEmpty]
    omega
  · by_cases atMostLow : value ≤ low
    · rw [meets4 low high value atMostLow]
      omega
    · by_cases atLeastHigh : high ≤ value
      · rw [meets5 low high value (by omega) atLeastHigh]
        omega
      · rw [meets3 low high value (by omega) (by omega)]
        omega

end ClampAudit
