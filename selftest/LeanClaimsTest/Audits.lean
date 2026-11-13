/-
  File: selftest/LeanClaimsTest/Audits.lean
  Purpose: Audit theorems of every shape `#audit_facts` must recognise, and of the shapes
  it must refuse, about the claims in `LeanClaimsTest/Claims.lean`. Each theorem's comment
  says what the command must report for it, and `selftest/audit_facts.py` holds the same
  expectation and compares.

  The theorems the command must refuse are all true and all proved. That is the point:
  each compiles and rests on no axiom, and only its statement shows that it is not the
  audit it could be taken for.
  Created: 2026-11-13
-/

import LeanClaims
import LeanClaimsTest.Claims

namespace LeanClaimsTest.Audits

open LeanClaimsTest

/-! ## Properties -/

/-- `double_even` asked of any function. -/
def IsEven (candidate : Nat → Nat) : Prop :=
  ∀ number, candidate number % 2 = 0

/-- `double_ge` and `double_pos` gathered into one property. -/
def GrowsAndStaysPositive (candidate : Nat → Nat) : Prop :=
  ∀ number, number ≤ candidate number ∧ (0 < number → 0 < candidate number)

/-- `double_lt_of_bounded` asked of any function. -/
def StaysBelowTwoHundred (candidate : Nat → Nat) : Prop :=
  ∀ smaller larger, smaller < larger → larger < 100 → candidate smaller < 200

/-- Says the same as `double_even` in other words. It is true of `double` and it is not
    the claim's statement, so it must not be tied. -/
def IsEvenInOtherWords (candidate : Nat → Nat) : Prop :=
  ∀ number, candidate number % 2 ≤ 0

/-- `double_ge` together with something no claim states. Failing it does not mean failing
    a claim, so it must not be tied. -/
def GrowsAndIsBounded (candidate : Nat → Nat) : Prop :=
  ∀ number, number ≤ candidate number ∧ candidate number ≤ 2 * number

/-- `double_eq` asked of any function. It pins the function down. -/
def IsDoubling (candidate : Nat → Nat) : Prop :=
  ∀ number, candidate number = number + number

/-! ## Ties -/

/-- Ties `IsDoubling` to `double_eq`. -/
theorem isDoubling_tie : IsDoubling double := Proofs.double_eq

/-- Ties `IsEven` to `double_even` directly. -/
theorem isEven_tie : IsEven double := Proofs.double_even

/-- Ties `GrowsAndStaysPositive` to both theorems it gathers. -/
theorem gathered_tie : GrowsAndStaysPositive double :=
  fun number => ⟨Proofs.double_ge number, Proofs.double_pos number⟩

/-- Ties `StaysBelowTwoHundred` to `double_lt_of_bounded` as one part of a conjunction. -/
theorem conjunction_tie : IsEven double ∧ StaysBelowTwoHundred double :=
  ⟨Proofs.double_even, Proofs.double_lt_of_bounded⟩

/-- Proved from the claim, and not the claim's statement: no tie. -/
theorem otherWords_holds : IsEvenInOtherWords double :=
  fun number => Nat.le_of_eq (Proofs.double_even number)

/-- One clause is a claim and the other is not: no tie. -/
theorem growsAndIsBounded_holds : GrowsAndIsBounded double :=
  fun number => ⟨Proofs.double_ge number, by unfold double; omega⟩

/-! ## Fails -/

/-- Must be reported as failing `double_even`. -/
theorem constantOne_fails_isEven : ¬ IsEven (fun _ => 1) :=
  fun meets => absurd (meets 0) (by decide)

/-- Must be reported as failing `double_ge` and `double_pos`, the two theorems its
    property gathers. -/
theorem constantZero_fails_gathered : ¬ GrowsAndStaysPositive (fun _ => 0) :=
  fun meets => absurd (meets 1).1 (by decide)

/-- Must be reported as failing `double_lt_of_bounded`, tied through a conjunction. -/
theorem constantTwoHundred_fails_bound : ¬ StaysBelowTwoHundred (fun _ => 200) :=
  fun meets => absurd (meets 1 2 (by decide) (by decide)) (by decide)

/-- Must be reported as failing `double_fixesZero`: the claim states a type class of the
    function, and the class is the property. -/
theorem constantOne_fails_fixesZero : ¬ FixesZero (fun _ => 1) :=
  fun meets => absurd meets.atZero (by decide)

/-- Must be reported as failing nothing, with its property named: the property is not
    tied. -/
theorem constantOne_fails_otherWords : ¬ IsEvenInOtherWords (fun _ => 1) :=
  fun meets => absurd (meets 0) (by decide)

/-- Must be reported as failing nothing, with its property named: one clause of the
    property is no claim. -/
theorem triple_fails_growsAndIsBounded : ¬ GrowsAndIsBounded (fun number => 3 * number) :=
  fun meets => absurd (meets 1).2 (by decide)

/-- Must be reported as failing nothing and negating no property: the statement is a
    negation of a statement written out, with no property to compare with a claim. -/
theorem writtenOut_negation : ¬ ∀ number : Nat, (number + 1) % 2 = 0 :=
  fun meets => absurd (meets 0) (by decide)

/-- Must be reported as nothing at all. -/
theorem empty : True := trivial

/-! ## Determines -/

/-- Must be reported as determining `double_even`, `double_ge` and `double_pos`: two
    hypotheses ask tied properties of a candidate, and the conclusion relates it to `double`. -/
theorem determined_through_properties (candidate : Nat → Nat) (even : IsEven candidate)
    (grows : GrowsAndStaysPositive candidate) :
    ∀ number, candidate number % 2 = double number % 2 ∧ number ≤ candidate number :=
  fun number => ⟨(even number).trans (Proofs.double_even number).symm, (grows number).1⟩

/-- Must be reported as determining `double_ge`: the hypothesis is the claim's statement
    written out for the candidate. -/
theorem determined_through_statement (candidate : Nat → Nat) (grows : ∀ number, number ≤ candidate number) :
    ∀ number, number ≤ candidate number + double number :=
  fun number => Nat.le_add_right_of_le (grows number)

/-- Must be reported as determining `double_eq`: the conclusion relates the candidate to
    `double`. -/
theorem doubling_is_double (candidate : Nat → Nat) (doubles : IsDoubling candidate) : candidate = double :=
  funext fun number => (doubles number).trans (Proofs.double_eq number).symm

/-- Must be reported as determining `double_eq`: the conclusion relates two candidates
    that both meet the claim. -/
theorem two_doublings_agree (first second : Nat → Nat) (firstDoubles : IsDoubling first)
    (secondDoubles : IsDoubling second) : first = second :=
  funext fun number => (firstDoubles number).trans (secondDoubles number).symm

/-- Must be reported as determining nothing: the conclusion mentions the candidate and
    relates it to nothing, so it is true of every candidate. -/
theorem conclusion_says_nothing (candidate : Nat → Nat) (_doubles : IsDoubling candidate) : candidate = candidate :=
  rfl

/-- Must be reported as determining nothing: the conclusion does not mention the
    candidate. -/
theorem conclusion_without_candidate (candidate : Nat → Nat) (_even : IsEven candidate) : True :=
  trivial

/-- Must be reported as determining nothing: the hypothesis is about `double` itself, not
    about a candidate. -/
theorem hypothesis_about_the_implementation (_even : IsEven double) : double 0 = 0 :=
  rfl

/-! ## Can hold -/

/-- Must be reported as showing the hypotheses of `double_pos`. -/
theorem positive_can_hold : hypotheses_can_hold% Proofs.double_pos :=
  ⟨1, by decide, trivial⟩

/-- Must be reported as showing the hypotheses of `double_pos` and of `double_lt_of_bounded`. -/
theorem both_can_hold : hypotheses_can_hold% Proofs.double_pos ∧ hypotheses_can_hold% Proofs.double_lt_of_bounded :=
  ⟨⟨1, by decide, trivial⟩, ⟨1, 2, by decide, by decide, trivial⟩⟩

/-- Must be reported as showing nothing: the hypotheses with numbers put in, which Lean
    cannot tell from any other true statement about numbers. -/
theorem instances_of_the_hypotheses : 0 < 1 ∧ 1 < 2 ∧ 2 < 100 := by
  decide

/-- Must be reported as showing nothing: one of the two hypotheses of `double_lt_of_bounded`
    is left out, and the one left out could be the one that cannot hold. -/
theorem one_hypothesis_left_out : ∃ smaller larger : Nat, ∃ _ : smaller < larger, True :=
  ⟨1, 2, by decide, trivial⟩

end LeanClaimsTest.Audits
