/-
  File: selftest/LeanClaimsTest/Claims.lean
  Purpose: The function and the proved claims that the test of `#audit_facts` is about.
  They stand in for a project's code and its proofs: claims with no hypothesis, with one
  and with two, and a claim whose statement is a type class applied to the function.
  Created: 2026-11-13
-/

namespace LeanClaimsTest

/-- The function the claims are about. -/
def double (number : Nat) : Nat := number + number

/-- A property stated as a type class, as the standard library states the laws of a
    comparison. -/
class FixesZero (function : Nat → Nat) : Prop where
  atZero : function 0 = 0

namespace Proofs

theorem double_even (number : Nat) : double number % 2 = 0 := by
  unfold double
  omega

theorem double_ge (number : Nat) : number ≤ double number := by
  unfold double
  omega

theorem double_pos (number : Nat) (positive : 0 < number) : 0 < double number := by
  unfold double
  omega

theorem double_lt_of_bounded (smaller larger : Nat) (less : smaller < larger) (bounded : larger < 100) :
    double smaller < 200 := by
  unfold double
  omega

theorem double_fixesZero : FixesZero double := ⟨rfl⟩

theorem double_eq (number : Nat) : double number = number + number := rfl

end Proofs

end LeanClaimsTest
