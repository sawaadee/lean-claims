/-
  File: selftest/LeanClaimsTest/Surface/Proofs.lean
  Purpose: Stands in for a project's proved claims in the test of `#surface_facts`. Each
  theorem is written to mention particular declarations of
  `LeanClaimsTest/Surface/Code.lean`, directly or through notation, and
  `selftest/surface_facts.py` holds what the command must report.
  Created: 2026-11-13
-/

import LeanClaimsTest.Surface.Code

namespace LeanClaimsTest.Surface.Proofs

open LeanClaimsTest.Surface

/-- Mentions `swap`, and `Pair` through its fields. -/
theorem swap_first (pair : Pair) : (swap pair).first = pair.second := rfl

/-- Mentions the instance of `<`, and through it `firstLess`. -/
theorem less_of_first (left right : Pair) (firstIsLess : left.first < right.first) : left < right :=
  firstIsLess

/-- Mentions `total`, and through it `sum`. It does not mention `helper`. -/
theorem total_eq (pair : Pair) : total pair = pair.first + pair.second := rfl

/-- Mentions `viaHidden`. -/
theorem viaHidden_eq (number : Nat) : viaHidden number = number := rfl

/-- Mentions `fast`. -/
theorem fast_eq (number : Nat) : fast number = number + 1 := rfl

/-- Mentions `replaced`. -/
theorem replaced_eq (number : Nat) : replaced number = number + 1 := rfl

/-- Mentions `sealed`. -/
theorem sealed_eq : sealed = sealed := rfl

end LeanClaimsTest.Surface.Proofs
