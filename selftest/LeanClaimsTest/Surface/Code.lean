/-
  File: selftest/LeanClaimsTest/Surface/Code.lean
  Purpose: Stands in for a project's code in the test of `#surface_facts`. It holds one
  declaration of every sort the command must tell apart: a type with fields and derived
  instances, functions a claim states, a function a claim reaches only through notation
  (an instance, an abbreviation), a helper a stated function merely calls, a private
  declaration, a function no claim mentions, functions whose running code is not their
  definition, an axiom, an opaque constant and a theorem.

  The claims about it are in `LeanClaimsTest/Surface/Proofs.lean`, and what the command
  must report for each declaration is in `selftest/surface_facts.py`.
  Created: 2026-11-13
-/

namespace LeanClaimsTest.Surface

/-- A type with two fields and two derived instances. The fields, the constructor and
    everything Lean generates for the type belong to it. The derived instances are
    declarations of their own, and no claim mentions them. -/
structure Pair where
  first : Nat
  second : Nat
deriving Repr, DecidableEq

/-- Stated by a claim directly. -/
def swap (pair : Pair) : Pair := { first := pair.second, second := pair.first }

/-- Reached by a claim through the instance of `<` below, which is notation for it. -/
def firstLess (left right : Pair) : Prop := left.first < right.first

instance : LT Pair := ⟨firstLess⟩

/-- Called by `sum`. No claim states what it does, so it is not mentioned, and it is part
    of the vocabulary because `sum` is defined by it. -/
def helper (left right : Nat) : Nat := left + right

/-- Reached by a claim through the abbreviation `total`, which is notation for it. -/
def sum (pair : Pair) : Nat := helper pair.first pair.second

abbrev total (pair : Pair) : Nat := sum pair

/-- Private: not part of the public surface, and read by a reviewer all the same because
    `viaHidden` is defined by it. -/
private def hidden (number : Nat) : Nat := number

def viaHidden (number : Nat) : Nat := hidden number

/-- No claim mentions it. -/
def unstated (number : Nat) : Nat := number + 2

/-- A claim states it, and what runs is foreign code the proofs do not reach. -/
@[extern "leanclaims_test_fast"]
def fast (number : Nat) : Nat := number + 1

def replacement (number : Nat) : Nat := number + 1

/-- A claim states it, and what runs is `replacement`. -/
@[implemented_by replacement]
def replaced (number : Nat) : Nat := number + 1

/-- An assumption, with nothing for a proof to be about. -/
axiom assumed : ∀ number : Nat, unstated number = number + 2

/-- A constant whose definition is sealed. -/
opaque sealed : Nat

/-- A theorem of the code itself. -/
theorem swap_swap (pair : Pair) : swap (swap pair) = pair := rfl

end LeanClaimsTest.Surface
