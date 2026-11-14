/-
  File: selftest/LeanClaimsTest/Surface/Code.lean
  Purpose: Stands in for a project's code in the test of `#surface_facts`. It holds one
  declaration of every sort the command must tell apart: a type with fields and derived
  instances, functions a claim states, a function a claim reaches only through notation
  (an instance, an abbreviation), a helper a stated function merely calls, a private
  declaration, a function no claim mentions, functions whose running code is not their
  definition, private ones of the same sort that public functions call, a type for which
  Lean itself generates such code, an axiom, an
  opaque constant and a theorem. At the end are the statements
  that two functions are equal, which are or could be `@[csimp]` replacements: one that
  is proved, and ones that rest on an axiom and replace a public function, a private
  helper and a function of Lean's own, one in force only in a namespace, one put in
  force by `attribute [local csimp]`, one whose statement is private, an axiom used as
  one directly, and a proved one that is not registered at all.

  The claims about it are in `LeanClaimsTest/Surface/Proofs.lean`, and what the command
  must report for each declaration is in `selftest/surface_facts.py`.
  Created: 2026-11-13
  Revised: 2026-11-14 (the statements that are or could be `@[csimp]` replacements)
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

/-- Private, and what runs is foreign code. `viaHiddenFast` is public and calls it. -/
@[extern "leanclaims_test_hidden_fast"]
private def hiddenFast (number : Nat) : Nat := number + 1

def viaHiddenFast (number : Nat) : Nat := hiddenFast number

/-- Private, and what runs is `replacement`. `viaHiddenReplaced` is public and calls it. -/
@[implemented_by replacement]
private def hiddenReplaced (number : Nat) : Nat := number + 3

def viaHiddenReplaced (number : Nat) : Nat := hiddenReplaced number

/-- Private and opaque, with a foreign implementation. The proofs see no definition of it,
    so it is not listed as hidden code. -/
@[extern "leanclaims_test_hidden_sealed"]
private opaque hiddenSealed : Nat → Nat

/-- A type with a computed field. Lean stores the field in each value, and to do so gives
    the field's function and the type's `casesOn` other code to run. The function is a
    public declaration. The `casesOn` is not: it belongs to the type. -/
inductive Shape where
  | point
  | joined (left right : Shape)
with
  @[computed_field] parts : Shape → Nat
    | .point => 1
    | .joined left right => left.parts + right.parts

/-- An assumption, with nothing for a proof to be about. -/
axiom assumed : ∀ number : Nat, unstated number = number + 2

/-- A constant whose definition is sealed. -/
opaque sealed : Nat

/-- A theorem of the code itself. -/
theorem swap_swap (pair : Pair) : swap (swap pair) = pair := rfl

/-! The statements that two functions are equal. They are last in the file because a
    registered one changes how everything after it is compiled. -/

def quick (number : Nat) : Nat := number.succ

/-- What runs is `quick`, and the kernel has checked that the two are the same function. -/
def slow (number : Nat) : Nat := number + 1

@[csimp] theorem slow_eq_quick : @slow = @quick := rfl

/-- Of the right form, proved, and not registered. Nothing is wrong with it. -/
theorem quick_eq_slow : @quick = @slow := rfl

/-- Not the same function as any below: it adds two. Private, as are the axioms, so none
    of them is a public declaration and only the statements give them away. -/
private def different (number : Nat) : Nat := number + 2

/-- A public function. What runs is `different`, on the word of an axiom: the definition
    says one more than the number and the compiled code returns two more. -/
def swapped (number : Nat) : Nat := number + 1

private axiom swappedIsDifferent : @swapped = @different

@[csimp] theorem swapped_eq_different : @swapped = @different := swappedIsDifferent

/-- A private helper replaced the same way. No public declaration carries the attribute
    or is named in the statement's left side. -/
private def inner (number : Nat) : Nat := number + 1

private axiom innerIsDifferent : @inner = @different

@[csimp] theorem inner_eq_different : @inner = @different := innerIsDifferent

/-- Public, and compiled with `different` in the place of `inner`. -/
def viaInner (number : Nat) : Nat := inner number

/-- A function of Lean's own replaced, for whatever the project compiles after this. -/
private axiom predIsDifferent : @Nat.pred = @different

@[csimp] theorem pred_eq_different : @Nat.pred = @different := predIsDifferent

/-- In force only where this namespace is open. -/
def scopedSlow (number : Nat) : Nat := number + 1

private axiom scopedSlowIsDifferent : @scopedSlow = @different

@[scoped csimp] theorem scopedSlow_eq_different : @scopedSlow = @different := scopedSlowIsDifferent

/-- Put in force for one section, of which Lean keeps no record. -/
def localSlow (number : Nat) : Nat := number + 1

private axiom localSlowIsDifferent : @localSlow = @different

theorem localSlow_eq_different : @localSlow = @different := localSlowIsDifferent

section
attribute [local csimp] localSlow_eq_different

/-- Compiled with `different` in the place of `localSlow`. -/
def viaLocal (number : Nat) : Nat := localSlow number
end

/-- Replaced by a statement that is itself private, so no entry can list it. -/
def hiddenSlow (number : Nat) : Nat := number + 1

private axiom hiddenSlowIsDifferent : @hiddenSlow = @different

@[csimp] private theorem hiddenSlow_eq_different : @hiddenSlow = @different := hiddenSlowIsDifferent

/-- Replaced by an axiom carrying the attribute itself. -/
def decreedSlow (number : Nat) : Nat := number + 1

@[csimp] private axiom decreedSlowIsDifferent : @decreedSlow = @different

end LeanClaimsTest.Surface
