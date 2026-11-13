/-
  File: tests/Axioms.lean
  Purpose: Asserts that every theorem in the project's proof modules, and in the test
  package's modules of theorems, rests only on the allowed axioms. A theorem that used
  `sorry`, `native_decide` or a new axiom would make this file fail to compile, which
  fails the build of the test library. The theorems are the ones Lean finds in each
  module. The proof modules are checked together, since a proof file may only import
  the others. A test module in which no theorem is found is an error, so a misspelt
  or emptied one cannot pass by checking nothing.

  Written by `claims sync` from `claims.toml`. Not edited by hand.
  Created: 2026-11-14
-/

import LeanClaims
import MiniJson.Proofs
import JsonAudit

#assert_axioms_among [propext, Classical.choice, Quot.sound] across
  MiniJson.Proofs.Claims MiniJson.Proofs.Digits MiniJson.Proofs.Stripped MiniJson.Proofs.Text
  MiniJson.Proofs.Tokens MiniJson.Proofs.Written

#assert_axioms_among [propext, Classical.choice, Quot.sound] in
  JsonAudit
