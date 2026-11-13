/-
  File: LeanClaims/Axioms.lean
  Purpose: Commands that fail the build when a theorem rests on an axiom outside an
  allowed list. A theorem that used `sorry`, `native_decide` or a new axiom depends on
  `sorryAx`, `Lean.ofReduceBool` or that axiom, and the file holding the assertion then
  fails to compile.

  Every theorem in each named module is checked, so a new theorem is covered without
  being named, and the theorems are the ones Lean finds, not ones read from source text.
  After `in`, a module in which no theorem is found is an error, so a misspelt or emptied
  module cannot pass by checking nothing. After `across`, the modules are taken together
  and must declare at least one theorem between them: this is for a set of files matched
  by a pattern, some of which only import the others.

  This file imports `Lean` to read the environment. A project uses it from its test
  package, so the `Lean` package does not reach the project's own library.
  Created: 2026-11-13
-/

import Lean

open Lean Elab Command

namespace LeanClaims

/-- The axioms of Lean's standard logic: propositional extensionality, the axiom of
    choice and quotient soundness. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Fails unless each named module is imported and every theorem it declares depends only
    on axioms in `allowedAxioms`. With `eachMustDeclare`, a module that declares no
    theorem is an error; without it, the modules together must declare at least one. The
    error is reported at the module's name and names the first offending theorem with its
    extra axioms. -/
def assertModulesWithinAxioms (allowedAxioms : List Name) (modules : Array (TSyntax `ident))
    (eachMustDeclare : Bool) : CommandElabM Unit := do
  let environment ← getEnv
  let mut theoremCount := 0
  for moduleSyntax in modules do
    let moduleName := moduleSyntax.getId
    let some moduleIndex := environment.getModuleIdx? moduleName
      | throwErrorAt moduleSyntax m!"module {moduleName} is not imported here"
    -- Every theorem whose declaration comes from this module, in a fixed order so that
    -- any report reads the same from run to run.
    let theorems := environment.constants.map₁.toList.filterMap fun (name, info) =>
      if environment.getModuleIdxFor? name == some moduleIndex && info matches .thmInfo _ then
        some name
      else
        none
    if theorems.isEmpty && eachMustDeclare then
      throwErrorAt moduleSyntax m!"no theorems found in {moduleName}, so nothing was checked"
    theoremCount := theoremCount + theorems.length
    for theoremName in theorems.toArray.qsort Name.lt do
      let axioms ← liftCoreM <| collectAxioms theoremName
      let unexpected := axioms.filter (· ∉ allowedAxioms)
      unless unexpected.isEmpty do
        throwErrorAt moduleSyntax
          m!"{theoremName} depends on {unexpected.toList}, beyond the allowed axioms {allowedAxioms}"
  if theoremCount == 0 then
    throwError m!"no theorems found in any of the {modules.size} modules, so nothing was checked"

/-- `#assert_standard_axioms M₁ M₂ …` fails unless each named module declares at least one
    theorem and every theorem it declares depends on the standard axioms only. -/
elab "#assert_standard_axioms " modules:ident* : command =>
  assertModulesWithinAxioms standardAxioms modules (eachMustDeclare := true)

/-- The names in an allowed list, each of which must be an axiom in the environment, so
    that a misspelt axiom cannot widen or narrow the list unnoticed. -/
def allowedAxiomsOf (allowed : Array (TSyntax `ident)) : CommandElabM (List Name) := do
  let environment ← getEnv
  let mut allowedAxioms : List Name := []
  for allowedSyntax in allowed do
    let axiomName := allowedSyntax.getId
    match environment.find? axiomName with
    | some (.axiomInfo _) => allowedAxioms := allowedAxioms ++ [axiomName]
    | _ => throwErrorAt allowedSyntax m!"{axiomName} is not an axiom in this environment"
  return allowedAxioms

/-- `#assert_axioms_among [a₁, a₂, …] in M₁ M₂ …` is the same check against a list of
    axioms the project chooses. Every module must declare at least one theorem. -/
elab "#assert_axioms_among " "[" allowed:ident,* "]" " in " modules:ident* : command => do
  assertModulesWithinAxioms (← allowedAxiomsOf allowed.getElems) modules (eachMustDeclare := true)

/-- `#assert_axioms_among [a₁, a₂, …] across M₁ M₂ …` checks every theorem of the modules
    taken together. A module may declare none, as a file that only imports the others
    does; the modules together must declare at least one. -/
elab "#assert_axioms_among " "[" allowed:ident,* "]" " across " modules:ident* : command => do
  assertModulesWithinAxioms (← allowedAxiomsOf allowed.getElems) modules (eachMustDeclare := false)

end LeanClaims
