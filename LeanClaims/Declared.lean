/-
  File: LeanClaims/Declared.lean
  Purpose: Which theorems a module declares, as Lean knows them. The tools read some
  things from a project's source text, because text can be read when a file does not
  compile. Text reading has blind spots: a theorem behind `set_option … in`, or made by a
  macro, is one a pattern over the text does not see. `#declared_theorems` gives the
  tools Lean's own list to compare their reading with, so that a blind spot shows as a
  difference and not as a theorem silently left out.

  The helpers here are also what `#audit_facts` uses to list a module's theorems.
  Created: 2026-11-13
-/

import Lean

open Lean Elab Command

namespace LeanClaims

/-- A theorem's name as it was written: a `private` theorem's name without the prefix Lean
    adds to keep it private. -/
def writtenName (name : Name) : Name := privateToUserName name

/-- Whether a constant is a theorem a person declared, as opposed to one Lean derives
    from a definition (its equation and unfolding lemmas) or an internal piece of a
    declaration. -/
def isWrittenTheorem (environment : Environment) (name : Name) (info : ConstantInfo) : Bool :=
  info matches .thmInfo _ && !(writtenName name).isInternalDetail && !isReservedName environment name

/-- The index of each named module, which must be imported. -/
def moduleIndexesOf (moduleSyntax : Array (TSyntax `ident)) : CommandElabM (Array ModuleIdx) := do
  let environment ← getEnv
  moduleSyntax.mapM fun moduleIdent =>
    match environment.getModuleIdx? moduleIdent.getId with
    | some moduleIndex => pure moduleIndex
    | none => throwErrorAt moduleIdent m!"the module {moduleIdent.getId} is not imported"

/-- The name of the module a constant was declared in. -/
def moduleNameOf (environment : Environment) (name : Name) : Name :=
  match environment.getModuleIdxFor? name with
  | some moduleIndex => environment.header.moduleNames[moduleIndex.toNat]!
  | none => Name.anonymous

/-- The line a declaration's name is on in its file, or 0 when Lean has no record of it. -/
def lineOf (name : Name) : CommandElabM Nat := do
  match ← findDeclarationRanges? name with
  | some ranges => return ranges.selectionRange.pos.line
  | none => return 0

/-- `#declared_theorems modules [M₁, M₂, …]` prints one line, `declared-theorems {…}`,
    listing every theorem the named modules declare: its name as written, its module, the
    line its name is on, and whether it is an instance (declared with `instance`, which
    the tools' reading of `theorem` declarations is not meant to find). -/
elab "#declared_theorems " "modules " "[" moduleSyntax:ident,* "]" : command => do
  let environment ← getEnv
  let moduleIndexes ← moduleIndexesOf moduleSyntax.getElems
  let mut entries : Array Json := #[]
  for (name, info) in environment.constants.map₁.toList do
    let some moduleIndex := environment.getModuleIdxFor? name | continue
    unless moduleIndexes.contains moduleIndex && isWrittenTheorem environment name info do continue
    entries := entries.push <| Json.mkObj [
      ("name", Json.str (writtenName name).toString), ("module", Json.str (moduleNameOf environment name).toString),
      ("line", toJson (← lineOf name)), ("instance", toJson (← liftCoreM <| Meta.isInstance name))]
  logInfo m!"declared-theorems {(Json.mkObj [("theorems", Json.arr entries)]).compress}"

end LeanClaims
