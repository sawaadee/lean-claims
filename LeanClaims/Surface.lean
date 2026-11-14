/-
  File: LeanClaims/Surface.lean
  Purpose: The public surface of a project's code, and what its claims say about it. A
  project can prove every claim it makes and still ship a function no claim mentions.
  `#surface_facts` lists every public declaration of the code modules, and for each one
  the claim theorems whose statements mention it, so that `claims trust` can require
  every declaration to be proved, tested or trusted and can show a reviewer which
  definitions the claims are written in.

  What counts as a public declaration: a definition, theorem, type, instance, axiom or
  opaque constant that a person declared in a code module and did not mark `private`.
  What Lean generates for a declaration belongs to it and is not listed on its own: a
  type's constructors, fields, recursors and the helpers of a derived instance. A mention
  of one of those counts as a mention of its owner.

  What counts as a mention: the declaration appears in the claim theorem's statement, or
  in the body of an instance or of a reducible definition that the statement uses. Those
  two are notation: a statement that says `u < v` mentions the instance of `<`, and
  through it the function the instance is defined by. Nothing else is unfolded. A helper
  that a stated function merely calls is not mentioned, because no claim says what the
  helper does for inputs the stated function never gives it.

  The vocabulary is wider: every declaration reached from a claim's statement through the
  types and bodies of definitions. That is what a reviewer has to read to know what the
  claims mean.

  What this cannot establish: that a mention is a guarantee. A claim may mention a
  function and say little about it. The audit and the mutation run are the checks on
  that.

  Compiled replacements. A `@[csimp]` theorem states `@f = @g` and has the compiler run
  `g` wherever later code names `f`. What it replaces need not be a public declaration of
  the project: it can be a private helper, or a function of Lean or of a dependency that
  the project's code calls. So the command does not ask of each public declaration
  whether it is replaced. It lists every constant of the project's modules whose
  statement has that form, with the axioms it depends on beyond the standard ones and
  whether Lean has it registered as a replacement, everywhere or in a namespace.

  One with that form that is not registered is listed all the same, because
  `attribute [local csimp]` puts a replacement in force for the rest of a section and
  Lean keeps no record of it afterwards. Whether that happened cannot be asked, so every
  statement that could be used that way is reported and `claims trust` judges it by its
  axioms.

  Hidden code. `@[extern]` and `@[implemented_by]` can be put on a private definition
  that a public one calls. The public one then runs code the proofs do not reach, and
  nothing about it says so. So the command also lists, under `hidden`, every definition
  of the code that is not a public declaration and carries either attribute. Lean puts
  `@[implemented_by]` on definitions of its own making too: a type with a computed field
  gets a `casesOn` that runs other code. Such a definition belongs to a public
  declaration, and is listed with that owner, so that an entry for the owner can account
  for it. One a person wrote and marked `private` has no owner.

  What the list cannot hold: a replacement declared in a module that neither the code
  nor the proofs import, such as one in the test package, which changes only what the
  tests run.
  Created: 2026-11-13
  Revised: 2026-11-14 (every statement of the project that is or could be a `@[csimp]`
  replacement, with the axioms behind it; the definitions that are not public and run
  other code than their definition)
-/

import Lean
import LeanClaims.Axioms
import LeanClaims.Declared

open Lean Elab Command Meta

namespace LeanClaims

/-- What the surface command needs to know about the environment it reads. -/
structure SurfaceContext where
  environment : Environment
  /-- Whether a module holds the project's code, as opposed to its proofs. -/
  isCodeModule : Name → Bool

/-- Whether a constant was declared in one of the project's code modules. -/
def SurfaceContext.inCode (context : SurfaceContext) (name : Name) : Bool :=
  match context.environment.getModuleIdxFor? name with
  | some moduleIndex => context.isCodeModule context.environment.header.moduleNames[moduleIndex.toNat]!
  | none => false

/-- Whether a person declared this constant: it has a place in a source file recorded
    for it, which the constants Lean generates alongside a declaration do not. -/
def hasOwnSourcePosition (environment : Environment) (name : Name) : Bool :=
  (declRangeExt.find? (level := .exported) environment name).isSome ||
    (declRangeExt.find? (level := .server) environment name).isSome

/-- The place in the source of a constant's name, when it has one of its own. -/
def ownSelectionRange? (environment : Environment) (name : Name) : Option DeclarationRange :=
  let ranges := (declRangeExt.find? (level := .exported) environment name).orElse
    fun _ => declRangeExt.find? (level := .server) environment name
  ranges.map (·.selectionRange)

/-- Whether a constant of the code is a declaration in its own right: declared by a
    person, public, and not a constructor or a field, which belong to their type, nor a
    helper of a derived instance, which shares the instance's place in the source. -/
def SurfaceContext.isSurfaceDeclaration (context : SurfaceContext) (name : Name) (info : ConstantInfo) : Bool :=
  let environment := context.environment
  context.inCode name && !isPrivateName name && !name.isInternalDetail && !isReservedName environment name &&
    hasOwnSourcePosition environment name && !(info matches .ctorInfo _) && !(info matches .recInfo _) &&
    !environment.isProjectionFn name &&
    -- A helper such as `instReprMode.repr` sits at the same place as `instReprMode`.
    !(name.getPrefix != .anonymous && context.inCode name.getPrefix &&
      (ownSelectionRange? environment name.getPrefix).isSome &&
      (ownSelectionRange? environment name.getPrefix).map (·.pos) == (ownSelectionRange? environment name).map (·.pos))

/-- The surface declaration a constant of the code belongs to: itself when it is one, the
    type of a constructor or a field, and otherwise the nearest enclosing name that is
    one, which is where Lean puts what it generates. `none` for a private declaration and
    for anything that belongs to one. -/
partial def SurfaceContext.ownerOf (context : SurfaceContext) (name : Name) : Option Name := do
  let environment := context.environment
  let info ← environment.find? name
  if context.isSurfaceDeclaration name info then
    return name
  if isPrivateName name then
    none
  match info with
  | .ctorInfo constructor => context.ownerOf constructor.induct
  | _ =>
    match environment.getProjectionFnInfo? name with
    | some projection => context.ownerOf projection.ctorName
    | none => if name.getPrefix == .anonymous then none else context.ownerOf name.getPrefix

/-- The constants a declaration is made of: those in its type, and those in its body
    when it has one that is part of what it means. A theorem's proof is not. -/
def constantsOfDeclaration (info : ConstantInfo) : Array Name :=
  let fromType := info.type.getUsedConstants
  match info with
  | .defnInfo definition => fromType ++ definition.value.getUsedConstants
  | .opaqueInfo opaqueConstant => fromType ++ opaqueConstant.value.getUsedConstants
  | .inductInfo inductiveType => fromType ++ inductiveType.ctors.toArray
  | _ => fromType

/-- Every constant reached from `start` by following `expand` on the constants already
    reached. -/
partial def reachedFrom (environment : Environment) (start : Array Name) (expand : Name → ConstantInfo → Bool) :
    NameSet := Id.run do
  let mut reached : NameSet := {}
  let mut pending := start
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if reached.contains name then continue
    reached := reached.insert name
    if let some info := environment.find? name then
      if expand name info then
        pending := pending ++ constantsOfDeclaration info
  return reached

/-- The kind of a surface declaration, as the report names it. -/
def kindOf (info : ConstantInfo) (isInstance : Bool) : String :=
  if isInstance then "instance" else
  match info with
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .inductInfo _ => "type"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | _ => "other"

/-- The name a person wrote for a constant, which for a private one is not the name Lean
    keeps for it. -/
def shownName (name : Name) : String :=
  (if isPrivateName name then privateToUserName name else name).toString

/-- The two constants of a statement `@f = @g`, which is the only form Lean accepts for a
    `@[csimp]` theorem. Lean also requires the two to take the same universe parameters;
    that is not asked here, so that nothing Lean would accept is left out. -/
def constantEquality? (type : Expr) : Option (Name × Name) :=
  match type.eq? with
  | some (_, .const replaced _, .const replacement _) => some (replaced, replacement)
  | _ => none

/-- Where Lean has a constant registered as a `@[csimp]` replacement: `some none` when it
    is in force everywhere it is imported, `some (some namespace)` when it is in force
    where that namespace is open, and `none` when it is not registered. -/
def registeredReplacement? (environment : Environment) (name : Name) : Option (Option Name) :=
  if (Compiler.CSimp.ext.getState environment).thmNames.contains name then
    some none
  else
    (Compiler.CSimp.ext.ext.getState environment).scopedEntries.map.fold (init := none)
      fun found scopeName entries =>
        if found.isSome then found
        else if entries.toArray.any (·.thmName == name) then some (some scopeName)
        else none

/-- `#surface_facts claims [T₁, …] code [P₁, …] proofs [M₁, …]` prints one line,
    `surface-facts {…}`. The code modules are the imported modules whose name starts with
    one of the prefixes `Pᵢ` and is not one of the proof modules `Mᵢ`. The line holds
    every public declaration of the code with its kind, its place, whether what runs for
    it is other than its definition (`@[extern]` or `@[implemented_by]`) and the claim
    theorems that mention it; under `replacements`, every constant of the project's
    modules, public or not, that states two constants are equal, and under `hidden` every
    definition of the code that is not public and runs other code than its definition, as
    the header describes; for every claim theorem the declarations it mentions; and
    the vocabulary, every declaration of the code the claims are written in. -/
elab "#surface_facts " "claims " "[" claimSyntax:ident,* "]" " code " "[" codeSyntax:ident,* "]"
    " proofs " "[" proofSyntax:ident,* "]" : command => do
  let environment ← getEnv
  let mut claimTheorems : Array Name := #[]
  for theoremSyntax in claimSyntax.getElems do
    match environment.find? theoremSyntax.getId with
    | some (.thmInfo _) => claimTheorems := claimTheorems.push theoremSyntax.getId
    | _ => throwErrorAt theoremSyntax m!"{theoremSyntax.getId} is not a theorem in this environment"
  let codePrefixes := codeSyntax.getElems.map (·.getId)
  let proofModules := proofSyntax.getElems.map (·.getId)
  for codeIdent in codeSyntax.getElems do
    unless environment.header.moduleNames.any codeIdent.getId.isPrefixOf do
      throwErrorAt codeIdent m!"no imported module has a name starting with {codeIdent.getId}"
  let context : SurfaceContext := {
    environment
    isCodeModule := fun moduleName => codePrefixes.any (·.isPrefixOf moduleName) && !proofModules.contains moduleName }

  let inProject (name : Name) : Bool :=
    match environment.getModuleIdxFor? name with
    | some moduleIndex => codePrefixes.any (·.isPrefixOf environment.header.moduleNames[moduleIndex.toNat]!)
    | none => false
  let mut instanceNames : NameSet := {}
  let mut surface : Array (Name × ConstantInfo) := #[]
  let mut replacementStatements : Array (Name × Name × Name) := #[]
  for (name, info) in environment.constants.map₁.toList do
    -- Proof modules are searched as well as code: a replacement declared among the proofs
    -- is in force for whatever imports them.
    if inProject name then
      if let some (replaced, replacement) := constantEquality? info.type then
        replacementStatements := replacementStatements.push (name, replaced, replacement)
    unless context.inCode name do continue
    if ← liftCoreM <| Meta.isInstance name then
      instanceNames := instanceNames.insert name
    if context.isSurfaceDeclaration name info then
      surface := surface.push (name, info)
  let surfaceNames : NameSet := surface.foldl (init := {}) fun names (name, _) => names.insert name

  -- A statement's mentions: its own constants, and those behind the instances and the
  -- reducible definitions among them, which are notation for what they unfold to.
  let isNotation (name : Name) (info : ConstantInfo) : Bool :=
    instanceNames.contains name ||
      (info matches .defnInfo _ && getReducibilityStatusCore environment name == .reducible)
  let owned (names : NameSet) : Array Name :=
    (names.toList.filterMap context.ownerOf).foldl (init := #[]) fun found name =>
      if found.contains name then found else found.push name
  let mut mentionsOf : Array (Name × Array Name) := #[]
  let mut statedBy : NameMap (Array Name) := {}
  let mut statementConstants : Array Name := #[]
  for claimTheorem in claimTheorems do
    let some info := environment.find? claimTheorem | continue
    let direct := info.type.getUsedConstants
    statementConstants := statementConstants ++ direct
    let mentioned := (owned (reachedFrom environment direct isNotation)).qsort Name.lt
    mentionsOf := mentionsOf.push (claimTheorem, mentioned)
    for name in mentioned do
      statedBy := statedBy.insert name ((statedBy.find? name |>.getD #[]).push claimTheorem)
  -- The vocabulary: everything of the code reached through types and definition bodies.
  let vocabularyConstants := reachedFrom environment statementConstants fun name _ => context.inCode name
  let vocabulary := ((owned vocabularyConstants).filter surfaceNames.contains).qsort Name.lt
  -- Private declarations the claims are written in. They are not surface, and a
  -- reviewer reads them all the same.
  let privateVocabulary := (vocabularyConstants.toList.filter fun name =>
    context.inCode name && isPrivateName name && hasOwnSourcePosition environment name &&
      !(privateToUserName name).isInternalDetail).map privateToUserName

  let namesToJson (names : Array Name) : Json := Json.arr (names.map fun name => Json.str name.toString)
  let mut surfaceJson : Array Json := #[]
  for (name, info) in surface do
    let implementedBy := (Compiler.getImplementedBy? environment name).map fun implementation =>
      Json.str implementation.toString
    surfaceJson := surfaceJson.push <| Json.mkObj [
      ("name", Json.str name.toString), ("module", Json.str (moduleNameOf environment name).toString),
      ("line", toJson (← lineOf name)), ("kind", Json.str (kindOf info (instanceNames.contains name))),
      ("extern", toJson (isExtern environment name)), ("implemented_by", implementedBy.getD Json.null),
      ("stated_by", namesToJson (statedBy.find? name |>.getD #[]))]
  -- Definitions outside the surface whose running code is not their definition. An
  -- opaque constant is left out: the proofs see no definition of it, so they claim nothing
  -- the code that runs could contradict.
  let mut hiddenJson : Array Json := #[]
  let hiddenDefinitions := (environment.constants.map₁.toList.toArray.filterMap fun (name, info) =>
    if context.inCode name && !surfaceNames.contains name && info matches .defnInfo _ then some name else none)
  for name in hiddenDefinitions.qsort Name.lt do
    let implementedBy := Compiler.getImplementedBy? environment name
    if isExtern environment name || implementedBy.isSome then
      hiddenJson := hiddenJson.push <| Json.mkObj [
        ("name", Json.str (shownName name)), ("module", Json.str (moduleNameOf environment name).toString),
        ("line", toJson (← lineOf name)), ("extern", toJson (isExtern environment name)),
        ("implemented_by", (implementedBy.map fun implementation => Json.str (shownName implementation)).getD Json.null),
        ("owner", ((context.ownerOf name).map fun owner => Json.str owner.toString).getD Json.null)]
  let claimsJson := mentionsOf.map fun (claimTheorem, mentioned) =>
    Json.mkObj [("name", Json.str claimTheorem.toString), ("mentions", namesToJson mentioned)]
  let mut replacementsJson : Array Json := #[]
  for (name, replaced, replacement) in replacementStatements.qsort fun left right => Name.lt left.1 right.1 do
    let axioms ← liftCoreM <| collectAxioms name
    let beyondStandard := (axioms.filter fun usedAxiom => !standardAxioms.contains usedAxiom).qsort Name.lt
    let registered := registeredReplacement? environment name
    replacementsJson := replacementsJson.push <| Json.mkObj [
      ("statement", Json.str (shownName name)), ("statement_is_public", toJson (surfaceNames.contains name)),
      ("module", Json.str (moduleNameOf environment name).toString), ("line", toJson (← lineOf name)),
      ("replaced", Json.str (shownName replaced)), ("replaced_is_public", toJson (surfaceNames.contains replaced)),
      ("replacement", Json.str (shownName replacement)),
      ("registered", toJson registered.isSome),
      ("namespace", match registered with
        | some (some scopeName) => Json.str scopeName.toString
        | _ => Json.null),
      ("axioms", Json.arr (beyondStandard.map fun usedAxiom => Json.str (shownName usedAxiom)))]
  let document := Json.mkObj [
    ("surface", Json.arr surfaceJson), ("claims", Json.arr claimsJson), ("vocabulary", namesToJson vocabulary),
    ("replacements", Json.arr replacementsJson), ("hidden", Json.arr hiddenJson),
    ("private_vocabulary", namesToJson (privateVocabulary.toArray.qsort Name.lt))]
  logInfo m!"surface-facts {document.compress}"

end LeanClaims
