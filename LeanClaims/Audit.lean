/-
  File: LeanClaims/Audit.lean
  Purpose: What Lean can confirm about a project's audit theorems. An audit theorem says
  in its doc comment what it audits, and a comment proves nothing: a theorem proving
  `True` under the comment "fails claim 3" compiles and rests on no axiom. This file gives
  the facts `claims audit` requires, each established by Lean from the statements
  themselves.

  A claim is audited through a property: a definition in an audit module that asks the
  claim of any candidate implementation, such as

    def MeetsClaim2 (candidate : Nat → Nat → Nat → Nat) : Prop :=
      ∀ low high value, low ≤ high → candidate low high value ≤ high

  A property is tied to a claim's theorem when an audit module proves a theorem whose
  statement is the property applied to something, and that statement is, by definitional
  unfolding, the statement of a claim's theorem that its proof uses. `theorem tie :
  MeetsClaim2 clamp := Proofs.clamp_le_high` is such a theorem. Only the claim theorems
  the proof uses are compared. That is what tying a property to a claim means, and it
  keeps Lean from unfolding unrelated statements against each other.

  A conjunction of such statements ties each of its parts. A property that gathers
  several claim theorems, `∀ x, A x ∧ B x` where the claims state `∀ x, A x` and
  `∀ x, B x`, is tied to all of them, provided every part is a claim theorem's statement.

  When a claim's own statement is a type class applied to the implementation, such as
  `Std.TransCmp compare`, the class is the property and needs no tie.

  With the ties known, three shapes of audit theorem are recognised:

    fails       `¬ P wrong`, where `P` is a tied property. A wrong implementation does
                not meet the claim.
    determines  A hypothesis about a bound variable `candidate` that the conclusion
                mentions: either `P candidate` for a tied property `P`, or a claim
                theorem's statement written out with `candidate` where the claim has
                the implementation. The conclusion must relate the candidate to
                something: to a declaration from outside Lean's own libraries, as in
                `candidate = clamp`, or to a second candidate that meets claims too, as
                in `first = second`. A conclusion such as `candidate = candidate` pins
                nothing down and is not recognised.
    can hold    `hypotheses_can_hold% T`, the statement that values exist for which every
                hypothesis of the theorem `T` is true, or a conjunction of such
                statements.

  `#audit_facts` prints these facts as one line of JSON for the tools to read.

  What this cannot establish: that a property depends on its candidate in the way a
  reader expects. Lean confirms that the property, asked of the project's own
  implementation, is the claim. The reviewer still reads the property.
  Created: 2026-11-13
-/

import Lean
import LeanClaims.Declared

open Lean Elab Command Meta

namespace LeanClaims

/-- The number of hypotheses of a statement: its arguments that are proofs of
    propositions, such as `(h : low ≤ high)` or the left side of an arrow. Arguments that
    are values, such as `(n : Nat)`, are not hypotheses. Whether a statement has
    hypotheses cannot be told reliably from its text, so Lean is asked. -/
def hypothesisCount (statement : Expr) : MetaM Nat :=
  forallTelescope statement fun arguments _ => do
    let mut count := 0
    for argument in arguments do
      if ← isProp (← inferType argument) then
        count := count + 1
    return count

/-- The statement that the hypotheses of a theorem can hold together: for a theorem
    `(x : A) (h : P x) : Q x` it is `∃ x, ∃ _ : P x, True`. Every argument is bound, values
    and proofs alike and in order, so a hypothesis that mentions an earlier one is still
    well formed. -/
def hypothesesCanHoldStatement (statement : Expr) : MetaM Expr :=
  forallTelescope statement fun arguments _ => do
    let mut result := mkConst ``True
    for argument in arguments.reverse do
      let predicate ← mkLambdaFVars #[argument] result
      result ← mkAppM ``Exists #[predicate]
    return result

/-- The statement of a theorem, with fresh universe levels so that it can be compared
    with a statement at any universe. -/
def statementOfTheorem (theoremName : Name) : MetaM Expr := do
  inferType (← mkConstWithFreshMVarLevels theoremName)

/-- `hypotheses_can_hold% T` is the statement that the hypotheses of the theorem `T` can
    hold together. A proof gives a value for every argument of `T` and a proof of every
    hypothesis, and ends with `trivial`:

      theorem range_can_be_non_empty : hypotheses_can_hold% Proofs.clamp_le_high :=
        ⟨5, 10, 7, by decide, trivial⟩ -/
elab "hypotheses_can_hold% " theoremSyntax:ident : term => do
  let theoremName ← realizeGlobalConstNoOverloadWithInfo theoremSyntax
  match (← getEnv).find? theoremName with
  | some (.thmInfo _) => hypothesesCanHoldStatement (← statementOfTheorem theoremName)
  | _ => throwErrorAt theoremSyntax m!"{theoremName} is not a theorem"

/-- The parts of a conjunction, left to right. A statement that is not a conjunction is
    its own single part. -/
partial def conjunctsOf (proposition : Expr) : Array Expr :=
  match proposition.consumeMData.and? with
  | some (left, right) => conjunctsOf left ++ conjunctsOf right
  | none => #[proposition.consumeMData]

/-- The heartbeats one comparison of two statements may use, the same number Lean allows
    a whole declaration by default. -/
def comparisonHeartbeats : Nat := 200000

/-- The clauses of a statement: it is taken apart at every conjunction, under any
    quantifiers and hypotheses in front of it, and each part is closed again under those
    same quantifiers and hypotheses. `∀ x, A x ∧ B x` has the clauses `∀ x, A x` and
    `∀ x, B x`. A statement with no conjunction is its own single clause. -/
partial def clausesOf (proposition : Expr) : MetaM (Array Expr) :=
  forallTelescope proposition fun binders body => do
    match body.consumeMData.and? with
    | some (left, right) =>
      let inner := (← clausesOf left) ++ (← clausesOf right)
      inner.mapM fun clause => mkForallFVars binders clause
    | none => return #[proposition]

/-- Whether two statements are the same up to definitional unfolding. The comparison is
    made in a scope of its own, so that nothing it assigns leaks into the next one. A
    comparison that Lean gives up on counts as "not the same" and is reported through
    `gaveUp`, so that it is never taken silently for a mismatch. -/
def sameStatement (left : Expr) (right : MetaM Expr) (gaveUp : IO.Ref (Array String)) (what : String)
    (transparency : TransparencyMode := .default) : MetaM Bool := do
  -- Running out of recursion depth or of heartbeats is not caught by an ordinary `try`.
  -- Each comparison gets a budget of its own, so that one that runs out does not take
  -- the rest of the command with it.
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun context => { context with maxHeartbeats := comparisonHeartbeats * 1000 }) <|
      withCurrHeartbeats <| withNewMCtxDepth <| withTransparency transparency do
        isDefEq left (← right))
    fun exception => do
      gaveUp.modify (·.push s!"{what}: {← exception.toMessageData.toString}")
      return false

/-- The claim theorems whose statement is `proposition`. -/
def claimTheoremsStating (proposition : Expr) (claimTheorems : Array Name) (gaveUp : IO.Ref (Array String)) :
    MetaM (Array Name) :=
  claimTheorems.filterM fun claimTheorem =>
    sameStatement proposition (statementOfTheorem claimTheorem) gaveUp s!"comparing with {claimTheorem}"

/-- A property and the claim theorems it stands for. -/
structure PropertyTie where
  property : Name
  claimTheorems : Array Name
  tiedBy : Name

/-- The ties one audit theorem's statement establishes. Each part of the statement whose
    head is a definition of an audit module is compared with `claimTheorems`, the claim
    theorems the audit theorem's proof uses: first as it stands, then, when it unfolds
    to several clauses, clause by clause. A property with a clause that is no claim's
    statement is not tied, because failing it would not mean failing a
    claim. -/
def tiesFrom (auditTheorem : Name) (statement : Expr) (isProperty : Name → Bool) (claimTheorems : Array Name)
    (gaveUp : IO.Ref (Array String)) : MetaM (Array PropertyTie) := do
  let mut ties := #[]
  for part in conjunctsOf statement do
    let .const property _ := part.getAppFn | continue
    unless isProperty property do continue
    let direct ← claimTheoremsStating part claimTheorems gaveUp
    if !direct.isEmpty then
      ties := ties.push { property, claimTheorems := direct, tiedBy := auditTheorem }
      continue
    let some unfolded ← unfoldDefinition? part | continue
    let innerParts ← clausesOf unfolded
    if innerParts.size < 2 then continue
    let mut stated := #[]
    let mut everyPartIsAClaim := true
    for innerPart in innerParts do
      let matching ← claimTheoremsStating innerPart claimTheorems gaveUp
      if matching.isEmpty then
        everyPartIsAClaim := false
        break
      stated := stated ++ matching
    if everyPartIsAClaim then
      ties := ties.push { property, claimTheorems := stated, tiedBy := auditTheorem }
  return ties

/-- What Lean finds an audit theorem's statement to be. -/
structure AuditTheoremFacts where
  /-- The claim theorems a wrong implementation is shown not to meet. -/
  fails : Array Name := #[]
  /-- The property under the negation, when the statement is `¬ P …`. -/
  negatedProperty : Option Name := none
  /-- The claim theorems asked, in the hypotheses, of a bound candidate that the
      conclusion mentions. -/
  determines : Array Name := #[]
  /-- The claim theorems whose hypotheses are shown to hold together. -/
  canHold : Array Name := #[]

/-- Read one audit theorem's statement against the ties. -/
def factsOf (statement : Expr) (tiesOf : Name → Array Name) (claimTheorems : Array Name)
    (claimTheoremsWithHypotheses : Array Name) (gaveUp : IO.Ref (Array String)) : MetaM AuditTheoremFacts := do
  let mut facts : AuditTheoremFacts := {}
  if let some negated := statement.consumeMData.not? then
    if let .const property _ := negated.getAppFn then
      facts := { facts with negatedProperty := some property, fails := tiesOf property }
  let determined ← forallTelescope statement fun arguments conclusion => do
    let mut found := #[]
    let mut candidatesMeetingClaims : Array Expr := #[]
    for argument in arguments do
      let argumentType ← inferType argument
      unless ← isProp argumentType do continue
      let foundBefore := found.size
      -- The candidates this hypothesis is about: bound values the conclusion mentions.
      let mut candidates := #[]
      for candidate in arguments do
        if candidate != argument && argumentType.containsFVar candidate.fvarId! &&
            conclusion.containsFVar candidate.fvarId! && !(← isProp (← inferType candidate)) then
          candidates := candidates.push candidate
      if candidates.isEmpty then continue
      if let .const property _ := argumentType.getAppFn then
        if argumentType.getAppArgs.any candidates.contains then
          found := found ++ tiesOf property
      -- The hypothesis written out: it is a claim theorem's statement once the candidate
      -- is replaced by whatever the claim has in its place. Nothing is unfolded here, so
      -- the comparison is cheap and matches only a statement of the same shape.
      for candidate in candidates do
        let overCandidate ← mkLambdaFVars #[candidate] argumentType
        for claimTheorem in claimTheorems do
          let same ← sameStatement (← statementOfTheorem claimTheorem)
            (do return overCandidate.beta #[← mkFreshExprMVar (← inferType candidate)]) gaveUp
            s!"comparing a hypothesis with {claimTheorem}" (transparency := .reducible)
          if same && !found.contains claimTheorem then
            found := found.push claimTheorem
      if found.size > foundBefore then
        for candidate in candidates do
          unless candidatesMeetingClaims.contains candidate do
            candidatesMeetingClaims := candidatesMeetingClaims.push candidate
    -- The conclusion has to relate a candidate to something. `candidate = candidate` is
    -- true of every candidate and mentions nothing else.
    let environment ← getEnv
    let fromOutsideLean := conclusion.getUsedConstants.any fun name =>
      match environment.getModuleIdxFor? name with
      | some moduleIndex => ![`Init, `Std, `Lean].contains environment.header.moduleNames[moduleIndex.toNat]!.getRoot
      | none => true
    if fromOutsideLean || candidatesMeetingClaims.size ≥ 2 then
      return found
    return #[]
  facts := { facts with determines := determined }
  let mut satisfiable := #[]
  for part in conjunctsOf statement do
    -- Only a statement of the form `∃ …` can be a "can hold" statement.
    unless part.isAppOf ``Exists do continue
    for claimTheorem in claimTheoremsWithHypotheses do
      let same ← sameStatement part (do hypothesesCanHoldStatement (← statementOfTheorem claimTheorem)) gaveUp
        s!"comparing with the hypotheses of {claimTheorem}"
      if same then
        satisfiable := satisfiable.push claimTheorem
  return { facts with canHold := satisfiable }

private def namesToJson (names : Array Name) : Json :=
  Json.arr (names.map fun name => Json.str name.toString)

/-- `#audit_facts claims [T₁, T₂, …] modules [M₁, M₂, …]` prints one line,
    `audit-facts {…}`, holding for the claim theorems `Tᵢ` the number of hypotheses of
    each, and for the audit modules `Mᵢ` every theorem they declare with its line, its
    doc comment and what Lean finds its statement to be, and every
    property with the claim theorems it is tied to. The modules must be imported. -/
elab "#audit_facts " "claims " "[" claimSyntax:ident,* "]" " modules " "[" moduleSyntax:ident,* "]" : command => do
  let environment ← getEnv
  let mut claimTheorems : Array Name := #[]
  for theoremSyntax in claimSyntax.getElems do
    match environment.find? theoremSyntax.getId with
    | some (.thmInfo _) => claimTheorems := claimTheorems.push theoremSyntax.getId
    | _ => throwErrorAt theoremSyntax m!"{theoremSyntax.getId} is not a theorem in this environment"
  let moduleIndexes ← moduleIndexesOf moduleSyntax.getElems
  let inAuditModule (name : Name) : Bool :=
    match environment.getModuleIdxFor? name with
    | some moduleIndex => moduleIndexes.contains moduleIndex
    | none => false
  let mut auditTheorems : Array (Name × Expr × Array Name) := #[]
  let mut propertyNames : NameSet := {}
  for (name, info) in environment.constants.map₁.toList do
    unless inAuditModule name do continue
    match info with
    | .thmInfo theoremInfo =>
      unless isWrittenTheorem environment name info do continue
      let usedInProof := theoremInfo.value.getUsedConstantsAsSet
      auditTheorems := auditTheorems.push (name, theoremInfo.type, claimTheorems.filter usedInProof.contains)
    | .defnInfo _ =>
      unless (writtenName name).isInternalDetail || isReservedName environment name do
        propertyNames := propertyNames.insert name
    | _ => pure ()
  let gaveUp ← IO.mkRef (#[] : Array String)
  let (ties, hypothesisCounts, theoremFacts) ← liftTermElabM do
    let mut ties : Array PropertyTie := #[]
    -- A claim that states a type class of the implementation: the class is the property.
    for claimTheorem in claimTheorems do
      if let .const headConstant _ := (← statementOfTheorem claimTheorem).consumeMData.getAppFn then
        if isClass environment headConstant then
          ties := ties.push { property := headConstant, claimTheorems := #[claimTheorem], tiedBy := claimTheorem }
    for (name, statement, claimTheoremsUsed) in auditTheorems do
      ties := ties ++ (← tiesFrom name statement propertyNames.contains claimTheoremsUsed gaveUp)
    let tiesOf (property : Name) : Array Name :=
      ties.foldl (init := #[]) fun found tie =>
        if tie.property == property then
          tie.claimTheorems.foldl (init := found) fun soFar claimTheorem =>
            if soFar.contains claimTheorem then soFar else soFar.push claimTheorem
        else found
    let mut hypothesisCounts : Array (Name × Nat) := #[]
    for claimTheorem in claimTheorems do
      hypothesisCounts := hypothesisCounts.push (claimTheorem, ← hypothesisCount (← statementOfTheorem claimTheorem))
    let withHypotheses := (hypothesisCounts.filter fun (_, count) => count > 0).map (·.1)
    let mut theoremFacts : Array (Name × AuditTheoremFacts) := #[]
    for (name, statement, _) in auditTheorems do
      theoremFacts := theoremFacts.push (name, ← factsOf statement tiesOf claimTheorems withHypotheses gaveUp)
    return (ties, hypothesisCounts, theoremFacts)
  let mut theoremsJson : Array Json := #[]
  for (name, facts) in theoremFacts do
    let moduleName := moduleNameOf environment name
    let line ← lineOf name
    let docLine := match ← findDocString? environment name with
      | some docComment => Json.str docComment
      | none => Json.null
    theoremsJson := theoremsJson.push <| Json.mkObj [
      ("name", Json.str (writtenName name).toString), ("module", Json.str moduleName.toString), ("line", toJson line),
      ("doc", docLine), ("fails", namesToJson facts.fails),
      ("negated_property", match facts.negatedProperty with
        | some property => Json.str property.toString
        | none => Json.null),
      ("determines", namesToJson facts.determines), ("can_hold", namesToJson facts.canHold)]
  let claimsJson := hypothesisCounts.map fun (name, count) =>
    Json.mkObj [("name", Json.str name.toString), ("hypotheses", toJson count)]
  let tiesJson := ties.map fun tie =>
    Json.mkObj [("property", Json.str tie.property.toString), ("claim_theorems", namesToJson tie.claimTheorems),
      ("tied_by", Json.str tie.tiedBy.toString)]
  let document := Json.mkObj [
    ("claims", Json.arr claimsJson), ("ties", Json.arr tiesJson), ("theorems", Json.arr theoremsJson),
    ("gave_up", Json.arr ((← gaveUp.get).map Json.str))]
  logInfo m!"audit-facts {document.compress}"

end LeanClaims
