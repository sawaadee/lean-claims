/-
  File: tests/JsonAudit.lean
  Purpose: The audit of the claims in `Spec.lean`. The proofs show the claims are true of
  the parser and the renderer. The theorems here show the claims are worth having: for
  each claim a wrong implementation that fails it, that the hypotheses of the two claims
  that have one can hold, and that claim 1 and claim 7 each leave the parser no freedom.

  Each claim is written as a property of an arbitrary candidate, so that it can be asked
  of wrong implementations, and a theorem ties each property to its claim by proving it
  of the real implementation with the claim's theorem.

  The renderer is not determined, and is not meant to be: white space between tokens is
  free, so many renderers meet claim 2. `claims.toml` carries the waivers.
  Created: 2026-11-14
-/

import LeanClaims
import MiniJson.Proofs

namespace JsonAudit

open MiniJson

/-- A parser on lists of characters. -/
abbrev CharParser := List Char → Option Json

/-- A renderer to lists of characters. -/
abbrev CharRenderer := Json → List Char

/-! ## The claims as properties of any candidate -/

/-- Claim 1 asked of a candidate parser. -/
def ParsesByTokens (candidate : CharParser) : Prop :=
  ∀ text value, candidate text = some value ↔ tokenize text = some (tokensOf value)

/-- Claim 2 asked of a candidate renderer. -/
def WritesTheTokens (candidate : CharRenderer) : Prop :=
  ∀ value, tokenize (candidate value) = some (tokensOf value)

/-- Claim 3 asked of a candidate parser: it reads back what `renderChars` writes. -/
def ReadsBack (candidate : CharParser) : Prop :=
  ∀ value, candidate (renderChars value) = some value

/-- Claim 4 asked of a candidate renderer. -/
def OneTextOneValue (candidate : CharRenderer) : Prop :=
  ∀ first second, candidate first = candidate second → first = second

/-- Claim 5 asked of a candidate parser on strings. -/
def ParsesItsCharacters (candidate : String → Option Json) : Prop :=
  ∀ text, candidate text = parseChars text.toList

/-- Claim 5 asked of a candidate renderer to strings. -/
def RendersTheCharacters (candidate : Json → String) : Prop :=
  ∀ value, (candidate value).toList = renderChars value

/-- Claim 6 asked of a candidate parser. -/
def AcceptsOnlyRenderedText (candidate : CharParser) : Prop :=
  ∀ text value, candidate text = some value → text.filter (fun character => !isSpace character) = renderChars value

/-- Claim 7 asked of a candidate parser. -/
def ParsesWhatIsWritten (candidate : CharParser) : Prop :=
  ∀ text value, candidate text = some value ↔ writes (tokensOf value) text = true

/-! ## Each property, asked of the real implementation, is its claim -/

theorem parseChars_parsesWhatIsWritten : ParsesWhatIsWritten parseChars := Proofs.parseChars_iff_writes

theorem parseChars_acceptsOnlyRenderedText : AcceptsOnlyRenderedText parseChars := Proofs.parseChars_text

theorem parseChars_parsesByTokens : ParsesByTokens parseChars := Proofs.parseChars_iff

theorem renderChars_writesTheTokens : WritesTheTokens renderChars := Proofs.tokenize_renderChars

theorem parseChars_readsBack : ReadsBack parseChars := Proofs.parseChars_renderChars

theorem renderChars_oneTextOneValue : OneTextOneValue renderChars := Proofs.renderChars_injective

theorem parse_parsesItsCharacters : ParsesItsCharacters parse := Proofs.parse_eq_parseChars

theorem render_rendersTheCharacters : RendersTheCharacters render := Proofs.render_toList

/-! ## A wrong implementation for each claim -/

/-- A parser that reads one value and does not look at what follows it. -/
def ignoresWhatFollows : CharParser := fun text =>
  (tokenize text).bind fun tokens => (parseValue (tokens.length + 1) tokens).map (·.1)

/-- Audit: fails claim 1. A parser that ignores what follows the first value accepts the
    text `null null`, whose tokens are not those of any value. -/
theorem ignoresWhatFollows_fails_claim1 : ¬ ParsesByTokens ignoresWhatFollows := fun meets =>
  absurd ((meets ['n', 'u', 'l', 'l', ' ', 'n', 'u', 'l', 'l'] Json.null).mp rfl) (by decide)

/-- Audit: fails claim 1. A parser that refuses every text refuses `null`. -/
theorem refusesEverything_fails_claim1 : ¬ ParsesByTokens (fun _ => none) := fun meets =>
  nomatch (meets ['n', 'u', 'l', 'l'] Json.null).mpr (by decide)

/-- A renderer that writes `true` as the number 1. -/
def writesTrueAsOne : CharRenderer
  | .bool true => ['1']
  | other => renderChars other

/-- Audit: fails claim 2. A renderer that writes `true` as `1` writes a number token where
    the value has the word `true`. -/
theorem writesTrueAsOne_fails_claim2 : ¬ WritesTheTokens writesTrueAsOne := fun meets =>
  absurd (meets (Json.bool true)) (by decide)

/-- A parser that keeps only the first item of an array. -/
def keepsFirstItemOnly : CharParser := fun text =>
  (parseChars text).map fun
    | .array (first :: _) => .array [first]
    | other => other

/-- Audit: fails claim 3. A parser that keeps only the first item of an array reads the
    text of `[null,null]` back as `[null]`. -/
theorem keepsFirstItemOnly_fails_claim3 : ¬ ReadsBack keepsFirstItemOnly := fun meets => by
  have readBack : some (Json.array [Json.null]) = some (Json.array [Json.null, Json.null]) :=
    meets (Json.array [Json.null, Json.null])
  cases readBack

/-- A renderer that writes both booleans as `true`. -/
def writesBothAsTrue : CharRenderer
  | .bool _ => ['t', 'r', 'u', 'e']
  | other => renderChars other

/-- Audit: fails claim 4. A renderer that writes both booleans as `true` gives two values
    one text. -/
theorem writesBothAsTrue_fails_claim4 : ¬ OneTextOneValue writesBothAsTrue := fun meets => by
  have same : Json.bool true = Json.bool false := meets (Json.bool true) (Json.bool false) rfl
  cases same

/-- Audit: fails claim 5. A parser on strings that refuses every string refuses the string
    `null`, which `parseChars` reads. -/
theorem refusesEveryString_fails_claim5 : ¬ ParsesItsCharacters (fun _ => none) := fun meets => by
  have refused := meets (String.ofList ['n', 'u', 'l', 'l'])
  rw [String.toList_ofList] at refused
  have impossible : none = some Json.null := refused
  cases impossible

/-- Audit: fails claim 5. A renderer to strings that writes nothing writes no characters
    for `null`, where `renderChars` writes four. -/
theorem writesNothing_fails_claim5 : ¬ RendersTheCharacters (fun _ => String.ofList []) := fun meets => by
  have written := meets Json.null
  rw [String.toList_ofList] at written
  cases written

/-- A parser that reads `01` as the number 1 and nothing else. -/
def readsLeadingZero : CharParser := fun text =>
  if text = ['0', '1'] then some (Json.number 1) else none

/-- Audit: fails claim 6. A parser that reads `01` as the number 1 accepts a text that is
    not the rendered text of 1, which is `1`. -/
theorem readsLeadingZero_fails_claim6 : ¬ AcceptsOnlyRenderedText readsLeadingZero := fun meets => by
  have stripped := meets ['0', '1'] (Json.number 1) rfl
  simp [renderChars, digitsOf, digitChar, isSpace] at stripped

/-- A parser that also reads `true` with a tab inside it. -/
def readsTabInsideTrue : CharParser := fun text =>
  if text = ['t', 'r', '\t', 'u', 'e'] then some (Json.bool true) else parseChars text

/-- Audit: fails claim 7. A parser that reads `true` with a tab inside it accepts a text
    that is not the word `true` written out. Claim 6 cannot tell: with its white space
    taken out, that text is `true`. -/
theorem readsTabInsideTrue_fails_claim7 : ¬ ParsesWhatIsWritten readsTabInsideTrue := fun meets =>
  absurd ((meets ['t', 'r', '\t', 'u', 'e'] (Json.bool true)).mp rfl) (by decide)

/-- A parser that refuses any text with a tab in it. -/
def refusesTabs : CharParser := fun text =>
  if text.contains '\t' then none else parseChars text

/-- Audit: fails claim 7. A parser that refuses tabs refuses `null` with a tab in front of
    it, which is `null` written out. No other claim says the parser must accept it. -/
theorem refusesTabs_fails_claim7 : ¬ ParsesWhatIsWritten refusesTabs := fun meets =>
  nomatch (meets ['\t', 'n', 'u', 'l', 'l'] Json.null).mpr (by decide)

/-! ## The hypotheses of claims 4 and 6 can hold -/

/-- Audit: hypotheses of claim 4 can hold. A value has the same text as itself. -/
theorem claim4_hypotheses_can_hold : hypotheses_can_hold% Proofs.renderChars_injective :=
  ⟨Json.null, Json.null, rfl, trivial⟩

/-- Audit: hypotheses of claim 6 can hold. The text `null` parses to the value `null`. -/
theorem claim6_hypotheses_can_hold : hypotheses_can_hold% Proofs.parseChars_text :=
  ⟨['n', 'u', 'l', 'l'], Json.null, rfl, trivial⟩

/-! ## The claims about the parser determine it -/

/-- Audit: determines claim 1. Any parser that meets claim 1 is `parseChars`: for every
    text the claim says which value is returned, and that none is when no value has the
    text's tokens. -/
theorem claim1_determines_parseChars (candidate : CharParser) (meets : ParsesByTokens candidate) :
    candidate = parseChars :=
  funext fun text => Option.ext fun value =>
    (meets text value).trans (Proofs.parseChars_iff text value).symm

/-- Audit: determines claim 7. Any parser that meets claim 7 is `parseChars`, and this time
    nothing in the claim is the tokenizer's. -/
theorem claim7_determines_parseChars (candidate : CharParser) (meets : ParsesWhatIsWritten candidate) :
    candidate = parseChars :=
  funext fun text => Option.ext fun value =>
    (meets text value).trans (Proofs.parseChars_iff_writes text value).symm

/-- Audit: determines claim 5. Any parser on strings that meets claim 5 is `parse`. -/
theorem claim5_determines_parse (candidate : String → Option Json) (meets : ParsesItsCharacters candidate) :
    candidate = parse :=
  funext fun text => (meets text).trans (Proofs.parse_eq_parseChars text).symm

/-- Audit: determines claim 5. Any renderer to strings that meets claim 5 is `render`: a
    string is fixed by its characters. -/
theorem claim5_determines_render (candidate : Json → String) (meets : RendersTheCharacters candidate) :
    candidate = render :=
  funext fun value => String.toList_inj.mp ((meets value).trans (Proofs.render_toList value).symm)

end JsonAudit
