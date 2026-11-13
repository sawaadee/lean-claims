<!--
File: TRUST.md
Purpose: What MiniJson guarantees and on what each guarantee rests: which declarations are
proved, which are tested, which are trusted, and what was waived. Written by `claims trust`
from the spec, `claims.toml`, the catalogs and what Lean reports. Not edited by hand:
`claims trust --check` fails when this file differs from what would be written.
Created: 2026-11-14
-->

# What MiniJson guarantees

7 claims, stated in `Spec.lean` as 9 theorems. 23 public declarations: 10 mentioned by a claim, 2 tested, 2 trusted, 11 supporting, 0 a theorem of the code, 0 at no level.

A declaration can stand at more than one level. "Mentioned by a claim" means a claim's statement
uses it. It does not mean the claims say everything about it: the audits and the mutation run are
the checks on that, and the waivers below are where they were not met. "Supporting" means no
claim mentions it and a declaration that a claim does mention is defined by it: the claims bind it
as far as that declaration uses it, and say nothing of it otherwise.

## Claims

| Claim | States | Theorems | Mentions |
|-------|--------|----------|----------|
| 1 | A text parses to a value exactly when the text's tokens are the value's tokens. | `parseChars_iff` | `MiniJson.Json`, `MiniJson.Token`, `MiniJson.parseChars`, `MiniJson.tokenize`, `MiniJson.tokensOf` |
| 2 | The text the renderer writes for a value has exactly that value's tokens. | `tokenize_renderChars` | `MiniJson.Json`, `MiniJson.Token`, `MiniJson.renderChars`, `MiniJson.tokenize`, `MiniJson.tokensOf` |
| 3 | Parsing the text rendered for a value gives the value back. | `parseChars_renderChars`, `parse_render` | `MiniJson.Json`, `MiniJson.parse`, `MiniJson.parseChars`, `MiniJson.render`, `MiniJson.renderChars` |
| 4 | Two values with the same rendered text are the same value. | `renderChars_injective` | `MiniJson.Json`, `MiniJson.renderChars` |
| 5 | The functions on strings are the functions on lists of characters. | `parse_eq_parseChars`, `render_toList` | `MiniJson.Json`, `MiniJson.parse`, `MiniJson.parseChars`, `MiniJson.render`, `MiniJson.renderChars` |
| 6 | A text that parses to a value is that value's rendered text with white space added. | `parseChars_text` | `MiniJson.Json`, `MiniJson.isSpace`, `MiniJson.parseChars`, `MiniJson.renderChars` |
| 7 | A text parses to a value exactly when it is the value's tokens written out. | `parseChars_iff_writes` | `MiniJson.Json`, `MiniJson.parseChars`, `MiniJson.tokensOf`, `MiniJson.writes` |

## What a reviewer reads

The claims are written in 21 public declarations, directly or through the
definitions of the ones they use. Knowing what the claims mean requires reading each one.

`MiniJson.Json`, `MiniJson.Token`, `MiniJson.digitChar`, `MiniJson.digitsOf`, `MiniJson.dropSpaces`, `MiniJson.isSpace`, `MiniJson.natOfDigits`, `MiniJson.parse`, `MiniJson.parseAfterFirst`, `MiniJson.parseChars`, `MiniJson.parseTokens`, `MiniJson.parseValue`, `MiniJson.render`, `MiniJson.renderAfterFirst`, `MiniJson.renderChars`, `MiniJson.tokenText`, `MiniJson.tokenize`, `MiniJson.tokenizeWith`, `MiniJson.tokensAfterFirst`, `MiniJson.tokensOf`, `MiniJson.writes`

## Public declarations

| Declaration | Kind | Where | Proved by claims | Tested by | Trusted | Supporting |
|-------------|------|-------|------------------|-----------|---------|------------|
| `MiniJson.parseValue` | definition | MiniJson/Parse.lean:17 |  |  |  | yes |
| `MiniJson.parseAfterFirst` | definition | MiniJson/Parse.lean:35 |  |  |  | yes |
| `MiniJson.parseTokens` | definition | MiniJson/Parse.lean:50 |  |  |  | yes |
| `MiniJson.parseChars` | definition | MiniJson/Parse.lean:56 | 1, 3, 5, 6, 7 |  |  |  |
| `MiniJson.parse` | definition | MiniJson/Parse.lean:60 | 3, 5 | differential |  |  |
| `MiniJson.digitChar` | definition | MiniJson/Render.lean:14 |  |  |  | yes |
| `MiniJson.digitsOf` | definition | MiniJson/Render.lean:18 |  |  |  | yes |
| `MiniJson.renderChars` | definition | MiniJson/Render.lean:28 | 2, 3, 4, 5, 6 |  |  |  |
| `MiniJson.renderAfterFirst` | definition | MiniJson/Render.lean:37 |  |  |  | yes |
| `MiniJson.render` | definition | MiniJson/Render.lean:44 | 3, 5 | differential |  |  |
| `MiniJson.isSpace` | definition | MiniJson/Tokenize.lean:20 | 6 |  |  |  |
| `MiniJson.natOfDigits` | definition | MiniJson/Tokenize.lean:24 |  |  |  | yes |
| `MiniJson.tokenizeWith` | definition | MiniJson/Tokenize.lean:29 |  |  |  | yes |
| `MiniJson.tokenize` | definition | MiniJson/Tokenize.lean:51 | 1, 2 |  |  |  |
| `MiniJson.Json` | type | MiniJson/Value.lean:16 | 1, 2, 3, 4, 5, 6, 7 |  |  |  |
| `MiniJson.Token` | type | MiniJson/Value.lean:24 | 1, 2 |  |  |  |
| `MiniJson.instDecidableEqToken` | instance | MiniJson/Value.lean:32 |  |  | yes |  |
| `MiniJson.instReprToken` | instance | MiniJson/Value.lean:32 |  |  | yes |  |
| `MiniJson.tokensOf` | definition | MiniJson/Value.lean:38 | 1, 2, 7 |  |  |  |
| `MiniJson.tokensAfterFirst` | definition | MiniJson/Value.lean:48 |  |  |  | yes |
| `MiniJson.tokenText` | definition | MiniJson/Written.lean:21 |  |  |  | yes |
| `MiniJson.dropSpaces` | definition | MiniJson/Written.lean:31 |  |  |  | yes |
| `MiniJson.writes` | definition | MiniJson/Written.lean:38 | 7 |  |  |  |

## Tested, not proved

| What | Check | Fault it has been seen to catch | Declarations |
|------|-------|---------------------------------|--------------|
| The compiled parser and renderer do what their definitions say. The proofs are about the definitions; the compiler that turns them into the code that runs is not verified. | `differential` | `compiled-tokenizer-accepts-a-leading-zero` | `MiniJson.parse`, `MiniJson.render` |

## Trusted

| What | Why | Declarations |
|------|-----|--------------|
| Python's `json` module, the answer key of the differential test. | It shares no code with this library. A fault in both that agrees on every text of the test would go unseen. |  |
| The equality test and the display form Lean derives for tokens. | Written by Lean's deriving handlers. The equality test carries its own proof in its type. The display form is used by no function of the library. | `MiniJson.instDecidableEqToken`, `MiniJson.instReprToken` |

Every project built this way also trusts: Lean's kernel and the kernels `lake comparator` runs,
which check the proofs; the Lean compiler and runtime, which turn definitions into the code that
runs; the axioms `propext`, `Classical.choice`, `Quot.sound`; and the lean-claims
tools, which are tested and not proved.

## Waivers

| Claim | Requirement lifted | Reason |
|-------|--------------------|--------|
| 2 | determines | Many renderers meet it: white space between tokens is free. The claim is meant to leave that open. |
| 3 | determines | A consequence of claims 1 and 2. It is stated because it is the property callers rely on. |
| 4 | determines | A consequence of claim 3. It is stated because callers compare and index values by their text. |
| 6 | determines | A consequence of claim 7, which determines the parser. It is stated because it is the plain form: take the white space out and the rendered text is left. |

## What the catalogs plant

`claims mutate` plants 12 changes to the code from `mutations.toml`. 11 name a claim: each must break a proof and have that claim proved false, unless the build
refuses the change. 1 keep the code's behaviour and name none.

`claims checks` plants 4 faults from `faults.toml`, and the faults it
generates for every project. The check each is planted for must catch it.

This file records what would be planted, not the result of a run. Run the two commands for that.
