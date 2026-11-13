/-
  File: mutations/prelude.lean
  Purpose: The setting every refutation in `mutations.toml` is read in. The mutation run
  puts this file's text in front of each refutation and compiles the result, so this is
  where the imports, the open namespaces and any values the refutations share belong.

  It imports the spec, whose theorems are admitted with `sorry`. A refutation applies one
  of them to a concrete input and derives `False`, which shows the statement is false of
  the code as mutated.
  Created: 2026-11-13
-/

import Example
import Spec

open Example Example.Proofs
