/-
  File: selftest/LeanClaimsTest.lean
  Purpose: The root of the library the self-test uses to test the Lean commands. For
  `#audit_facts`: a few claims about a small function, and audit theorems of every shape
  the command must recognise or refuse. For `#surface_facts`: code with one declaration of
  every sort the command must tell apart, and claims that mention some of it.
  `selftest/audit_facts.py` and `selftest/surface_facts.py` build it and compare what
  the commands report with what each declaration was written to be. It is not a default
  target and no project that requires LeanClaims builds it.
  Created: 2026-11-13
-/

import LeanClaimsTest.Claims
import LeanClaimsTest.Audits
import LeanClaimsTest.Surface.Code
import LeanClaimsTest.Surface.Proofs
