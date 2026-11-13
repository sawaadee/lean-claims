"""
File: selftest/mutation_engine.py
Purpose: Tests the mutation run itself, on the starter project. The run's whole value is
that it fails when a bug is not caught, so each test here hands it a catalog that must
make it fail, and requires the failure and its reason.

  1. The starter project's own catalog passes.
  2. A bug whose refutation does not prove the claim false must be reported NOT REFUTED.
  3. A change no proof notices, entered as a bug, must be reported SURVIVED.
  4. A refutation that compiles on the unchanged code must stop the run at its controls,
     before any bug is planted.
  5. A catalog naming a claim the spec does not state must be refused.
  6. An edit whose text is not in the file must stop the run and leave nothing planted.

After every test the starter project's code must be byte for byte what it was.

Usage: python3 -I selftest/mutation_engine.py
Exit status: 0 when every test passes, 1 otherwise.
Created: 2026-11-13
"""

import hashlib
import sys
import tempfile
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parent.parent
TOOLS_DIRECTORY = REPOSITORY / "tools"
TEMPLATE = REPOSITORY / "template"
# `python3 -I` leaves this script's directory off the import path, so the tools are added here.
sys.path.insert(0, str(TOOLS_DIRECTORY))

from leanclaims.process import run_command  # noqa: E402

EDIT = '''
  [[mutation.edit]]
  file = "Example/Clamp.lean"
  find = "max low (min high value)"
  replace = "{replace}"
'''

# The bounds exchanged is a real bug, but it does not make claim 2 false at this input.
WRONG_REFUTATION = '''[[mutation]]
layer = "main"
description = "a real bug with a refutation that proves nothing"
refuted_claim = "clamp_le_high"
refutation = "absurd (clamp_le_high 5 10 7 (by decide)) (by decide)"
''' + EDIT.format(replace="max high (min low value)")

# Writing min's arguments the other way round changes nothing, so no proof can notice it.
UNNOTICED_CHANGE = '''[[mutation]]
layer = "main"
description = "a change no proof notices, entered as a bug"
refuted_claim = "clamp_eq_self"
refutation = "absurd (clamp_eq_self 5 10 7 (by decide) (by decide)) (by decide)"
''' + EDIT.format(replace="max low (min value high)")

# `by sorry` proves anything, so this refutation compiles whether or not a bug is planted.
REFUTATION_TRUE_OF_CORRECT_CODE = '''[[mutation]]
layer = "main"
description = "a refutation that needs no bug"
refuted_claim = "clamp_eq_self"
refutation = "by sorry"
''' + EDIT.format(replace="max high (min low value)")

UNKNOWN_CLAIM = '''[[mutation]]
layer = "main"
description = "a claim the spec does not state"
refuted_claim = "clamp_is_fast"
refutation = "absurd (clamp_eq_self 5 10 7 (by decide) (by decide)) (by decide)"
''' + EDIT.format(replace="max high (min low value)")

TEXT_NOT_IN_FILE = '''[[mutation]]
layer = "main"
description = "an edit whose text is not in the file"
refuted_claim = "clamp_eq_self"
refutation = "absurd (clamp_eq_self 5 10 7 (by decide) (by decide)) (by decide)"

  [[mutation.edit]]
  file = "Example/Clamp.lean"
  find = "text that is not there"
  replace = "anything"
'''

# (what is tested, catalog text or None for the project's own, exit status required, text the output must hold)
CASES = [
    ("the starter project's own catalog passes", None, 0,
     ("6 of 6 behaviour-changing bugs broke at least one proof", "6 of 6 had their claim's statement proved false")),
    ("a refutation that does not prove the claim false is reported", WRONG_REFUTATION, 1,
     ("clamp_le_high: NOT REFUTED", "0 of 1 had their claim's statement proved false")),
    ("a change no proof notices is reported as surviving", UNNOTICED_CHANGE, 1,
     ("SURVIVED", "0 of 1 behaviour-changing bugs broke at least one proof")),
    ("a refutation that compiles on unchanged code stops the run at its controls", REFUTATION_TRUE_OF_CORRECT_CODE, 1,
     ("The controls on unchanged code failed", "compiles on unchanged code")),
    ("a claim the spec does not state is refused", UNKNOWN_CLAIM, 2,
     ("the spec states no theorem Example.Proofs.clamp_is_fast",)),
    ("an edit whose text is not in the file stops the run", TEXT_NOT_IN_FILE, 2,
     ("the text to find occurs 0 times in Example/Clamp.lean",)),
]


def code_hash() -> str:
    return hashlib.sha256((TEMPLATE / "Example" / "Clamp.lean").read_bytes()).hexdigest()


def main() -> int:
    hash_before = code_hash()
    failures = []
    with tempfile.TemporaryDirectory() as temporary:
        for index, (what, catalog_text, required_status, required_texts) in enumerate(CASES, start=1):
            command = [sys.executable, "-I", str(TOOLS_DIRECTORY / "claims.py"), "--project", str(TEMPLATE), "mutate"]
            if catalog_text is not None:
                catalog_path = Path(temporary) / f"catalog{index}.toml"
                catalog_path.write_text(catalog_text, encoding="utf-8")
                command += ["--catalog", str(catalog_path)]
            status, output = run_command(command, TEMPLATE)
            missing = [text for text in required_texts if text not in output]
            restored = code_hash() == hash_before and not (TEMPLATE / ".lake" / "planted-faults.json").exists()
            passed = status == required_status and not missing and restored
            print(f"{'passed' if passed else 'FAILED'}  {what}")
            if not passed:
                failures.append(f"{what}: exit status {status} (required {required_status}), missing from the "
                                f"output {missing}, code restored {restored}\n{output[-1200:]}")
    print(f"{len(CASES) - len(failures)} of {len(CASES)} tests of the mutation run passed")
    for failure in failures:
        print(f"FAILED: {failure}")
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
