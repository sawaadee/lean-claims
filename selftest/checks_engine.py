"""
File: selftest/checks_engine.py
Purpose: Tests `claims checks` itself, on the starter project. Its whole value is that it
reports a fault no check caught, so each test here hands it a catalog that must make it
fail, and requires the failure and its reason.

  1. The starter project's own catalog passes.
  2. A fault its check does not notice must be reported MISSED.
  3. A fault its check fails on for another reason must be reported MISSED.
  4. A check that fails before anything is planted must stop the run.
  5. A fault for a check that does not exist must be refused.
  6. An edit whose text is not in the file must be refused.
  7. A fault that does not say what its check's output must hold must be refused.

After every test the starter project's files must be byte for byte what they were.

Usage: python3 -I selftest/checks_engine.py
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

# A change to a doc comment. Nothing checks the wording of a comment, so the build passes.
UNNOTICED_FAULT = '''[[fault]]
id = "comment-reworded"
description = "a doc comment reworded, which no check looks at"
check = "build"
caught_when_output_has = ["error"]

  [[fault.edit]]
  file = "Example/Clamp.lean"
  find = "brings a number into a"
  replace = "puts a number into a"
'''

# The build does fail, but not with the text the fault says it must show.
FAILS_FOR_ANOTHER_REASON = '''[[fault]]
id = "wrong-reason"
description = "a definition broken, with the wrong failure expected"
check = "build"
caught_when_output_has = ["a message this build does not print"]

  [[fault.edit]]
  file = "Example/Clamp.lean"
  find = "max low (min high value)"
  replace = "max low (min high"
'''

CHECK_ALREADY_FAILING = '''[[check]]
id = "always-fails"
command = ["false"]

[[fault]]
id = "anything"
description = "a fault for a check that fails with nothing planted"
check = "always-fails"
caught_when_output_has = ["anything"]

  [[fault.edit]]
  file = "Example/Clamp.lean"
  find = "max low (min high value)"
  replace = "max low (min high"
'''

UNKNOWN_CHECK = FAILS_FOR_ANOTHER_REASON.replace('check = "build"', 'check = "no-such-check"')
TEXT_NOT_IN_FILE = FAILS_FOR_ANOTHER_REASON.replace('find = "max low (min high value)"', 'find = "text that is not there"')
NOTHING_EXPECTED = FAILS_FOR_ANOTHER_REASON.replace('caught_when_output_has = ["a message this build does not print"]\n', "")

# (what is tested, catalog text or None for the project's own, exit status required, text the output must hold)
CASES = [
    ("the starter project's own catalog passes", None, 0,
     ("27 of 27 planted faults were caught", "byte for byte what it was before the run: True")),
    ("a fault its check does not notice is reported", UNNOTICED_FAULT, 1,
     ("MISSED  [build] a doc comment reworded", "the check passed with the fault planted")),
    ("a fault caught for another reason is reported", FAILS_FOR_ANOTHER_REASON, 1,
     ("MISSED  [build] a definition broken", "the check failed without mentioning")),
    ("a check that fails with nothing planted stops the run", CHECK_ALREADY_FAILING, 1,
     ("the 'always-fails' check fails before anything is planted",)),
    ("a fault for a check that does not exist is refused", UNKNOWN_CHECK, 2, ("no check is named 'no-such-check'",)),
    ("an edit whose text is not in the file is refused", TEXT_NOT_IN_FILE, 2,
     ("the text to find occurs 0 times in Example/Clamp.lean",)),
    ("a fault that expects nothing of the output is refused", NOTHING_EXPECTED, 2,
     ("say what the check's output must hold",)),
]

WATCHED_FILES = ["Example/Clamp.lean", "Example/Proofs/Clamp.lean", "Example/Verify.lean", "Spec.lean", "spec.lock",
                 "tests/ClampAudit.lean", "tests/RunClamp.lean", "faults.toml", "claims.toml", "TRUST.md", "Example.lean"]


def watched_hash() -> str:
    digest = hashlib.sha256()
    for relative_path in WATCHED_FILES:
        digest.update((TEMPLATE / relative_path).read_bytes())
    return digest.hexdigest()


def main() -> int:
    hash_before = watched_hash()
    failures = []
    with tempfile.TemporaryDirectory() as temporary:
        for index, (what, catalog_text, required_status, required_texts) in enumerate(CASES, start=1):
            command = [sys.executable, "-I", str(TOOLS_DIRECTORY / "claims.py"), "--project", str(TEMPLATE), "checks"]
            if catalog_text is not None:
                catalog_path = Path(temporary) / f"faults{index}.toml"
                catalog_path.write_text(catalog_text, encoding="utf-8")
                command += ["--catalog", str(catalog_path)]
            status, output = run_command(command, TEMPLATE)
            missing = [text for text in required_texts if text not in output]
            restored = watched_hash() == hash_before and not (TEMPLATE / ".lake" / "planted-faults.json").exists()
            passed = status == required_status and not missing and restored
            print(f"{'passed' if passed else 'FAILED'}  {what}", flush=True)
            if not passed:
                failures.append(f"{what}: exit status {status} (required {required_status}), missing from the "
                                f"output {missing}, files restored {restored}\n{output[-1200:]}")
    print(f"{len(CASES) - len(failures)} of {len(CASES)} tests of the test of the checks passed")
    for failure in failures:
        print(f"FAILED: {failure}")
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
