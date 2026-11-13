"""
File: selftest/second_claim.py
Purpose: Tests that a project started from the starter can grow. It creates a project,
then adds a second function with a seventh claim about it by the steps of the project's
`AGENTS.md`: state the claim and update the lock, write the code and the proof, audit
the claim in a second audit module, plant a bug, write the trust report. Each step ends
with the check `AGENTS.md` names for it, and at the end every check, the mutation run
and the test of the checks must pass.

It also takes two wrong turns on the way and requires the check that should stop each
one to stop it: the claim added without updating the lock, and the new function left
without a claim.

Usage: python3 -I selftest/second_claim.py
Exit status: 0 when every step passes, 1 otherwise.
Created: 2026-11-13
"""

import shutil
import sys
import tempfile
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parent.parent
FIXTURES = REPOSITORY / "selftest" / "second_claim"
# `python3 -I` leaves this script's directory off the import path, so the tools are added here.
sys.path.insert(0, str(REPOSITORY / "tools"))

from leanclaims.process import run_command  # noqa: E402

NAME = "RangeTools"


def append(path: Path, text: str) -> None:
    path.write_text(path.read_text(encoding="utf-8") + text, encoding="utf-8")


def replace_once(path: Path, find: str, replace: str) -> None:
    text = path.read_text(encoding="utf-8")
    if text.count(find) != 1:
        raise SystemExit(f"{path}: expected the text {find!r} once, found it {text.count(find)} times")
    path.write_text(text.replace(find, replace), encoding="utf-8")


def main() -> int:
    failures = []
    with tempfile.TemporaryDirectory() as temporary:
        project = Path(temporary) / "range-tools"

        def claims(*arguments: str) -> tuple[int, str]:
            return run_command([sys.executable, "-I", str(REPOSITORY / "tools" / "claims.py"),
                                "--project", str(project), *arguments], REPOSITORY)

        def record(what: str, passed: bool, detail: str) -> None:
            print(f"{'passed' if passed else 'FAILED'}  {what}", flush=True)
            if not passed:
                failures.append(f"{what}:\n{detail[-2500:]}")

        status, output = run_command([sys.executable, "-I", str(REPOSITORY / "tools" / "claims.py"), "new",
                                      str(project), "--name", NAME], REPOSITORY)
        record("the project is created", status == 0, output)

        # The code first, with no claim about it: the surface check must refuse it.
        shutil.copy(FIXTURES / "InRange.lean", project / NAME / "InRange.lean")
        append(project / f"{NAME}.lean", f"import {NAME}.InRange\n")
        status, output = claims("trust", "--check")
        record("a new public function with no claim is refused by the trust check",
               status == 1 and f"{NAME}.inRange" in output and "is public and is not proved, tested or trusted" in output, output)

        # Step 1. The claim, at first without the lock.
        append(project / "Spec.lean", (FIXTURES / "claim7.lean.txt").read_text(encoding="utf-8"))
        status, output = claims("sync")
        record("the claim added without updating the lock stops every command",
               status == 1 and "claim 7 is in the spec and not in the lock" in output, output)
        status, output = claims("lock", "--update")
        record("step 1: the claim is stated and the lock updated", status == 0 and "claim 7" in output, output)

        # Step 2. The proof.
        shutil.copy(FIXTURES / "ProofsInRange.lean", project / NAME / "Proofs" / "InRange.lean")
        append(project / NAME / "Proofs.lean", f"import {NAME}.Proofs.InRange\n")
        status, output = claims("sync")
        build_status, build_output = run_command(["lake", "build"], project)
        record("step 2: the code and the proof build against the spec", status == 0 and build_status == 0,
               output + build_output)

        # Step 3. Before the audit is written, the audit must say what is missing.
        status, output = claims("audit")
        record("the claim without its audits is refused by the audit",
               status == 1 and "claim 7" in output and "no audit theorem shows a wrong implementation failing it" in output,
               output)
        shutil.copy(FIXTURES / "InRangeAudit.lean", project / "tests" / "InRangeAudit.lean")
        replace_once(project / "claims.toml", 'modules = ["ClampAudit"]', 'modules = ["ClampAudit", "InRangeAudit"]')
        replace_once(project / "tests" / "lakefile.toml", 'roots = ["ClampAudit", "Axioms"]',
                     'roots = ["ClampAudit", "InRangeAudit", "Axioms"]')
        claims("sync")
        status, output = claims("audit")
        record("with the audits written, only the mutation is missing",
               status == 1 and "claim 7" in output and "no mutation in mutations.toml is refuted by one of its theorems" in output
               and "no audit theorem" not in output, output)

        # Step 4. The planted bug.
        append(project / "mutations.toml", (FIXTURES / "mutation.toml.txt").read_text(encoding="utf-8"))
        status, output = claims("audit")
        record("step 3 and 4: the audit accepts claim 7", status == 0 and "every one of the 7 claims" in output, output)

        # Step 6 and 7.
        status, output = claims("trust")
        record("step 6: the trust report is written with both functions proved",
               status == 0 and "2 public declarations: 2 mentioned by a claim" in output, output)
        status, output = claims("verify", "--full")
        record("step 7: every check, the mutation run and the test of the checks pass",
               status == 0 and "all 11 passed" in output, output)

    print(f"{10 - len(failures)} of 10 steps of adding a second claim passed")
    for failure in failures:
        print(f"FAILED: {failure}")
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
