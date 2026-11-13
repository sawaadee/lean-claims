"""
File: selftest/new_project.py
Purpose: Tests `claims new`, and with it that the starter project works outside this
repository under another name. It creates a project in a temporary directory, builds it,
and runs `claims verify --full` there: every check, the mutation run and the test of the
checks. It then requires `claims new` to refuse the requests it should refuse.

A project created this way has had every identifier, every file name, the lock and every
generated file rewritten. If any of them still depended on the name `Example`, or on
where the starter sits in this repository, a check would fail here.

Usage: python3 -I selftest/new_project.py
Exit status: 0 when every test passes, 1 otherwise.
Created: 2026-11-13
"""

import sys
import tempfile
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parent.parent
# `python3 -I` leaves this script's directory off the import path, so the tools are added here.
sys.path.insert(0, str(REPOSITORY / "tools"))

from leanclaims.process import run_command  # noqa: E402

CLAIMS = [sys.executable, "-I", str(REPOSITORY / "tools" / "claims.py")]
NEW_NAME = "RangeTools"


def main() -> int:
    failures = []

    def record(what: str, passed: bool, detail: str) -> None:
        print(f"{'passed' if passed else 'FAILED'}  {what}", flush=True)
        if not passed:
            failures.append(f"{what}:\n{detail[-2500:]}")

    with tempfile.TemporaryDirectory() as temporary:
        project = Path(temporary) / "range-tools"
        status, output = run_command(CLAIMS + ["new", str(project), "--name", NEW_NAME], REPOSITORY)
        record("a project is created under a new name", status == 0 and (project / f"{NEW_NAME}.lean").is_file(), output)

        leftovers = [path.relative_to(project).as_posix() for path in sorted(project.rglob("*"))
                     if path.is_file() and ("Example" in path.name or "Example" in path.read_text(encoding="utf-8"))]
        record("nothing in it still carries the starter's name", not leftovers, f"files naming Example: {leftovers}")
        with_history = [path.relative_to(project).as_posix() for path in sorted(project.rglob("*"))
                        if path.is_file() and "Revised: " in path.read_text(encoding="utf-8")]
        record("none of its files carries the starter's history", not with_history, f"files with a Revised line: {with_history}")

        status, output = run_command(["lake", "build"], project)
        record("it builds", status == 0, output)
        status, output = run_command(["lake", "build"], project / "tests")
        record("its test package builds", status == 0, output)

        status, output = run_command(CLAIMS + ["--project", str(project), "verify", "--full"], REPOSITORY)
        record("every check, the mutation run and the test of the checks pass on it",
               status == 0 and "all 11 passed" in output, output)

        status, output = run_command(CLAIMS + ["new", str(project), "--name", "Another"], REPOSITORY)
        record("a directory that is not empty is refused", status == 2 and "is not an empty directory" in output, output)
        for bad_name, reason in (("range-tools", "cannot name a project"), ("Example", "the starter project's own name")):
            status, output = run_command(CLAIMS + ["new", str(Path(temporary) / "refused"), "--name", bad_name], REPOSITORY)
            record(f"the name '{bad_name}' is refused", status == 2 and reason in output
                   and not (Path(temporary) / "refused").exists(), output)
        status, output = run_command(
            CLAIMS + ["new", str(Path(temporary) / "refused"), "--name", "Pinned", "--leanclaims-git", "https://example.org/x"],
            REPOSITORY)
        record("a git requirement without a commit to pin is refused", status == 2 and "--leanclaims-rev" in output, output)

    print(f"{9 - len(failures)} of 9 tests of `claims new` passed")
    for failure in failures:
        print(f"FAILED: {failure}")
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
