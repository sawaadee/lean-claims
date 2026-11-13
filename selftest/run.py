"""
File: selftest/run.py
Purpose: Runs the whole self-test of lean-claims in one command: the builds, the unit
tests of the tools, the tests of the Lean commands, every check on the starter project
with the mutation run and the test of the checks, the tests that the two long runs fail
when they should, a new project created and checked from scratch, and the comparison of
the starter's proofs with its spec by every kernel. The same checks are then run on
`examples/minijson`, a second project of another kind.

Each step is a command that exits with status 0 when it passes. Every step is run even
after one fails, and the last lines of a failing step's output are shown.

Usage: python3 -I selftest/run.py
Exit status: 0 when every step passes, 1 otherwise.
Created: 2026-11-13
"""

import sys
import time
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parent.parent
# `python3 -I` leaves this script's directory off the import path, so the tools are added here.
sys.path.insert(0, str(REPOSITORY / "tools"))

from leanclaims.process import run_command  # noqa: E402

PYTHON = [sys.executable, "-I"]
CLAIMS = PYTHON + [str(REPOSITORY / "tools" / "claims.py"), "--project", str(REPOSITORY / "template")]

# (what the step shows, the command, the directory it runs in relative to the repository)
STEPS = [
    ("the Lean package builds", ["lake", "build"], "."),
    ("the starter project builds", ["lake", "build"], "template"),
    ("the starter's test package builds", ["lake", "build"], "template/tests"),
    ("the unit tests of the tools", PYTHON + ["selftest/test_tools.py"], "."),
    ("the repository's files have their headers and its documents name what exists",
     PYTHON + ["selftest/repository.py"], "."),
    ("#audit_facts reports what each audit theorem is", PYTHON + ["selftest/audit_facts.py"], "."),
    ("#surface_facts reports the public surface", PYTHON + ["selftest/surface_facts.py"], "."),
    ("every check, the mutation run and the test of the checks on the starter", CLAIMS + ["verify", "--full"], "."),
    ("the mutation run fails when it should", PYTHON + ["selftest/mutation_engine.py"], "."),
    ("the test of the checks fails when it should", PYTHON + ["selftest/checks_engine.py"], "."),
    ("a new project is created and passes every check", PYTHON + ["selftest/new_project.py"], "."),
    ("a second function and claim are added to a new project", PYTHON + ["selftest/second_claim.py"], "."),
    ("every kernel accepts the starter's proofs against its spec", ["lake", "comparator", "--paranoid"], "template"),
    ("the second project, MiniJson, builds", ["lake", "build"], "examples/minijson"),
    ("MiniJson's test package builds", ["lake", "build"], "examples/minijson/tests"),
    ("every check, the mutation run and the test of the checks on MiniJson",
     PYTHON + [str(REPOSITORY / "tools" / "claims.py"), "--project", str(REPOSITORY / "examples" / "minijson"),
               "verify", "--full"], "."),
    ("every kernel accepts MiniJson's proofs against its spec", ["lake", "comparator", "--paranoid"], "examples/minijson"),
]


def main() -> int:
    failed = []
    started = time.monotonic()
    for what, command, directory in STEPS:
        step_started = time.monotonic()
        status, output = run_command(command, REPOSITORY / directory)
        print(f"{'passed' if status == 0 else 'FAILED'}  {time.monotonic() - step_started:6.1f}s  {what}", flush=True)
        if status != 0:
            failed.append(what)
            for line in output[-3000:].rstrip().splitlines():
                print(f"        {line}")
    print(f"{len(STEPS) - len(failed)} of {len(STEPS)} steps passed in {time.monotonic() - started:.0f} seconds")
    return 0 if not failed else 1


if __name__ == "__main__":
    sys.exit(main())
