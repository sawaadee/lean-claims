"""
File: tools/leanclaims/checks.py
Purpose: The test of a project's checks. For each check it plants the fault that check
exists to catch and requires the check to fail. A check that has never been seen to fail
has not been shown to work.

For one project it does four things:
  1. Requires every check to pass on the project as it stands. A fault "caught" by a
     check that was already failing would prove nothing.
  2. Plants each fault in turn, the generated ones and the project's own from
     `faults.toml`, runs the check the fault is planted for, and requires that check to
     fail with the expected text in its output.
  3. Kills a process while it has a fault planted, and requires the journal to bring the
     file back unchanged.
  4. Requires every file a fault touched, and the spec, the lock, the proof files and the
     generated files, to be byte for byte what they were before the run.
Created: 2026-11-13
"""

import hashlib
import signal
import subprocess
import sys
import time
from pathlib import Path

from leanclaims.config import ProjectConfig
from leanclaims.faults import BUILT_IN_CHECK_IDS, Check, PlannedFault, built_in_checks
from leanclaims.generated_faults import generated_faults
from leanclaims.journal import PlantedFaults
from leanclaims.lock import LOCK_FILE_NAME
from leanclaims.process import run_command
from leanclaims.spec import Spec
from leanclaims.sync import generated_files

TOOLS_DIRECTORY = Path(__file__).resolve().parent.parent

# A program that plants a fault through the journal and then waits to be killed.
PLANT_AND_WAIT_PROGRAM = """
import sys, time
sys.path.insert(0, sys.argv[1])
from pathlib import Path
from leanclaims.journal import PlantedFaults
planted_faults = PlantedFaults(Path(sys.argv[2]))
relative_path = sys.argv[3]
original_text = (Path(sys.argv[2]) / relative_path).read_text(encoding="utf-8")
planted_faults.plant({relative_path: original_text + "\\n-- planted by the kill test\\n"}, "kill test")
print("planted", flush=True)
time.sleep(600)
"""


class ChecksRun:
    """One test of one project's checks."""

    def __init__(self, config: ProjectConfig, spec: Spec, declared_checks: dict[str, Check],
                 catalog_faults: list[PlannedFault], report=print):
        self.config = config
        self.spec = spec
        self.report = report
        self.project_directory = config.project_directory
        self.checks = dict(built_in_checks(config, TOOLS_DIRECTORY), **declared_checks)
        self.declared_check_ids = list(declared_checks)
        generated, self.not_possible = generated_faults(config, spec)
        self.faults = generated + catalog_faults
        self.planted_faults = PlantedFaults(self.project_directory)

    def run_check(self, check_id: str, extra_environment: dict[str, str] | None = None) -> tuple[int, str]:
        check = self.checks[check_id]
        return run_command(list(check.command), self.project_directory / check.directory, extra_environment)

    def watched_file_hashes(self) -> dict[str, str]:
        """A SHA-256 hash of every file a fault touches, and of the proof files, the spec,
        the lock and the generated files, by path relative to the project."""
        relative_paths = {
            proof_file.relative_to(self.project_directory).as_posix()
            for layer in self.config.layers
            for proof_file in layer.proof_files
        }
        relative_paths |= {self.spec.file_name, LOCK_FILE_NAME} | set(generated_files(self.config, self.spec))
        for fault in self.faults:
            relative_paths |= set(fault.new_texts)
        return {
            relative_path: hashlib.sha256((self.project_directory / relative_path).read_bytes()).hexdigest()
            for relative_path in sorted(relative_paths)
        }

    def baseline_problems(self) -> list[str]:
        """The checks that fail on the project as it stands."""
        problems = []
        for check_id in list(BUILT_IN_CHECK_IDS) + self.declared_check_ids:
            status, output = self.run_check(check_id)
            if status != 0:
                problems.append(f"the '{check_id}' check fails before anything is planted:\n{output[-1500:]}")
        return problems

    def fault_is_caught(self, fault: PlannedFault) -> tuple[bool, str]:
        """Plant the fault, run its check, restore the files."""
        if fault.new_texts:
            self.planted_faults.plant(fault.new_texts, fault.description)
        try:
            status, output = self.run_check(fault.check_id, fault.environment)
        finally:
            self.planted_faults.restore()
        return fault.is_caught_by(status, output)

    def killed_tool_leaves_nothing_planted(self) -> tuple[bool, str]:
        """Kill a process while its fault is planted. The fault must be on disk at that
        moment, and replaying the journal must bring the file back unchanged."""
        proof_file = self.config.layers[0].proof_files[0]
        relative_path = proof_file.relative_to(self.project_directory).as_posix()
        original_bytes = proof_file.read_bytes()
        process = subprocess.Popen(
            [sys.executable, "-I", "-c", PLANT_AND_WAIT_PROGRAM, str(TOOLS_DIRECTORY),
             str(self.project_directory), relative_path],
            stdout=subprocess.PIPE, text=True)
        try:
            announced = process.stdout.readline().strip()
        finally:
            # SIGKILL cannot be caught, so the process gets no chance to clean up after itself.
            process.send_signal(signal.SIGKILL)
            process.wait()
        if announced != "planted":
            self.planted_faults.restore_leftover()
            return False, "the process did not report planting its fault"
        fault_was_on_disk = proof_file.read_bytes() != original_bytes
        restored_files = self.planted_faults.restore_leftover()
        if not fault_was_on_disk:
            return False, "the fault was not on disk when the process was killed, so nothing was tested"
        if restored_files != [relative_path]:
            return False, f"the journal restored {restored_files}, not [{relative_path}]"
        if proof_file.read_bytes() != original_bytes:
            return False, "the file differs from the original after the journal was replayed"
        return True, ""

    def run(self) -> bool:
        """Run the whole test. Returns whether every fault was caught and every file restored."""
        leftover = self.planted_faults.restore_leftover()
        if leftover:
            self.report(f"restored files left planted by an interrupted run: {', '.join(leftover)}")
        hashes_before = self.watched_file_hashes()
        started = time.monotonic()

        problems = self.baseline_problems()
        if problems:
            self.report("the project must pass every check before faults are planted:")
            for problem in problems:
                self.report(f"  {problem}")
            return False
        check_ids = list(BUILT_IN_CHECK_IDS) + self.declared_check_ids
        self.report(f"baseline: all {len(check_ids)} checks pass on the unchanged project ({', '.join(check_ids)})")
        for reason in self.not_possible:
            self.report(f"not planted: {reason}")

        missed = []
        for fault in self.faults:
            caught, reason = self.fault_is_caught(fault)
            self.report(f"{'caught' if caught else 'MISSED'}  [{fault.check_id}] {fault.description}")
            if not caught:
                missed.append(f"{fault.description}: {reason}")
        caught, reason = self.killed_tool_leaves_nothing_planted()
        self.report(f"{'caught' if caught else 'MISSED'}  [journal] a process killed while its fault is planted")
        if not caught:
            missed.append(f"killed process: {reason}")

        files_unchanged = self.watched_file_hashes() == hashes_before
        total = len(self.faults) + 1
        self.report(f"{total - len(missed)} of {total} planted faults were caught by the check meant to catch them")
        self.report(f"every file a fault touched is byte for byte what it was before the run: {files_unchanged}")
        self.report(f"took {time.monotonic() - started:.0f} seconds")
        for reason in missed:
            self.report(f"MISSED: {reason}")
        return not missed and files_unchanged
