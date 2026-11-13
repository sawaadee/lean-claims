"""
File: tools/leanclaims/process.py
Purpose: Runs the commands the checks are made of (`lake`, `lean`) and returns their exit
status and output together.
Created: 2026-11-13
"""

import os
import subprocess
from pathlib import Path

# elan installs `lake` under the home directory, which a bare environment may not search.
ENVIRONMENT = dict(os.environ, PATH=f"{Path.home()}/.elan/bin:{os.environ['PATH']}")


def run_command(command: list[str], directory: Path, extra_environment: dict[str, str] | None = None) -> tuple[int, str]:
    """Run a command in a directory and return its exit status with its standard output
    and standard error joined. `extra_environment` adds or replaces environment variables
    for this one command."""
    environment = dict(ENVIRONMENT, **(extra_environment or {}))
    completed = subprocess.run(command, cwd=directory, env=environment, capture_output=True, text=True)
    return completed.returncode, completed.stdout + completed.stderr
