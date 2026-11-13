"""
File: tools/leanclaims/journal.py
Purpose: Plants deliberate faults in a project's files so that they are always taken out
again, even when the tool that planted them is killed. The mutation run and the test of
the checks both change a project on purpose and restore it afterwards. A restore that
runs only when the tool exits normally is not enough: a tool killed part way would leave
a planted bug in the working tree.

Before any file is changed, the original text of every file about to be changed is
written to a journal file and flushed to disk. The journal is removed only after the
originals have been written back. A tool calls `restore_leftover` when it starts, so a
journal left by an interrupted run is replayed before anything else happens.

The journal lives under the project's `.lake/` directory, which git ignores.
Created: 2026-11-13
"""

import json
import os
from dataclasses import dataclass
from pathlib import Path


class PlantingError(Exception):
    """A fault could not be planted. Nothing was changed."""


@dataclass(frozen=True)
class Edit:
    """Replace `find`, which must occur exactly once, with `replace` in one file. The
    path is relative to the project directory."""

    file: str
    find: str
    replace: str


def texts_after_edits(project_directory: Path, edits: list[Edit], description: str) -> dict[str, str]:
    """The full new text of every file `edits` touches, without writing anything. Edits to
    one file apply in order, and each `find` must occur exactly once at the time its edit
    is applied."""
    new_texts: dict[str, str] = {}
    for edit in edits:
        if edit.file not in new_texts:
            new_texts[edit.file] = (project_directory / edit.file).read_text(encoding="utf-8")
        occurrences = new_texts[edit.file].count(edit.find)
        if occurrences != 1:
            raise PlantingError(f"{description}: the text to find occurs {occurrences} times in {edit.file}")
        new_texts[edit.file] = new_texts[edit.file].replace(edit.find, edit.replace)
    return new_texts


class PlantedFaults:
    """The faults one tool has planted in one project, and the way back from them."""

    def __init__(self, project_directory: Path):
        self.project_directory = Path(project_directory).resolve()
        self.journal_path = self.project_directory / ".lake" / "planted-faults.json"

    def restore_leftover(self) -> list[str]:
        """Write back the originals a journal records, then remove the journal. Returns
        the files restored, as paths relative to the project; empty when there was no
        journal."""
        if not self.journal_path.exists():
            return []
        originals = json.loads(self.journal_path.read_text(encoding="utf-8"))
        for relative_path, original_text in originals.items():
            (self.project_directory / relative_path).write_text(original_text, encoding="utf-8")
        self.journal_path.unlink()
        return sorted(originals)

    def plant(self, new_texts: dict[str, str], description: str) -> None:
        """Replace the text of each file in `new_texts` (relative path to full new text).
        The originals are in the journal, on disk, before any file changes."""
        if self.journal_path.exists():
            raise PlantingError(
                f"{description}: a journal of planted faults already exists; restore it before planting")
        originals = {
            relative_path: (self.project_directory / relative_path).read_text(encoding="utf-8")
            for relative_path in new_texts
        }
        self.journal_path.parent.mkdir(parents=True, exist_ok=True)
        temporary_path = self.journal_path.with_suffix(".tmp")
        with open(temporary_path, "w", encoding="utf-8") as handle:
            json.dump(originals, handle)
            handle.flush()
            # The journal must be on disk, not in a buffer, before the first file changes.
            os.fsync(handle.fileno())
        os.replace(temporary_path, self.journal_path)
        for relative_path, new_text in new_texts.items():
            (self.project_directory / relative_path).write_text(new_text, encoding="utf-8")

    def plant_edits(self, edits: list[Edit], description: str) -> None:
        """Apply find-and-replace edits. Nothing is written unless every edit applies."""
        self.plant(texts_after_edits(self.project_directory, edits, description), description)

    def restore(self) -> list[str]:
        """Write back the originals of the faults now planted, if any."""
        return self.restore_leftover()
