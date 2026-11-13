"""
File: selftest/test_tools.py
Purpose: Unit tests for the parts of the tools that need no Lean build: reading Lean
source text, validating `claims.toml`, the journal of planted faults, the spec file's
rules, the lock, the text of the generated files, and the audit rule applied to what
Lean reports. Each test builds what it needs in a temporary directory.

Usage: python3 -I selftest/test_tools.py
Created: 2026-11-13
Revised: 2026-11-13 (the spec, the lock and the generated files)
Revised: 2026-11-13 (the mutation catalog and the mutation probe)
Revised: 2026-11-13 (the fault catalog and how a fault is judged)
Revised: 2026-11-13 (the audit rule)
Revised: 2026-11-13 (the audit is given what Lean reports, and every Audit line must be confirmed)
Revised: 2026-11-13 (the levels of the public declarations and the trust report)
Revised: 2026-11-13 (starting a project, and the order of the checks)
"""

import dataclasses
import sys
from datetime import date
import tempfile
import unittest
from pathlib import Path

# `python3 -I` leaves this script's directory off the import path, so the tools are added here.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "tools"))

from leanclaims.audit import (AuditError, AuditFacts, LeanTheorem, PropertyTie, audit, parse_audit_facts,  # noqa: E402
                              parse_audit_line, tagged_theorems_in_source)
from leanclaims.config import ConfigError, load_config  # noqa: E402
from leanclaims.faults import BUILT_IN_CHECK_IDS, Check, FaultCatalogError, PlannedFault, load_fault_catalog  # noqa: E402
from leanclaims.journal import Edit, PlantedFaults, PlantingError  # noqa: E402
from leanclaims.lean_source import blank_comments_and_strings, declared_theorems  # noqa: E402
from leanclaims.lock import lock_differences, lock_text, parse_lock  # noqa: E402
from leanclaims.mutate import probe_files_in_order, probe_source  # noqa: E402
from leanclaims.mutations import Mutation, MutationCatalogError, load_mutations  # noqa: E402
from leanclaims.new_project import LeanClaimsSource, NewProjectError, create_project, renamed, template_files  # noqa: E402
from leanclaims.verify import checks_in_order, shown_command  # noqa: E402
from leanclaims.names import (LeanDeclaredTheorem, NamesError, find_duplicate_theorems,  # noqa: E402
                              parse_declared_theorems, reading_differences)
from leanclaims.spec import SpecError, parse_spec  # noqa: E402
from leanclaims.sync import axioms_text, comparator_text, verify_text  # noqa: E402
from leanclaims.trust import (SurfaceDeclaration, SurfaceFacts, TrustError, parse_surface_facts,  # noqa: E402
                              surface_levels, trust_text)

VALID_CONFIG = """
[project]
name = "Example"
spec_module = "Spec"
code_library = "Example"
proofs_library = "ExampleProofs"
proofs_module = "Example.Proofs"
verify_file = "Example/Verify.lean"
allowed_axioms = ["propext", "Classical.choice", "Quot.sound"]

[tests]
directory = "tests"
library = "ExampleTests"

[[layer]]
name = "main"
namespace = "Example.Proofs"
proof_files = "Example/Proofs/*.lean"
"""


def make_project(directory: Path, config_text: str = VALID_CONFIG, proof_files: dict[str, str] | None = None) -> Path:
    """Write a project skeleton: `claims.toml`, a tests directory and the proof files."""
    (directory / "tests").mkdir(parents=True)
    (directory / "Example" / "Proofs").mkdir(parents=True)
    (directory / "claims.toml").write_text(config_text, encoding="utf-8")
    for name, text in (proof_files or {"One.lean": "theorem first : True := trivial\n"}).items():
        (directory / "Example" / "Proofs" / name).write_text(text, encoding="utf-8")
    return directory


class LeanSourceTests(unittest.TestCase):
    def test_blanking_keeps_length_and_lines(self):
        source = 'theorem a : x = "-- not a comment" := rfl -- comment\n/- block\n more -/ theorem b : True := trivial\n'
        blanked = blank_comments_and_strings(source)
        self.assertEqual(len(blanked), len(source))
        self.assertEqual(blanked.count("\n"), source.count("\n"))
        self.assertNotIn("not a comment", blanked)
        self.assertNotIn("block", blanked)
        self.assertIn("theorem b", blanked)

    def test_nested_block_comments(self):
        source = "/- outer /- inner -/ theorem hidden : True := trivial -/\ntheorem shown : True := trivial\n"
        self.assertEqual([theorem.name for theorem in declared_theorems(source)], ["shown"])

    def test_theorem_in_doc_comment_and_string_is_not_counted(self):
        source = ('/-- Example:\ntheorem inDoc : True := trivial -/\n'
                  'def text := "\ntheorem inString : True := trivial"\n'
                  "theorem real : True := trivial\n")
        self.assertEqual([theorem.name for theorem in declared_theorems(source)], ["real"])

    def test_double_quote_character_literal_does_not_open_a_string(self):
        source = "def quote : Char := '\"'\ntheorem afterQuote : True := trivial\n"
        self.assertEqual([theorem.name for theorem in declared_theorems(source)], ["afterQuote"])

    def test_modifiers_attributes_and_line_numbers(self):
        source = ("private theorem one : True := trivial\n"
                  "@[simp] theorem two (n : Nat) : n = n := rfl\n"
                  "@[simp]\nprotected theorem three: True := trivial\n"
                  "theorem ofBytes?_toBytes : True := trivial\n")
        found = declared_theorems(source)
        self.assertEqual([theorem.name for theorem in found], ["one", "two", "three", "ofBytes?_toBytes"])
        self.assertEqual([theorem.line_number for theorem in found], [1, 2, 4, 5])

    def test_a_word_ending_in_theorem_is_not_a_declaration(self):
        source = "def mytheorem := 1\n-- theorem commented : True\n"
        self.assertEqual(declared_theorems(source), [])


class ConfigTests(unittest.TestCase):
    def load(self, config_text: str, proof_files: dict[str, str] | None = None):
        with tempfile.TemporaryDirectory() as temporary:
            return load_config(make_project(Path(temporary), config_text, proof_files))

    def test_valid_config(self):
        config = self.load(VALID_CONFIG)
        self.assertEqual(config.name, "Example")
        self.assertEqual(len(config.layers), 1)
        self.assertEqual(len(config.layers[0].proof_files), 1)

    def test_missing_file(self):
        with tempfile.TemporaryDirectory() as temporary:
            with self.assertRaisesRegex(ConfigError, "does not exist"):
                load_config(Path(temporary))

    def test_unknown_key_is_an_error(self):
        with self.assertRaisesRegex(ConfigError, "unknown key spec_modul"):
            self.load(VALID_CONFIG.replace("spec_module", "spec_modul"))

    def test_missing_key_is_an_error(self):
        with self.assertRaisesRegex(ConfigError, "'proofs_module' must be a non-empty string"):
            self.load(VALID_CONFIG.replace('proofs_module = "Example.Proofs"\n', ""))

    def test_empty_allowed_axioms_is_an_error(self):
        with self.assertRaisesRegex(ConfigError, "'allowed_axioms' must not be empty"):
            self.load(VALID_CONFIG.replace('["propext", "Classical.choice", "Quot.sound"]', "[]"))

    def test_pattern_matching_no_file_is_an_error(self):
        with self.assertRaisesRegex(ConfigError, "matches no file"):
            self.load(VALID_CONFIG.replace("Example/Proofs/*.lean", "Example/Missing/*.lean"))

    def test_repeated_layer_name_is_an_error(self):
        second_layer = '\n[[layer]]\nname = "main"\nnamespace = "Other"\nproof_files = "Example/Proofs/*.lean"\n'
        with self.assertRaisesRegex(ConfigError, "two layers share a name"):
            self.load(VALID_CONFIG + second_layer)

    def test_file_in_two_layers_is_an_error(self):
        second_layer = '\n[[layer]]\nname = "other"\nnamespace = "Other"\nproof_files = "Example/Proofs/*.lean"\n'
        with self.assertRaisesRegex(ConfigError, "belongs to both"):
            self.load(VALID_CONFIG + second_layer)

    def test_missing_tests_directory_is_an_error(self):
        with self.assertRaisesRegex(ConfigError, "is not a directory"):
            self.load(VALID_CONFIG.replace('directory = "tests"', 'directory = "absent"'))

    def test_waiver_rules(self):
        waiver = '\n[[waiver]]\nclaim = 3\nkind = "determines"\nreason = "Many printers are correct."\n'
        self.assertEqual(self.load(VALID_CONFIG + waiver).waivers[0].claim, 3)
        with self.assertRaisesRegex(ConfigError, "'kind' must be one of"):
            self.load(VALID_CONFIG + waiver.replace("determines", "because"))
        with self.assertRaisesRegex(ConfigError, "'claim' must be a claim number"):
            self.load(VALID_CONFIG + waiver.replace("claim = 3", "claim = true"))
        with self.assertRaisesRegex(ConfigError, "waived twice"):
            self.load(VALID_CONFIG + waiver + waiver)

    def test_tested_entry_needs_its_fault(self):
        tested = '\n[[tested]]\nwhat = "the lock"\ntest = "concurrency"\n'
        with self.assertRaisesRegex(ConfigError, "'fault' must be a non-empty string"):
            self.load(VALID_CONFIG + tested)


class NamesTests(unittest.TestCase):
    def test_duplicate_across_files_and_within_a_file(self):
        proof_files = {
            "One.lean": "theorem shared : True := trivial\ntheorem twice : True := trivial\n",
            "Two.lean": "private theorem shared : True := trivial\ntheorem alone : True := trivial\n",
            "Three.lean": "theorem twice' : True := trivial\n\nnamespace Other\ntheorem twice : True := trivial\n"
                          "end Other\ntheorem twice : True := trivial\n",
        }
        with tempfile.TemporaryDirectory() as temporary:
            config = load_config(make_project(Path(temporary), proof_files=proof_files))
            duplicates = find_duplicate_theorems(config)
        self.assertEqual([duplicate.theorem_name for duplicate in duplicates], ["shared", "twice"])
        self.assertEqual(duplicates[0].places, ("Example/Proofs/One.lean:1", "Example/Proofs/Two.lean:1"))
        self.assertEqual(len(duplicates[1].places), 3)

    def test_no_duplicates(self):
        with tempfile.TemporaryDirectory() as temporary:
            config = load_config(make_project(Path(temporary)))
            self.assertEqual(find_duplicate_theorems(config), [])

    def test_the_reading_of_the_text_is_compared_with_what_lean_declares(self):
        proof_files = {
            "One.lean": "namespace Example.Proofs\ntheorem first : True := trivial\n\n"
                        "set_option maxRecDepth 512 in theorem hidden : True := trivial\n"
                        "instance : Inhabited Nat := ⟨0⟩\nend Example.Proofs\n",
            "All.lean": "import Example.Proofs.One\n",
        }
        module = "Example.Proofs.One"
        first = LeanDeclaredTheorem("Example.Proofs.first", module, 2, False)
        hidden = LeanDeclaredTheorem("Example.Proofs.hidden", module, 4, False)
        instance = LeanDeclaredTheorem("Example.Proofs.instInhabitedNat", module, 5, True)
        with tempfile.TemporaryDirectory() as temporary:
            config = load_config(make_project(Path(temporary), proof_files=proof_files))
            self.assertEqual(reading_differences(config, [first, instance]), [])
            self.assertEqual(reading_differences(config, [first, hidden, instance]), [
                "Example/Proofs/One.lean:4: Lean declares the theorem Example.Proofs.hidden here, and the reading of "
                "the file as text did not find it"])
            self.assertEqual(reading_differences(config, [instance]), [
                "Example/Proofs/One.lean:2: the reading of the file as text found the theorem 'first' here, and "
                "Lean declares none"])
            renamed = LeanDeclaredTheorem("Example.Proofs.afirst", module, 2, False)
            self.assertEqual(reading_differences(config, [renamed, instance]), [
                "Example/Proofs/One.lean:2: Lean declares the theorem Example.Proofs.afirst here, and the reading of "
                "the file as text found 'first'"])

    def test_the_theorems_lean_prints_are_read(self):
        output = ('Probe.lean:4:0: info: declared-theorems {"theorems":[{"instance":false,"line":7,'
                  '"module":"A.B","name":"A.t"}]}\n')
        self.assertEqual(parse_declared_theorems(output), [LeanDeclaredTheorem("A.t", "A.B", 7, False)])
        with self.assertRaisesRegex(NamesError, "did not report"):
            parse_declared_theorems("error: unknown module\n")


class JournalTests(unittest.TestCase):
    def test_plant_and_restore(self):
        with tempfile.TemporaryDirectory() as temporary:
            project = make_project(Path(temporary))
            proof_file = project / "Example" / "Proofs" / "One.lean"
            original = proof_file.read_text(encoding="utf-8")
            planted_faults = PlantedFaults(project)
            planted_faults.plant_edits([Edit("Example/Proofs/One.lean", "trivial", "sorry")], "test")
            self.assertIn("sorry", proof_file.read_text(encoding="utf-8"))
            self.assertTrue(planted_faults.journal_path.exists())
            self.assertEqual(planted_faults.restore(), ["Example/Proofs/One.lean"])
            self.assertEqual(proof_file.read_text(encoding="utf-8"), original)
            self.assertFalse(planted_faults.journal_path.exists())

    def test_text_found_twice_or_never_plants_nothing(self):
        with tempfile.TemporaryDirectory() as temporary:
            project = make_project(Path(temporary), proof_files={"One.lean": "theorem a : True := trivial\n"
                                                                             "theorem b : True := trivial\n"})
            proof_file = project / "Example" / "Proofs" / "One.lean"
            original = proof_file.read_text(encoding="utf-8")
            planted_faults = PlantedFaults(project)
            for find in ("trivial", "absent"):
                with self.assertRaises(PlantingError):
                    planted_faults.plant_edits([Edit("Example/Proofs/One.lean", find, "sorry")], "test")
            self.assertEqual(proof_file.read_text(encoding="utf-8"), original)
            self.assertFalse(planted_faults.journal_path.exists())

    def test_second_plant_is_refused_while_a_journal_exists(self):
        with tempfile.TemporaryDirectory() as temporary:
            project = make_project(Path(temporary))
            planted_faults = PlantedFaults(project)
            planted_faults.plant_edits([Edit("Example/Proofs/One.lean", "trivial", "sorry")], "first")
            with self.assertRaisesRegex(PlantingError, "already exists"):
                planted_faults.plant_edits([Edit("Example/Proofs/One.lean", "sorry", "rfl")], "second")
            planted_faults.restore()
            self.assertIn("trivial", (project / "Example" / "Proofs" / "One.lean").read_text(encoding="utf-8"))

    def test_two_edits_to_one_file_apply_in_order(self):
        with tempfile.TemporaryDirectory() as temporary:
            project = make_project(Path(temporary))
            planted_faults = PlantedFaults(project)
            planted_faults.plant_edits(
                [Edit("Example/Proofs/One.lean", "first", "second"), Edit("Example/Proofs/One.lean", "second", "third")],
                "test")
            self.assertIn("theorem third", (project / "Example" / "Proofs" / "One.lean").read_text(encoding="utf-8"))
            planted_faults.restore()

VALID_SPEC = """/-
  File: Spec.lean
-/

import Example

/-! ## Claim 1. The first thing.

More words about it. -/

namespace Example.Proofs

open Example

/-- Explains `first`. A comment may mention
theorem notReal : True -/
theorem first (n : Nat) : n = n := by
  sorry

end Example.Proofs

/-! ## Claim 2. The second thing. -/

namespace Example.Proofs

/-- Explains `second`. -/
theorem second (n : Nat) (positive : 0 < n) :
    n ≠ 0 := by
  sorry

/-- Explains `third`. -/
theorem third : True := by sorry

end Example.Proofs
"""


class SpecTests(unittest.TestCase):
    def parse(self, source: str):
        return parse_spec(source, "Spec.lean")

    def assert_rejected(self, source: str, message: str):
        with self.assertRaisesRegex(SpecError, message):
            self.parse(source)

    def test_valid_spec(self):
        spec = self.parse(VALID_SPEC)
        self.assertEqual([claim.number for claim in spec.claims], [1, 2])
        self.assertEqual([claim.title for claim in spec.claims], ["The first thing.", "The second thing."])
        self.assertEqual([theorem.qualified_name for theorem in spec.theorems],
                         ["Example.Proofs.first", "Example.Proofs.second", "Example.Proofs.third"])
        self.assertEqual(spec.theorems[0].signature, " (n : Nat) : n = n")
        self.assertEqual(spec.theorems[1].signature, " (n : Nat) (positive : 0 < n) :\n    n ≠ 0")
        self.assertTrue(spec.theorems[0].doc_comment.startswith("/-- Explains `first`."))
        self.assertEqual([part.text for part in spec.claims[0].parts if not hasattr(part, "signature")],
                         ["namespace Example.Proofs", "open Example", "end Example.Proofs"])

    def test_one_line_header(self):
        self.assertEqual(self.parse(VALID_SPEC).claims[1].title, "The second thing.")

    def test_numbers_must_run_from_one_in_order(self):
        self.assert_rejected(VALID_SPEC.replace("## Claim 2.", "## Claim 3."), "found claim 3 where claim 2 belongs")
        self.assert_rejected(VALID_SPEC.replace("## Claim 2.", "## Claim 1."), "found claim 1 where claim 2 belongs")
        self.assert_rejected(VALID_SPEC.replace("## Claim 1.", "## Claim 2."), "found claim 2 where claim 1 belongs")

    def test_theorem_needs_a_doc_comment(self):
        self.assert_rejected(VALID_SPEC.replace("/-- Explains `second`. -/\n", ""), "theorem second needs a doc comment")

    def test_proof_must_be_left_out(self):
        self.assert_rejected(VALID_SPEC.replace("n = n := by\n  sorry", "n = n := by\n  rfl"),
                             "the proof of first must be exactly 'by sorry'")
        self.assert_rejected(VALID_SPEC.replace("n = n := by\n  sorry", "n = n := rfl"),
                             "the proof of first must be exactly 'by sorry'")

    def test_the_spec_defines_nothing(self):
        self.assert_rejected(VALID_SPEC.replace("open Example\n", "open Example\n\ndef extra : Nat := 1\n"),
                             "the spec defines nothing: def extra")
        self.assert_rejected(VALID_SPEC.replace("import Example\n", "import Example\n\naxiom anything : False\n"),
                             "before the first claim only comments, import lines and open lines")

    def test_namespaces_are_closed_by_the_claim_that_opens_them(self):
        self.assert_rejected(VALID_SPEC.replace("end Example.Proofs\n\n/-! ## Claim 2", "/-! ## Claim 2"),
                             "claim 1 leaves namespace Example.Proofs open")
        self.assert_rejected(VALID_SPEC.replace("end Example.Proofs\n\n/-! ## Claim 2", "end Other\n\n/-! ## Claim 2"),
                             "closes a namespace that is not the open one")

    def test_withdrawn_claims(self):
        withdrawn = VALID_SPEC[:VALID_SPEC.index("/-! ## Claim 2.")] + "/-! ## Claim 2. Withdrawn: it said too much. -/\n"
        spec = self.parse(withdrawn)
        self.assertTrue(spec.claims[1].withdrawn)
        self.assertEqual(spec.claims[1].theorems, ())
        self.assert_rejected(VALID_SPEC.replace("## Claim 2. The second thing.", "## Claim 2. Withdrawn."),
                             "claim 2 is withdrawn and must hold no theorem")
        self.assert_rejected(VALID_SPEC[:VALID_SPEC.index("/-! ## Claim 2.")] + "/-! ## Claim 2. Empty. -/\n",
                             "claim 2 states no theorem")

    def test_a_theorem_is_stated_once(self):
        self.assert_rejected(VALID_SPEC.replace("theorem third : True", "theorem first : True"),
                             "Example.Proofs.first is stated in claim 1 and again in claim 2")

    def test_open_lines_only_list_namespaces(self):
        self.assert_rejected(VALID_SPEC.replace("open Example\n", "open Example in\n"), "an open line may only list namespaces")
        self.assert_rejected(VALID_SPEC.replace("open Example\n", "open Example hiding first\n"),
                             "an open line may only list namespaces")

    def test_a_file_with_no_claim_is_rejected(self):
        self.assert_rejected("import Example\n", "no claim header")
        self.assert_rejected(VALID_SPEC.replace("## Claim 1. The first thing.", "## Claim one"), "a claim header must read")

    def test_malformed_header(self):
        self.assert_rejected(VALID_SPEC.replace("## Claim 1. The first thing.", "## Claim 1 The first thing."),
                             "a claim header must read")

    def test_hashes_cover_exactly_their_own_text(self):
        spec = self.parse(VALID_SPEC)
        trailing_space = self.parse(VALID_SPEC + "\n\n")
        self.assertEqual(spec.claims[1].text_hash, trailing_space.claims[1].text_hash)
        doc_changed = self.parse(VALID_SPEC.replace("Explains `second`.", "Explains `second` differently."))
        self.assertEqual(spec.claims[0].text_hash, doc_changed.claims[0].text_hash)
        self.assertNotEqual(spec.claims[1].text_hash, doc_changed.claims[1].text_hash)
        self.assertEqual(spec.preamble_hash, doc_changed.preamble_hash)
        import_changed = self.parse(VALID_SPEC.replace("import Example\n", "import Example\nimport Other\n"))
        self.assertNotEqual(spec.preamble_hash, import_changed.preamble_hash)
        self.assertEqual(spec.claims[0].text_hash, import_changed.claims[0].text_hash)


class LockTests(unittest.TestCase):
    def test_lock_round_trip_and_differences(self):
        with tempfile.TemporaryDirectory() as temporary:
            project = Path(temporary)
            spec = parse_spec(VALID_SPEC, "Spec.lean")
            self.assertEqual(lock_differences(spec, project), ["spec.lock does not exist"])
            text = lock_text(spec, None)
            (project / "spec.lock").write_text(text, encoding="utf-8")
            self.assertEqual(lock_differences(spec, project), [])
            self.assertEqual(sorted(parse_lock(text).claims), [1, 2])
            # Writing the lock again keeps its creation date, so the file does not change.
            self.assertEqual(lock_text(spec, text), text)

            changed = parse_spec(VALID_SPEC.replace("n ≠ 0", "n ≠ 1"), "Spec.lean")
            self.assertEqual(lock_differences(changed, project), ["claim 2 changed: The second thing."])
            shorter = parse_spec(VALID_SPEC[:VALID_SPEC.index("/-! ## Claim 2.")], "Spec.lean")
            self.assertEqual(lock_differences(shorter, project),
                             ["claim 2 is in the lock and not in the spec: The second thing."])
            longer = parse_spec(VALID_SPEC + "\n/-! ## Claim 3. Withdrawn. -/\n", "Spec.lean")
            self.assertEqual(lock_differences(longer, project), ["claim 3 is in the spec and not in the lock: Withdrawn."])
            other_import = parse_spec(VALID_SPEC.replace("import Example\n", "import Other\n"), "Spec.lean")
            self.assertEqual(lock_differences(other_import, project), ["the preamble (imports and open lines) changed"])

    def test_a_lock_edited_by_hand_is_reported(self):
        with tempfile.TemporaryDirectory() as temporary:
            project = Path(temporary)
            spec = parse_spec(VALID_SPEC, "Spec.lean")
            (project / "spec.lock").write_text(lock_text(spec, None) + "something else\n", encoding="utf-8")
            self.assertIn("not a line this tool writes", lock_differences(spec, project)[0])


class SyncTests(unittest.TestCase):
    def test_generated_texts(self):
        with tempfile.TemporaryDirectory() as temporary:
            config_text = VALID_CONFIG.replace('library = "ExampleTests"',
                                               'library = "ExampleTests"\ntheorem_modules = ["RunTheorems"]')
            proof_files = {"One.lean": "theorem first : True := trivial\n", "All.lean": "import Example.Proofs.One\n"}
            config = load_config(make_project(
                Path(temporary), config_text + '\n[audit]\nmodules = ["ClampAudit"]\n', proof_files))
            spec = parse_spec(VALID_SPEC, "Spec.lean")

            comparator = comparator_text(config, spec)
            self.assertIn('"challenge_module": "Spec"', comparator)
            self.assertIn('"Example.Proofs.second"', comparator)
            self.assertIn('"Quot.sound"', comparator)

            verify = verify_text(config, spec, None)
            self.assertIn("import Example.Proofs\n", verify)
            self.assertIn("recall first (n : Nat) : n = n\n#print axioms first\n", verify)
            self.assertIn("recall second (n : Nat) (positive : 0 < n) :\n    n ≠ 0\n", verify)
            self.assertEqual(verify.count("namespace Example.Proofs"), 2)
            self.assertNotIn("sorry", verify)
            dated = verify.replace(verify[verify.index("Created: "):].split("\n")[0], "Created: 2020-01-02")
            self.assertEqual(verify_text(config, spec, dated), dated)

            # Every proof file is listed, `All.lean` included, which only imports. Lean finds the theorems.
            axioms = axioms_text(config, None)
            self.assertIn("import LeanClaims\nimport Example.Proofs\nimport ClampAudit\nimport RunTheorems\n", axioms)
            self.assertIn("#assert_axioms_among [propext, Classical.choice, Quot.sound] across\n"
                          "  Example.Proofs.All Example.Proofs.One\n\n"
                          "#assert_axioms_among [propext, Classical.choice, Quot.sound] in\n"
                          "  ClampAudit RunTheorems\n", axioms)

VALID_MUTATION = """[[mutation]]
layer = "main"
description = "first becomes false"
refuted_claim = "first"
refutation = "absurd (first 0) (by decide)"

  [[mutation.edit]]
  file = "Example/Proofs/One.lean"
  find = "trivial"
  replace = "sorry"
"""


class MutationCatalogTests(unittest.TestCase):
    def load(self, catalog_text: str, with_prelude: bool = True):
        with tempfile.TemporaryDirectory() as temporary:
            config_text = VALID_CONFIG + ('refutation_prelude = "prelude.lean"\n' if with_prelude else "")
            project = make_project(Path(temporary), config_text)
            (project / "mutations.toml").write_text(catalog_text, encoding="utf-8")
            return load_mutations(load_config(project), parse_spec(VALID_SPEC, "Spec.lean"))

    def assert_refused(self, catalog_text: str, message: str, with_prelude: bool = True):
        with self.assertRaisesRegex(MutationCatalogError, message):
            self.load(catalog_text, with_prelude)

    def test_valid_catalog(self):
        keeps_behaviour = VALID_MUTATION.replace('refuted_claim = "first"\nrefutation = "absurd (first 0) (by decide)"\n',
                                                 "same_behaviour = true\n").replace("first becomes false", "no change")
        mutations = self.load(VALID_MUTATION + "\n" + keeps_behaviour)
        self.assertEqual([mutation.changes_behaviour for mutation in mutations], [True, False])
        self.assertEqual(mutations[0].edits[0].find, "trivial")

    def test_rules(self):
        self.assert_refused(VALID_MUTATION.replace('layer = "main"', 'layer = "other"'), "no layer is named 'other'")
        self.assert_refused(VALID_MUTATION.replace("refuted_claim", "refuted_clam"), "unknown key refuted_clam")
        self.assert_refused(VALID_MUTATION.replace('refuted_claim = "first"', 'refuted_claim = "absent"'),
                            "the spec states no theorem Example.Proofs.absent")
        self.assert_refused(VALID_MUTATION.replace('refutation = "absurd (first 0) (by decide)"\n', ""),
                            "give 'refuted_claim' and 'refutation', or mark the mutation")
        self.assert_refused(VALID_MUTATION.replace('description = "first becomes false"',
                                                   'description = "first becomes false"\nsame_behaviour = true'),
                            "a mutation that keeps behaviour refutes no claim")
        self.assert_refused(VALID_MUTATION + "\n" + VALID_MUTATION, "this description is used twice")
        self.assert_refused(VALID_MUTATION.replace("Example/Proofs/One.lean", "Example/Absent.lean"), "does not exist")
        self.assert_refused(VALID_MUTATION.replace('replace = "sorry"', 'replace = "trivial"'), "the same text")
        self.assert_refused(VALID_MUTATION[:VALID_MUTATION.index("  [[mutation.edit]]")], "at least one")
        self.assert_refused(VALID_MUTATION, "has no refutation_prelude", with_prelude=False)
        self.assert_refused("", "at least one")


class MutationProbeTests(unittest.TestCase):
    def test_files_are_ordered_by_their_imports_and_joined(self):
        proof_files = {
            "A.lean": "import Example.Proofs.Z\nimport Example.Clamp\n\ntheorem second : True := trivial\n",
            "Z.lean": "import Example.Clamp\n-- import Not.A.Real.Import\ntheorem first : True := trivial\n",
            "All.lean": "import Example.Proofs.A\nimport Example.Proofs.Z\n",
        }
        with tempfile.TemporaryDirectory() as temporary:
            config = load_config(make_project(Path(temporary), proof_files=proof_files))
            layer = config.layers[0]
            self.assertEqual([path.name for path in probe_files_in_order(config, layer)], ["Z.lean", "A.lean"])
            probe = probe_source(config, parse_spec(VALID_SPEC, "Spec.lean"), layer)
        self.assertTrue(probe.startswith("import Example.Clamp\n\nset_option Elab.async false\n"))
        self.assertEqual(probe.count("import Example.Clamp"), 1)
        self.assertNotIn("import Example.Proofs.Z", probe)
        self.assertLess(probe.index("theorem first"), probe.index("theorem second"))
        self.assertIn("-- import Not.A.Real.Import", probe)
        self.assertTrue(probe.rstrip().endswith("#print axioms Example.Proofs.third"))

VALID_FAULTS = """[[check]]
id = "test"
command = ["lake", "test"]

[[fault]]
id = "first-broken"
description = "the first theorem's proof removed"
check = "test"
caught_when_output_has = ["FAILED", "first"]
caught_when_output_has_any = ["one reason", "another reason"]
environment = { SUITE_PYTHON = "/nonexistent" }

  [[fault.edit]]
  file = "Example/Proofs/One.lean"
  find = "trivial"
  replace = "sorry"
"""


class FaultCatalogTests(unittest.TestCase):
    def load(self, catalog_text: str | None):
        with tempfile.TemporaryDirectory() as temporary:
            project = make_project(Path(temporary))
            if catalog_text is not None:
                (project / "faults.toml").write_text(catalog_text, encoding="utf-8")
            return load_fault_catalog(load_config(project))

    def assert_refused(self, catalog_text: str, message: str):
        with self.assertRaisesRegex(FaultCatalogError, message):
            self.load(catalog_text)

    def test_a_project_without_a_catalog_has_no_faults_of_its_own(self):
        self.assertEqual(self.load(None), ({}, []))

    def test_valid_catalog(self):
        checks, faults = self.load(VALID_FAULTS)
        self.assertEqual(checks["test"].command, ("lake", "test"))
        self.assertEqual(checks["test"].directory, ".")
        self.assertEqual(faults[0].new_texts, {"Example/Proofs/One.lean": "theorem first : True := sorry\n"})
        self.assertEqual(faults[0].environment, {"SUITE_PYTHON": "/nonexistent"})

    def test_rules(self):
        self.assert_refused(VALID_FAULTS.replace('id = "test"', 'id = "build"'), "'build' is the name of a built-in check")
        self.assert_refused(VALID_FAULTS.replace('check = "test"', 'check = "absent"'), "no check is named 'absent'")
        self.assert_refused(VALID_FAULTS.replace("description", "descripton"), "unknown key descripton")
        self.assert_refused(VALID_FAULTS.replace('find = "trivial"', 'find = "absent"'), "occurs 0 times")
        self.assert_refused(VALID_FAULTS + VALID_FAULTS[VALID_FAULTS.index("[[fault]]"):], "the id is used twice")
        nothing_expected = VALID_FAULTS.replace('caught_when_output_has = ["FAILED", "first"]\n', "").replace(
            'caught_when_output_has_any = ["one reason", "another reason"]\n', "")
        self.assert_refused(nothing_expected, "say what the check's output must hold")
        changes_nothing = VALID_FAULTS[:VALID_FAULTS.index("  [[fault.edit]]")].replace(
            'environment = { SUITE_PYTHON = "/nonexistent" }\n', "")
        self.assert_refused(changes_nothing, "changes neither")

    def test_the_catalog_can_be_read_while_one_of_its_faults_is_planted(self):
        """With a fault planted, its own edit no longer finds its text. The audit reads the
        catalog for ids and checks only, and must still get them."""
        with tempfile.TemporaryDirectory() as temporary:
            project = make_project(Path(temporary))
            (project / "faults.toml").write_text(VALID_FAULTS, encoding="utf-8")
            (project / "Example" / "Proofs" / "One.lean").write_text("theorem first : True := sorry\n", encoding="utf-8")
            config = load_config(project)
            with self.assertRaisesRegex(FaultCatalogError, "occurs 0 times"):
                load_fault_catalog(config)
            _, faults = load_fault_catalog(config, apply_edits=False)
            self.assertEqual([(fault.fault_id, fault.check_id, fault.new_texts) for fault in faults],
                             [("first-broken", "test", {})])

    def test_a_fault_is_caught_only_when_the_check_fails_for_the_stated_reason(self):
        fault = PlannedFault("id", "description", "build", {}, expected_in_output=("FAILED", "first"),
                             expected_any_in_output=("one reason", "another reason"))
        self.assertTrue(fault.is_caught_by(1, "FAILED first: another reason")[0])
        self.assertFalse(fault.is_caught_by(0, "FAILED first: another reason")[0])
        self.assertFalse(fault.is_caught_by(1, "FAILED second: another reason")[0])
        self.assertFalse(fault.is_caught_by(1, "FAILED first: a third reason")[0])

def lean_theorem(name: str, line_number: int, doc_comment: str | None, **found) -> LeanTheorem:
    return LeanTheorem(name=f"ExampleAudit.{name}", module="ExampleAudit", line_number=line_number,
                       doc_comment=doc_comment, **{kind: tuple(names) for kind, names in found.items()})


FIRST, SECOND, THIRD = "Example.Proofs.first", "Example.Proofs.second", "Example.Proofs.third"

# What Lean reports for an audit module in which every Audit line is true.
FULL_AUDIT = (
    lean_theorem("helper", 4, "A helper with no Audit line. "),
    lean_theorem("wrong_fails_claim1", 7, "Audit: fails claim 1. The wrong function returns 3 for the input 5. ",
                 fails=[FIRST]),
    lean_theorem("wrong_fails_claim2", 10, "Audit: fails claim 2. ", fails=[THIRD]),
    lean_theorem("claims_determine", 13, "Audit: determines claims 1 and 2. Any function meeting both is the\n"
                 "library's. ", determines=[FIRST, SECOND]),
    lean_theorem("hypotheses_can_hold", 16, "Audit: hypotheses of claim 2 can hold. ", can_hold=[SECOND]),
)


class AuditTests(unittest.TestCase):
    """Claim 1 of VALID_SPEC has one theorem without hypotheses. Claim 2 has two theorems,
    one of which has a hypothesis."""

    HYPOTHESES = {FIRST: 0, SECOND: 1, THIRD: 0}
    MUTATIONS = [Mutation("main", "one", (), "first", "proof"), Mutation("main", "two", (), "third", "proof")]

    def run_audit(self, theorems=FULL_AUDIT, extra_config: str = "", mutations=None, faults=(), gave_up=()):
        with tempfile.TemporaryDirectory() as temporary:
            project = make_project(Path(temporary), VALID_CONFIG + '\n[audit]\nmodules = ["ExampleAudit"]\n' + extra_config)
            config = load_config(project)
            facts = AuditFacts(hypotheses=self.HYPOTHESES, theorems=tuple(theorems), gave_up=tuple(gave_up))
            return audit(config, parse_spec(VALID_SPEC, "Spec.lean"),
                         self.MUTATIONS if mutations is None else mutations, {}, list(faults), facts)

    @staticmethod
    def without(name: str) -> tuple:
        return tuple(theorem for theorem in FULL_AUDIT if theorem.name != f"ExampleAudit.{name}")

    @staticmethod
    def with_changed(name: str, **changes) -> tuple:
        return tuple(dataclasses.replace(theorem, **changes) if theorem.name == f"ExampleAudit.{name}" else theorem
                     for theorem in FULL_AUDIT)

    def test_every_requirement_met(self):
        report = self.run_audit()
        self.assertEqual(report.problems, ())
        self.assertEqual(report.audit_theorem_count, 4)
        self.assertEqual(report.untagged_theorem_count, 1)
        self.assertEqual([claim.has_hypotheses for claim in report.claims], [False, True])
        self.assertEqual(report.claims[1].fails, ("ExampleAudit.wrong_fails_claim2",))

    def test_each_missing_audit_is_a_problem(self):
        for removed, message in (
            ("wrong_fails_claim1", "claim 1 (The first thing.): no audit theorem shows a wrong implementation failing it"),
            ("claims_determine", "claim 2 (The second thing.): no audit theorem shows the claims determine"),
            ("hypotheses_can_hold", "claim 2 (The second thing.): no audit theorem shows the hypotheses of second can hold"),
        ):
            report = self.run_audit(self.without(removed))
            self.assertTrue(any(message in problem for problem in report.problems), report.problems)

    def test_an_audit_line_lean_does_not_confirm_is_a_problem(self):
        """The Audit line is intent. A theorem that proves `True` under it, or whose
        property is not a claim's statement, or is another claim's, does not count."""
        where = "tests/ExampleAudit.lean:7: ExampleAudit.wrong_fails_claim1: the Audit line names claim 1 and Lean does not confirm it: "
        for changes, reason in (
            ({"fails": ()}, "its statement is not '¬ P candidate' for a property P"),
            ({"fails": (), "negated_property": "ExampleAudit.Loose"},
             "its property ExampleAudit.Loose is not tied to a claim"),
            ({"fails": (THIRD,), "negated_property": "ExampleAudit.Other"},
             "its property ExampleAudit.Other is the statement of Example.Proofs.third, of claim 2"),
        ):
            problems = self.run_audit(self.with_changed("wrong_fails_claim1", **changes)).problems
            self.assertTrue(any(problem.startswith(where + reason) for problem in problems), problems)
            self.assertIn("claim 1 (The first thing.): no audit theorem shows a wrong implementation failing it", problems)
        problems = self.run_audit(self.with_changed("claims_determine", determines=(FIRST,))).problems
        self.assertEqual(problems, (
            "tests/ExampleAudit.lean:13: ExampleAudit.claims_determine: the Audit line names claim 2 and Lean does not "
            "confirm it: no hypothesis of it asks a property tied to claim 2 of a candidate that its conclusion mentions",
            "claim 2 (The second thing.): no audit theorem shows the claims determine the implementation"))
        problems = self.run_audit(self.with_changed("hypotheses_can_hold", can_hold=())).problems
        self.assertEqual(problems, (
            "tests/ExampleAudit.lean:16: ExampleAudit.hypotheses_can_hold: the Audit line names claim 2 and Lean does "
            "not confirm it: its statement is not 'hypotheses_can_hold% T' for a theorem T of claim 2",
            "claim 2 (The second thing.): no audit theorem shows the hypotheses of second can hold"))

    def test_failing_a_property_that_gathers_several_claims_fails_none_of_them(self):
        """`¬ (A ∧ B)` does not say which of A and B is false."""
        gathered = self.with_changed("wrong_fails_claim1", fails=(FIRST, THIRD), negated_property="ExampleAudit.Both")
        problems = self.run_audit(gathered).problems
        self.assertEqual(problems, (
            "tests/ExampleAudit.lean:7: ExampleAudit.wrong_fails_claim1: the Audit line names claim 1 and Lean does not "
            "confirm it: its property ExampleAudit.Both gathers theorems of claims 1, 2, so failing it does not show "
            "which claim fails. Use a property that states this claim alone",
            "claim 1 (The first thing.): no audit theorem shows a wrong implementation failing it"))
        # Several theorems of one claim are one claim: failing the property fails the claim.
        within = self.with_changed("wrong_fails_claim2", fails=(SECOND, THIRD), negated_property="ExampleAudit.Both")
        self.assertEqual(self.run_audit(within).problems, ())

    def test_a_theorem_counts_only_through_its_audit_line(self):
        """What Lean finds in an untagged theorem's statement meets no requirement."""
        untagged = self.with_changed("wrong_fails_claim1", doc_comment="The Audit line was taken off. ")
        report = self.run_audit(untagged)
        self.assertEqual(report.problems,
                         ("claim 1 (The first thing.): no audit theorem shows a wrong implementation failing it",))
        self.assertEqual((report.audit_theorem_count, report.untagged_theorem_count), (3, 2))

    def test_a_comparison_lean_gave_up_on_is_a_problem(self):
        self.assertEqual(self.run_audit(gave_up=["comparing with Example.Proofs.first: timeout"]).problems,
                         ("Lean gave up on a comparison, which may hide an audit: comparing with Example.Proofs.first: timeout",))

    def test_a_claim_without_hypotheses_needs_no_can_hold_theorem(self):
        report = self.run_audit()
        self.assertEqual(report.claims[0].can_hold, ())
        self.assertFalse(any("claim 1" in problem for problem in report.problems))

    def test_a_claim_needs_a_mutation(self):
        report = self.run_audit(mutations=[self.MUTATIONS[0]])
        self.assertEqual(report.problems,
                         ("claim 2 (The second thing.): no mutation in mutations.toml is refuted by one of its theorems",))

    def test_a_waiver_lifts_a_requirement_and_shows(self):
        waiver = '\n[[waiver]]\nclaim = 2\nkind = "mutation"\nreason = "No bug of this code can violate it alone."\n'
        report = self.run_audit(extra_config=waiver, mutations=[self.MUTATIONS[0]])
        self.assertEqual(report.problems, ())
        self.assertEqual(report.claims[1].waived, ("mutation",))

    def test_a_waiver_that_is_not_needed_is_a_problem(self):
        met = '\n[[waiver]]\nclaim = 1\nkind = "fails"\nreason = "Not needed."\n'
        self.assertEqual(self.run_audit(extra_config=met).problems,
                         ("claim 1: the waiver for 'fails' is not needed, the requirement is met",))
        no_hypotheses = '\n[[waiver]]\nclaim = 1\nkind = "can hold"\nreason = "Not needed."\n'
        self.assertEqual(self.run_audit(extra_config=no_hypotheses).problems,
                         ("claim 1: the waiver for 'can hold' is not needed, the claim has no hypotheses",))
        absent = '\n[[waiver]]\nclaim = 7\nkind = "fails"\nreason = "No such claim."\n'
        self.assertEqual(self.run_audit(extra_config=absent).problems,
                         ("a waiver names claim 7, which the spec does not have",))

    def test_an_audit_of_a_claim_the_spec_lacks_is_a_problem(self):
        report = self.run_audit(self.with_changed("wrong_fails_claim2", doc_comment="Audit: fails claims 2 and 9. "))
        self.assertTrue(any("is about claim 9, which the spec does not have" in problem for problem in report.problems))

    def test_audit_lines(self):
        self.assertEqual(parse_audit_line(" determines claims 3 to 5, 8 and 11. With 2 extra cases in 7 files.", "here"),
                         ("determines", (3, 4, 5, 8, 11)))
        self.assertEqual(parse_audit_line(" hypotheses of claims 2 to 3 can hold. The range 10 to 5 is empty.", "here"),
                         ("can hold", (2, 3)))
        for malformed, message in ((" proves claim 1.", "an Audit line reads"),
                                   (" fails claim.", "names no claim number"),
                                   (" fails claims 5 to 3.", "runs backwards")):
            with self.assertRaisesRegex(AuditError, message):
                parse_audit_line(malformed, "here")
            with self.assertRaisesRegex(AuditError, message):
                self.run_audit(self.with_changed("wrong_fails_claim1", doc_comment=f"Audit:{malformed}"))

    def test_the_facts_lean_prints_are_read(self):
        output = ('LeanClaimsAuditProbe.lean:5:0: info: audit-facts {"claims":[{"hypotheses":1,"name":"A.t"}],'
                  '"gave_up":[],"theorems":[{"can_hold":[],"determines":[],"doc":"Audit: fails claim 1. ","fails":["A.t"],'
                  '"line":9,"module":"M","name":"M.wrong","negated_property":"M.Meets"},{"can_hold":["A.t"],'
                  '"determines":[],"doc":null,"fails":[],"line":3,"module":"M","name":"M.early","negated_property":null}],'
                  '"ties":[{"claim_theorems":["A.t"],"property":"M.Meets","tied_by":"M.tie"}]}\n')
        facts = parse_audit_facts(output)
        self.assertEqual(facts.hypotheses, {"A.t": 1})
        self.assertEqual([theorem.name for theorem in facts.theorems], ["M.early", "M.wrong"])
        self.assertEqual(facts.theorems[1].fails, ("A.t",))
        self.assertEqual(facts.ties, (PropertyTie("M.Meets", ("A.t",), "M.tie"),))
        with self.assertRaisesRegex(AuditError, "did not report"):
            parse_audit_facts("error: unknown constant\n")

    def test_tagged_theorems_are_found_in_the_source_for_planting(self):
        with tempfile.TemporaryDirectory() as temporary:
            project = make_project(Path(temporary), VALID_CONFIG + '\n[audit]\nmodules = ["ExampleAudit"]\n')
            (project / "tests" / "ExampleAudit.lean").write_text(
                "/-- A helper. -/\ntheorem helper : True := trivial\n\n"
                "/-- Audit: fails claim 2. -/\n@[simp] theorem wrong : True := trivial\n", encoding="utf-8")
            tagged = tagged_theorems_in_source(load_config(project))
            self.assertEqual([(found.name, found.kind, found.claim_numbers) for found in tagged], [("wrong", "fails", (2,))])

    def test_a_tested_entry_names_a_check_and_a_fault_planted_for_it(self):
        tested = '\n[[tested]]\nwhat = "the lock"\ntest = "build"\nfault = "lock-released"\n'
        self.assertEqual(self.run_audit(extra_config=tested).problems,
                         ("tested entry 'the lock': faults.toml has no fault 'lock-released'",))
        for_another_check = PlannedFault("lock-released", "description", "names", {}, expected_in_output=("text",))
        self.assertEqual(self.run_audit(extra_config=tested, faults=[for_another_check]).problems,
                         ("tested entry 'the lock': the fault 'lock-released' is planted for the check 'names', not for 'build'",))
        for_this_check = PlannedFault("lock-released", "description", "build", {}, expected_in_output=("text",))
        self.assertEqual(self.run_audit(extra_config=tested, faults=[for_this_check]).problems, ())
        unknown_check = tested.replace('test = "build"', 'test = "absent"')
        self.assertIn("tested entry 'the lock': no check is named 'absent'",
                      self.run_audit(extra_config=unknown_check, faults=[for_this_check]).problems)


def declaration(name: str, kind: str = "definition", stated_by=(), line_number: int = 3, **flags) -> SurfaceDeclaration:
    return SurfaceDeclaration(name=f"Example.{name}", module="Example.Code", line_number=line_number, kind=kind,
                              is_extern=flags.get("is_extern", False), implemented_by=flags.get("implemented_by"),
                              stated_by=tuple(stated_by))


class TrustTests(unittest.TestCase):
    """VALID_SPEC has claim 1 with the theorem `first` and claim 2 with `second` and `third`."""

    ENTRIES = (
        '\n[[tested]]\nwhat = "the clock is read once"\ntest = "build"\nfault = "clock-read-twice"\n'
        'declarations = ["Example.readClock"]\n'
        '\n[[trusted]]\nwhat = "the random source"\nwhy = "Part of the operating system."\n'
        'declarations = ["Example.randomBytes"]\n')

    def levels(self, surface, extra_config: str = ""):
        with tempfile.TemporaryDirectory() as temporary:
            config = load_config(make_project(Path(temporary), VALID_CONFIG + extra_config))
            facts = SurfaceFacts(surface=tuple(surface), mentions={FIRST: ("Example.stated",)},
                                 vocabulary=("Example.stated",), private_vocabulary=())
            spec = parse_spec(VALID_SPEC, "Spec.lean")
            levels, problems = surface_levels(config, spec, facts)
            return config, spec, facts, levels, problems

    def test_every_level(self):
        surface = [declaration("stated", stated_by=[FIRST, THIRD]), declaration("readClock"),
                   declaration("randomBytes"), declaration("lemma", kind="theorem")]
        _, _, _, levels, problems = self.levels(surface, self.ENTRIES)
        self.assertEqual(problems, [])
        self.assertEqual([level.levels for level in levels], [("proved",), ("tested",), ("trusted",), ("theorem",)])
        self.assertEqual(levels[0].claims, (1, 2))
        self.assertEqual(levels[1].tests, ("build",))

    def test_a_declaration_at_no_level_is_a_problem(self):
        _, _, _, levels, problems = self.levels([declaration("stated", stated_by=[FIRST]), declaration("unstated", line_number=9)])
        self.assertEqual(levels[1].levels, ())
        self.assertEqual(problems, [
            "Example.unstated (Example/Code.lean:9) is public and is not proved, tested or trusted: no claim's "
            "statement mentions it, nothing a claim mentions is defined by it, and no entry of claims.toml lists it"])

    def test_a_helper_a_stated_declaration_is_defined_by_is_supporting(self):
        """`facts.vocabulary` holds what the claims are written in. A declaration there
        that no claim mentions is at the supporting level, and one a claim mentions is
        proved and not also supporting."""
        with tempfile.TemporaryDirectory() as temporary:
            config = load_config(make_project(Path(temporary)))
            surface = (declaration("stated", stated_by=[FIRST]), declaration("helper"), declaration("unstated"))
            facts = SurfaceFacts(surface=surface, mentions={FIRST: ("Example.stated",)},
                                 vocabulary=("Example.stated", "Example.helper"), private_vocabulary=())
            levels, problems = surface_levels(config, parse_spec(VALID_SPEC, "Spec.lean"), facts)
        self.assertEqual([level.levels for level in levels], [("proved",), ("supporting",), ()])
        self.assertEqual(len(problems), 1)
        self.assertIn("Example.unstated", problems[0])

    def test_code_the_proofs_do_not_reach_needs_an_entry_even_when_a_claim_mentions_it(self):
        surface = [declaration("readClock", stated_by=[FIRST], is_extern=True),
                   declaration("randomBytes", stated_by=[FIRST], implemented_by="Example.fastBytes"),
                   declaration("assumed", kind="axiom", stated_by=[FIRST]),
                   declaration("sealed", kind="opaque", stated_by=[FIRST])]
        _, _, _, _, problems = self.levels(surface)
        self.assertEqual(len(problems), 4)
        self.assertIn("runs other code than its definition (@[extern])", problems[0])
        self.assertIn("runs other code than its definition (@[implemented_by Example.fastBytes])", problems[1])
        self.assertIn("is an axiom constant, which has no definition for a proof to be about", problems[2])
        self.assertIn("is an opaque constant", problems[3])
        _, _, _, _, problems = self.levels(surface[:2], self.ENTRIES)
        self.assertEqual(problems, [])

    def test_an_entry_that_lists_a_declaration_the_project_lacks_is_a_problem(self):
        _, _, _, _, problems = self.levels([declaration("stated", stated_by=[FIRST])], self.ENTRIES)
        self.assertEqual(problems, [
            "the tested entry 'the clock is read once' lists Example.readClock, which is not a public declaration of the project",
            "the trusted entry 'the random source' lists Example.randomBytes, which is not a public declaration of the project"])

    def test_the_report(self):
        surface = [declaration("stated", stated_by=[FIRST]), declaration("readClock", is_extern=True),
                   declaration("randomBytes")]
        waiver = '\n[[waiver]]\nclaim = 2\nkind = "determines"\nreason = "Many are | correct."\n'
        config, spec, facts, levels, _ = self.levels(surface, self.ENTRIES + waiver)
        mutations = [Mutation("main", "one", (), "first", "proof"), Mutation("main", "two", (), None, None)]
        report = trust_text(config, spec, facts, levels, mutations, [], None)
        self.assertIn("2 claims, stated in `Spec.lean` as 3 theorems. 3 public declarations: 1 mentioned by a claim, "
                      "1 tested, 1 trusted, 0 supporting, 0 a theorem of the code, 0 at no level.", report)
        self.assertIn("| 1 | The first thing. | `first` | `Example.stated` |", report)
        self.assertIn("| 2 | The second thing. | `second`, `third` | no declaration of the project |", report)
        self.assertIn("| `Example.readClock` | definition (runs `@[extern]` code) | Example/Code.lean:3 |  | build |  |  |", report)
        self.assertIn("| `Example.randomBytes` | definition | Example/Code.lean:3 |  |  | yes |  |", report)
        self.assertIn("| 2 | determines | Many are \\| correct. |", report)
        self.assertIn("plants 2 changes to the code from `mutations.toml`. 1 name a claim", report)
        # Writing it again from itself changes nothing, and the date it was created is kept.
        dated = report.replace(report[report.index("Created: "):].split("\n")[0], "Created: 2020-01-02")
        self.assertEqual(trust_text(config, spec, facts, levels, mutations, [], dated), dated)

    def test_the_surface_lean_prints_is_read(self):
        output = ('Probe.lean:4:0: info: surface-facts {"claims":[{"mentions":["A.f"],"name":"A.P.t"}],'
                  '"private_vocabulary":["A.g"],"surface":[{"extern":true,"implemented_by":null,"kind":"definition",'
                  '"line":7,"module":"A.B","name":"A.f","stated_by":["A.P.t"]}],"vocabulary":["A.f"]}\n')
        facts = parse_surface_facts(output)
        self.assertEqual(facts.surface, (SurfaceDeclaration("A.f", "A.B", 7, "definition", True, None, ("A.P.t",)),))
        self.assertEqual((facts.mentions, facts.vocabulary, facts.private_vocabulary), ({"A.P.t": ("A.f",)}, ("A.f",), ("A.g",)))
        with self.assertRaisesRegex(TrustError, "did not report"):
            parse_surface_facts("error: unknown constant\n")

    def test_code_modules_default_to_the_code_library(self):
        with tempfile.TemporaryDirectory() as temporary:
            self.assertEqual(load_config(make_project(Path(temporary))).code_modules, ("Example",))
        with tempfile.TemporaryDirectory() as temporary:
            listed = VALID_CONFIG.replace('code_library = "Example"', 'code_library = "Example"\ncode_modules = ["Example", "Extra"]')
            self.assertEqual(load_config(make_project(Path(temporary), listed)).code_modules, ("Example", "Extra"))


class NewProjectTests(unittest.TestCase):
    def test_the_name_is_replaced_as_a_whole_word_only(self):
        text = ('import Example.Proofs\nopen Example\nname = "example"\nname = "exampletests"\n'
                'library = "ExampleTests"\n-- for example, an Examples list and MyExample stay\n')
        self.assertEqual(renamed(text, "JsonParser"),
                         'import JsonParser.Proofs\nopen JsonParser\nname = "jsonparser"\nname = "jsonparsertests"\n'
                         'library = "JsonParserTests"\n-- for example, an Examples list and MyExample stay\n')

    def test_a_new_projects_files_carry_its_own_date_and_no_history(self):
        header = "# File: claims.toml\n# Created: 2020-01-02\n# Revised: 2020-03-04 (a key)\nkey = 1\n"
        self.assertEqual(renamed(header, "JsonParser"),
                         f"# File: claims.toml\n# Created: {date.today().isoformat()}\nkey = 1\n")

    def test_what_a_new_project_gets(self):
        files = [path.as_posix() for path in template_files()]
        self.assertIn("Spec.lean", files)
        self.assertIn("tests/lakefile.toml", files)
        self.assertFalse([name for name in files if ".lake" in name or name.endswith("lake-manifest.json")])

    def test_a_requirement_on_leanclaims(self):
        self.assertEqual(LeanClaimsSource(path=Path("/opt/lean-claims")).requirement(),
                         '[[require]]\nname = "LeanClaims"\npath = "/opt/lean-claims"\n')
        self.assertEqual(LeanClaimsSource(git_url="https://example.org/lean-claims", revision="abc123").requirement(),
                         '[[require]]\nname = "LeanClaims"\ngit = "https://example.org/lean-claims"\nrev = "abc123"\n')

    def test_requests_that_are_refused(self):
        with tempfile.TemporaryDirectory() as temporary:
            target = Path(temporary) / "new"
            for name, message in (("json-parser", "cannot name a project"), ("Example", "the starter project's own name")):
                with self.assertRaisesRegex(NewProjectError, message):
                    create_project(target, name, LeanClaimsSource(path=Path(temporary)))
            with self.assertRaisesRegex(NewProjectError, "say where LeanClaims is"):
                create_project(target, "Fine", LeanClaimsSource())
            self.assertFalse(target.exists())
            with self.assertRaisesRegex(NewProjectError, "is not an empty directory"):
                create_project(Path(temporary).parent, "Fine", LeanClaimsSource(path=Path(temporary)))


class VerifyTests(unittest.TestCase):
    def test_the_checks_run_in_a_fixed_order_with_the_projects_own_last(self):
        with tempfile.TemporaryDirectory() as temporary:
            config = load_config(make_project(Path(temporary)))
            own = Check("suite", ("lake", "test"), ".")
            checks = checks_in_order(config, {"suite": own})
            self.assertEqual([check.check_id for check in checks],
                             ["lock", "sync", "build", "names", "axioms", "comparator", "audit", "trust", "suite"])
            self.assertEqual(shown_command(checks[0]), "claims lock --check")
            self.assertEqual(shown_command(own), "lake test")
            self.assertEqual(sorted(check.check_id for check in checks[:-1]), sorted(BUILT_IN_CHECK_IDS))


if __name__ == "__main__":
    unittest.main(verbosity=1)
