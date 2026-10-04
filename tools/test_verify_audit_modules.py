"""Focused checks for the root-only audit dependency runner (no Lean required)."""

import contextlib
import io
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import verify_audit_modules as runner


class AuditRunnerTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        (self.root / "audit").mkdir()

    def source(self, name, text):
        source = self.root / "audit" / name
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text(text, encoding="utf-8")
        return source

    def test_dependency_order_beats_alphabetical_order(self):
        self.source("AInventory.lean", "import audit.ZRegression\nimport audit.ZRegression\n")
        self.source("ZRegression.lean", "import audit.MBase\n")
        self.source("MBase.lean", "import Mathlib\n")
        self.assertEqual(
            [p.name for p in runner.audit_order(self.root)],
            ["MBase.lean", "ZRegression.lean", "AInventory.lean"],
        )

    def test_header_comments_modifiers_and_body_text(self):
        source = self.source("Header.lean", """/- import audit.Absent /- nested -/ -/
module
prelude
public meta import Mathlib
import all audit.ZRegression -- import audit.Missing
import/- separator -/audit.YRegression
def text := "import audit.NotAnImport"
""")
        self.assertEqual(runner.imports(source),
                         ["Mathlib", "audit.ZRegression", "audit.YRegression"])

    def test_unsupported_module_spelling_fails_closed(self):
        source = self.source("A.lean", "import audit.«ZRegression»\n")
        with self.assertRaisesRegex(ValueError, "unsupported import module"):
            runner.imports(source)

    def test_second_local_module_in_import_is_rejected(self):
        self.source("A.lean", "import Mathlib audit.ZRegression\n")
        self.source("ZRegression.lean", "import Mathlib\n")
        with patch.object(runner.subprocess, "run") as compile_source:
            with self.assertRaisesRegex(ValueError, "each import must name exactly one module"):
                runner.verify(self.root)
        compile_source.assert_not_called()

    def test_nested_snapshot_is_never_a_target(self):
        root_source = self.source("Only.lean", "import Mathlib\n")
        self.source("semantic-review/sources/Bad.lean", "import audit.Absent\n/-")
        self.assertEqual(runner.audit_order(self.root), [root_source])

    def test_nested_source_does_not_satisfy_local_import(self):
        self.source("A.lean", "import audit.snapshots.Hidden\n")
        self.source("snapshots/Hidden.lean", "import Mathlib\n")
        with self.assertRaisesRegex(ValueError, "unknown local audit dependency"):
            runner.audit_order(self.root)

    def test_symlink_does_not_promote_a_nested_snapshot(self):
        snapshot = self.source("snapshots/Hidden.lean", "import audit.Absent\n")
        (self.root / "audit" / "Hidden.lean").symlink_to(snapshot)
        self.assertEqual(runner.audit_order(self.root), [])

    def test_missing_dependency_fails_before_compilation(self):
        self.source("A.lean", "import audit.Missing\n")
        with patch.object(runner.subprocess, "run") as compile_source:
            with self.assertRaisesRegex(ValueError, "unknown local audit dependency"):
                runner.verify(self.root)
        compile_source.assert_not_called()

    def test_cycle_fails_before_compilation(self):
        self.source("A.lean", "import audit.B\n")
        self.source("B.lean", "import audit.A\n")
        with patch.object(runner.subprocess, "run") as compile_source:
            with self.assertRaisesRegex(ValueError, "audit import cycle"):
                runner.verify(self.root)
        compile_source.assert_not_called()

    def test_self_import_fails(self):
        self.source("A.lean", "import audit.A\n")
        with self.assertRaisesRegex(ValueError, "audit import cycle"):
            runner.audit_order(self.root)

    def test_private_namespace_and_cleanup_after_success(self):
        self.source("AInventory.lean", "import audit.ZRegression\n")
        self.source("ZRegression.lean", "import Mathlib\n")
        calls = []

        def compile_source(command, *, cwd, env):
            namespace = Path(env["LEAN_PATH"].split(os.pathsep)[0])
            self.assertEqual(env["LEAN_PATH"], str(namespace) + os.pathsep + "cached-deps")
            self.assertEqual(cwd, self.root)
            self.assertEqual(command[:3], ["lean", "-R", str(self.root)])
            destination = Path(command[command.index("-o") + 1])
            self.assertEqual(destination.parent, namespace / "audit")
            if not calls:
                self.assertEqual(list(destination.parent.iterdir()), [])
            else:
                self.assertTrue((destination.parent / "ZRegression.olean").is_file())
            destination.write_text("test object")
            calls.append(destination)
            return subprocess.CompletedProcess(command, 0)

        with patch.dict(os.environ, {"LEAN_PATH": "cached-deps"}), \
             patch.object(runner.subprocess, "run", side_effect=compile_source), \
             contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(runner.verify(self.root), 0)
        self.assertEqual([p.stem for p in calls], ["ZRegression", "AInventory"])
        self.assertTrue(all(not p.exists() for p in calls))
        self.assertEqual(list(self.root.rglob("*.olean")), [])

    def test_compiler_error_is_propagated_and_stops_dependents(self):
        self.source("AInventory.lean", "import audit.ZRegression\n")
        self.source("ZRegression.lean", "import Mathlib\n")
        destinations = []

        def fail(command, **kwargs):
            destinations.append(Path(command[command.index("-o") + 1]))
            return subprocess.CompletedProcess(command, 37)

        with patch.object(runner.subprocess, "run", side_effect=fail), \
             contextlib.redirect_stdout(io.StringIO()), \
             contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(runner.verify(self.root), 37)
        self.assertEqual(len(destinations), 1)
        self.assertFalse(destinations[0].parent.exists())


if __name__ == "__main__":
    unittest.main()
