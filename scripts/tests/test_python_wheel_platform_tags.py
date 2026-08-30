############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Unit tests for Python wheel platform tag generation.
############################################
import importlib.util
import contextlib
import io
import os
import pathlib
import sys
import types
import unittest
from unittest.mock import patch


class DummyBdistWheel:
    def finalize_options(self):
        pass


def load_python_setup():
    repo_root = pathlib.Path(__file__).resolve().parents[2]
    setup_py = repo_root / "src" / "api" / "python" / "setup.py"
    spec = importlib.util.spec_from_file_location("z3_python_setup_for_tests", setup_py)
    module = importlib.util.module_from_spec(spec)
    bdist_wheel_module = types.ModuleType("setuptools.command.bdist_wheel")
    bdist_wheel_module.bdist_wheel = DummyBdistWheel
    with patch.dict(os.environ, {}, clear=False), \
         patch.dict(sys.modules, {"setuptools.command.bdist_wheel": bdist_wheel_module}), \
         patch("setuptools.setup"), \
         contextlib.redirect_stdout(io.StringIO()):
        os.environ.pop("PACKAGE_FROM_RELEASE", None)
        os.environ.pop("PYODIDE_ROOT", None)
        spec.loader.exec_module(module)
    return module


class TestPythonWheelPlatformTags(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.python_setup = load_python_setup()

    def test_macos_11_and_newer_use_major_zero_tags(self):
        for platform in ("osx", "darwin", "sequoia"):
            with self.subTest(platform=platform):
                self.assertEqual(
                    "13_0",
                    self.python_setup.normalize_macos_wheel_os_version(platform, "13_3"),
                )

    def test_bdist_wheel_normalizes_release_metadata_tag(self):
        cmd = self.python_setup.bdist_wheel()
        self.assertEqual("13_0", cmd.remove_build_machine_os_version("osx", "13_3"))

    def test_macos_10_keeps_minor_version(self):
        self.assertEqual(
            "10_15",
            self.python_setup.normalize_macos_wheel_os_version("osx", "10_15"),
        )

    def test_non_macos_platforms_are_unchanged(self):
        self.assertEqual(
            "13_3",
            self.python_setup.normalize_macos_wheel_os_version("linux", "13_3"),
        )


if __name__ == '__main__':
    unittest.main()
