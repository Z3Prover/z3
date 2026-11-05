############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Unit tests for Unix distribution packaging.
############################################
from contextlib import ExitStack
from pathlib import Path
import shlex
import sys
import tempfile
import unittest
from unittest.mock import patch


_SCRIPTS_DIR = str(Path(__file__).resolve().parents[1])
if _SCRIPTS_DIR not in sys.path:
    sys.path.insert(0, _SCRIPTS_DIR)

import mk_unix_dist


class TestUnixStaticLibrary(unittest.TestCase):
    def setUp(self):
        self.stack = ExitStack()
        self.addCleanup(self.stack.close)
        temp = self.stack.enter_context(tempfile.TemporaryDirectory())
        self.build = Path(temp) / "build with spaces"
        self.dist = Path(temp) / "distribution"
        self.build.mkdir()
        (self.dist / "bin").mkdir(parents=True)
        self.bindings = {
            "Z3_BUILD_DOTNET_BINDINGS": "ON",
            "Z3_BUILD_GO_BINDINGS": "OFF",
            "Z3_BUILD_JAVA_BINDINGS": "OFF",
            "Z3_BUILD_JULIA_BINDINGS": "ON",
            "Z3_BUILD_OCAML_BINDINGS": "OFF",
            "Z3_BUILD_PYTHON_BINDINGS": "ON",
        }
        cache = ''.join('%s:BOOL=%s\n' % item for item in self.bindings.items())
        cache += "CMAKE_OSX_ARCHITECTURES:STRING=x86_64\n"
        (self.build / "CMakeCache.txt").write_text(cache, encoding="utf-8")
        (self.build / "libz3.a").write_bytes(b"static archive")
        self.stack.enter_context(patch.object(mk_unix_dist, "BUILD_DIR", str(self.build)))
        self.stack.enter_context(patch.object(mk_unix_dist, "VERBOSE", False))
        self.stack.enter_context(patch.object(mk_unix_dist, "get_build_dist_path",
                                             return_value=str(self.dist)))
        self.exec_cmds = self.stack.enter_context(patch.object(mk_unix_dist, "exec_cmds",
                                                              return_value=0))

    def assert_binding_options(self, call_index, bindings):
        command = self.exec_cmds.call_args_list[call_index].args[0][0]
        options = shlex.split(command)
        for name, value in bindings.items():
            self.assertIn('-D%s=%s' % (name, value), options)
        self.assertEqual(options[options.index("-B") + 1], str(self.build))
        return options

    def assert_shared_restored(self):
        options = self.assert_binding_options(1, self.bindings)
        self.assertIn("-DBUILD_SHARED_LIBS=ON", options)
        self.assertIn("-DZ3_BUILD_LIBZ3_SHARED=ON", options)

    def test_static_build_disables_and_restores_cached_bindings(self):
        mk_unix_dist.build_static_lib()

        self.assertEqual(self.exec_cmds.call_count, 2)
        options = self.assert_binding_options(0, dict.fromkeys(self.bindings, "OFF"))
        self.assertIn("-DBUILD_SHARED_LIBS=OFF", options)
        self.assertIn("-DZ3_BUILD_LIBZ3_SHARED=OFF", options)
        self.assertIn("&&", options)
        self.assert_shared_restored()
        self.assertEqual((self.dist / "bin" / "libz3.a").read_bytes(), b"static archive")

    def test_failed_static_build_restores_shared_bindings(self):
        self.exec_cmds.side_effect = [1, 0]

        with self.assertRaisesRegex(mk_unix_dist.MKException, "Failed to build static libz3"):
            mk_unix_dist.build_static_lib()

        self.assert_shared_restored()
        self.assertFalse((self.dist / "bin" / "libz3.a").exists())

    def test_non_bool_cache_type_restores_original_value(self):
        cache = self.build / "CMakeCache.txt"
        cache.write_text(cache.read_text().replace(
            "Z3_BUILD_PYTHON_BINDINGS:BOOL=ON",
            "Z3_BUILD_PYTHON_BINDINGS:STRING=YES"), encoding="utf-8")
        self.bindings["Z3_BUILD_PYTHON_BINDINGS"] = "YES"

        mk_unix_dist.build_static_lib()

        self.assert_binding_options(0, dict.fromkeys(self.bindings, "OFF"))
        self.assert_shared_restored()

    def test_failed_archive_copy_restores_shared_bindings(self):
        with patch.object(mk_unix_dist.shutil, "copy2", side_effect=OSError("copy failed")):
            with self.assertRaisesRegex(OSError, "copy failed"):
                mk_unix_dist.build_static_lib()

        self.assert_shared_restored()

    def test_failed_shared_restore_is_reported(self):
        self.exec_cmds.side_effect = [0, 1]

        with self.assertRaisesRegex(mk_unix_dist.MKException,
                                    "Failed to restore shared libz3 build"):
            mk_unix_dist.build_static_lib()

    def test_missing_cache_does_not_reconfigure(self):
        (self.build / "CMakeCache.txt").unlink()

        with self.assertRaises(FileNotFoundError):
            mk_unix_dist.build_static_lib()

        self.exec_cmds.assert_not_called()


if __name__ == "__main__":
    unittest.main()
