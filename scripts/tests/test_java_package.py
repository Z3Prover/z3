############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Unit tests for Java release package assembly.
############################################
import os
import sys
import tempfile
import unittest
import zipfile

_SCRIPTS_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _SCRIPTS_DIR not in sys.path:
    sys.path.insert(0, _SCRIPTS_DIR)

import mk_java_package


class TestJavaPackageAssembly(unittest.TestCase):
    def _write_release_zip(self, root, name, libraries):
        path = os.path.join(root, name)
        with zipfile.ZipFile(path, "w") as zf:
            zf.writestr("z3-release/bin/com.microsoft.z3.jar", self.base_jar_bytes)
            for library in libraries:
                zf.writestr("z3-release/bin/" + library, library.encode("ascii"))
        return path

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        base_jar = os.path.join(self.tmp.name, "base.jar")
        with zipfile.ZipFile(base_jar, "w") as zf:
            zf.writestr("com/microsoft/z3/Native.class", b"native")
        with open(base_jar, "rb") as f:
            self.base_jar_bytes = f.read()

    def test_creates_native_classifier_jar(self):
        release_zip = self._write_release_zip(
            self.tmp.name,
            "z3-5.0.0-x64-glibc-2.35.zip",
            ["libz3.so", "libz3java.so"],
        )
        out_dir = os.path.join(self.tmp.name, "out")
        base_zip, base_entry = mk_java_package.find_base_jar([release_zip])
        base_jar = os.path.join(out_dir, "z3-5.0.0.jar")
        os.makedirs(out_dir)
        mk_java_package.copy_base_jar(base_zip, base_entry, base_jar)

        output = os.path.join(out_dir, "z3-5.0.0-linux-x64.jar")
        mk_java_package.create_native_jar(base_jar, release_zip, mk_java_package.PLATFORMS[0], output)

        with zipfile.ZipFile(output) as zf:
            names = set(zf.namelist())
            self.assertIn("com/microsoft/z3/Native.class", names)
            self.assertIn("com/microsoft/z3/native/linux-x64/libz3.so", names)
            self.assertIn("com/microsoft/z3/native/linux-x64/libz3java.so", names)

    def test_write_pom_uses_maven_coordinates(self):
        pom = os.path.join(self.tmp.name, "z3-5.0.0.pom")
        mk_java_package.write_pom(pom, "com.microsoft", "z3", "5.0.0")
        with open(pom, encoding="utf-8") as f:
            text = f.read()
        self.assertIn("<groupId>com.microsoft</groupId>", text)
        self.assertIn("<artifactId>z3</artifactId>", text)
        self.assertIn("<version>5.0.0</version>", text)

    def test_rejects_platform_jar_without_jni_library(self):
        release_zip = self._write_release_zip(
            self.tmp.name,
            "z3-5.0.0-x64-win.zip",
            ["libz3.dll", "z3.dll"],
        )
        out_dir = os.path.join(self.tmp.name, "out")
        base_zip, base_entry = mk_java_package.find_base_jar([release_zip])
        base_jar = os.path.join(out_dir, "z3-5.0.0.jar")
        os.makedirs(out_dir)
        mk_java_package.copy_base_jar(base_zip, base_entry, base_jar)

        output = os.path.join(out_dir, "z3-5.0.0-win-x64.jar")
        with self.assertRaisesRegex(RuntimeError, "required native libraries"):
            mk_java_package.create_native_jar(base_jar, release_zip, mk_java_package.PLATFORMS[5], output)

    def test_main_creates_all_release_artifacts(self):
        for platform in mk_java_package.PLATFORMS:
            self._write_release_zip(
                self.tmp.name,
                platform["pattern"].replace("*", "5.0.0"),
                platform["libraries"][:2],
            )
        out_dir = os.path.join(self.tmp.name, "dist")

        old_argv = sys.argv
        try:
            sys.argv = [
                "mk_java_package.py",
                "--artifacts-dir",
                self.tmp.name,
                "--out-dir",
                out_dir,
                "--version",
                "5.0.0",
            ]
            mk_java_package.main()
        finally:
            sys.argv = old_argv

        expected = {"z3-5.0.0.jar", "z3-5.0.0.pom"}
        expected.update("z3-5.0.0-{}.jar".format(p["classifier"]) for p in mk_java_package.PLATFORMS)
        self.assertEqual(expected, set(os.listdir(out_dir)))


if __name__ == '__main__':
    unittest.main()
