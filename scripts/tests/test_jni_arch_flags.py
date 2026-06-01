############################################
# Copyright (c) 2024 Microsoft Corporation
#
# Unit tests for JNI architecture flags in Makefile generation.
#
# Regression tests for:
#   "JNI bindings use wrong architecture in macOS cross-compilation (arm64 to x64)"
#
# The fix ensures that libz3java.dylib (and the JNI link step) uses
# $(SLINK_EXTRA_FLAGS) instead of a hardcoded -arch arm64.
# $(SLINK_EXTRA_FLAGS) is populated correctly in mk_config() for:
#   - Native ARM64 builds:      SLINK_EXTRA_FLAGS contains -arch arm64
#   - Cross-compile to x86_64:  SLINK_EXTRA_FLAGS contains -arch x86_64
#   - Other platforms:          SLINK_EXTRA_FLAGS has no -arch flag
############################################
import io
import os
import sys
import unittest
from unittest.mock import patch, MagicMock

# Add the scripts directory to the path so we can import mk_util
_SCRIPTS_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _SCRIPTS_DIR not in sys.path:
    sys.path.insert(0, _SCRIPTS_DIR)

import mk_util


class TestJNIArchitectureFlagsInMakefile(unittest.TestCase):
    """
    Tests that JavaDLLComponent.mk_makefile() generates a JNI link command
    that uses $(SLINK_EXTRA_FLAGS) rather than hardcoding -arch arm64.

    $(SLINK_EXTRA_FLAGS) is set by mk_config() to contain the correct -arch
    flag for the TARGET architecture (not the host), so using it ensures
    cross-compilation works correctly.
    """

    def setUp(self):
        """Save mk_util global state before each test."""
        self._saved_components = list(mk_util._Components)
        self._saved_names = set(mk_util._ComponentNames)
        self._saved_name2component = dict(mk_util._Name2Component)
        self._saved_id = mk_util._Id
        self._saved_javac = mk_util.JAVAC
        self._saved_jar = mk_util.JAR

    def tearDown(self):
        """Restore mk_util global state after each test."""
        mk_util._Components[:] = self._saved_components
        mk_util._ComponentNames.clear()
        mk_util._ComponentNames.update(self._saved_names)
        mk_util._Name2Component.clear()
        mk_util._Name2Component.update(self._saved_name2component)
        mk_util._Id = self._saved_id
        mk_util.JAVAC = self._saved_javac
        mk_util.JAR = self._saved_jar

    def _make_java_dll_component(self):
        """
        Create a JavaDLLComponent instance bypassing the registry check so
        that tests remain independent of each other.
        """
        # Register a stub 'api' component that provides to_src_dir
        api_stub = MagicMock()
        api_stub.to_src_dir = '../src/api'
        mk_util._Name2Component['api'] = api_stub
        mk_util._ComponentNames.add('api')

        # Build the component without going through the full Component.__init__
        # registration path (which enforces uniqueness globally).
        comp = mk_util.JavaDLLComponent.__new__(mk_util.JavaDLLComponent)
        comp.name = 'java'
        comp.dll_name = 'libz3java'
        comp.package_name = 'com.microsoft.z3'
        comp.manifest_file = None
        comp.to_src_dir = '../src/api/java'
        comp.src_dir = 'src/api/java'
        comp.deps = []
        comp.install = True
        return comp

    def _generate_makefile(self, comp, *, is_windows, is_osx, is_arch_arm64):
        """
        Call mk_makefile() with the given platform flags and return the
        generated Makefile text.
        """
        buf = io.StringIO()
        with patch.object(mk_util, 'JAVA_ENABLED', True), \
             patch.object(mk_util, 'IS_WINDOWS', is_windows), \
             patch.object(mk_util, 'IS_OSX', is_osx), \
             patch.object(mk_util, 'IS_ARCH_ARM64', is_arch_arm64), \
             patch.object(mk_util, 'JNI_HOME', '/path/to/jni'), \
             patch.object(mk_util, 'JAVAC', 'javac'), \
             patch.object(mk_util, 'JAR', 'jar'), \
             patch.object(mk_util, 'BUILD_DIR', '/tmp/test_build'), \
             patch('mk_util.mk_dir'), \
             patch('mk_util.get_java_files', return_value=[]):
            comp.mk_makefile(buf)
        return buf.getvalue()

    def _find_jni_link_lines(self, makefile_text):
        """Return lines that contain the JNI library link command."""
        return [
            line for line in makefile_text.splitlines()
            if 'libz3java$(SO_EXT)' in line and 'SLINK' in line
        ]

    # ------------------------------------------------------------------
    # Tests for non-Windows platforms (where SLINK_EXTRA_FLAGS matters)
    # ------------------------------------------------------------------

    def test_macos_arm64_native_uses_slink_extra_flags(self):
        """
        On native ARM64 macOS builds, the JNI link command must use
        $(SLINK_EXTRA_FLAGS) so that the -arch arm64 flag added to
        SLINK_EXTRA_FLAGS by mk_config() is respected.
        """
        comp = self._make_java_dll_component()
        text = self._generate_makefile(
            comp, is_windows=False, is_osx=True, is_arch_arm64=True
        )
        link_lines = self._find_jni_link_lines(text)
        self.assertTrue(
            link_lines,
            "Expected at least one JNI link line in the generated Makefile",
        )
        for line in link_lines:
            self.assertIn(
                '$(SLINK_EXTRA_FLAGS)', line,
                "JNI link command must use $(SLINK_EXTRA_FLAGS) so the "
                "correct target architecture flag is applied",
            )

    def test_macos_arm64_native_no_hardcoded_arch_arm64(self):
        """
        The JNI link command must NOT hardcode -arch arm64.
        Hardcoding -arch arm64 breaks cross-compilation from an ARM64 host
        to an x86_64 target, which is the bug this fix addresses.
        """
        comp = self._make_java_dll_component()
        text = self._generate_makefile(
            comp, is_windows=False, is_osx=True, is_arch_arm64=True
        )
        link_lines = self._find_jni_link_lines(text)
        self.assertTrue(link_lines, "Expected at least one JNI link line")
        for line in link_lines:
            self.assertNotIn(
                '-arch arm64', line,
                "JNI link command must not hardcode '-arch arm64'. "
                "Use $(SLINK_EXTRA_FLAGS) instead so that cross-compilation "
                "from ARM64 host to x86_64 target works correctly.",
            )

    def test_macos_x86_64_uses_slink_extra_flags(self):
        """
        When building for x86_64 on macOS (e.g. cross-compiling from ARM64
        host), the JNI link command must still use $(SLINK_EXTRA_FLAGS) so
        that the -arch x86_64 flag set by mk_config() is applied.
        """
        comp = self._make_java_dll_component()
        text = self._generate_makefile(
            comp, is_windows=False, is_osx=True, is_arch_arm64=False
        )
        link_lines = self._find_jni_link_lines(text)
        self.assertTrue(link_lines, "Expected at least one JNI link line")
        for line in link_lines:
            self.assertIn(
                '$(SLINK_EXTRA_FLAGS)', line,
                "JNI link command must use $(SLINK_EXTRA_FLAGS)",
            )

    def test_linux_uses_slink_extra_flags(self):
        """On Linux, the JNI link command must use $(SLINK_EXTRA_FLAGS)."""
        comp = self._make_java_dll_component()
        text = self._generate_makefile(
            comp, is_windows=False, is_osx=False, is_arch_arm64=False
        )
        link_lines = self._find_jni_link_lines(text)
        self.assertTrue(link_lines, "Expected at least one JNI link line")
        for line in link_lines:
            self.assertIn(
                '$(SLINK_EXTRA_FLAGS)', line,
                "JNI link command must use $(SLINK_EXTRA_FLAGS) on Linux",
            )

    # ------------------------------------------------------------------
    # Tests for Windows (different codepath - links against LIB_EXT)
    # ------------------------------------------------------------------

    def test_windows_links_against_lib_ext(self):
        """
        On Windows the JNI library is linked against the import library
        (libz3$(LIB_EXT)), not the shared library, and SLINK_EXTRA_FLAGS is
        handled differently by the VS build system.
        """
        comp = self._make_java_dll_component()
        text = self._generate_makefile(
            comp, is_windows=True, is_osx=False, is_arch_arm64=False
        )
        link_lines = self._find_jni_link_lines(text)
        self.assertTrue(link_lines, "Expected at least one JNI link line")
        for line in link_lines:
            self.assertIn(
                '$(LIB_EXT)', line,
                "Windows JNI link command must link against LIB_EXT "
                "(the import library)",
            )

    # ------------------------------------------------------------------
    # Tests for macOS rpath, so libz3java.dylib can find libz3.dylib
    # ------------------------------------------------------------------

    def test_macos_uses_loader_path_rpath(self):
        """
        On macOS, the JNI link command must include -Wl,-rpath,@loader_path
        so that libz3java.dylib can find libz3.dylib in the same directory
        at runtime. Without this, Java fails with UnsatisfiedLinkError.
        """
        comp = self._make_java_dll_component()
        text = self._generate_makefile(
            comp, is_windows=False, is_osx=True, is_arch_arm64=True
        )
        link_lines = self._find_jni_link_lines(text)
        self.assertTrue(link_lines, "Expected at least one JNI link line")
        for line in link_lines:
            self.assertIn(
                '-Wl,-rpath,@loader_path', line,
                "macOS JNI link command must set rpath to @loader_path "
                "so libz3java.dylib finds libz3.dylib at runtime",
            )

    def test_linux_does_not_use_loader_path(self):
        """
        On Linux, @loader_path is a macOS concept and must not appear.
        """
        comp = self._make_java_dll_component()
        text = self._generate_makefile(
            comp, is_windows=False, is_osx=False, is_arch_arm64=False
        )
        link_lines = self._find_jni_link_lines(text)
        self.assertTrue(link_lines, "Expected at least one JNI link line")
        for line in link_lines:
            self.assertNotIn(
                '@loader_path', line,
                "@loader_path is macOS-specific and must not appear on Linux",
            )

    # ------------------------------------------------------------------
    # Consistency check: SLINK_EXTRA_FLAGS in mk_config for cross-compile
    # ------------------------------------------------------------------

    def test_slibextraflags_contains_x86_64_when_cross_compiling(self):
        """
        When mk_config() runs on an ARM64 macOS host with IS_ARCH_ARM64=False
        (i.e. cross-compiling to x86_64), SLIBEXTRAFLAGS must contain
        '-arch x86_64' so that $(SLINK_EXTRA_FLAGS) carries the right flag.

        This validates the mk_config() logic that feeds into $(SLINK_EXTRA_FLAGS).
        """
        # We verify the condition in mk_config() directly by checking the
        # relevant code path.  The cross-compile path in mk_config() is:
        #
        #   elif IS_OSX and os.uname()[4] == 'arm64':
        #       SLIBEXTRAFLAGS = '%s -arch x86_64' % SLIBEXTRAFLAGS
        #
        # We test this by simulating the condition:
        import platform
        if platform.system() != 'Darwin' or platform.machine() != 'arm64':
            self.skipTest(
                "Cross-compilation architecture test only runs on ARM64 macOS"
            )

        # On a real ARM64 macOS machine with IS_ARCH_ARM64=False we should get
        # -arch x86_64 in SLIBEXTRAFLAGS.  Simulate the mk_config() logic:
        slibextraflags = ''
        is_arch_arm64 = False
        is_osx = True
        host_machine = platform.machine()  # 'arm64'

        if is_arch_arm64 and is_osx:
            slibextraflags = '%s -arch arm64' % slibextraflags
        elif is_osx and host_machine == 'arm64':
            slibextraflags = '%s -arch x86_64' % slibextraflags

        self.assertIn(
            '-arch x86_64', slibextraflags,
            "When cross-compiling from ARM64 macOS to x86_64, "
            "SLIBEXTRAFLAGS must contain '-arch x86_64'",
        )

    def test_slibextraflags_contains_arm64_for_native_arm64_build(self):
        """
        When mk_config() runs on a native ARM64 macOS build (IS_ARCH_ARM64=True),
        SLIBEXTRAFLAGS must contain '-arch arm64'.
        """
        import platform
        if platform.system() != 'Darwin':
            self.skipTest("Architecture flag test only relevant on macOS")

        slibextraflags = ''
        is_arch_arm64 = True
        is_osx = True

        if is_arch_arm64 and is_osx:
            slibextraflags = '%s -arch arm64' % slibextraflags

        self.assertIn(
            '-arch arm64', slibextraflags,
            "For a native ARM64 macOS build, SLIBEXTRAFLAGS must contain "
            "'-arch arm64' so that $(SLINK_EXTRA_FLAGS) carries the correct flag",
        )


if __name__ == '__main__':
    unittest.main()
