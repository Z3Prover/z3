############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Unit tests for z3core.py library loading generation.
############################################
import io
import os
import sys
import unittest

# Add the scripts directory to the path so we can import update_api
_SCRIPTS_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _SCRIPTS_DIR not in sys.path:
    sys.path.insert(0, _SCRIPTS_DIR)

import update_api

class TestZ3PyLibraryLoading(unittest.TestCase):
    def _render_preamble(self, soversion):
        buf = io.StringIO()
        update_api.write_core_py_preamble(buf, soversion)
        update_api.write_core_py_post(buf)
        return buf.getvalue()

    def test_linux_loader_uses_soversion_when_available(self):
        text = self._render_preamble("5.0")
        self.assertIn("_sover = '5.0'", text)
        self.assertIn("sys.platform.startswith('linux') and _sover", text)
        # Should have a fallback list with both versioned and unversioned names
        self.assertIn("_lib_names", text)
        self.assertIn("del _lib_names", text)
        self.assertIn('raise Z3Exception("%s not found." % _lib_name)', text)

    def test_linux_loader_falls_back_to_unversioned(self):
        text = self._render_preamble("5.0")
        # The loader should try multiple names (versioned + unversioned fallback)
        self.assertIn("for _name in _lib_names:", text)
        self.assertIn("d = os.path.join(d, _name)", text)
        self.assertIn("_lib = ctypes.CDLL(_name)", text)

    def test_loader_falls_back_to_unsuffixed_name_without_soversion(self):
        text = self._render_preamble(None)
        self.assertIn("_sover = None", text)
        self.assertIn(
            "_lib_name = 'libz3.%s.%s' % (_ext, _sover) if sys.platform.startswith('linux') and _sover else 'libz3.%s' % _ext",
            text,
        )
        self.assertIn("del _lib_name", text)
        self.assertIn("del _sover", text)


if __name__ == '__main__':
    unittest.main()
