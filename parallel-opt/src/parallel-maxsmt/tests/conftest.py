from __future__ import annotations

import sys
from pathlib import Path

# Keep the prototype runnable directly from the checkout without packaging or
# mutating the repository's global Python environment.
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
