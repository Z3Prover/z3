from __future__ import annotations

import json

import pytest

from pmaxsmt.cli import main


@pytest.mark.parametrize(
    "extra",
    (
        ("--threads", "8"),
        ("--roles", "hs=1,mss=0,backbone=0,maxres=0,zopt=0"),
    ),
)
def test_sequential_rejects_parallel_allocation_options(extra, capsys):
    exit_code = main(["solve", "unused.wcnf", "--sequential", *extra])
    payload = json.loads(capsys.readouterr().out)

    assert exit_code == 2
    assert "--sequential cannot be combined" in payload["error"]
