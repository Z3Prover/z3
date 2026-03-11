#!/usr/bin/env python3
"""
z3db: shared library and CLI for Z3 skill scripts.

Library usage:
    from z3db import Z3DB, find_z3, run_z3

CLI usage:
    python z3db.py init
    python z3db.py status
    python z3db.py log [--run-id N]
    python z3db.py runs [--skill solve] [--last N]
    python z3db.py query "SELECT ..."
"""

import argparse
import hashlib
import json
import logging
import os
import re
import shutil
import sqlite3
import subprocess
import sys
import time
from pathlib import Path
from typing import Optional

SCHEMA_PATH = Path(__file__).parent / "schema.sql"
DEFAULT_DB_DIR = ".z3-agent"
DEFAULT_DB_NAME = "z3agent.db"

logger = logging.getLogger("z3agent")


def setup_logging(debug: bool = False):
    level = logging.DEBUG if debug else logging.INFO
    fmt = (
        "[%(levelname)s] %(message)s"
        if not debug
        else "[%(levelname)s %(asctime)s] %(message)s"
    )
    logging.basicConfig(level=level, format=fmt, stream=sys.stderr)


class Z3DB:
    """SQLite handle for z3agent.db, tracks runs, formulas, findings, logs."""

    def __init__(self, db_path: Optional[str] = None):
        if db_path is None:
            db_dir = Path(DEFAULT_DB_DIR)
            db_dir.mkdir(exist_ok=True)
            db_path = str(db_dir / DEFAULT_DB_NAME)
        self.db_path = db_path
        self.conn = sqlite3.connect(db_path)
        self.conn.execute("PRAGMA foreign_keys=ON")
        self.conn.row_factory = sqlite3.Row
        self._init_schema()

    def _init_schema(self):
        self.conn.executescript(SCHEMA_PATH.read_text())

    def close(self):
        self.conn.close()

    def start_run(self, skill: str, input_text: str = "") -> int:
        input_hash = hashlib.sha256(input_text.encode()).hexdigest()[:16]
        cur = self.conn.execute(
            "INSERT INTO runs (skill, input_hash) VALUES (?, ?)",
            (skill, input_hash),
        )
        self.conn.commit()
        run_id = cur.lastrowid
        logger.debug("started run %d (skill=%s, hash=%s)", run_id, skill, input_hash)
        return run_id

    def finish_run(
        self, run_id: int, status: str, duration_ms: int, exit_code: int = 0
    ):
        self.conn.execute(
            "UPDATE runs SET status=?, duration_ms=?, exit_code=? WHERE run_id=?",
            (status, duration_ms, exit_code, run_id),
        )
        self.conn.commit()
        logger.debug("finished run %d: %s (%dms)", run_id, status, duration_ms)

    def log_formula(
        self,
        run_id: int,
        smtlib2: str,
        result: str = None,
        model: str = None,
        stats: dict = None,
    ) -> int:
        cur = self.conn.execute(
            "INSERT INTO formulas (run_id, smtlib2, result, model, stats) "
            "VALUES (?, ?, ?, ?, ?)",
            (run_id, smtlib2, result, model, json.dumps(stats) if stats else None),
        )
        self.conn.commit()
        return cur.lastrowid

    def log_finding(
        self,
        run_id: int,
        category: str,
        message: str,
        severity: str = None,
        file: str = None,
        line: int = None,
        details: dict = None,
    ) -> int:
        cur = self.conn.execute(
            "INSERT INTO findings (run_id, category, severity, file, line, "
            "message, details) VALUES (?, ?, ?, ?, ?, ?, ?)",
            (
                run_id,
                category,
                severity,
                file,
                line,
                message,
                json.dumps(details) if details else None,
            ),
        )
        self.conn.commit()
        return cur.lastrowid

    def log(self, message: str, level: str = "info", run_id: int = None):
        """Write to stderr and to the interaction_log table."""
        getattr(logger, level, logger.info)(message)
        self.conn.execute(
            "INSERT INTO interaction_log (run_id, level, message) " "VALUES (?, ?, ?)",
            (run_id, level, message),
        )
        self.conn.commit()

    def get_runs(self, skill: str = None, last: int = 10):
        sql = "SELECT * FROM runs"
        params = []
        if skill:
            sql += " WHERE skill = ?"
            params.append(skill)
        sql += " ORDER BY run_id DESC LIMIT ?"
        params.append(last)
        return self.conn.execute(sql, params).fetchall()

    def get_status(self) -> dict:
        rows = self.conn.execute(
            "SELECT status, COUNT(*) as cnt FROM runs GROUP BY status"
        ).fetchall()
        total = sum(r["cnt"] for r in rows)
        by_status = {r["status"]: r["cnt"] for r in rows}
        last = self.conn.execute(
            "SELECT timestamp FROM runs ORDER BY run_id DESC LIMIT 1"
        ).fetchone()
        return {
            "total": total,
            **by_status,
            "last_run": last["timestamp"] if last else None,
        }

    def get_logs(self, run_id: int = None, last: int = 50):
        if run_id:
            return self.conn.execute(
                "SELECT * FROM interaction_log WHERE run_id=? "
                "ORDER BY log_id DESC LIMIT ?",
                (run_id, last),
            ).fetchall()
        return self.conn.execute(
            "SELECT * FROM interaction_log ORDER BY log_id DESC LIMIT ?", (last,)
        ).fetchall()

    def query(self, sql: str):
        return self.conn.execute(sql).fetchall()


def find_z3(hint: str = None) -> str:
    """Locate the z3 binary: explicit path > build dirs > PATH."""
    candidates = []
    if hint:
        candidates.append(hint)

    repo_root = _find_repo_root()
    if repo_root:
        for build_dir in ["build", "build/release", "build/debug"]:
            candidates.append(str(repo_root / build_dir / "z3"))

    path_z3 = shutil.which("z3")
    if path_z3:
        candidates.append(path_z3)

    for c in candidates:
        p = Path(c)
        if p.is_file() and os.access(p, os.X_OK):
            logger.debug("found z3: %s", p)
            return str(p)

    logger.error("z3 binary not found. Searched: %s", candidates)
    sys.exit(1)


def _find_repo_root() -> Optional[Path]:
    d = Path.cwd()
    for _ in range(10):
        if (d / "CMakeLists.txt").exists() and (d / "src").is_dir():
            return d
        parent = d.parent
        if parent == d:
            break
        d = parent
    return None


def run_z3(
    formula: str,
    z3_bin: str = None,
    timeout: int = 30,
    args: list = None,
    debug: bool = False,
) -> dict:
    """Pipe an SMT-LIB2 formula into z3 -in, return parsed output."""
    z3_path = find_z3(z3_bin)
    cmd = [z3_path, "-in"] + (args or [])

    logger.debug("cmd: %s", " ".join(cmd))
    logger.debug("stdin:\n%s", formula)

    start = time.monotonic()
    try:
        proc = subprocess.run(
            cmd,
            input=formula,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        duration_ms = int((time.monotonic() - start) * 1000)
        logger.warning("z3 timed out after %dms", duration_ms)
        return {
            "stdout": "",
            "stderr": "timeout",
            "exit_code": -1,
            "duration_ms": duration_ms,
            "result": "timeout",
        }

    duration_ms = int((time.monotonic() - start) * 1000)

    logger.debug("exit_code=%d duration=%dms", proc.returncode, duration_ms)
    logger.debug("stdout:\n%s", proc.stdout)
    if proc.stderr:
        logger.debug("stderr:\n%s", proc.stderr)

    first_line = proc.stdout.strip().split("\n")[0].strip() if proc.stdout else ""
    result = first_line if first_line in ("sat", "unsat", "unknown") else "error"

    return {
        "stdout": proc.stdout,
        "stderr": proc.stderr,
        "exit_code": proc.returncode,
        "duration_ms": duration_ms,
        "result": result,
    }


def parse_model(stdout: str) -> Optional[dict]:
    """Pull define-fun entries from a (get-model) response."""
    model = {}
    for m in re.finditer(r"\(define-fun\s+(\S+)\s+\(\)\s+\S+\s+(.+?)\)", stdout):
        model[m.group(1)] = m.group(2).strip()
    return model if model else None


def parse_stats(stdout: str) -> Optional[dict]:
    """Parse :key value pairs from z3 -st output."""
    stats = {}
    for m in re.finditer(r":(\S+)\s+([\d.]+)", stdout):
        key, val = m.group(1), m.group(2)
        stats[key] = float(val) if "." in val else int(val)
    return stats if stats else None


def parse_unsat_core(stdout: str) -> Optional[list]:
    for line in stdout.strip().split("\n"):
        line = line.strip()
        if line.startswith("(") and not line.startswith("(error"):
            labels = line.strip("()").split()
            if labels:
                return labels
    return None


def cli():
    parser = argparse.ArgumentParser(
        description="Z3 Agent database CLI",
        prog="z3db",
    )
    parser.add_argument("--db", default=None, help="path to z3agent.db")
    parser.add_argument("--debug", action="store_true", help="verbose output")

    sub = parser.add_subparsers(dest="command")

    sub.add_parser("init", help="initialize the database")

    sub.add_parser("status", help="show run summary")

    log_p = sub.add_parser("log", help="show interaction log")
    log_p.add_argument("--run-id", type=int, help="filter by run ID")
    log_p.add_argument("--last", type=int, default=50)

    runs_p = sub.add_parser("runs", help="list runs")
    runs_p.add_argument("--skill", help="filter by skill name")
    runs_p.add_argument("--last", type=int, default=10)

    query_p = sub.add_parser("query", help="run raw SQL")
    query_p.add_argument("sql", help="SQL query string")

    args = parser.parse_args()
    setup_logging(args.debug)

    db = Z3DB(args.db)

    if args.command == "init":
        print(f"Database initialized at {db.db_path}")

    elif args.command == "status":
        s = db.get_status()
        print(
            f"Runs: {s['total']}"
            f" | success: {s.get('success', 0)}"
            f" | error: {s.get('error', 0)}"
            f" | timeout: {s.get('timeout', 0)}"
            f" | Last: {s['last_run'] or 'never'}"
        )

    elif args.command == "log":
        for row in db.get_logs(args.run_id, args.last):
            print(
                f"[{row['level']}] {row['timestamp']} "
                f"(run {row['run_id']}): {row['message']}"
            )

    elif args.command == "runs":
        for row in db.get_runs(args.skill, args.last):
            print(
                f"#{row['run_id']} {row['skill']} {row['status']} "
                f"{row['duration_ms']}ms @ {row['timestamp']}"
            )

    elif args.command == "query":
        for row in db.query(args.sql):
            print(dict(row))

    else:
        parser.print_help()

    db.close()


if __name__ == "__main__":
    cli()
