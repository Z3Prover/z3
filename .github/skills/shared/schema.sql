-- z3agent schema v1

PRAGMA journal_mode=WAL;
PRAGMA foreign_keys=ON;

CREATE TABLE IF NOT EXISTS runs (
    run_id      INTEGER PRIMARY KEY AUTOINCREMENT,
    skill       TEXT NOT NULL,
    input_hash  TEXT,
    status      TEXT NOT NULL DEFAULT 'running',
    duration_ms INTEGER,
    exit_code   INTEGER,
    timestamp   TEXT NOT NULL DEFAULT (datetime('now'))
);

CREATE INDEX IF NOT EXISTS idx_runs_skill ON runs(skill);
CREATE INDEX IF NOT EXISTS idx_runs_status ON runs(status);

CREATE TABLE IF NOT EXISTS formulas (
    formula_id  INTEGER PRIMARY KEY AUTOINCREMENT,
    run_id      INTEGER REFERENCES runs(run_id) ON DELETE CASCADE,
    smtlib2     TEXT NOT NULL,
    result      TEXT,
    model       TEXT,
    stats       TEXT,
    timestamp   TEXT NOT NULL DEFAULT (datetime('now'))
);

CREATE INDEX IF NOT EXISTS idx_formulas_run ON formulas(run_id);
CREATE INDEX IF NOT EXISTS idx_formulas_result ON formulas(result);

CREATE TABLE IF NOT EXISTS findings (
    finding_id  INTEGER PRIMARY KEY AUTOINCREMENT,
    run_id      INTEGER REFERENCES runs(run_id) ON DELETE CASCADE,
    category    TEXT NOT NULL,
    severity    TEXT,
    file        TEXT,
    line        INTEGER,
    message     TEXT NOT NULL,
    details     TEXT,
    timestamp   TEXT NOT NULL DEFAULT (datetime('now'))
);

CREATE INDEX IF NOT EXISTS idx_findings_run ON findings(run_id);
CREATE INDEX IF NOT EXISTS idx_findings_category ON findings(category);
CREATE INDEX IF NOT EXISTS idx_findings_severity ON findings(severity);

CREATE TABLE IF NOT EXISTS interaction_log (
    log_id      INTEGER PRIMARY KEY AUTOINCREMENT,
    run_id      INTEGER REFERENCES runs(run_id) ON DELETE SET NULL,
    level       TEXT NOT NULL DEFAULT 'info',
    message     TEXT NOT NULL,
    timestamp   TEXT NOT NULL DEFAULT (datetime('now'))
);

CREATE INDEX IF NOT EXISTS idx_log_run ON interaction_log(run_id);
CREATE INDEX IF NOT EXISTS idx_log_level ON interaction_log(level);
