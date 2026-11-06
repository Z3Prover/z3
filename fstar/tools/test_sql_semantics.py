"""Independent SQLite checks of Sql.Examples and SQL semantic edge cases.

BIRD-derived SQL: birdsql/bird_mini_dev, CC BY-SA 4.0, revision
5b256b5a9c17478f06ed6912612e9a14d17065c8, question IDs 9, 49, 55, 297, 346.
Spider-derived SQL: taoyds/spider, Apache-2.0, revision
b7b5b8c890cd30e35427348bb9eb8c6d1350ca7c, evaluation_examples/gold_example.txt.
The query pairs are authored rewrites, not an official equivalence benchmark.
See ../FSTAR_SQL_REPORT.md for attribution, translations, and scope.
"""

import random
import sqlite3
import unittest
from collections import Counter
from contextlib import closing


EQUIVALENCES = [
    ("E01/BIRD297",
     "SELECT notes FROM income WHERE source='Fundraising' AND date_received='2019-09-14'",
     "SELECT notes FROM (SELECT * FROM income WHERE date_received='2019-09-14') "
     "WHERE source='Fundraising'"),
    ("E02/BIRD49",
     "SELECT id FROM cards WHERE borderColor='borderless' AND "
     "(cardKingdomId IS NULL OR cardKingdomFoilId IS NULL) ORDER BY id",
     "SELECT id FROM (SELECT * FROM cards WHERE "
     "cardKingdomId IS NULL OR cardKingdomFoilId IS NULL) "
     "WHERE borderColor='borderless' ORDER BY id"),
    ("E03/BIRD55",
     "SELECT COUNT(DISTINCT c.id) FROM cards c JOIN legalities l ON l.uuid=c.uuid "
     "WHERE l.status='Banned' AND c.borderColor='white'",
     "SELECT COUNT(DISTINCT c.id) FROM cards c JOIN legalities l ON "
     "l.uuid=c.uuid AND l.status='Banned' AND c.borderColor='white'"),
    ("E04/Spider-count",
     "SELECT COUNT(*) FROM singer", "SELECT COUNT(1) FROM singer"),
    ("E05/Spider-between",
     "SELECT location,name FROM stadium WHERE capacity BETWEEN 5000 AND 10000",
     "SELECT location,name FROM stadium WHERE 5000<=capacity AND capacity<=10000"),
    ("E06/nullable-count",
     "SELECT COUNT(age) FROM singer",
     "SELECT COUNT(*) FROM singer WHERE age IS NOT NULL"),
    ("E07/count-case",
     "SELECT COUNT(CASE WHEN a>1 THEN 1 END) FROM t",
     "SELECT COUNT(*) FROM t WHERE a>1"),
    ("E08/union-all-filter",
     "SELECT a FROM (SELECT a FROM t UNION ALL SELECT a FROM u) WHERE a>1",
     "SELECT a FROM t WHERE a>1 UNION ALL SELECT a FROM u WHERE a>1"),
    ("E09/union-all-commute",
     "SELECT a FROM t UNION ALL SELECT a FROM u",
     "SELECT a FROM u UNION ALL SELECT a FROM t"),
    ("E10/projection-pushdown",
     "SELECT c FROM (SELECT a+1 AS c FROM t) WHERE c>2",
     "SELECT a+1 AS c FROM t WHERE a+1>2"),
]

# Each fixture lists the SQL tables, the exact SQL pair, and both expected bags.
# They are schema projections, not downloads of real BIRD/Spider databases.
COUNTEREXAMPLES = [
    ("N01/BIRD9",
     """CREATE TABLE schools(CDSCode TEXT PRIMARY KEY, NCESSchool TEXT);
        CREATE TABLE frpm(CDSCode TEXT PRIMARY KEY REFERENCES schools,
                          "Enrollment (Ages 5-17)" INTEGER);
        INSERT INTO schools VALUES('1751010130583','00001'),('1612910137588','00002');
        INSERT INTO frpm VALUES('1751010130583',100),('1612910137588',100);""",
     """SELECT s.NCESSchool FROM schools s JOIN frpm f ON s.CDSCode=f.CDSCode
        WHERE CAST(f.CDSCode AS INTEGER) IN (1751010130583,1612910137588,1611760134270)
        AND f."Enrollment (Ages 5-17)" =
          (SELECT MAX("Enrollment (Ages 5-17)") FROM frpm
           WHERE CAST(CDSCode AS INTEGER) IN (1751010130583,1612910137588,1611760134270))""",
     """SELECT s.NCESSchool FROM schools s JOIN frpm f ON s.CDSCode=f.CDSCode
        WHERE CAST(f.CDSCode AS INTEGER) IN (1751010130583,1612910137588,1611760134270)
        ORDER BY f."Enrollment (Ages 5-17)" DESC, s.CDSCode DESC LIMIT 1""",
     [("00001",), ("00002",)], [("00001",)]),
    ("N02/BIRD55",
     """CREATE TABLE cards(id INTEGER PRIMARY KEY,uuid TEXT UNIQUE,borderColor TEXT);
        CREATE TABLE legalities(uuid TEXT REFERENCES cards(uuid),status TEXT,format TEXT,
                                PRIMARY KEY(uuid,format));
        INSERT INTO cards VALUES(1,'u','white');
        INSERT INTO legalities VALUES('u','Banned','modern'),('u','Banned','legacy');""",
     "SELECT COUNT(DISTINCT c.id) FROM cards c JOIN legalities l ON l.uuid=c.uuid "
     "WHERE l.status='Banned' AND c.borderColor='white'",
     "SELECT COUNT(c.id) FROM cards c JOIN legalities l ON l.uuid=c.uuid "
     "WHERE l.status='Banned' AND c.borderColor='white'",
     [(1,)], [(2,)]),
    ("N03/BIRD346",
     """CREATE TABLE alignment(id INTEGER PRIMARY KEY,alignment TEXT);
        CREATE TABLE superhero(id INTEGER PRIMARY KEY,
                               alignment_id INTEGER REFERENCES alignment(id));
        INSERT INTO superhero VALUES(1,NULL);""",
     "SELECT COUNT(*) FROM superhero s LEFT JOIN alignment a ON s.alignment_id=a.id "
     "WHERE a.alignment IS NULL OR a.alignment NOT IN ('Good','Bad')",
     "SELECT COUNT(*) FROM superhero s JOIN alignment a ON s.alignment_id=a.id "
     "WHERE a.alignment IS NULL OR a.alignment NOT IN ('Good','Bad')",
     [(1,)], [(0,)]),
    ("N04/Spider-count-age",
     """CREATE TABLE singer(name TEXT,country TEXT,age INTEGER);
        INSERT INTO singer VALUES('Ada','France',NULL);""",
     "SELECT COUNT(*) FROM singer", "SELECT COUNT(age) FROM singer",
     [(1,)], [(0,)]),
    ("N05/Spider-not-in",
     """CREATE TABLE stadium(stadium_id INTEGER PRIMARY KEY,name TEXT);
        CREATE TABLE concert(concert_id INTEGER PRIMARY KEY,
                             stadium_id INTEGER REFERENCES stadium);
        INSERT INTO stadium VALUES(1,'A'); INSERT INTO concert VALUES(1,NULL);""",
     "SELECT name FROM stadium WHERE stadium_id NOT IN (SELECT stadium_id FROM concert)",
     "SELECT name FROM stadium s WHERE NOT EXISTS "
     "(SELECT 1 FROM concert c WHERE c.stadium_id=s.stadium_id)",
     [], [("A",)]),
    ("N06/Spider-distinct",
     """CREATE TABLE singer(name TEXT,country TEXT,age INTEGER);
        INSERT INTO singer VALUES('Ada','France',21),('Bea','France',22);""",
     "SELECT DISTINCT country FROM singer WHERE age>20",
     "SELECT country FROM singer WHERE age>20",
     [("France",)], [("France",), ("France",)]),
    ("N07/sum-empty",
     "CREATE TABLE t(a INTEGER);",
     "SELECT SUM(a) FROM t", "SELECT COALESCE(SUM(a),0) FROM t",
     [(None,)], [(0,)]),
    ("N08/average-null",
     "CREATE TABLE t(a INTEGER); INSERT INTO t VALUES(2),(NULL);",
     "SELECT AVG(a) FROM t", "SELECT 1.0*SUM(a)/COUNT(*) FROM t",
     [(2.0,)], [(1.0,)]),
    ("N09/average-of-averages",
     "CREATE TABLE t(k INTEGER,a INTEGER); INSERT INTO t VALUES(0,2),(0,4),(1,12);",
     "SELECT AVG(a) FROM t", "SELECT AVG(m) FROM (SELECT AVG(a) AS m FROM t GROUP BY k)",
     [(6.0,)], [(7.5,)]),
    ("N10/union",
     "", "SELECT 1 UNION ALL SELECT 1", "SELECT 1 UNION SELECT 1",
     [(1,), (1,)], [(1,)]),
    ("N11/outer-predicate",
     """CREATE TABLE l(id INTEGER PRIMARY KEY);
        CREATE TABLE r(id INTEGER,x INTEGER); INSERT INTO l VALUES(1);""",
     "SELECT l.id,r.id,r.x FROM l LEFT JOIN r ON l.id=r.id WHERE r.x>0",
     "SELECT l.id,r.id,r.x FROM l LEFT JOIN r ON l.id=r.id AND r.x>0",
     [], [(1, None, None)]),
    ("N12/order-limit",
     "CREATE TABLE t(a INTEGER); INSERT INTO t VALUES(2),(1);",
     "SELECT a FROM t ORDER BY a DESC LIMIT 1",
     "SELECT a FROM t ORDER BY a ASC LIMIT 1",
     [(2,)], [(1,)]),
]


class SqlSemanticsTests(unittest.TestCase):
    def test_equivalences_on_generated_databases(self):
        rng = random.Random(20261105)
        for iteration in range(100):
            with closing(sqlite3.connect(":memory:")) as db:
                db.executescript("""
                    PRAGMA foreign_keys=ON;
                    CREATE TABLE income(notes TEXT,source TEXT,date_received TEXT);
                    CREATE TABLE cards(id INTEGER PRIMARY KEY,uuid TEXT UNIQUE,
                                       borderColor TEXT,cardKingdomId INTEGER,
                                       cardKingdomFoilId INTEGER);
                    CREATE TABLE legalities(uuid TEXT REFERENCES cards(uuid),
                                            status TEXT,format TEXT,PRIMARY KEY(uuid,format));
                    CREATE TABLE singer(name TEXT,country TEXT,age INTEGER);
                    CREATE TABLE stadium(location TEXT,name TEXT,capacity INTEGER);
                    CREATE TABLE t(a INTEGER); CREATE TABLE u(a INTEGER);
                """)
                for i in range(iteration % 10):
                    db.execute("INSERT INTO income VALUES(?,?,?)",
                               (str(i), rng.choice([None, "Fundraising", "Other"]),
                                rng.choice([None, "2019-09-14", "2020-01-01"])))
                    db.execute("INSERT INTO cards VALUES(?,?,?,?,?)",
                               (i, str(i), rng.choice([None, "white", "borderless"]),
                                rng.choice([None, 1]), rng.choice([None, 2])))
                    for fmt in range(rng.randrange(4)):
                        db.execute("INSERT INTO legalities VALUES(?,?,?)",
                                   (str(i), rng.choice([None, "Banned", "Legal"]), str(fmt)))
                    db.execute("INSERT INTO singer VALUES(?,?,?)",
                               (str(i), rng.choice([None, "France", "UK"]),
                                rng.choice([None, 20, 21, 40])))
                    db.execute("INSERT INTO stadium VALUES(?,?,?)",
                               ("L", str(i), rng.choice([None, 4999, 5000, 10000, 10001])))
                    db.execute("INSERT INTO t VALUES(?)", (rng.choice([None, 0, 1, 2, 3]),))
                    db.execute("INSERT INTO u VALUES(?)", (rng.choice([None, 0, 1, 2, 3]),))
                for name, left, right in EQUIVALENCES:
                    with self.subTest(case=name, iteration=iteration):
                        a, b = list(db.execute(left)), list(db.execute(right))
                        if name == "E02/BIRD49":
                            self.assertEqual(a, b)
                        else:
                            self.assertEqual(Counter(a), Counter(b))

    def test_counterexample_databases(self):
        for name, setup, left, right, expected_a, expected_b in COUNTEREXAMPLES:
            with self.subTest(case=name), closing(sqlite3.connect(":memory:")) as db:
                db.execute("PRAGMA foreign_keys=ON")
                db.executescript(setup)
                self.assertEqual(list(db.execute("PRAGMA foreign_key_check")), [])
                a, b = list(db.execute(left)), list(db.execute(right))
                self.assertEqual(Counter(a), Counter(expected_a))
                self.assertEqual(Counter(b), Counter(expected_b))
                self.assertNotEqual(Counter(a), Counter(b))

    def test_semantic_edges(self):
        with closing(sqlite3.connect(":memory:")) as db:
            checks = [
                ("SELECT NULL=NULL, NOT NULL, NULL OR 1, NULL AND 0",
                 [(None, None, 1, 0)]),
                ("SELECT NULL IN (SELECT 1 WHERE 0), 1 IN (NULL,1), 1 IN (NULL,2)",
                 [(0, 1, None)]),
                ("SELECT COUNT(*),COUNT(x),SUM(x),AVG(x),MIN(x),MAX(x) "
                 "FROM (SELECT 1 AS x WHERE 0)", [(0, 0, None, None, None, None)]),
                ("SELECT x,COUNT(*) FROM (SELECT NULL AS x UNION ALL SELECT 1 "
                 "UNION ALL SELECT NULL) GROUP BY x HAVING COUNT(*)>1", [(None, 2)]),
                ("SELECT NULL INTERSECT SELECT NULL", [(None,)]),
                ("SELECT NULL EXCEPT SELECT NULL", []),
                ("SELECT x FROM (SELECT 1 AS x UNION ALL SELECT 2 UNION ALL SELECT 3) "
                 "ORDER BY x LIMIT 1 OFFSET 1", [(2,)]),
                ("SELECT 'abz' LIKE 'a%z', '' LIKE '%%', '' LIKE '_', "
                 "'%' LIKE '\\%' ESCAPE '\\', NULL LIKE '%'", [(1, 1, 0, 1, None)]),
                ("SELECT CASE WHEN NULL THEN 1 ELSE 2 END, 1.0/0", [(2, None)]),
            ]
            for sql, expected in checks:
                with self.subTest(sql=sql):
                    self.assertEqual(list(db.execute(sql)), expected)


if __name__ == "__main__":
    print(f"SQLite {sqlite3.sqlite_version}: 10 equivalences x 100 databases, "
          "12 counterexamples, 9 edge checks", flush=True)
    unittest.main(verbosity=2)
