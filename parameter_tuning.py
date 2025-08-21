import os
import z3

MAX_CONFLICTS = 5000
MAX_EXAMPLES = 5
bench_dir = "/home/t-ilshapiro/z3-poly-testing/inputs/QF_LIA"

params = [
    ("smt.arith.eager_eq_axioms", False),
    ("smt.restart_factor", 1.2),
    ("smt.restart_factor", 1.4),
    ("smt.relevancy", 0),
    ("smt.phase_caching_off", 200),
    ("smt.phase_caching_on", 600),
]

# Iterate through all .smt2 files in the directory
num_examples = 0
for benchmark in os.listdir(bench_dir):
    if num_examples > MAX_EXAMPLES:
        break
    if not benchmark.endswith(".smt2"):
        continue

    filepath = os.path.join(bench_dir, benchmark)
    print(f"Running {filepath}\n")

    scores = {}
    for n, v in params:
        s = z3.SimpleSolver()
        s.from_file(filepath)

        s.set("smt.auto_config", False)
        s.set(n, v)
        s.set("smt.max_conflicts", MAX_CONFLICTS)

        r = s.check()
        st = s.statistics()

        try:
            conf = st.get_key_value('conflicts')
        except:
            try:
                conf = st.num_conflicts()
            except AttributeError:
                conf = None

        scores[(n, v)] = conf
    
    num_examples += 1

    print(f"Scores for {benchmark}: {scores}")
