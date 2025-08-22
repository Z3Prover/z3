import os
import z3

MAX_CONFLICTS = 5000
MAX_EXAMPLES = 5
bench_dir = "/home/t-ilshapiro/z3-poly-testing/inputs/QF_LIA"
bench_dir = "C:/tmp/parameter-tuning"

params = [
    ("smt.arith.eager_eq_axioms", False),
    ("smt.restart_factor", 1.2),
    ("smt.restart_factor", 1.4),
    ("smt.relevancy", 0),
    ("smt.phase_caching_off", 200),
    ("smt.phase_caching_on", 600),

# For LIA: 
# arith.eager_eq_axioms
# arith.branch_cut_ratio
# arith.bprop_on_pivoted_rows
# arith.int_eq_branch
# arith.propagate_eqs 
# restart_strategy

# For NIA, Certora
# arith.nl.branching
# etc many arith.nl options
]


def score_benchmark(filepath):
    scores = {}
    print(f"Running {filepath}\n")
    for n, v in params:
        s = z3.SimpleSolver()
        s.from_file(filepath)

        s.set("smt.auto_config", False)
        s.set(n, v)
        s.set("smt.max_conflicts", MAX_CONFLICTS)

        r = s.check()
        st = s.statistics()

        # TODO: if r != unknown, the score should be better than
        # scores of runs that don't finish

        try:
            d = st.get_key_value('decisions')
        except:
            try:
                d = st.decisions()
            except AttributeError:
                d = None

        print(n, v, d, st)

        scores[(n, v)] = d
   return scores

# Iterate through all .smt2 files in the directory
num_examples = 0
for benchmark in os.listdir(bench_dir):
    if num_examples > MAX_EXAMPLES:
        break
    if not benchmark.endswith(".smt2"):
        continue

    filepath = os.path.join(bench_dir, benchmark)

    scores = score_benchmark(filepath)

    evaluate_score(filepath, scores)
    
    num_examples += 1

    print(f"Scores for {benchmark}: {scores}")

def evaluate_score(filepath, scores):
    # Pick the top score, 
    # Run the benchmark with default config and with updated config based on best score.
    # Check if time improves.
    pass

