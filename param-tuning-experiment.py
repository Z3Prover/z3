import os
import z3

MAX_CONFLICTS = 1000
MAX_EXAMPLES = 5
bench_dir = "C:/tmp/parameter-tuning"

# Baseline parameter candidates (you can grow this)
BASE_PARAM_CANDIDATES = [
    ("smt.arith.eager_eq_axioms", False),
    ("smt.restart_factor", 1.2),
    ("smt.relevancy", 0),
    ("smt.phase_caching_off", 200),
    ("smt.phase_caching_on", 600),
]

# --------------------------
# One class: BatchManager
# --------------------------
class BatchManager:
    def __init__(self):
        self.best_param_state = None
        self.best_score = (10**9, 10**9, 10**9)  # (conflicts, decisions, rlimit)
        self.search_complete = False

    def mark_complete(self):
        self.search_complete = True

    def maybe_update_best(self, param_state, triple):
        if self._better(triple, self.best_score):
            self.best_param_state = list(param_state)
            self.best_score = triple

    @staticmethod
    def _better(a, b):
        return a < b  # lexicographic

# -------------------
# Helpers
# -------------------

def get_stat_int(st, key):
    try:
        v = st.get_key_value(key)
        if isinstance(v, (int, float)):
            return int(v)
    except Exception:
        pass
    if key == "decisions" and hasattr(st, "decisions"):
        try:
            return int(st.decisions())
        except Exception:
            return 0
    return 0

def solver_from_file(filepath):
    s = z3.Solver()
    s.set("smt.auto_config", False)
    s.from_file(filepath)
    return s

def apply_param_state(s, param_state):
    for name, value in param_state:
        s.set(name, value)

def stats_tuple(st):
    return (
        get_stat_int(st, "conflicts"),
        get_stat_int(st, "decisions"),
        get_stat_int(st, "rlimit count"),
    )

# --------------------------
# Protocol steps
# --------------------------

def run_prefix_step(S, K):
    S.set("smt.K", K)
    r = S.check()
    return r, S.statistics()

def collect_conflict_clauses_placeholder(S, limit = 4):
    return []

def replay_prefix_on_pps(filepath, clauses, param_state, budget):
    if not clauses:
        s = solver_from_file(filepath)
        apply_param_state(s, param_state)
        s.set("smt.K", budget)
        _ = s.check()
        st = s.statistics()
        return stats_tuple(st)

    total_conflicts = 0
    total_decisions = 0
    total_rlimit = 0

    PPS = solver_from_file(filepath)
    apply_param_state(PPS, param_state)

    for Cj in clauses:
        PPS.set("smt.K", budget)
        assumption = z3.Not(Cj)
        PPS.check([assumption])
        st = PPS.statistics()
        c, d, rl = stats_tuple(st)
        total_conflicts += c
        total_decisions += d
        total_rlimit += rl

    return (total_conflicts, total_decisions, total_rlimit)

def choose_best_pps(filepath, clauses, base_param_state, candidate_param_states, K, eps = 200):
    budget = K + eps
    best_param_state = base_param_state
    best_score = (10**9, 10**9, 10**9)

    score0 = replay_prefix_on_pps(filepath, clauses, base_param_state, budget)
    if score0 < best_score:
        best_param_state, best_score = base_param_state, score0

    for p_state in candidate_param_states:
        sc = replay_prefix_on_pps(filepath, clauses, p_state, budget)
        if sc < best_score:
            best_param_state, best_score = p_state, sc

    return best_param_state, best_score

def next_perturbations(around_state):
    outs = []
    for name, val in around_state:
        if isinstance(val, (int, float)) and "restart_factor" in name:
            outs.append([(name, float(val) * 0.9)])
            outs.append([(name, float(val) * 1.1)])
        elif isinstance(val, int) and "phase_caching" in name:
            k = max(1, int(val))
            outs.append([(name, k // 2)])
            outs.append([(name, k * 2)])
        else:
            if name == "smt.relevancy":
                outs.extend([[(name, 0)], [(name, 1)], [(name, 2)]])
    return outs or [around_state]

# --------------------------
# Protocol iteration
# --------------------------

def protocol_iteration(filepath, manager, K, eps=200):
    S = solver_from_file(filepath) # Proof Prefix solver
    P = manager.best_param_state or BASE_PARAM_CANDIDATES # current optimal parameter setting
    apply_param_state(S, P)

    # Run S with max conflicts K
    r, st = run_prefix_step(S, K)

    # If S returns SAT, or UNSAT we have a verdict. Tell the central dispatch that search is complete. Exit.
    if r == z3.sat or r == z3.unsat:
        print(f"[S] {os.path.basename(filepath)} → {r} (within max_conflicts={K}). Search complete.")
        manager.mark_complete()
        return

    # Collect a subset of conflict clauses from the bounded run of S. Call these clauses C1, ..., Cl.
    C_list = collect_conflict_clauses_placeholder(S)
    print(f"[S] collected {len(C_list)} conflict clauses for replay")

    PPS0 = P
    PPS_perturb = next_perturbations(P)

    best_state, best_score = choose_best_pps(filepath, C_list, PPS0, PPS_perturb, K, eps)
    print(f"[Replay] best={best_state} score(conf, dec, rlim)={best_score}")

    if best_state != P:
        print(f"[Dispatch] updating best param state")
        manager.maybe_update_best(best_state, best_score)
        P = best_state

    PPS0 = P
    PPS_perturb = next_perturbations(P)
    print(f"[Dispatch] PPS_0 := {PPS0}, new perturbations: {PPS_perturb}")

# --------------------------
# Main
# --------------------------

def main():
    manager = BatchManager()

    for benchmark in os.listdir(bench_dir):
        if benchmark != "From_T2__hqr.t2_fixed__term_unfeasibility_1_0.smt2":
            continue

        filepath = os.path.join(bench_dir, benchmark)
        protocol_iteration(filepath, manager, K=MAX_CONFLICTS, eps=200)

    if manager.best_param_state:
        print(f"\n[GLOBAL] Best parameter state: {manager.best_param_state} with score {manager.best_score}")

if __name__ == "__main__":
    main()
