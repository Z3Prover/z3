import os
from z3 import *
import threading
import math

MAX_CONFLICTS = 1000
MAX_EXAMPLES = 5
bench_dir = "C:/tmp/parameter-tuning"

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
        self.best_score = (math.inf, math.inf, math.inf)
        self.search_complete = False

    def mark_complete(self):
        self.search_complete = True

    def maybe_update_best(self, param_state, triple):
        if self._better(triple, self.best_score):
            self.best_param_state = list(param_state)
            self.best_score = triple

    @staticmethod
    def _better(a, b):
        return a < b  # lexicographic compare


# -------------------
# Helpers
# -------------------

def solver_from_file(filepath):
    s = Solver()
    s.set("smt.auto_config", False)
    s.from_file(filepath)
    return s


def apply_param_state(s, param_state):
    for name, value in param_state:
        s.set(name, value)


def stats_tuple(st):
    return (
        int(st["conflicts"]),
        int(st["decisions"]),
        int(st["rlimit count"]),
    )


# --------------------------
# Protocol steps
# --------------------------

def run_prefix_step(S, K):
    S.set("smt.max_conflicts", K)
    r = S.check()
    return r, S.statistics()


def collect_conflict_clauses_placeholder(S, limit=4):
    return []

# Replay proof prefix on an existing PPS_solver (no solver recreation)
# Solver continues from its current state.
def replay_prefix_on_pps(PPS_solver, clauses, param_state, budget):
    apply_param_state(PPS_solver, param_state)
    PPS_solver.set("smt.max_conflicts", budget)

    asms = []
    for Cj in clauses:
      PPS_solver.set("smt.max_conflicts", budget)
      asms.append(Not(Cj))

    PPS_solver.check(asms)
    st = PPS_solver.statistics()

    return stats_tuple(st)


# For each PPS_i, replay the proof prefix of S
def replay_proof_prefixes(clauses, param_states, PPS_solvers, K, eps=200):
    budget = K + eps
    base_param_state, candidate_param_states = param_states[0], param_states[1:]

    # PPS_0 (baseline)
    score0 = replay_prefix_on_pps(PPS_solvers[0], clauses, base_param_state, budget)
    best_param_state, best_score = base_param_state, score0

    # PPS_i, i > 0
    for i, p_state in enumerate(candidate_param_states, start=1):
        score = replay_prefix_on_pps(PPS_solvers[i], clauses, p_state, budget)
        if score < best_score:
            best_param_state, best_score = p_state, score

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
        elif name == "smt.relevancy":
            outs.extend([[(name, 0)], [(name, 1)], [(name, 2)]])
    return outs or [around_state]

# --------------------------
# Protocol iteration
# --------------------------

def protocol_iteration(filepath, manager, S, PPS_solvers, PPS_states, K, eps=200):
    # --- Proof Prefix Solver (S) ---
    P = manager.best_param_state or BASE_PARAM_CANDIDATES
    apply_param_state(S, P)

    # Run S with max conflicts K
    r, st = run_prefix_step(S, K)

    # If S returns SAT or UNSAT we have a verdict
    # Tell the central dispatch that search is complete and exit
    if r == sat or r == unsat:
        print(f"[S] {os.path.basename(filepath)} → {r} (within max_conflicts={K}). Search complete.")
        manager.mark_complete()
        return

    # Collect subset of conflict clauses from the bounded run of S. Call these clauses C1...Cl
    C_list = collect_conflict_clauses_placeholder(S)
    print(f"[S] collected {len(C_list)} conflict clauses for replay")

    # For each PPS_i, replay the proof prefix of S
    best_state, best_score = replay_proof_prefixes(C_list, PPS_states, PPS_solvers, K, eps)
    print(f"[Replay] best={best_state} score(conf, dec, rlim)={best_score}")

    if best_state != P:
        print(f"[Dispatch] updating best param state")
        manager.maybe_update_best(best_state, best_score)
        P = best_state

    # Update PPS_0 to use P (if it changed), and update all PPS_i > 0 with new perturbations of P
    PPS_states[0] = P
    new_perturb = next_perturbations(P)
    for i in range(1, len(PPS_states)):
        PPS_states[i] = new_perturb[i - 1]
    print(f"[Dispatch] PPS_0 := {PPS_states[0]}, new perturbations: {new_perturb}")


# --------------------------
# Prefix probing thread
# --------------------------

def prefix_probe_thread(filepath, manager):
    # Proof prefix solver S
    S = solver_from_file(filepath)
    apply_param_state(S, BASE_PARAM_CANDIDATES)

    PPS_solvers = []
    PPS_states = []
    PPS_states.append(list(BASE_PARAM_CANDIDATES))
    perturbations = next_perturbations(BASE_PARAM_CANDIDATES)

    for i in range(4):
        st = perturbations[i] if i < len(perturbations) else BASE_PARAM_CANDIDATES
        PPS_solver = Solver()
        apply_param_state(PPS_solver, st)
        PPS_solvers.append(PPS_solver)
        PPS_states.append(st)
        print(f"[Init] PPS_{i} initialized with params={st}")

    # Reuse the same solvers each iteration
    for iteration in range(3):  # run a few iterations
        if manager.search_complete:
            break
        print(f"\n[PrefixThread] Iteration {iteration}")
        protocol_iteration(filepath, manager, S, PPS_solvers, PPS_states, K=MAX_CONFLICTS, eps=200)


# --------------------------
# Main
# --------------------------

def main():
    manager = BatchManager()

    for benchmark in os.listdir(bench_dir):
        if benchmark != "From_T2__hqr.t2_fixed__term_unfeasibility_1_0.smt2":
            continue

        filepath = os.path.join(bench_dir, benchmark)
        prefix_thread = threading.Thread(target=prefix_probe_thread, args=(filepath, manager))
        prefix_thread.start()

        # main thread can perform monitoring or waiting
        while prefix_thread.is_alive():
            if manager.search_complete:
                break

        prefix_thread.join()

    if manager.best_param_state:
        print(f"\n[GLOBAL] Best parameter state: {manager.best_param_state} with score {manager.best_score}")


if __name__ == "__main__":
    main()
