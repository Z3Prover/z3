import os
from more_itertools import iterate
from z3 import *
from multiprocessing import Process
import math, random

MAX_CONFLICTS = 100
MAX_EXAMPLES = 5
bench_dir = "../z3-poly-testing/inputs/QF_NIA_small"

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
    print(f"Applying param state: {param_state}")
    for name, value in param_state:
        s.set(name, value)


def stats_tuple(st):
    def get(key):
        return int(st.get_key_value(key)) if key in st.keys() else 0
    return (get("conflicts"), get("decisions"), get("rlimit count"))


# --------------------------
# Protocol steps
# --------------------------

def run_prefix_step(S, K, clause_limit):
    clauses = []

    def on_clause(premises, deps, clause):
        if len(clauses) < clause_limit:
            clauses.append(clause)

    OnClause(S, on_clause)
    S.set("max_conflicts", K)
    r = S.check()
    return r, clauses

# Replay proof prefix on an existing PPS_solver (no solver recreation)
# Solver continues from its current state.
def replay_prefix_on_pps(PPS_solver, clauses, param_state, budget):
    print(f"[Replaying] on PPS with params={param_state} and budget={budget}")
    apply_param_state(PPS_solver, param_state)

    total_conflicts = total_decisions = total_rlimit = 0

    # For each learned clause Cj = [l1, l2, ...], check ¬(l1 ∨ l2 ∨ ...)
    for idx, Cj in enumerate(clauses):
        if isinstance(Cj, AstVector):
            lits = [Cj[i].translate(PPS_solver.ctx) for i in range(len(Cj))]
        else:
            lits = [l.translate(PPS_solver.ctx) for l in Cj]

        negated_lits = []
        for l in lits:
            negated_lits.append(Not(l))

        PPS_solver.set("max_conflicts", budget)
        r = PPS_solver.check(negated_lits)
        st = PPS_solver.statistics()

        c, d, rl = stats_tuple(st)
        total_conflicts += c
        total_decisions += d
        total_rlimit += rl

        print(f"  [C{idx}] result={r}, conflicts={c}, decisions={d}, rlimit={rl}")

    return (total_conflicts, total_decisions, total_rlimit)


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

# return a variant of the given param state
def perturbate(param_state):
    new_state = []
    for name, val in param_state:
        if isinstance(val, (int, float)) and "restart_factor" in name:
            # perturb multiplicatively +/-10%
            factor = random.choice([0.9, 1.1])
            new_state.append((name, round(val * factor, 3)))
        elif isinstance(val, int) and "phase_caching" in name:
            # pick half or double
            new_val = random.choice([max(1, val // 2), val * 2])
            new_state.append((name, new_val))
        elif name == "smt.relevancy":
            # pick random alternative from {0,1,2}
            new_val = random.choice([0, 1, 2])
            new_state.append((name, new_val))
        else:
            # unchanged
            new_state.append((name, val))
    return new_state

# --------------------------
# Protocol iteration
# --------------------------

def protocol_iteration(filepath, manager, S, PPS_solvers, PPS_states, K, eps=200):
    # --- Proof Prefix Solver (S) ---
    P = manager.best_param_state or BASE_PARAM_CANDIDATES
    apply_param_state(S, P)

    # Run S with max conflicts K
    # Simultaneously, collect subset of conflict clauses from the bounded run of S. 
    # Right now clause collection is pretty naive as we just take the first clause_limit clauses from OnClause
    print(f"[S] Running proof prefix solver with params={P} and max_conflicts={K}")
    r, C_list = run_prefix_step(S, K, clause_limit=MAX_EXAMPLES)

    # If S returns SAT or UNSAT we have a verdict
    # Tell the central dispatch that search is complete and exit
    if r == sat or r == unsat:
        print(f"[S] {os.path.basename(filepath)} → {r} (within max_conflicts={K}). Search complete.")
        manager.mark_complete()
        return

    # For each PPS_i, replay the proof prefix of S
    print(f"[Replaying] Replaying proof prefix on PPS solvers with budget={K + eps}")
    best_state, best_score = replay_proof_prefixes(C_list, PPS_states, PPS_solvers, K, eps)

    if best_state != P:
        print(f"[Dispatch] updating best param state")
        manager.maybe_update_best(best_state, best_score)
        P = best_state

    # Update PPS_0 to use P (if it changed), and update all PPS_i > 0 with new perturbations of P
    PPS_states[0] = P 
    for i in range(1, len(PPS_states)):
        PPS_states[i] = perturbate(P)
        
    return PPS_states


# --------------------------
# Prefix probing thread
# --------------------------

def prefix_probe_thread(filepath, manager):
    # Proof prefix solver S
    S = solver_from_file(filepath)
    apply_param_state(S, BASE_PARAM_CANDIDATES)

    PPS_solvers = []
    PPS_states = []

    # set up the 4 variant parameter probe solvers PPS_1 ... PPS_4 as new contexts on the proof prefix solver S
    for i in range(4):
        st = BASE_PARAM_CANDIDATES if i == 0 else perturbate(BASE_PARAM_CANDIDATES) # PPS_0 uses base params
        ctx = Context()
        PPS_solver = S.translate(ctx)  # clone S (proof prefix) into new context
        apply_param_state(PPS_solver, st)
        PPS_solvers.append(PPS_solver)
        PPS_states.append(st)
        print(f"[Init] PPS_{i} inherited prefix in new context with params={st}")

    # Reuse the same solvers each iteration
    iteration = 0
    while not manager.search_complete:
        print(f"\n[PrefixThread] Iteration {iteration}")
        PPS_states = protocol_iteration(filepath, manager, S, PPS_solvers, PPS_states, K=MAX_CONFLICTS, eps=200)
        iteration += 1


# --------------------------
# Main
# --------------------------

def run_main_solver(filepath):
    set_param("parallel.enable", True)
    main_solver = solver_from_file(filepath)
    apply_param_state(main_solver, BASE_PARAM_CANDIDATES)
    print(f"[Main] Started main solver on {os.path.basename(filepath)} with parallel.enable=True")
    r = main_solver.check()
    print(f"[Main] {os.path.basename(filepath)} → {r}")

def main():
    manager = BatchManager()
    for benchmark in os.listdir(bench_dir):
        if benchmark != "From_T2__hqr.t2_fixed__term_unfeasibility_1_0.smt2":
            continue

        filepath = os.path.join(bench_dir, benchmark)
        prefix_proc = Process(target=prefix_probe_thread, args=(filepath, manager))
        main_proc = Process(target=run_main_solver, args=(filepath,))
        prefix_proc.start()
        main_proc.start()
        prefix_proc.join()
        main_proc.join()

    if manager.best_param_state:
        print(f"\n[GLOBAL] Best parameter state: {manager.best_param_state} with score {manager.best_score}")

if __name__ == "__main__":
    main()
