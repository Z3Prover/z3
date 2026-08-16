from __future__ import annotations

import io
import json
import random
import threading
from pathlib import Path
import time

import pytest
import z3
from pmaxsmt import (
    ParallelMaxSMTSolver,
    Problem,
    RoleSpec,
    WeightedObjective,
    parse_file,
    parse_wcnf,
    verify_certificate,
    z3_optimize_baseline,
)
from pmaxsmt.certify import CertificateError, verify_certificate_or_raise
from pmaxsmt.coordinator import Coordinator
from pmaxsmt.objective import UnweightedObjective
from pmaxsmt.trace import TraceWriter
from pmaxsmt.workers.backbone_worker import BackboneWorker
from pmaxsmt.workers.mss_worker import MSSWorker


def hs_roles() -> RoleSpec:
    return RoleSpec(hs=1, mss=0, backbone=0, maxres=0, zopt=0)


def test_wcnf_formats_and_smt2_parse(tmp_path):
    new = "h 1 0\n1 -1 0\n2 2 0\n"
    p = parse_wcnf(new)
    assert len(p.hard) == 1 and p.weights == (1, 2)
    old = "p wcnf 1 2 10\n10 1 0\n3 -1 0\n"
    q = parse_wcnf(old)
    assert len(q.hard) == 1 and q.weights == (3,)
    smt = tmp_path / "x.smt2"
    smt.write_text(
        "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (>= x 0))\n"
        "(assert-soft (= x 1) :weight 3)\n(assert-soft (= x 2) :weight 5)\n(check-sat)\n",
        encoding="utf-8",
    )
    r = parse_file(smt)
    assert r.source_format == "smt2"
    assert r.weights == (3, 5)
    assert len(r.translate(z3.Context()).soft) == 2

def test_plain_cnf_clauses_are_unit_weight_soft_without_dropping_literals():
    problem = parse_wcnf("p cnf 3 3\n1 0\n2 -3 0\n3 0\n")
    assert problem.hard == ()
    assert problem.weights == (1, 1, 1)
    assert problem.soft[0].formula == "x1"
    assert problem.soft[1].formula == "(or x2 (not x3))"
    assert problem.soft[2].formula == "x3"

    root = Path(__file__).resolve().parents[1]
    manifest = json.loads((root / "benchmarks" / "manifest.json").read_text(encoding="utf-8"))
    expected = next(row for row in manifest if row["path"] == "public/dpmaxsat_test.cnf")
    shipped = parse_file(root / "benchmarks" / expected["path"])
    assert len(shipped.hard) == expected["nhard"]
    assert len(shipped.soft) == expected["nsoft"]
    assert sum(shipped.weights) == expected["total_soft_weight"]


def _expected(problem: Problem) -> int:
    ctx = z3.Context()
    t = problem.translate(ctx)
    opt = z3.Optimize(ctx=ctx)
    opt.add(*t.hard)
    for s in t.soft:
        opt.add_soft(s.formula, weight=str(s.weight))
    assert opt.check() == z3.sat
    m = opt.model()
    return sum(s.weight for s in t.soft if not z3.is_true(m.eval(s.formula, model_completion=True)))


def test_ten_small_instances_match_z3_optimize():
    x, y, z = z3.Bools("x y z")
    instances = [
        Problem.from_formulas([], [(x, 1), (z3.Not(x), 1)]),
        Problem.from_formulas([z3.Or(x, y)], [(x, 1), (y, 1), (z3.Not(x), 1)]),
        Problem.from_formulas([z3.Xor(x, y)], [(x, 1), (y, 1)]),
        Problem.from_formulas([z3.Implies(x, y)], [(x, 1), (z3.Not(y), 1)]),
        Problem.from_formulas([z3.Or(x, z)], [(x, 1), (y, 1), (z3.Not(z), 1)]),
        Problem.from_formulas([x == y], [(x, 1), (y, 1), (z3.Not(x), 1)]),
        Problem.from_formulas([z3.Or(x, y, z)], [(x, 1), (y, 1), (z, 1), (z3.Not(x), 1)]),
        Problem.from_formulas([z3.And(z3.Or(x, y), z3.Or(z3.Not(x), z))], [(x, 1), (y, 1), (z, 1)]),
        Problem.from_formulas([], [(x, 1), (z3.Not(x), 1), (y, 1), (z3.Not(y), 1)]),
        Problem.from_formulas([z3.Or(x, y), z3.Or(z3.Not(x), z3.Not(y))], [(x, 1), (y, 1), (z, 1)]),
    ]
    for problem in instances:
        result = ParallelMaxSMTSolver(problem, roles=hs_roles(), threads=1, timeout=3).solve()
        assert result.status == "OPTIMAL", result
        assert result.upper_bound == _expected(problem)
        assert result.lower_bound == result.upper_bound


def test_z3_baseline_keeps_real_incumbent_when_optimize_times_out():
    root = Path(__file__).resolve().parents[1]

    result = z3_optimize_baseline(
        root / "benchmarks" / "local" / "hard_set_cover_u_2.wcnf",
        timeout=0.1,
    )

    assert result["status"] == "SAT", result
    assert result["cost"] == 39, result


def test_weighted_optimum_matches_z3():
    x, y = z3.Bools("wx wy")
    problem = Problem.from_formulas([z3.Or(x, y)], [(x, 7), (y, 2), (z3.Not(x), 5)])
    result = ParallelMaxSMTSolver(problem, roles=hs_roles(), threads=1, timeout=3).solve()
    assert result.status == "OPTIMAL"
    assert result.upper_bound == _expected(problem)


def test_coordinator_concurrent_updates_and_core_guard():
    c = Coordinator(UnweightedObjective(3), 3)
    errors = []

    def publish(i):
        try:
            c.publish_core(f"w{i}", "hs", {i, (i + 1) % 3})
        except Exception as exc:
            errors.append(exc)

    threads = [threading.Thread(target=publish, args=(i,)) for i in range(3)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    assert not errors
    assert c.snapshot().lower_bound >= 1
    with pytest.raises(ValueError):
        c.publish_core("maxres-0", "maxres", {0}, original=False)
    with pytest.raises(ValueError):
        c.publish_core("hs-0", "hs", {3})


def test_refuted_backbone_never_asserted():
    x = z3.Bool("bbx")
    problem = Problem.from_formulas([z3.Not(x)], [(x, 1)])
    coordinator = Coordinator(UnweightedObjective(1), 1)
    stop = threading.Event()
    worker = BackboneWorker("backbone-0", "backbone", problem.to_payload(), coordinator, stop)
    worker.ctx = z3.Context()
    worker.problem = Problem.from_payload(problem.to_payload())
    worker.translated = worker.problem.translate(worker.ctx)
    outcome, countermodel = worker.validate_candidate(("bbx", True))
    assert outcome == "refuted"
    assert countermodel is not None
    assert ("bbx", True) not in worker.asserted_backbones


def test_certificate_passes_and_corruptions_fail(tmp_path):
    x = z3.Bool("cx")
    problem = Problem.from_formulas([], [(x, 1), (z3.Not(x), 1)])
    result = ParallelMaxSMTSolver(problem, roles=hs_roles(), threads=1, timeout=3).solve()
    assert result.certificate is not None
    cert = json.loads(json.dumps(result.certificate))
    assert verify_certificate(problem, cert)
    bad_cost = dict(cert, cost=cert["cost"] + 1)
    assert not verify_certificate(problem, bad_cost)
    bad_core = dict(cert, cores=[[0]])
    assert not verify_certificate(problem, bad_core)
    bad_model = dict(cert, assignment={"cx": True if cert["assignment"].get("cx") is False else False})
    assert not verify_certificate(problem, bad_model)
    out = tmp_path / "cert.json"
    out.write_text(json.dumps(cert), encoding="utf-8")
    verify_certificate_or_raise(problem, out)


@pytest.mark.parametrize("timeout", (0.5, 1.0))
def test_timeout_has_no_live_threads(timeout):
    """A real timeout returns only after all eight worker contexts stop."""
    root = Path(__file__).resolve().parents[1]
    problem = parse_file(
        root / "benchmarks" / "local" / "eval_random_2sat_u_0.wcnf"
    )
    roles = RoleSpec(hs=1, mss=2, backbone=1, maxres=2, zopt=2)

    result = ParallelMaxSMTSolver(
        problem, roles=roles, threads=8, timeout=timeout, seed=20260901
    ).solve()

    assert not result.threads_alive, result


@pytest.mark.parametrize(
    "instance_name",
    ("eval_random_2sat_u_0.wcnf", "eval_random_2sat_u_1.wcnf"),
)
def test_timeout_contract_on_large_instance_at_eight_threads(instance_name):
    """The public solve call includes shutdown and incumbent validation time."""
    root = Path(__file__).resolve().parents[1]
    problem = parse_file(root / "benchmarks" / "local" / instance_name)
    roles = RoleSpec(hs=1, mss=2, backbone=1, maxres=2, zopt=2)
    timeout = 8.0
    solver = ParallelMaxSMTSolver(
        problem, roles=roles, threads=8, timeout=timeout, seed=20260901
    )

    started = time.perf_counter()
    result = solver.solve()
    wall = time.perf_counter() - started

    # The largest shipped 54k-constraint case measures about 1.48x because
    # the fresh-context incumbent gate is included in caller wall time.  A
    # 55% bound covers that worst case plus scheduler jitter while remaining
    # well below the roughly 2x pre-fix overrun.
    assert wall < timeout * 1.55, (wall, result)
    assert abs(result.elapsed - wall) < 0.25, (wall, result.elapsed)
    assert not result.threads_alive


def test_deadline_poll_is_not_blocked_by_core_lower_bound_search():
    entered = threading.Event()
    rng = random.Random(20260901)
    stress_cores = [
        frozenset(rng.sample(range(120), rng.randint(3, 5)))
        for _ in range(35)
    ]

    class SignalingObjective(UnweightedObjective):
        def minimum_hitting_set(self, cores, **limits):
            entered.set()
            return super().minimum_hitting_set(cores, **limits)

    coordinator = Coordinator(SignalingObjective(120), 120)
    # Seed one realistic exponential search without paying for 34 preceding
    # public recomputations.  The final core still travels through the public
    # API whose lock responsiveness is under test.
    coordinator._cores.update(stress_cores[:-1])
    coordinator._core_generation = len(coordinator._cores)
    publisher = threading.Thread(
        target=coordinator.publish_core,
        args=("hs", "hs", stress_cores[-1]),
    )
    publisher.start()
    assert entered.wait(1.0)

    started = time.perf_counter()
    assert not coordinator.is_done()
    blocked = time.perf_counter() - started
    publisher.join(3.0)

    assert blocked < 0.1, blocked
    assert not publisher.is_alive()


def test_certificate_does_not_repeat_hitting_set_search_under_lock():
    entered = threading.Event()

    class SignalingObjective(UnweightedObjective):
        signal = False

        def minimum_hitting_set(self, cores, **limits):
            if self.signal:
                entered.set()
            return super().minimum_hitting_set(cores, **limits)

    rng = random.Random(20260901)
    stress_cores = {
        frozenset(rng.sample(range(120), rng.randint(3, 5)))
        for _ in range(60)
    }
    objective = SignalingObjective(120)
    cost, hitting_set = objective.minimum_hitting_set(stress_cores)
    coordinator = Coordinator(objective, 120)
    # Seed the realistic exponential store without paying for 60 public
    # prefix recomputations; publish_model drives the coordinator to OPTIMAL.
    coordinator._cores.update(stress_cores)
    coordinator._core_generation = len(stress_cores)
    coordinator._lower_bound = cost
    assert coordinator.publish_model(
        "model", "test", {}, hitting_set, cost=cost
    )
    assert coordinator.snapshot().status == "OPTIMAL"

    objective.signal = True
    result = {}

    def create_certificate():
        started = time.perf_counter()
        result["certificate"] = coordinator.certificate()
        result["elapsed"] = time.perf_counter() - started

    creator = threading.Thread(target=create_certificate)
    creator.start()
    entered.wait(0.25)
    started = time.perf_counter()
    snapshot = coordinator.snapshot()
    blocked = time.perf_counter() - started
    creator.join(5.0)

    assert snapshot.status == "OPTIMAL"
    assert not creator.is_alive()
    assert blocked < 0.1, blocked
    assert result["elapsed"] < 0.25, result["elapsed"]
    assert result["certificate"]["hitting_set"] == sorted(hitting_set)


def test_expired_core_search_keeps_core_and_previous_certified_bound():
    coordinator = Coordinator(UnweightedObjective(20), 20)
    coordinator.set_hitting_set_limits(deadline=time.perf_counter() - 1.0)

    assert coordinator.publish_core("hs", "hs", {2, 5, 11})

    snapshot = coordinator.snapshot()
    assert snapshot.cores == (frozenset({2, 5, 11}),)
    assert snapshot.lower_bound == 0


def test_elapsed_includes_final_incumbent_gate(monkeypatch):
    x = z3.Bool("elapsed_gate_x")
    problem = Problem.from_formulas([], [(x, 1)])
    solver = ParallelMaxSMTSolver(problem, roles=hs_roles(), threads=1, timeout=0)
    solver._make_workers = lambda: []
    solver.coordinator.publish_model(
        "candidate", "test", {"elapsed_gate_x": True}, set(), cost=0
    )
    gate_seconds = 0.15

    def delayed_gate(*_args, **_kwargs):
        time.sleep(gate_seconds)
        return True

    monkeypatch.setattr("pmaxsmt.solver._incumbent_is_feasible", delayed_gate)
    started = time.perf_counter()
    result = solver.solve()
    wall = time.perf_counter() - started

    assert wall >= gate_seconds
    assert abs(result.elapsed - wall) < 0.05, (wall, result.elapsed)


def _random_instance(seed: int) -> Problem:
    """Small reproducible Boolean/QF_LIA differential-test portfolio."""
    rng = random.Random(seed)
    count = rng.randint(8, 25)
    if seed % 2 == 0:
        variables = list(z3.Bools(" ".join(f"rb_{seed}_{i}" for i in range(6))))
        hard = [z3.Or(variables[0], variables[1]), z3.Or(z3.Not(variables[2]), variables[3])]
        soft = []
        for _ in range(count):
            width = rng.choice((1, 1, 2, 3))
            literals = []
            for _ in range(width):
                variable = variables[rng.randrange(len(variables))]
                literals.append(variable if rng.randrange(2) else z3.Not(variable))
            formula = literals[0] if len(literals) == 1 else z3.Or(*literals)
            weight = rng.choice((1, 1, 2, 3, 5))
            soft.append((formula, weight))
        return Problem.from_formulas(hard, soft, source_format="random-boolean")

    x, y = z3.Ints(f"rl_{seed}_x rl_{seed}_y")
    hard = [x >= -5, x <= 5, y >= -5, y <= 5]
    soft = []
    for _ in range(count):
        kind = rng.randrange(6)
        k = rng.randint(-4, 4)
        if kind == 0:
            formula = x <= k
        elif kind == 1:
            formula = x >= k
        elif kind == 2:
            formula = y <= k
        elif kind == 3:
            formula = y >= k
        elif kind == 4:
            formula = x + y <= k
        else:
            formula = x - y >= k
        soft.append((formula, rng.choice((1, 1, 2, 3, 5))))
    return Problem.from_formulas(hard, soft, source_format="random-qf-lia")


def _independent_optimum(problem: Problem) -> int:
    ctx = z3.Context()
    translated = problem.translate(ctx)
    optimize = z3.Optimize(ctx=ctx)
    optimize.add(*translated.hard)
    for soft in translated.soft:
        optimize.add_soft(soft.formula, weight=str(soft.weight))
    assert optimize.check() == z3.sat
    model = optimize.model()
    return sum(
        soft.weight
        for soft in translated.soft
        if not z3.is_true(model.eval(soft.formula, model_completion=True))
    )


@pytest.mark.parametrize(
    "roles",
    [
        pytest.param(RoleSpec(hs=1, mss=1, backbone=1, maxres=1, zopt=1), id="all-roles"),
        pytest.param(RoleSpec(hs=1, mss=1, backbone=1, maxres=1, zopt=0), id="without-zopt"),
    ],
)
def test_randomized_differential_parallel_portfolio(roles):
    """Forty seeded 8--25-soft Boolean/QF_LIA cases match fresh Optimize."""
    for seed in range(40):
        problem = _random_instance(seed)
        expected = _independent_optimum(problem)
        result = ParallelMaxSMTSolver(
            problem,
            roles=roles,
            threads=roles.total,
            seed=seed,
            timeout=5,
        ).solve()
        assert result.status == "OPTIMAL", (seed, result)
        assert not result.worker_errors, (seed, result.worker_errors)
        assert result.lower_bound == expected
        assert result.upper_bound == expected
        assert result.certificate is not None
        assert verify_certificate(problem, result.certificate)


@pytest.mark.parametrize("role", ("hs", "mss", "backbone", "maxres", "zopt"))
def test_each_worker_role_closes_zero_cost_instance(role):
    """Each role independently publishes a certified optimum on an easy case."""
    x, y = z3.Bools(f"role_{role}_x role_{role}_y")
    tautology = z3.Or(x, z3.Not(x))
    problem = Problem.from_formulas([], [(tautology, 1), (z3.Or(y, z3.Not(y)), 2)] + [(tautology, 1)] * 6)
    counts = {name: 0 for name in ("hs", "mss", "backbone", "maxres", "zopt")}
    counts[role] = 1
    roles = RoleSpec(**counts)
    result = ParallelMaxSMTSolver(problem, roles=roles, threads=1, timeout=3, seed=17).solve()
    assert result.status == "OPTIMAL", (role, result)
    assert result.lower_bound == result.upper_bound == 0
    assert result.certificate is not None
    assert verify_certificate(problem, result.certificate)


def test_all_non_hs_roles_with_hs_reach_certified_weighted_optimum():
    x, y, z = z3.Bools("together_x together_y together_z")
    problem = Problem.from_formulas(
        [z3.Or(x, y)],
        [(x, 7), (y, 2), (z3.Not(x), 5), (z, 3), (z3.Not(z), 4)],
    )
    roles = RoleSpec(hs=1, mss=1, backbone=1, maxres=1, zopt=1)
    result = ParallelMaxSMTSolver(problem, roles=roles, threads=5, timeout=5, seed=29).solve()
    assert result.status == "OPTIMAL"
    assert result.lower_bound == result.upper_bound == _independent_optimum(problem)
    assert result.certificate is not None and verify_certificate(problem, result.certificate)


def _prepare_worker(worker, problem: Problem) -> None:
    worker.ctx = z3.Context()
    worker.problem = Problem.from_payload(problem.to_payload())
    worker.translated = worker.problem.translate(worker.ctx)


def test_distinct_mss_seeds_diverge_in_probe_sequences():
    variables = list(z3.Bools(" ".join(f"seed_diverge_{i}" for i in range(8))))
    soft = [(variable, 1) for variable in variables] + [(z3.Not(variable), 1) for variable in variables]
    problem = Problem.from_formulas([], soft)
    workers = []
    for worker_id, seed in (("mss-a", 7), ("mss-b", 11)):
        coordinator = Coordinator(UnweightedObjective(len(soft)), len(soft))
        stop = threading.Event()
        worker = MSSWorker(worker_id, "mss", problem.to_payload(), coordinator, stop, seed=seed)
        _prepare_worker(worker, problem)
        solver = z3.Solver(ctx=worker.ctx)
        solver.add(*worker.translated.hard)
        assert solver.check() == z3.sat
        worker.local_mss(solver.model())
        workers.append(worker)
    assert workers[0].probe_history
    assert workers[1].probe_history
    assert workers[0].probe_history != workers[1].probe_history


def test_validated_backbone_is_entailing_in_fresh_context():
    x = z3.Bool("entailed_backbone")
    problem = Problem.from_formulas([x], [(x, 1)])
    coordinator = Coordinator(UnweightedObjective(1), 1)
    worker = BackboneWorker(
        "backbone-entail", "backbone", problem.to_payload(), coordinator, threading.Event(), seed=3
    )
    _prepare_worker(worker, problem)
    solver = z3.Solver(ctx=worker.ctx)
    solver.add(*worker.translated.hard)
    assert solver.check() == z3.sat
    worker._triage(solver.model())
    assert ("entailed_backbone", True) in worker.asserted_backbones

    fresh = z3.Context()
    translated = problem.translate(fresh)
    independent = z3.Solver(ctx=fresh)
    independent.add(*translated.hard)
    independent.add(z3.Not(translated.soft[0].formula))
    assert independent.check() == z3.unsat


def test_unsat_hard_constraints_are_reported():
    x = z3.Bool("hard_unsat")
    problem = Problem.from_formulas([x, z3.Not(x)], [(x, 1), (z3.Not(x), 1)])
    result = ParallelMaxSMTSolver(problem, roles=hs_roles(), threads=1, timeout=3).solve()
    assert result.status == "UNSAT"
    assert result.upper_bound is None
    assert result.certificate is None


def test_all_softs_satisfiable_has_zero_optimum():
    x, y = z3.Bools("zero_x zero_y")
    problem = Problem.from_formulas([], [(x, 1), (z3.Or(y, z3.Not(y)), 4), (z3.Or(x, y), 2)])
    roles = RoleSpec(hs=1, mss=1, backbone=1, maxres=1, zopt=0)
    result = ParallelMaxSMTSolver(problem, roles=roles, threads=4, timeout=3, seed=4).solve()
    assert result.status == "OPTIMAL"
    assert result.lower_bound == result.upper_bound == 0
    assert result.certificate is not None and verify_certificate(problem, result.certificate)


def test_repeated_parallel_runs_have_same_certified_bounds():
    x, y, z = z3.Bools("repeat_x repeat_y repeat_z")
    problem = Problem.from_formulas(
        [z3.Or(x, y), z3.Or(z3.Not(y), z)],
        [(x, 3), (z3.Not(x), 2), (y, 5), (z3.Not(y), 7), (z, 1), (z3.Not(z), 4)],
    )
    roles = RoleSpec(hs=1, mss=1, backbone=1, maxres=1, zopt=0)
    results = [
        ParallelMaxSMTSolver(problem, roles=roles, threads=4, timeout=5, seed=seed).solve()
        for seed in (1, 2, 3)
    ]
    assert all(result.status == "OPTIMAL" for result in results)
    assert {(result.lower_bound, result.upper_bound) for result in results} == {(results[0].lower_bound, results[0].upper_bound)}
    assert all(result.certificate is not None and verify_certificate(problem, result.certificate) for result in results)


def test_correction_sets_are_guarded_and_excluded_from_lower_bound():
    coordinator = Coordinator(UnweightedObjective(3), 3)
    assert coordinator.publish_correction_set("mss", "mss", {0, 2})
    assert coordinator.snapshot().correction_sets == (frozenset({0, 2}),)
    assert coordinator.lower_bound == 0
    with pytest.raises(ValueError):
        coordinator.publish_correction_set("maxres", "maxres", {0}, original=False)
    with pytest.raises(ValueError):
        coordinator.publish_correction_set("mss", "mss", {3})


def test_maxres_selects_both_private_transformations():
    from pmaxsmt.workers.maxres_worker import MaxResWorker

    x, y = z3.Bools("maxres_x maxres_y")
    problem = Problem.from_formulas([], [(x, 2), (y, 3)])
    coordinator = Coordinator(WeightedObjective(problem.weights), len(problem.soft))
    stop = threading.Event()
    worker = MaxResWorker("maxres-test", "maxres", problem.to_payload(), coordinator, stop, seed=5)
    _prepare_worker(worker, problem)
    coordinator.publish_model("mss", "mss", {}, {0}, cost=2)
    coordinator.publish_correction_set("mss", "mss", {0})
    coordinator.publish_core("hs", "hs", {0, 1})
    first = worker.maxres(coordinator.snapshot())
    assert first and worker.last_action == "relax_core"
    assert worker.private_offset == 2
    assert worker._counter > 0
    second = worker.maxres(coordinator.snapshot())
    assert second and worker.last_action == "restrict_cs"
    assert not worker.corr_set_enabled


def test_maxres_searches_private_softs_and_maps_original_model():
    from pmaxsmt.workers.maxres_worker import MaxResWorker

    x, y = z3.Bools("private_x private_y")
    problem = Problem.from_formulas([z3.Or(x, y)], [(x, 4), (z3.Not(x), 2), (y, 3)])
    coordinator = Coordinator(WeightedObjective(problem.weights), len(problem.soft))
    worker = MaxResWorker("maxres-private", "maxres", problem.to_payload(), coordinator, threading.Event(), seed=9)
    _prepare_worker(worker, problem)
    worker.relax_core(frozenset({0, 1}))
    published = []
    worker._publish_model = lambda model: published.append(worker._falsified(model)) or True
    worker._solve_transformed_once()
    assert worker.private_best_cost is not None
    assert published
    assert all(0 <= index < len(problem.soft) for index in published[0])


def test_worker_discards_model_that_violates_hard_constraints():
    x = z3.Bool("guarded_model_x")
    problem = Problem.from_formulas([x], [(z3.Not(x), 1)])
    trace = io.StringIO()
    coordinator = Coordinator(
        UnweightedObjective(1), 1, trace=TraceWriter(trace)
    )
    worker = MSSWorker(
        "mss-guard", "mss", problem.to_payload(), coordinator, threading.Event()
    )
    _prepare_worker(worker, problem)
    solver = z3.Solver(ctx=worker.ctx)
    solver.add(z3.Not(worker.translated.hard[0]))
    assert solver.check() == z3.sat

    assert not worker._publish_model(solver.model())
    assert worker.invalid_model_count == 1
    event = json.loads(trace.getvalue())
    assert event["event"] == "invalid_model_discarded"
    assert event["details"]["violated_hard"] == 1
    assert coordinator.snapshot().upper_bound is None


def test_solve_final_gate_rejects_invalid_incumbent():
    x = z3.Bool("final_gate_x")
    problem = Problem.from_formulas([x], [(x, 1)])
    solver = ParallelMaxSMTSolver(problem, roles=hs_roles(), threads=1, timeout=0)
    solver._make_workers = lambda: []
    solver.coordinator.publish_model("corrupt", "test", {"final_gate_x": False}, {0}, cost=1)

    result = solver.solve()

    assert result.status == "UNKNOWN"
    assert result.upper_bound is None
    assert result.assignment is None
    assert result.falsified is None


def test_try_rotate_publishes_only_genuine_original_cores():
    x = z3.Bool("rotate_core_x")
    tautology = z3.Or(x, z3.Not(x))
    problem = Problem.from_formulas(
        [],
        [(tautology, 1), (tautology, 1), (x, 1), (tautology, 1), (z3.Not(x), 1)],
    )
    coordinator = Coordinator(UnweightedObjective(5), 5)
    worker = MSSWorker(
        "mss-rotate", "mss", problem.to_payload(), coordinator, threading.Event(), seed=1
    )
    _prepare_worker(worker, problem)

    # try_rotate starts with no local negative assumptions but inherits a
    # support for index 4 from local_mss.  A positive assumption at index 4
    # must not be rewritten to that inherited support.
    worker.try_rotate({0, 1, 2, 3}, {4: frozenset({2})})

    assert coordinator.snapshot().cores
    fresh = z3.Context()
    translated = problem.translate(fresh)
    for core in coordinator.snapshot().cores:
        check = z3.Solver(ctx=fresh)
        check.add(*translated.hard)
        check.add(*(translated.soft[index].formula for index in core))
        assert check.check() == z3.unsat, core


def test_large_instance_timeout_is_prompt_and_joins_all_workers():
    root = Path(__file__).resolve().parents[1]
    problem = parse_file(root / "benchmarks" / "local" / "eval_random_2sat_u_0.wcnf")
    roles = RoleSpec(hs=1, mss=1, backbone=1, maxres=0, zopt=1)
    started = time.perf_counter()
    result = ParallelMaxSMTSolver(
        problem, roles=roles, threads=4, timeout=1.0, seed=41
    ).solve()
    wall = time.perf_counter() - started

    assert wall < 4.0, (wall, result)
    assert not result.threads_alive


@pytest.mark.parametrize("seed", (20260901, 20260815, 1012))
def test_vertex_cover_parallel_incumbent_is_hard_feasible_and_not_below_optimum(seed):
    root = Path(__file__).resolve().parents[1]
    relative = "local/eval_vertex_cover_u_2.wcnf"
    manifest = json.loads((root / "benchmarks" / "manifest.json").read_text(encoding="utf-8"))
    known_optimum = next(row["known_optimum"] for row in manifest if row["path"] == relative)
    problem = parse_file(root / "benchmarks" / relative)
    roles = RoleSpec(hs=1, mss=2, backbone=1, maxres=2, zopt=2)

    solver = ParallelMaxSMTSolver(
        problem, roles=roles, threads=8, timeout=8, seed=seed
    )
    result = solver.solve()

    assert result.upper_bound is not None, result
    assert result.upper_bound >= known_optimum
    assert result.assignment is not None
    assert all(worker.invalid_model_count == 0 for worker in solver.workers)
    fresh = z3.Context()
    translated = problem.translate(fresh)
    constants = {}
    for formula in (*translated.hard, *(soft.formula for soft in translated.soft)):
        stack = [formula]
        while stack:
            expression = stack.pop()
            if z3.is_const(expression) and expression.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                constants.setdefault(str(expression.decl().name()), expression.decl())
            stack.extend(expression.children())
    check = z3.Solver(ctx=fresh)
    check.add(*translated.hard)
    for name, value in result.assignment.items():
        check.add(constants[name]() == z3.BoolVal(value, ctx=fresh))
    assert check.check() == z3.sat


def test_optimal_certificate_verification_is_default_with_explicit_opt_out(monkeypatch):
    x = z3.Bool("default_verify_x")
    problem = Problem.from_formulas([], [(x, 1), (z3.Not(x), 1)])
    calls = []

    def reject_certificate(_problem, _certificate):
        calls.append(True)
        raise CertificateError("injected verification failure")

    monkeypatch.setattr("pmaxsmt.solver.verify_certificate_or_raise", reject_certificate)
    with pytest.raises(CertificateError, match="injected verification failure"):
        ParallelMaxSMTSolver(problem, roles=hs_roles(), threads=1, timeout=3).solve()
    assert calls == [True]

    result = ParallelMaxSMTSolver(
        problem, roles=hs_roles(), threads=1, timeout=3, verify_optimal=False
    ).solve()
    assert result.status == "OPTIMAL"
    assert calls == [True]


def test_sampled_backbone_candidates_and_refutations_use_distinct_channels():
    x = z3.Bool("candidate_channel_x")
    problem = Problem.from_formulas([], [(x, 1)])

    candidate_trace = io.StringIO()
    candidate_coordinator = Coordinator(
        UnweightedObjective(1), 1, trace=TraceWriter(candidate_trace)
    )
    candidate_worker = BackboneWorker(
        "backbone-candidate",
        "backbone",
        problem.to_payload(),
        candidate_coordinator,
        threading.Event(),
    )
    _prepare_worker(candidate_worker, problem)
    sample = z3.Solver(ctx=candidate_worker.ctx)
    sample.add(candidate_worker.translated.soft[0].formula)
    assert sample.check() == z3.sat
    candidate_worker.validate_candidate = lambda _literal: ("unknown", None)
    candidate_worker._triage(sample.model())
    assert candidate_coordinator.snapshot().candidate_backbones == (
        ("candidate_channel_x", True),
    )
    assert "backbone_candidate" in candidate_trace.getvalue()

    refuted_trace = io.StringIO()
    refuted_coordinator = Coordinator(
        UnweightedObjective(1), 1, trace=TraceWriter(refuted_trace)
    )
    refuted_worker = BackboneWorker(
        "backbone-refuted",
        "backbone",
        problem.to_payload(),
        refuted_coordinator,
        threading.Event(),
    )
    _prepare_worker(refuted_worker, problem)
    refuted_sample = z3.Solver(ctx=refuted_worker.ctx)
    refuted_sample.add(refuted_worker.translated.soft[0].formula)
    assert refuted_sample.check() == z3.sat
    refuted_worker._triage(refuted_sample.model())
    snapshot = refuted_coordinator.snapshot()
    assert snapshot.candidate_backbones == ()
    assert snapshot.refuted_backbones == (("candidate_channel_x", True),)
    events = [json.loads(line)["event"] for line in refuted_trace.getvalue().splitlines()]
    assert events == ["backbone_candidate", "backbone_refuted"]


def test_inconsistent_published_bound_is_rejected_instead_of_clamped():
    coordinator = Coordinator(UnweightedObjective(3), 3)
    coordinator.publish_model("model", "test", {}, {0, 1}, cost=2)

    with pytest.raises(
        ValueError, match="lower bound exceeds incumbent upper bound"
    ):
        coordinator.publish_bound("bound", "test", 5)

    snapshot = coordinator.snapshot()
    assert snapshot.status == "RUNNING"
    assert snapshot.lower_bound == 0
    assert snapshot.upper_bound == 2
    assert coordinator.certificate() is None


def test_large_shipped_instance_translation_completes_in_a_few_seconds():
    root = Path(__file__).resolve().parents[1]
    problem = parse_file(
        root / "benchmarks" / "local" / "eval_random_2sat_u_0.wcnf"
    )

    started = time.perf_counter()
    translated = problem.translate(z3.Context())
    elapsed = time.perf_counter() - started

    assert len(translated.hard) == len(problem.hard)
    assert len(translated.soft) == len(problem.soft)
    assert elapsed < 3.0, elapsed


def test_large_shipped_instance_short_solve_runs_worker_search():
    root = Path(__file__).resolve().parents[1]
    problem = parse_file(
        root / "benchmarks" / "local" / "eval_random_2sat_u_0.wcnf"
    )
    stream = io.StringIO()
    roles = RoleSpec(hs=1, mss=1, backbone=1, maxres=0, zopt=1)

    result = ParallelMaxSMTSolver(
        problem,
        roles=roles,
        threads=4,
        timeout=10.0,
        seed=5,
        trace=TraceWriter(stream),
    ).solve()
    events = [json.loads(line)["event"] for line in stream.getvalue().splitlines()]

    assert result.upper_bound is not None, (result, events)
    assert any(
        event in {"incumbent", "core", "backbone", "backbone_candidate"}
        for event in events
    ), events


def test_zopt_worker_minimizes_total_weight_instead_of_soft_index_order():
    problem = parse_wcnf(
        "p wcnf 1 2 100\n"
        "1 1 0\n"
        "10 -1 0\n"
    )
    roles = RoleSpec(hs=0, mss=0, backbone=0, maxres=0, zopt=1)

    result = ParallelMaxSMTSolver(
        problem, roles=roles, threads=1, timeout=1.0, seed=5
    ).solve()

    assert result.upper_bound == 1, result
    assert result.assignment == {"x1": False}


def test_zopt_worker_reaches_certified_weighted_set_cover_optimum():
    root = Path(__file__).resolve().parents[1]
    problem = parse_file(root / "benchmarks" / "local" / "gen_set_cover_0_w.wcnf")
    roles = RoleSpec(hs=0, mss=0, backbone=0, maxres=0, zopt=1)

    result = ParallelMaxSMTSolver(
        problem, roles=roles, threads=1, timeout=1.0, seed=5
    ).solve()

    assert result.upper_bound == 6, result


def test_mss_reduction_does_not_publish_negative_probe_members_as_positive():
    x = z3.Bool("negative_probe_core_x")
    problem = Problem.from_formulas(
        [],
        [(z3.Not(x), 1), (x, 1), (x, 1), (x, 1)],
    )
    coordinator = Coordinator(UnweightedObjective(4), 4)
    worker = MSSWorker(
        "mss-negative-core",
        "mss",
        problem.to_payload(),
        coordinator,
        threading.Event(),
    )
    _prepare_worker(worker, problem)

    # Index 3 is a negative assumption whose inherited support injects index
    # 2, also currently negative.  Mixed-polarity reduction can return {1, 2},
    # but those two positive softs are satisfiable and must not be published.
    reduced = worker._publish_probe_core(
        frozenset({1, 3}),
        {0: True, 1: True, 2: False, 3: False},
        {3: frozenset({0, 2})},
    )

    assert reduced
    fresh = z3.Context()
    translated = problem.translate(fresh)
    check = z3.Solver(ctx=fresh)
    check.add(*(translated.soft[index].formula for index in reduced))
    assert check.check() == z3.unsat, reduced


def test_unsat_publication_is_rejected_after_a_feasible_incumbent():
    coordinator = Coordinator(UnweightedObjective(2), 2)
    coordinator.publish_model(
        "model", "test", {"x": True}, falsified={0}, cost=1
    )

    with pytest.raises(ValueError, match="UNSAT.*feasible incumbent"):
        coordinator.add_core([])

    snapshot = coordinator.snapshot()
    assert snapshot.status == "RUNNING"
    assert snapshot.upper_bound == 1
    assert snapshot.incumbent_assignment == {"x": True}
    assert snapshot.incumbent_falsified == frozenset({0})
