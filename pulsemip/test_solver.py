from fractions import Fraction as F
import itertools
import random
import subprocess
import unittest

from solve import command, normalize, solve


def row(coefficients, rhs, relation="<="):
    return {"coefficients": coefficients, "rhs": rhs, "relation": relation}


def vertices(constraints):
    points = []
    for r, s in itertools.combinations(constraints, 2):
        a, b = map(F, r["coefficients"])
        c, d = map(F, s["coefficients"])
        u, v = F(r["rhs"]), F(s["rhs"])
        det = a * d - b * c
        if det:
            x = ((u * d - b * v) / det, (a * v - u * c) / det)
            if all(sum(F(k) * q for k, q in zip(t["coefficients"], x)) <= F(t["rhs"])
                   for t in constraints):
                points.append(x)
    return points


def verify_certificate(problem, result):
    n, integers, cost, rows, _ = normalize(problem)
    if "point" in result:
        x = list(map(F, result["point"]))
        assert len(x) == n
        assert all(a[0] + sum(c * v for c, v in zip(a[1:], x)) <= 0 for a in rows)
        assert all(x[v].denominator == 1 for v in integers)
    if result["status"] == "UNBOUNDED":
        d = list(map(F, result["direction"]))
        assert len(d) == n and all(d[v].denominator == 1 for v in integers)
        assert all(sum(c * v for c, v in zip(a[1:], d)) <= 0 for a in rows)
        assert sum(c * v for c, v in zip(cost[1:], d)) < 0
    if result["status"] not in ("OPTIMAL", "INFEASIBLE"):
        return
    cutoff = cost[0] + sum(c * v for c, v in zip(cost[1:], x)) if "point" in result else None

    def check(tree, current):
        if tree["kind"] == "split":
            v, k = tree["variable"], int(tree["pivot"])
            assert v in integers
            lower, upper = [-k] + [0] * n, [k + 1] + [0] * n
            lower[v + 1], upper[v + 1] = 1, -1
            check(tree["left"], [lower, *current])
            check(tree["right"], [upper, *current])
        else:
            weights = list(map(int, tree["weights"]))
            assert len(weights) == len(current) and all(w >= 0 for w in weights)
            combined = [sum(w * a[i] for w, a in zip(weights, current)) for i in range(n + 1)]
            if tree["kind"] == "infeasible":
                assert combined[0] > 0 and all(a == 0 for a in combined[1:])
            else:
                s = int(tree["scale"])
                assert s > 0 and cutoff is not None
                assert all(a + s * c == 0 for a, c in zip(combined[1:], cost[1:]))
                assert combined[0] + s * cost[0] >= s * cutoff

    check(result["certificate"], rows)


class SolverTests(unittest.TestCase):
    def check(self, problem, status, objective=None, **limits):
        result = solve(problem, **limits)
        self.assertEqual(result["status"], status, result)
        verify_certificate(problem, result)
        if objective is not None:
            self.assertEqual(F(result["objective"]), F(objective))
        return result

    def test_mixed_fractional_optimum(self):
        self.check({"objective": [-1, -1], "integers": [0], "constraints": [
            row([1, 0], "3/2"), row([-1, 0], 0),
            row([0, 1], "1/3"), row([0, -1], 0),
        ]}, "OPTIMAL", "-4/3")

    def test_integer_infeasibility_requires_both_branches(self):
        result = self.check({"objective": [0], "integers": [0],
                             "constraints": [row([2], 1, "=")]}, "INFEASIBLE")
        self.assertEqual(result["certificate"]["kind"], "split")

    def test_continuous_infeasible_and_zero_dimensions(self):
        for p in [
            {"objective": [1], "constraints": [row([1], 0), row([-1], -1)]},
            {"objective": [], "constraints": [row([], -1)]},
        ]:
            self.check(p, "INFEASIBLE")
        self.check({"objective": [], "objective_offset": "2/3"}, "OPTIMAL", "2/3")

    def test_unbounded_requires_integral_anchor_and_scaled_ray(self):
        self.check({"objective": [-1, 0], "integers": [0], "constraints": [
            row([1, -3], 0, "="), row([-1, 0], "-1/2"),
        ]}, "UNBOUNDED")
        self.check({"objective": [-1], "integers": [0]}, "UNBOUNDED")

    def test_unbounded_lp_does_not_imply_unbounded_mip(self):
        self.check({"objective": [0, -1], "integers": [0],
                    "constraints": [row([2, 0], 1, "=")]}, "INFEASIBLE")

    def test_tiny_gap_and_large_integers(self):
        huge = 2 ** 180 + 1
        self.check({"objective": [1], "integers": [0],
                    "constraints": [row([1], huge), row([-1], -huge)]}, "OPTIMAL", huge)
        tiny = F(1, 10 ** 80)
        self.check({"objective": [1], "constraints": [
            row([1], "1"), row([-1], str(-(1 + tiny))),
        ]}, "INFEASIBLE")

    def test_negative_fraction_floor(self):
        self.check({"objective": [1], "integers": [0], "constraints": [
            row([-1], "3/2"), row([1], "-1/2"),
        ]}, "OPTIMAL", -1)

    def test_maximization_and_decimal_strings(self):
        self.check({"objective": ["0.1"], "objective_offset": "0.2", "sense": "max",
                    "integers": [0], "constraints": [row([1], "3.9")]}, "OPTIMAL", "0.5")

    def test_limits_do_not_claim_infeasibility_or_optimality(self):
        p = {"objective": [-1], "integers": [0],
             "constraints": [row([1], "3/2"), row([-1], 0)]}
        self.check(p, "UNKNOWN", node_limit=0)
        self.check(p, "UNKNOWN", row_limit=0)
        r = self.check(p, "UNKNOWN", node_limit=2)
        self.assertEqual(r["reason"], "NODE_LIMIT")
        self.assertEqual(r["point"], ["1"])

    def test_free_unbounded_integer_infeasibility_returns_unknown(self):
        p = {"objective": [0, 0], "integers": [0, 1],
             "constraints": [row([2, -2], 1, "=")]}
        self.check(p, "UNKNOWN", node_limit=12)

    def test_invalid_input_and_binary_float_rejected(self):
        for p in [
            {"objective": [0.1]},
            {"objective": ["1/0"]},
            {"objective": [1], "integers": [-1]},
            {"objective": [1], "integers": [1]},
            {"objective": [1], "constraints": [row([1, 2], 0)]},
            {"objective": [1], "constraints": [row([1], 0, "<")]},
        ]:
            with self.subTest(problem=p), self.assertRaises(ValueError):
                solve(p)

    def test_windows_crlf_protocol(self):
        wire = "1 1 1 100 100\r\n0\r\n0 -1\r\n-3 1\r\n"
        result = subprocess.run(command(), input=wire, capture_output=True, text=True, check=True)
        self.assertEqual(result.stdout.splitlines()[:3], ["OPTIMAL", "3/1", "-3/1"])

    def test_random_bounded_mips_against_exhaustive_exact_search(self):
        rng = random.Random(17)
        domain = list(itertools.product(range(-2, 3), repeat=2))
        for _ in range(100):
            objective = [rng.randint(-3, 3), rng.randint(-3, 3)]
            offset = rng.randint(-3, 3)
            constraints = [row([1, 0], 2), row([-1, 0], 2),
                           row([0, 1], 2), row([0, -1], 2)]
            constraints += [row([rng.randint(-4, 4), rng.randint(-4, 4)],
                                str(F(rng.randint(-6, 6), rng.randint(1, 5)))) for _ in range(3)]
            p = {"objective": objective, "objective_offset": offset,
                 "integers": [0, 1], "constraints": constraints}
            feasible = [x for x in domain if all(
                sum(F(c) * v for c, v in zip(r["coefficients"], x)) <= F(r["rhs"])
                for r in constraints)]
            if feasible:
                optimum = min(offset + sum(c * v for c, v in zip(objective, x)) for x in feasible)
                self.check(p, "OPTIMAL", optimum)
            else:
                self.check(p, "INFEASIBLE")

    def test_random_continuous_and_mixed_against_exact_vertices(self):
        rng = random.Random(31)
        for integers in ([], [0]):
            for _ in range(30):
                objective = [str(F(rng.randint(-4, 4), rng.randint(1, 3))) for _ in range(2)]
                constraints = [row([1, 0], 2), row([-1, 0], 2),
                               row([0, 1], 2), row([0, -1], 2)]
                constraints += [row([rng.randint(-4, 4), rng.randint(-4, 4)],
                                    str(F(rng.randint(-6, 6), rng.randint(1, 5)))) for _ in range(3)]
                p = {"objective": objective, "integers": integers, "constraints": constraints}
                if integers:
                    candidates = [x for k in range(-2, 3) for x in vertices([
                        *constraints, row([1, 0], k), row([-1, 0], -k)])]
                else:
                    candidates = vertices(constraints)
                if candidates:
                    optimum = min(sum(F(c) * q for c, q in zip(objective, x)) for x in candidates)
                    self.check(p, "OPTIMAL", optimum)
                else:
                    self.check(p, "INFEASIBLE")


if __name__ == "__main__":
    unittest.main()
