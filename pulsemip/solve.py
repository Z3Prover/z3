"""JSON interface to the extracted, exact Pulse MIP solver."""

import argparse
from decimal import Decimal
from fractions import Fraction
import json
import math
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def rational(value):
    if isinstance(value, bool) or not isinstance(value, (int, str, Decimal, Fraction)):
        raise ValueError("coefficients must be exact integers, decimal strings, or rational strings")
    try:
        return Fraction(value)
    except ZeroDivisionError as error:
        raise ValueError("rational denominator must not be zero") from error


def natural(value, name):
    if type(value) is not int or value < 0:
        raise ValueError(f"{name} must be a nonnegative integer")
    return value


def scale_row(coefficients, constant):
    values = [constant, *coefficients]
    denominator = math.lcm(*(q.denominator for q in values))
    return [int(q * denominator) for q in values], denominator


def normalize(problem):
    objective = [rational(q) for q in problem["objective"]]
    n = len(objective)
    offset = rational(problem.get("objective_offset", 0))
    sense = problem.get("sense", "min")
    if sense not in ("min", "max"):
        raise ValueError("sense must be min or max")
    sign = 1 if sense == "min" else -1
    cost, scale = scale_row([sign * q for q in objective], sign * offset)
    integers = [natural(v, "integer variable index") for v in problem.get("integers", [])]
    if any(v >= n for v in integers):
        raise ValueError("integer variable index out of range")
    constraints = []
    for row in problem.get("constraints", []):
        coefficients = [rational(q) for q in row["coefficients"]]
        if len(coefficients) != n:
            raise ValueError("constraint dimension differs from objective")
        rhs = rational(row["rhs"])
        relation = row.get("relation", "<=")
        if relation not in ("<=", ">=", "="):
            raise ValueError("only closed linear relations <=, >=, = are supported")
        converted, _ = scale_row(coefficients, -rhs)
        if relation in ("<=", "="):
            constraints.append(converted)
        if relation in (">=", "="):
            constraints.append([-a for a in converted])
    return n, integers, cost, constraints, sign * scale


def command():
    executable = ROOT / "_build" / "pulsemip"
    if os.name == "nt":
        path = "/mnt/" + executable.drive[0].lower() + executable.as_posix()[2:]
        return ["wsl", "-d", os.environ.get("Z3_FSTAR_WSL_DISTRO", "Ubuntu"), "--", path]
    return [str(executable)]


def solve(problem, node_limit=1000, row_limit=10000):
    n, integers, objective, constraints, cost_scale = normalize(problem)
    natural(node_limit, "node limit")
    natural(row_limit, "row limit")
    lines = [
        f"{n} {len(integers)} {len(constraints)} {node_limit} {row_limit}",
        " ".join(map(str, integers)),
        " ".join(map(str, objective)),
        *(" ".join(map(str, row)) for row in constraints),
    ]
    completed = subprocess.run(command(), input="\n".join(lines) + "\n",
                               capture_output=True, text=True, check=False)
    output = completed.stdout.splitlines()
    if completed.returncode or not output:
        raise RuntimeError(f"solver failed ({completed.returncode}): {completed.stdout}{completed.stderr}")
    header = output[0].split()
    result = {"status": header[0]}
    if result["status"] in ("OPTIMAL", "UNBOUNDED") or (
            result["status"] == "UNKNOWN" and header[2] == "INCUMBENT"):
        result["point"] = [str(Fraction(q)) for q in output[1].split()]
        if result["status"] == "UNBOUNDED":
            result["direction"] = [str(Fraction(q)) for q in output[2].split()]
        else:
            result["objective"] = str(Fraction(output[2]) / cost_scale)
    if result["status"] in ("OPTIMAL", "INFEASIBLE"):
        result["certificate"] = json.loads(output[-1])
    if result["status"] == "UNKNOWN":
        result["reason"] = header[1]
    if result["status"] not in ("OPTIMAL", "INFEASIBLE", "UNBOUNDED", "UNKNOWN"):
        raise RuntimeError(f"unexpected solver response: {completed.stdout}")
    return result


def reject_constant(value):
    raise ValueError(f"non-finite JSON number: {value}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input", nargs="?", type=Path)
    parser.add_argument("--nodes", type=int, default=1000)
    parser.add_argument("--rows", type=int, default=10000)
    args = parser.parse_args()
    try:
        if args.input:
            with args.input.open() as stream:
                problem = json.load(stream, parse_float=Decimal, parse_constant=reject_constant)
        else:
            problem = json.load(sys.stdin, parse_float=Decimal, parse_constant=reject_constant)
        print(json.dumps(solve(problem, args.nodes, args.rows)))
    except (ValueError, KeyError, TypeError, OSError, RuntimeError) as error:
        print(json.dumps({"status": "ERROR", "message": str(error)}))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
