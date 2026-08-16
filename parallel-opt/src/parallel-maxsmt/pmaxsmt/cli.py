"""Command line interface for the prototype."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import signal
import sys

from .certify import CertificateError, verify_certificate_or_raise
from .roles import parse_roles
from .sequential import SequentialMaxSMTSolver
from .solver import ParallelMaxSMTSolver
from .trace import TraceWriter


def _install_interrupt_handler() -> None:
    """Map Windows console break events to the solver's cooperative path.

    ``CTRL_C_EVENT`` is not delivered reliably to subprocesses launched by
    the non-console Windows runners used for the evaluation.  Registering the
    equivalent ``SIGBREAK`` event lets the existing KeyboardInterrupt cleanup
    path stop worker contexts and join every thread before returning.
    """
    def raise_keyboard_interrupt(_signum: int, _frame: object) -> None:
        raise KeyboardInterrupt

    sigbreak = getattr(signal, "SIGBREAK", None)
    if sigbreak is not None:
        signal.signal(sigbreak, raise_keyboard_interrupt)

def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="pmaxsmt", description="parallel anytime exact MaxSMT prototype")
    commands = parser.add_subparsers(dest="command", required=True)
    solve = commands.add_parser("solve", help="solve a WCNF or SMT-LIB2 MaxSMT instance")
    solve.add_argument("file")
    solve.add_argument("--threads", type=int, default=None)
    solve.add_argument("--roles", default=None, help="static counts, e.g. hs=1,mss=1,backbone=1,zopt=1")
    solve.add_argument("--timeout", type=float, default=None)
    solve.add_argument("--seed", type=int, default=0)
    solve.add_argument("--trace", default=None)
    solve.add_argument("--certificate", default=None)
    solve.add_argument("--sequential", action="store_true")
    solve.add_argument(
        "--no-verify",
        action="store_true",
        help="skip independent verification before reporting OPTIMAL",
    )

    verify = commands.add_parser("verify", help="independently verify an OPTIMAL certificate")
    verify.add_argument("file")
    verify.add_argument("--certificate", required=True)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.command == "verify":
        try:
            verify_certificate_or_raise(args.file, args.certificate)
        except Exception as exc:
            print(json.dumps({"verified": False, "error": str(exc)}, sort_keys=True))
            return 1
        print(json.dumps({"verified": True}, sort_keys=True))
        return 0

    trace = TraceWriter(args.trace) if args.trace else TraceWriter()
    try:
        if args.sequential and (args.threads is not None or args.roles is not None):
            raise ValueError(
                "--sequential cannot be combined with --threads or --roles"
            )
        if args.sequential:
            solver = SequentialMaxSMTSolver(
                args.file,
                seed=args.seed,
                timeout=args.timeout,
                trace=trace,
                verify_optimal=not args.no_verify,
            )
        else:
            threads = args.threads if args.threads is not None else 1
            roles = parse_roles(args.roles, threads)
            solver = ParallelMaxSMTSolver(
                args.file,
                roles=roles,
                threads=threads,
                seed=args.seed,
                timeout=args.timeout,
                trace=trace,
                verify_optimal=not args.no_verify,
            )
        _install_interrupt_handler()
        result = solver.solve()
        if args.certificate and result.certificate is not None:
            Path(args.certificate).write_text(json.dumps(result.certificate, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(json.dumps({"event": "final", **result.as_dict()}, sort_keys=True))
        if result.status in {"OPTIMAL", "UNSAT"} and not result.threads_alive:
            return 0
        if result.status == "SAT":
            return 10
        return 20
    except Exception as exc:
        print(json.dumps({"event": "error", "error": str(exc)}, sort_keys=True))
        return 2
    finally:
        trace.close()


if __name__ == "__main__":
    raise SystemExit(main())
