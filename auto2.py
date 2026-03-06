"""Automated theorem prover entrypoint for Sylow theory (Python version)."""

from __future__ import annotations

import argparse
import logging
from typing import Iterable, List

from sylow_solver.config import OutputMode, SolverConfig
from sylow_solver.facts import Fact
from sylow_solver.logging_utils import get_logger
from sylow_solver.search import ProofEnvironment, auto_solve
from sylow_solver.theorems import (
    DEFAULT_THEOREM_DICT,
    DEFAULT_THEOREMS,
    false,
    group,
    order,
    simple,
)


def build_environment(
    order_value: int, config: SolverConfig, logger: logging.Logger
) -> ProofEnvironment:
    """Create a proof environment for a group of given order."""
    facts: List[Fact] = [group("G"), simple("G"), order("G", str(order_value))]
    return ProofEnvironment(
        list(facts),
        DEFAULT_THEOREMS,
        DEFAULT_THEOREM_DICT,
        false(),
        config=config,
        logger=logger,
    )


def _parse_positive_order(raw: str) -> int | None:
    """Parse and validate a positive integer order."""
    try:
        value = int(raw)
    except ValueError:
        return None
    if value <= 0:
        return None
    return value


def solve_orders(orders: Iterable[str], config: SolverConfig, logger: logging.Logger) -> List[bool]:
    """Run the solver for each provided order and return success flags."""
    results: List[bool] = []
    processed = 0
    invalid = 0
    for raw_order in orders:
        order_value = _parse_positive_order(raw_order)
        if order_value is None:
            invalid += 1
            results.append(False)
            print(f"order {raw_order}: INVALID (must be a positive integer)")
            continue

        processed += 1
        env = build_environment(order_value, config, logger)
        logger.info("Starting proof search for |G| = %s", order_value)
        success = auto_solve(env)
        results.append(success)
        status = "SUCCESS" if success else "FAILURE"
        print(f"order {order_value}: {status}")
    if processed + invalid > 1:
        proved = sum(1 for result in results if result)
        print(
            f"summary: processed={processed}, proved={proved}, "
            f"failed={processed - proved}, invalid={invalid}"
        )
    return results


def interactive_loop(config: SolverConfig, logger: logging.Logger) -> None:
    """Interactive REPL for exploring proofs by group order."""
    while True:
        try:
            n = input("Enter a group order (or 'quit'): ").strip()
            if n.lower() == "quit":
                break
            if not n:
                continue
            solve_orders([n], config, logger)
        except KeyboardInterrupt:
            break


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Automated Sylow theorem prover (Python).")
    parser.add_argument(
        "orders",
        nargs="*",
        help="Group orders to test (omit for interactive mode).",
    )
    parser.add_argument(
        "--max-iterations",
        type=int,
        default=SolverConfig().max_iterations,
        help="Maximum iterations for proof search.",
    )
    parser.add_argument(
        "--batch-size",
        type=int,
        default=SolverConfig().batch_size,
        help="Batch size for agenda processing.",
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Enable verbose solver logging.",
    )
    parser.add_argument(
        "--tree",
        action="store_true",
        help="Use tree view output mode.",
    )
    parser.add_argument(
        "--classic",
        action="store_true",
        help="Use classic output mode.",
    )
    parser.add_argument(
        "--clean",
        action="store_true",
        help="Use clean output mode (default).",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    output_mode = OutputMode.CLEAN
    if args.tree:
        output_mode = OutputMode.TREE
    elif args.classic:
        output_mode = OutputMode.CLASSIC

    config = SolverConfig(
        max_iterations=args.max_iterations,
        batch_size=args.batch_size,
        verbose=args.verbose,
        output_mode=output_mode,
    )
    log_level = logging.INFO if args.verbose else logging.WARNING
    logger = get_logger("sylow_solver", level=log_level)

    if args.orders:
        solve_orders(args.orders, config, logger)
    else:
        interactive_loop(config, logger)


if __name__ == "__main__":
    main()
