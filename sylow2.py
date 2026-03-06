"""Number-theoretic utilities for Sylow theorem computations.

This module re-exports from sylow_solver.number_theory for backward compatibility.
"""

from sylow_solver.number_theory import (
    divisors,
    is_prime,
    max_p_divisor,
    num_sylow,
    p_killable,
    prime_factorization,
    prime_factors,
    primes,
    sylow_killable,
)

# Alias for backwards compatibility
prime = is_prime

__all__ = [
    "divisors",
    "is_prime",
    "max_p_divisor",
    "num_sylow",
    "p_killable",
    "prime",
    "prime_factorization",
    "prime_factors",
    "primes",
    "sylow_killable",
]
