"""sylow2 — number-theory utilities used by the Sylow solver.

This module provides small, efficient helpers for primes, divisors and
prime factorizations used by the proof engine. The implementation is a
lightweight refactor of the original project utilities to avoid a global
prime list and to improve performance for moderate inputs.
"""

import math
from typing import List, Tuple


# --- Utility number-theory helpers (faster versions) ---


def is_prime(n: int) -> bool:
    """Return True if n is prime.

    Uses simple deterministic trial division (sufficient for moderate n).
    """
    if n <= 1:
        return False
    if n <= 3:
        return True
    if n % 2 == 0:
        return False
    r = int(math.isqrt(n))
    i = 3
    while i <= r:
        if n % i == 0:
            return False
        i += 2
    return True


def primes(n: int) -> List[int]:
    """Return list of primes up to and including n using a simple sieve.

    The original code exposed a `primes(n)` function; keep the name and
    basic behaviour but make it significantly faster.
    """
    if n < 2:
        return []
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, int(math.isqrt(n)) + 1):
        if sieve[p]:
            step = p
            start = p * p
            sieve[start : n + 1 : step] = b"\x00" * (((n - start) // step) + 1)
    return [i for i, is_p in enumerate(sieve) if is_p]


def divisors(n: int) -> List[int]:
    """Return the divisors of n (unsorted order may vary)."""
    if n <= 0:
        return []
    divs = []
    r = int(math.isqrt(n))
    for i in range(1, r + 1):
        if n % i == 0:
            divs.append(i)
            j = n // i
            if j != i:
                divs.append(j)
    divs.sort()
    return divs


def max_p_divisor(n: int, p: int) -> int:
    """Return k maximal such that p**k divides n."""
    k = 0
    while n % p == 0:
        k += 1
        n //= p
    return k


def prime_factors(n: int) -> List[int]:
    """Return the list of prime divisors of n in ascending order.

    This is more efficient than testing every integer up to n.
    """
    if n <= 1:
        return []
    factors: List[int] = []
    # handle factor 2
    if n % 2 == 0:
        factors.append(2)
        while n % 2 == 0:
            n //= 2
    p = 3
    r = int(math.isqrt(n))
    while p <= r and n > 1:
        if n % p == 0:
            factors.append(p)
            while n % p == 0:
                n //= p
            r = int(math.isqrt(n))
        p += 2
    if n > 1:
        factors.append(n)
    return factors


def prime_factorization(n: int) -> List[Tuple[int, int]]:
    """Return prime factorization as a list of (prime, exponent).

    Kept for backward compatibility. Example: 12 -> [(2,2),(3,1)].
    """
    factors: List[Tuple[int, int]] = []
    for p in prime_factors(n):
        e = max_p_divisor(n, p)
        factors.append((p, e))
    return factors


# --- Public API kept for compatibility with original code ---


def prime(p: int) -> bool:
    """Compatibility wrapper for `is_prime`."""
    return is_prime(p)


def num_sylow(p: int, n: int) -> List[int]:
    """Return divisors d of n with d ≡ 1 (mod p).

    This mirrors the original behaviour but uses faster divisor enumeration.
    """
    return [d for d in divisors(n) if d % p == 1]


def p_killable(p: int, n: int) -> bool:
    """Return True if there is no divisor d>1 of n with d ≡ 1 (mod p).

    Matches the original semantics: check all divisors except 1.
    """
    divs = divisors(n)
    try:
        divs.remove(1)
    except ValueError:
        pass
    for d in divs:
        if d % p == 1:
            return False
    return True


__all__ = [
    "num_sylow",
    "p_killable",
    "prime",
    "primes",
    "max_p_divisor",
    "prime_factorization",
    "divisors",
    "sylow_killable",
    "prime_factors",
]


def sylow_killable(n: int) -> bool:
    """Return True if there exists a prime p dividing n for which p_killable(p,n) is True."""
    if n == 1:
        return True
    p_factors = prime_factors(n)
    p_factors.reverse()  # try big primes first (keeps previous heuristic)
    for p in p_factors:
        if p_killable(p, n):
            return True
    return False



# print(divisors(12))
# print out the "interesting" group orders

# upper = int(input("interesting orders up to... : "))

# prime_list = primes(upper)

# print("killable: ", sylow_killable(upper))

# print(divisors(n))

# count = 0
# for n in range(1,upper):
#        if n % 1000 == 0: print(n)
#        if(not sylow_killable(n)):
#                print(n)
#                count += 1
# print("count: ", count)
