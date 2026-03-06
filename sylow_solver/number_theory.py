"""Number-theoretic utilities for Sylow theorem computations."""

from typing import List, Tuple


def divisors(n: int) -> List[int]:
    """Computes the sorted list of divisors of n in O(sqrt(n)) time."""
    if n <= 0:
        return []
    divs = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            divs.append(i)
            if i != n // i:
                divs.append(n // i)
        i += 1
    return sorted(divs)


def is_prime(p: int) -> bool:
    """Determines if a number is prime using trial division."""
    if p < 2:
        return False
    if p == 2:
        return True
    if p % 2 == 0:
        return False
    i = 3
    while i * i <= p:
        if p % i == 0:
            return False
        i += 2
    return True


def primes(n: int) -> List[int]:
    """Generates a list of prime numbers up to and including n."""
    if n < 2:
        return []
    sieve = [True] * (n + 1)
    sieve[0] = sieve[1] = False
    i = 2
    while i * i <= n:
        if sieve[i]:
            for j in range(i * i, n + 1, i):
                sieve[j] = False
        i += 1
    return [i for i, is_p in enumerate(sieve) if is_p]


def max_p_divisor(n: int, p: int) -> int:
    """Finds the maximum k such that p^k divides n."""
    k = 0
    while n % p == 0:
        k += 1
        n //= p
    return k


def prime_factors(n: int) -> List[int]:
    """Computes the sorted list of prime factors of n in O(sqrt(n)) time."""
    if n <= 1:
        return []
    factors = []
    if n % 2 == 0:
        factors.append(2)
        while n % 2 == 0:
            n //= 2
    i = 3
    while i * i <= n:
        if n % i == 0:
            factors.append(i)
            while n % i == 0:
                n //= i
        i += 2
    if n > 1:
        factors.append(n)
    return factors


def prime_factorization(n: int) -> List[Tuple[int, int]]:
    """Computes the prime factorization of n as a list of (prime, exponent) tuples."""
    if n <= 1:
        return []
    factorization = []
    if n % 2 == 0:
        exp = 0
        while n % 2 == 0:
            exp += 1
            n //= 2
        factorization.append((2, exp))
    i = 3
    while i * i <= n:
        if n % i == 0:
            exp = 0
            while n % i == 0:
                exp += 1
                n //= i
            factorization.append((i, exp))
        i += 2
    if n > 1:
        factorization.append((n, 1))
    return factorization


def num_sylow(p: int, n: int) -> List[int]:
    """Computes possible numbers of Sylow p-subgroups in a group of order n."""
    return [d for d in divisors(n) if d % p == 1]


def p_killable(p: int, n: int) -> bool:
    """Determines if the Sylow p-subgroup is automatically normal."""
    for d in divisors(n):
        if d > 1 and d % p == 1:
            return False
    return True


def sylow_killable(n: int) -> bool:
    """Determines if some Sylow p-subgroup is automatically normal."""
    if n == 1:
        return True
    p_factors = prime_factors(n)
    p_factors.reverse()
    for p in p_factors:
        if p_killable(p, n):
            return True
    return False
