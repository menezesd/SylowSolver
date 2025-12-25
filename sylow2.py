"""Number-theoretic utilities for Sylow theorem computations.

This module provides fundamental number-theoretic functions needed for
group theory calculations, particularly for computing Sylow subgroup properties.
"""

from typing import List, Tuple


def divisors(n: int) -> List[int]:
    """
    Computes the list of divisors of n in O(√n) time.

    Args:
        n: The number for which divisors are to be computed.

    Returns:
        A sorted list of divisors of n.
    """
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
    """
    Determines if a number is prime using trial division.

    Args:
        p: The number to be checked for primality.

    Returns:
        True if p is prime, False otherwise.
    """
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


# Alias for backwards compatibility
prime = is_prime


def primes(n: int) -> List[int]:
    """
    Generates a list of prime numbers up to and including n using Sieve of Eratosthenes.

    Args:
        n: The upper bound for the prime numbers.

    Returns:
        A list of prime numbers up to and including n.
    """
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
    """
    Finds the maximum value of k such that p^k divides n.

    Args:
        n: The number to be divided.
        p: The prime number.

    Returns:
        The maximum value of k such that p^k divides n.
    """
    k = 0
    while n % p == 0:
        k += 1
        n //= p
    return k


def prime_factors(n: int) -> List[int]:
    """
    Computes the list of prime factors of n in O(√n) time.

    Args:
        n: The number for which prime factors are to be computed.

    Returns:
        A sorted list of prime factors of n.
    """
    if n <= 1:
        return []
    factors = []
    # Check for 2
    if n % 2 == 0:
        factors.append(2)
        while n % 2 == 0:
            n //= 2
    # Check odd factors
    i = 3
    while i * i <= n:
        if n % i == 0:
            factors.append(i)
            while n % i == 0:
                n //= i
        i += 2
    # If n is still greater than 1, it's a prime factor
    if n > 1:
        factors.append(n)
    return factors


def prime_factorization(n: int) -> List[Tuple[int, int]]:
    """
    Computes the prime factorization of n.

    Args:
        n: The number to be factored.

    Returns:
        A list of (prime, exponent) tuples in the factorization of n.
    """
    if n <= 1:
        return []
    factorization = []
    # Check for 2
    if n % 2 == 0:
        exp = 0
        while n % 2 == 0:
            exp += 1
            n //= 2
        factorization.append((2, exp))
    # Check odd factors
    i = 3
    while i * i <= n:
        if n % i == 0:
            exp = 0
            while n % i == 0:
                exp += 1
                n //= i
            factorization.append((i, exp))
        i += 2
    # If n is still greater than 1, it's a prime factor
    if n > 1:
        factorization.append((n, 1))
    return factorization


def num_sylow(p: int, n: int) -> List[int]:
    """
    Computes the possible numbers of Sylow p-subgroups in a group of order n.

    By Sylow's theorem, the number of Sylow p-subgroups n_p must satisfy:
    - n_p ≡ 1 (mod p)
    - n_p divides n

    Args:
        p: A prime number.
        n: The order of the group.

    Returns:
        A list of possible numbers of Sylow p-subgroups.
    """
    return [d for d in divisors(n) if d % p == 1]


def p_killable(p: int, n: int) -> bool:
    """
    Determines if the Sylow p-subgroup is automatically normal in a group of order n.

    A Sylow p-subgroup is automatically normal if there is only one possible
    count for Sylow p-subgroups (which must be 1).

    Args:
        p: A prime number.
        n: The order of the group.

    Returns:
        True if the Sylow p-subgroup is automatically normal, False otherwise.
    """
    for d in divisors(n):
        if d > 1 and d % p == 1:
            return False
    return True


def sylow_killable(n: int) -> bool:
    """
    Determines if there exists a prime p such that the Sylow p-subgroup
    is automatically normal in a group of order n.

    Args:
        n: The order of the group.

    Returns:
        True if there exists a prime p such that the Sylow p-subgroup
        is automatically normal, False otherwise.
    """
    if n == 1:
        return True

    p_factors = prime_factors(n)
    p_factors.reverse()  # try big primes first

    for p in p_factors:
        if p_killable(p, n):
            return True

    return False
