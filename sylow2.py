import math

prime_list = []


# computes the possible numbers of sylow-p subgroups in a group of order n
# too slow for huge orders
def num_sylow(p, n):
    """
    Computes the possible numbers of Sylow p-subgroups in a group of order n.

    Args:
        p (int): A prime number.
        n (int): The order of the group.

    Returns:
        list: A list of possible numbers of Sylow p-subgroups.
    """
    n_p = []
    for i in range(0, n):
        if (i % p == 1) and (n % i == 0):
            n_p.append(i)
    return n_p


# is the sylow p automatically normal?
def p_killable(p, n):
    """
    Determines if the Sylow p-subgroup is automatically normal in a group of order n.

    Args:
        p (int): A prime number.
        n (int): The order of the group.

    Returns:
        bool: True if the Sylow p-subgroup is automatically normal, False otherwise.
    """
    div = divisors(n)
    div.remove(1)
    for d in div:
        if d % p == 1:
            return False
    return True


# is p prime?
def prime(p):
    """
    Determines if a number is prime.

    Args:
        p (int): The number to be checked for primality.

    Returns:
        bool: True if p is prime, False otherwise.
    """
    if p == 1:
        return False
    u = int(math.sqrt(p)) + 1
    for i in range(2, u):
        if p % i == 0:
            return False
    return True


# list of primes up to and including n
# could be much faster
def primes(n):
    """
    Generates a list of prime numbers up to and including n.

    Args:
        n (int): The upper bound for the prime numbers.

    Returns:
        list: A list of prime numbers up to and including n.
    """
    return [i for i in range(1, n + 1) if prime(i)]


# returns k, maximal such that p^k divides n
def max_p_divisor(n, p):
    """
    Finds the maximum value of k such that p^k divides n.

    Args:
        n (int): The number to be divided.
        p (int): The prime number.

    Returns:
        int: The maximum value of k such that p^k divides n.
    """
    k = 0
    while n % p == 0:
        k += 1
        n = n // p  # probably not as fast as possible
    return k


# slower than necessary
def prime_factorization(n):
    """
    Computes the prime factorization of n.

    Args:
        n (int): The number to be factored.

    Returns:
        list: A list of prime factors and their exponents in the factorization of n.
    """
    global prime_list
    factorization = []
    for p in prime_list:
        if n % p == 0:
            factorization.append([p, max_p_divisor(n, p)])
    return factorization


# def primeFactors(n):
#    factorization = primeFactorization(n)
#    return [a[0] for a in factorization]


def divisors(n):
    """
    Computes the list of divisors of n.

    Args:
        n (int): The number for which divisors are to be computed.

    Returns:
        list: A list of divisors of n.
    """
    divs = []
    for i in range(1, n + 1):
        if n % i == 0:
            divs.append(i)
    return divs


# is there automatically a normal sylow-p for some p?
def sylow_killable(n):
    """Determines if there exists a prime p such that the Sylow
    p-subgroup is automatically normal in a group of order n.

    Args:
        n (int): The order of the group.

    Returns: 
    bool: True if there exists a prime p such that the Sylow
        p-subgroup is automatically normal, False otherwise.

    """
    if n == 1:
        return True

    p_factors = prime_factors(n)
    p_factors.reverse()  # try big primes first

    for p in p_factors:
        if p_killable(p, n):
            return True

    return False


def prime_factors(n):
    """
    Computes the list of prime factors of n.

    Args:
        n (int): The number for which prime factors are to be computed.

    Returns:
        list: A list of prime factors of n.
    """
    factors = []
    for i in range(1, n + 1):
        if n % i == 0:
            if prime(i):
                factors.append(i)
    return factors


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
