import sylow2


def test_divisors_ordering():
    assert sylow2.divisors(12) == [1, 2, 3, 4, 6, 12]
    assert sylow2.divisors(1) == [1]
    assert sylow2.divisors(0) == []


def test_prime_factorization():
    assert sylow2.prime_factorization(60) == [(2, 2), (3, 1), (5, 1)]
    assert sylow2.prime_factorization(13) == [(13, 1)]
    assert sylow2.prime_factors(84) == [2, 3, 7]


def test_num_sylow_constraints():
    # For p=3, |G|=12, valid n_p are divisors of 12 congruent 1 mod 3
    assert sylow2.num_sylow(3, 12) == [1, 4]
    # For p=5, |G|=30, divisors congruent to 1 mod 5 are 1 and 6
    assert sylow2.num_sylow(5, 30) == [1, 6]
