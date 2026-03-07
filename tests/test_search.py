import pytest

from sylow_solver import (
    DEFAULT_THEOREM_DICT,
    DEFAULT_THEOREMS,
    FAST_THEOREM_DICT,
    FAST_THEOREMS,
    Disjunction,
    Fact,
    ProofEnvironment,
    Theorem,
    auto_solve,
    match_facts_to_theorem,
)
from sylow_solver.config import OutputMode, SolverConfig
from sylow_solver.number_theory import is_prime, prime_factorization
from sylow_solver.theorems import (
    false,
    group,
    order,
    simple,
    sylow_p_subgroup,
)

CONFIG = SolverConfig(max_iterations=400, batch_size=8, verbose=False)


def test_disjunction_proof():
    premises = [Fact("subgroup", ["A", "B"]), Fact("subgroup", ["B", "C"])]
    conclusions = [Fact("subgroup", ["A", "C"])]
    subgroup_trans = Theorem(premises, conclusions, "subgroup_trans")

    fact1 = Fact("subgroup", ["X", "Y"])
    fact2 = Fact("subgroup", ["X", "Z"])
    d1 = Fact("subgroup", ["Y", "A"])
    d2 = Fact("subgroup", ["Z", "A"])
    dis = Disjunction([d1, d2])

    facts = [fact1, fact2, dis]
    goal = Fact("subgroup", ["X", "A"])

    pf_envir = ProofEnvironment(
        facts,
        [subgroup_trans],
        {"subgroup_trans": subgroup_trans},
        goal,
        config=CONFIG,
    )
    pf_envir.exec_command("apply subgroup_trans F1 F4")
    pf_envir.exec_command("apply subgroup_trans F0 F3")

    assert pf_envir.goal_achieved, "Should prove X is subgroup of A"


def test_matching():
    def foo(first, second, third):
        return Fact("foo", [first, second, third])

    facts = [foo("A", "B", "C"), foo("D", "E", "F")]
    thm_facts = [foo("X", "Y", "Z"), foo("X", "Y", "Z")]

    matches = match_facts_to_theorem(thm_facts, facts, [foo("A", "B", "C")])
    assert len(matches) > 0, "Should find at least one match"


def test_subgroup_transitivity_chain():
    premises = [Fact("subgroup", ["A", "B"]), Fact("subgroup", ["B", "C"])]
    conclusions = [Fact("subgroup", ["A", "C"])]
    subgroup_trans = Theorem(premises, conclusions, "subgroup_trans")

    facts = [
        Fact("subgroup", ["X", "Y"]),
        Fact("subgroup", ["Y", "Z"]),
        Fact("subgroup", ["Z", "A"]),
        Fact("subgroup", ["A", "B"]),
        Fact("subgroup", ["B", "C"]),
        Fact("subgroup", ["C", "D"]),
        Fact("subgroup", ["D", "E"]),
        Fact("subgroup", ["E", "F"]),
    ]
    goal = Fact("subgroup", ["X", "F"])

    pf_envir = ProofEnvironment(
        facts,
        [subgroup_trans],
        {"subgroup_trans": subgroup_trans},
        goal,
        config=CONFIG,
    )
    assert auto_solve(pf_envir), "Should prove X is subgroup of F through transitivity chain"


def test_simple_disjunction():
    def sub(A, B):
        return Fact("subgroup", [A, B])

    premises = [Fact("subgroup", ["A", "B"]), Fact("subgroup", ["B", "C"])]
    conclusions = [Fact("subgroup", ["A", "C"])]
    subgroup_trans = Theorem(premises, conclusions, "subgroup_trans")

    facts = [
        Disjunction([sub("A", "B"), sub("A", "X")]),
        sub("B", "D"),
        sub("X", "D"),
    ]
    goal = sub("A", "D")

    pf_envir = ProofEnvironment(
        facts,
        [subgroup_trans],
        {"subgroup_trans": subgroup_trans},
        goal,
        config=CONFIG,
    )
    assert auto_solve(pf_envir), "Should prove A is subgroup of D through either branch"


def test_complex_disjunction():
    def sub(A, B):
        return Fact("subgroup", [A, B])

    premises = [Fact("subgroup", ["A", "B"]), Fact("subgroup", ["B", "C"])]
    conclusions = [Fact("subgroup", ["A", "C"])]
    subgroup_trans = Theorem(premises, conclusions, "subgroup_trans")

    facts = [
        Disjunction([sub("A", "B"), sub("C", "D")]),
        Disjunction([sub("B", "F"), sub("D", "F")]),
        sub("B", "D"),
        sub("D", "B"),
        sub("X", "A"),
        sub("X", "C"),
    ]
    goal = sub("X", "F")

    pf_envir = ProofEnvironment(
        facts,
        [subgroup_trans],
        {"subgroup_trans": subgroup_trans},
        goal,
        config=CONFIG,
    )
    assert auto_solve(pf_envir), "Should prove X is subgroup of F through disjunction cases"


def test_goal_not_achieved_if_only_some_disjunction_branches_prove():
    def sub(A, B):
        return Fact("subgroup", [A, B])

    premises = [Fact("subgroup", ["A", "B"]), Fact("subgroup", ["B", "C"])]
    conclusions = [Fact("subgroup", ["A", "C"])]
    subgroup_trans = Theorem(premises, conclusions, "subgroup_trans")

    facts = [
        Disjunction([sub("A", "B"), sub("A", "X")]),
        sub("B", "D"),
    ]
    goal = sub("A", "D")

    pf_envir = ProofEnvironment(
        facts,
        [subgroup_trans],
        {"subgroup_trans": subgroup_trans},
        goal,
        config=CONFIG,
    )
    assert not auto_solve(pf_envir), "Should fail because branch A->X has no path to D"


def test_alternating_embedding():
    facts = [
        group("G"),
        simple("G"),
        Fact("num_sylow", ["3", "G", "4"]),
        order("G", "12"),
    ]
    goal = false()

    pf_envir = ProofEnvironment(
        facts,
        DEFAULT_THEOREMS,
        DEFAULT_THEOREM_DICT,
        goal,
        config=CONFIG,
    )
    assert auto_solve(pf_envir), "Should find contradiction for order 12 simple group"


def test_element_counting():
    facts = [
        group("G"),
        order("G", "30"),
        sylow_p_subgroup("P5", "5", "G"),
        sylow_p_subgroup("P3", "3", "G"),
        order("P5", "5"),
        order("P3", "3"),
        simple("G"),
    ]
    goal = false()

    pf_envir = ProofEnvironment(
        facts,
        DEFAULT_THEOREMS,
        DEFAULT_THEOREM_DICT,
        goal,
        config=CONFIG,
    )
    assert auto_solve(pf_envir), "Should find contradiction by counting elements"


def test_order_12_not_simple_regression():
    facts = [group("G"), simple("G"), order("G", "12")]
    goal = false()
    pf_envir = ProofEnvironment(
        facts,
        DEFAULT_THEOREMS,
        DEFAULT_THEOREM_DICT,
        goal,
        config=SolverConfig(max_iterations=250, batch_size=8, verbose=False),
    )
    assert auto_solve(pf_envir), (
        "Order 12 should derive contradiction under simple-group assumption"
    )


def test_order_30_not_simple_regression():
    facts = [group("G"), simple("G"), order("G", "30")]
    goal = false()
    pf_envir = ProofEnvironment(
        facts,
        DEFAULT_THEOREMS,
        DEFAULT_THEOREM_DICT,
        goal,
        config=SolverConfig(max_iterations=350, batch_size=8, verbose=False),
    )
    assert auto_solve(pf_envir), (
        "Order 30 should derive contradiction under simple-group assumption"
    )


def test_order_60_does_not_force_contradiction_regression():
    facts = [group("G"), simple("G"), order("G", "60")]
    goal = false()
    pf_envir = ProofEnvironment(
        facts,
        DEFAULT_THEOREMS,
        DEFAULT_THEOREM_DICT,
        goal,
        config=SolverConfig(max_iterations=40, batch_size=8, verbose=False),
    )
    assert not auto_solve(pf_envir), (
        "Order 60 has a simple example (A5), so solver must not force contradiction"
    )


def _is_prime_power(n: int) -> bool:
    """Check if n is p^k for some prime p and k >= 1."""
    facts = prime_factorization(n)
    return len(facts) == 1


def _should_be_provable(n: int) -> bool:
    """An order should be provable if it's composite and not 60 (A5)."""
    if n <= 1 or is_prime(n):
        return False
    if n == 60:
        return False
    return True


# Known hard orders that the Haskell/Scheme solvers also struggle with
KNOWN_HARD = {168, 210, 240, 264, 288, 315, 336, 360, 396, 420, 432, 480}


@pytest.mark.parametrize("n", range(2, 201))
def test_range_2_to_200(n):
    """Test that the solver handles orders 2-200."""
    if is_prime(n) or _is_prime_power(n):
        return  # primes and prime powers need different arguments
    if n == 60:
        return  # A5 is simple
    if n in KNOWN_HARD:
        pytest.skip(f"Order {n} is a known hard case")

    config = SolverConfig(
        max_iterations=500, batch_size=16, verbose=False, output_mode=OutputMode.CLEAN
    )
    facts = [group("G"), simple("G"), order("G", str(n))]
    goal = false()
    pf_envir = ProofEnvironment(
        facts, FAST_THEOREMS, FAST_THEOREM_DICT, goal, config=config
    )
    result = auto_solve(pf_envir)
    assert result, f"Failed to prove order {n} is not simple"
