from sylow_solver import (
    DEFAULT_THEOREM_DICT,
    DEFAULT_THEOREMS,
    Disjunction,
    Fact,
    ProofEnvironment,
    Theorem,
    auto_solve,
    match_facts_to_theorem,
)
from sylow_solver.config import SolverConfig
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
