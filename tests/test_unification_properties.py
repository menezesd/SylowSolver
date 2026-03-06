import random
import string

from sylow_solver.facts import Fact
from sylow_solver.search import _unify_facts, match_facts_to_template
from sylow_solver.substitution import Substitution


def _random_symbol(length: int = 3) -> str:
    return "".join(random.choice(string.ascii_uppercase) for _ in range(length))


def test_unify_respects_reused_variables():
    # Generate templates with repeated variable names to force consistent bindings.
    for _ in range(20):
        arity = random.randint(2, 4)
        var_names = [f"X{random.randint(0, arity // 2)}" for _ in range(arity)]
        template = Fact("foo", var_names)

        assignments = {}
        fact_args = []
        for var in var_names:
            if var not in assignments:
                assignments[var] = _random_symbol()
            fact_args.append(assignments[var])
        fact = Fact("foo", fact_args)

        subst = Substitution.empty()
        assert _unify_facts(template, fact, subst)
        assert dict(subst.items()) == assignments


def test_unify_exact_match_guard():
    template = Fact("bar", ["*A", "X"])
    matching_fact = Fact("bar", ["A", "B"])
    failing_fact = Fact("bar", ["C", "B"])

    assert _unify_facts(template, matching_fact, Substitution.empty()) is True
    assert _unify_facts(template, failing_fact, Substitution.empty()) is False


def test_match_facts_to_template_includes_all_matches():
    facts = [
        Fact("edge", ["A", "B"]),
        Fact("edge", ["A", "C"]),
        Fact("edge", ["B", "C"]),
    ]
    template = Fact("edge", ["*A", "X"])
    matches, substitutions = match_facts_to_template(template, facts)

    # Only facts starting with "A" should match due to the *A literal.
    assert len(matches) == 2
    assert all(f.args[0] == "A" for f in matches)

    # Verify substitution dictionaries align with matched facts.
    for match, subst in zip(matches, substitutions):
        assert subst["X"] == match.args[1]
