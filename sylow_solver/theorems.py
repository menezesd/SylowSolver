from __future__ import annotations

import math
from typing import Dict, List, Union

import sylow2

from .facts import Disjunction, Fact
from .predicates import Predicates
from .theorem_base import HyperTheorem, Theorem

################################### FACT GENERATORS ######################################


def group(G: str) -> Fact:
    return Fact(Predicates.GROUP.value, [G])


def order(G: str, n: str) -> Fact:
    return Fact(Predicates.ORDER.value, [G, n])


def sylow_p_order(G: str, p: str, pk: str) -> Fact:
    return Fact(Predicates.SYLOW_ORDER.value, [G, p, pk])


def sylow_p_subgroup(P: str, p: str, G: str) -> Fact:
    return Fact(Predicates.SYLOW_P_SUBGROUP.value, [P, p, G])


def alternating_group(A: str, n: str) -> Fact:
    return Fact(Predicates.ALTERNATING_GROUP.value, [A, n])


def num_sylow(p: str, G: str, n: str) -> Fact:
    return Fact(Predicates.NUM_SYLOW.value, [p, G, n])


def simple(G: str) -> Fact:
    return Fact(Predicates.SIMPLE.value, [G])


def not_simple(G: str) -> Fact:
    return Fact(Predicates.NOT_SIMPLE.value, [G])


def subgroup(H: str, G: str) -> Fact:
    return Fact(Predicates.SUBGROUP.value, [H, G])


def divides(m: str, n: str) -> Fact:
    return Fact(Predicates.DIVIDES.value, [m, n])


def false() -> Fact:
    return Fact(Predicates.FALSE.value, [])


def index(G: str, H: str, n: str) -> Fact:
    return Fact(Predicates.INDEX.value, [G, H, n])


def transitive_action(G: str, n: str) -> Fact:
    return Fact(Predicates.TRANSITIVE_ACTION.value, [G, n])


def order_pk_lower_bound(G: str, p: str, N: str) -> Fact:
    return Fact(Predicates.ORDER_PK_LOWER_BOUND.value, [G, p, N])


def more_than_one_sylow(p: str, G: str) -> Fact:
    return Fact(Predicates.MORE_THAN_ONE_SYLOW.value, [p, G])


def intersection(A: str, B: str, C: str) -> Fact:
    return Fact(Predicates.INTERSECTION.value, [A, B, C])


def normalizer(G: str, H: str, K: str) -> Fact:
    return Fact(Predicates.NORMALIZER.value, [G, H, K])


def order_lower_bound(H: str, n: str) -> Fact:
    return Fact(Predicates.ORDER_LOWER_BOUND.value, [H, n])


def max_sylow_intersection(G: str, p: str, m: str) -> Fact:
    return Fact(Predicates.MAX_SYLOW_INTERSECTION.value, [G, p, m])


def proper_subgroup(H: str, G: str) -> Fact:
    return Fact(Predicates.PROPER_SUBGROUP.value, [H, G])


def normal(H: str, G: str) -> Fact:
    return Fact(Predicates.NORMAL.value, [H, G])


def normalizer_of_sylow_intersection(p: str, G: str, T: str) -> Fact:
    return Fact(Predicates.NORMALIZER_OF_SYLOW_INTERSECTION.value, [p, G, T])


def OR(f1: Fact, f2: Fact) -> Disjunction:
    return Disjunction([f1, f2])


####################################### THEOREMS #######################################

# sylow's theorem
in_facts = [group("G"), order("G", "n")]


def _sylow_rule(facts: List[Fact]) -> List[Union[Fact, Disjunction]]:
    conclusions: List[Union[Fact, Disjunction]] = []
    group_name = facts[0].args[0]
    group_order = int(facts[1].args[1])
    for p in sylow2.prime_factors(group_order):
        sylow_order = p ** sylow2.max_p_divisor(group_order, p)
        conclusions.append(sylow_p_order(group_name, str(p), str(sylow_order)))
        conclusions.append(sylow_p_subgroup("?" + str(p), str(p), group_name))
        conclusions.append(order("?" + str(p), str(sylow_order)))
        n_p_list = sylow2.num_sylow(p, group_order)
        dis_facts = []
        for n_p in n_p_list:
            dis_facts.append(Fact(Predicates.NUM_SYLOW.value, [str(p), group_name, str(n_p)]))
        if len(dis_facts) == 1:
            conclusions.append(dis_facts[0])
        else:
            dis = Disjunction(dis_facts)
            conclusions.append(dis)
    return conclusions


sylow_theorem = HyperTheorem(in_facts, _sylow_rule, "sylow")

# single sylow subgroup
in_facts = [
    Fact(Predicates.SYLOW_P_SUBGROUP.value, ["H", "p", "G"]),
    Fact(Predicates.NUM_SYLOW.value, ["p", "G", "*1"]),
    Fact(Predicates.ORDER.value, ["G", "n"]),
]


def _single_sylow_rule(facts: List[Fact]) -> List[Fact]:
    conclusions: List[Fact] = []
    G = facts[0].args[2]
    p = int(facts[0].args[1])
    n = int(facts[2].args[1])
    p_power = True
    while n != 1:
        if n % p != 0:
            p_power = False
            break
        n = n // p
    if not p_power:
        conclusions = [Fact(Predicates.NOT_SIMPLE.value, [G])]
    return conclusions


single_sylow_not_simple = HyperTheorem(
    in_facts, _single_sylow_rule, "single_sylow_normal"
)

# simple + not_simple = false
in_facts = [Fact(Predicates.SIMPLE.value, ["G"]), Fact(Predicates.NOT_SIMPLE.value, ["G"])]
out_facts = [Fact(Predicates.FALSE.value, [])]
simple_not_simple = Theorem(in_facts, out_facts, "not_simple")

# embed into A_n
in_facts = [
    Fact(Predicates.NUM_SYLOW.value, ["p", "G", "n_p"]),
    Fact(Predicates.SIMPLE.value, ["G"]),
]


def _embed_in_an_rule(facts: List[Fact]) -> List[Fact]:
    conclusions: List[Fact] = []
    n_p = int(facts[0].args[2])
    G = facts[0].args[1]
    if n_p > 1:
        conclusions = [subgroup(G, "?alt"), alternating_group("?alt", str(n_p))]
    return conclusions


embed_in_An = HyperTheorem(in_facts, _embed_in_an_rule, "embed_An")

in_facts = [alternating_group("A", "n")]


def _alternating_order_rule(facts: List[Fact]) -> List[Fact]:
    A = facts[0].args[0]
    n = int(facts[0].args[1])

    if n > 1000:
        return []

    if n == 1:
        order_value = 1
    else:
        order_value = math.factorial(n) // 2
    conclusions = [Fact(Predicates.ORDER.value, [A, str(order_value)])]
    return conclusions


alternating_order = HyperTheorem(in_facts, _alternating_order_rule, "alternating_order")

# order of a subgroup divides the order of the group
in_facts = [
    Fact(Predicates.SUBGROUP.value, ["H", "G"]),
    Fact(Predicates.ORDER.value, ["H", "n"]),
    Fact(Predicates.ORDER.value, ["G", "m"]),
]
out_facts = [Fact(Predicates.DIVIDES.value, ["n", "m"])]
lagrange = Theorem(in_facts, out_facts, "lagrange")

# check if m divides n
in_facts = [Fact(Predicates.DIVIDES.value, ["m", "n"])]


def _divides_contradiction_rule(facts: List[Fact]) -> List[Fact]:
    m = int(facts[0].args[0])
    n = int(facts[0].args[1])
    conclusions: List[Fact] = []
    if n % m != 0:
        conclusions.append(Fact(Predicates.FALSE.value, []))
    return conclusions


divides_contradiction = HyperTheorem(in_facts, _divides_contradiction_rule, "divides_contradiction")

# an alternating group of order n > 5 is simple
in_facts = [alternating_group("A", "n")]


def _alternating_simple_rule(facts: List[Fact]) -> List[Fact]:
    conclusions: List[Fact] = []
    n = int(facts[0].args[1])
    if n >= 5:
        A = facts[0].args[0]
        conclusions = [simple(A)]
    return conclusions


alternating_simple = HyperTheorem(in_facts, _alternating_simple_rule, "alternating_simple")

# index of a subgroup
in_facts = [subgroup("H", "G"), order("H", "m"), order("G", "n")]


def _subgroup_index_rule(facts: List[Fact]) -> List[Fact]:
    conclusions: List[Fact] = []
    m = int(facts[1].args[1])
    n = int(facts[2].args[1])
    H = facts[0].args[0]
    G = facts[0].args[1]
    if n % m == 0:
        i = str(n // m)
        conclusions = [index(G, H, i)]
    return conclusions


subgroup_index = HyperTheorem(in_facts, _subgroup_index_rule, "subgroup_index")

# G acts transitively on the cosets of H
in_facts = [index("G", "H", "n")]
out_facts = [transitive_action("G", "n")]
coset_action = Theorem(in_facts, out_facts, "coset_action")

######
in_facts = [transitive_action("G", "n"), simple("G")]


def _simple_group_action_rule(facts: List[Fact]) -> List[Fact]:
    conclusions: List[Fact] = []
    n = int(facts[0].args[1])
    if n > 1:
        conclusions = [subgroup("G", "?alt"), alternating_group("?alt", str(n))]
    return conclusions


simple_group_action = HyperTheorem(in_facts, _simple_group_action_rule, "subgroup_index")

# counting elements of order p^k
in_facts = [
    sylow_p_subgroup("P", "p", "G"),
    num_sylow("p", "G", "n_p"),
    order("P", "pk"),
]


def _count_order_pk_elements_rule(facts: List[Fact]) -> List[Fact]:
    G = facts[0].args[2]
    p = int(facts[0].args[1])
    facts[0].args[0]
    n_p = int(facts[1].args[2])
    if (pk := int(facts[2].args[1])) == p:
        lower_bound = (p - 1) * n_p
    else:
        if n_p == 1:
            lower_bound = pk - 1
        else:
            lower_bound = pk
    conclusions = [order_pk_lower_bound(G, str(p), str(lower_bound))]
    return conclusions


count_order_pk_elements = HyperTheorem(
    in_facts, _count_order_pk_elements_rule, "count_order_pk_elements"
)

# getting a contradiction by counting
in_facts = [
    order_pk_lower_bound("G", "p1", "N1"),
    order_pk_lower_bound("G", "p2", "N2"),
    order("G", "n"),
]


def _counting_contradiction_rule(facts: List[Fact]) -> List[Fact]:
    conclusions: List[Fact] = []
    p1 = int(facts[0].args[1])
    p2 = int(facts[1].args[1])
    N1 = int(facts[0].args[2])
    N2 = int(facts[1].args[2])
    n = int(facts[2].args[1])
    if p1 == p2:
        return []

    if N1 + N2 + 1 > n:
        return [false()]
    else:
        return conclusions


counting_contradiction = HyperTheorem(
    in_facts, _counting_contradiction_rule, "counting_contradiction"
)

########################### NORMALIZER OF INTERSECTION #########################

# more than one sylow?
in_facts = [num_sylow("p", "G", "n_p")]


def _multiple_sylows_rule(facts: List[Fact]) -> List[Fact]:
    conclusions: List[Fact] = []
    n_p = int(facts[0].args[2])
    p = facts[0].args[0]
    G = facts[0].args[1]
    if n_p > 1:
        conclusions = [more_than_one_sylow(p, G)]
    return conclusions


multiple_sylows = HyperTheorem(in_facts, _multiple_sylows_rule, "multiple_sylows")

# possible maximal sylow intersections
in_facts = [more_than_one_sylow("p", "G"), sylow_p_order("G", "p", "pk")]


def _possible_max_intersections_rule(facts: List[Fact]) -> List[Disjunction]:
    p = int(facts[0].args[0])
    pk = int(facts[1].args[2])
    G = facts[0].args[1]
    possible_intersection = 1
    intersection_facts = []
    while possible_intersection != pk:
        intersection_facts.append(
            max_sylow_intersection(G, str(p), str(possible_intersection))
        )
        possible_intersection = possible_intersection * p
    return [Disjunction(intersection_facts)]


possible_max_intersections = HyperTheorem(
    in_facts, _possible_max_intersections_rule, "possible_max_intersections"
)

# If p^k is the maximum sylow intersection, then there are two sylow p-subgroups
in_facts = [max_sylow_intersection("G", "p", "p^k")]
out_facts = [
    sylow_p_subgroup("?P", "p", "G"),
    sylow_p_subgroup("?Q", "p", "G"),
    intersection("?P", "?Q", "?R"),
    order("?R", "p^k"),
]
intersection_of_sylows = Theorem(in_facts, out_facts, "intersection_of_sylows")

# normalizer of sylow intersection
in_facts = [
    sylow_p_subgroup("P", "p", "G"),
    sylow_p_subgroup("Q", "p", "G"),
    intersection("P", "Q", "R"),
    order("R", "p^l"),
    sylow_p_order("G", "p", "p^k"),
    order("G", "n"),
]


def _normalizer_sylow_intersection_rule(
    facts: List[Fact],
) -> List[Union[Disjunction, Fact]]:
    conclusions: List[Union[Disjunction, Fact]] = []
    pl = int(facts[3].args[1])
    pk = int(facts[4].args[2])
    p = int(facts[0].args[1])
    n = int(facts[5].args[1])
    G = facts[0].args[2]
    R = facts[3].args[0]
    if pk == pl * p:
        conclusions.append(normalizer(G, R, "?T"))
        conclusions.append(subgroup("?T", G))
        conclusions.append(normalizer_of_sylow_intersection(str(p), G, "?T"))

        possible_order_facts = []
        for d in sylow2.divisors(n):
            if (d % pk == 0) and (d > pk):
                possible_order_facts.append(order("?T", str(d)))

        conclusions.append(Disjunction(possible_order_facts))

    return conclusions


normalizer_sylow_intersection = HyperTheorem(
    in_facts, _normalizer_sylow_intersection_rule, "normalizer_sylow_intersection"
)

# if the normalizer of intersection is all of G, we're done
in_facts = [normalizer("G", "H", "X"), order("G", "n"), order("X", "n")]
out_facts = [normal("H", "G")]
normalizer_everything_implies_normal = Theorem(
    in_facts, out_facts, "normalizer_everything_implies_normal"
)

in_facts = [normal("H", "G"), order("H", "h"), order("G", "g")]


def _normal_subgroup_to_not_simple_rule(facts: List[Fact]) -> List[Fact]:
    conclusions: List[Fact] = []
    h = int(facts[1].args[1])
    g = int(facts[2].args[1])
    G = facts[0].args[1]
    facts[0].args[0]
    if 1 < h and h < g:
        conclusions.append(not_simple(G))
    return conclusions


normal_subgroup_to_not_simple = HyperTheorem(
    in_facts, _normal_subgroup_to_not_simple_rule, "normal_subgroup_to_not_simple"
)

# narrow down the possible max intersections
in_facts = [
    num_sylow("p", "G", "np"),
    max_sylow_intersection("G", "p", "p^l"),
    sylow_p_order("G", "p", "p^k"),
]


def _rule_out_max_intersections_rule(facts: List[Fact]) -> List[Fact]:
    conclusions: List[Fact] = []
    int(facts[0].args[0])
    np = int(facts[0].args[2])
    pl = int(facts[1].args[2])
    pk = int(facts[2].args[2])
    if np % (pk // pl) != 1:
        conclusions.append(false())
    return conclusions


rule_out_max_intersections = HyperTheorem(
    in_facts, _rule_out_max_intersections_rule, "rule_out_max_intersections"
)

in_facts = [normalizer_of_sylow_intersection("p", "G", "T"), order("T", "k")]


def _rule_out_normalizer_of_intersection_order_rule(
    facts: List[Fact],
) -> List[Fact]:
    conclusions: List[Fact] = []
    p = int(facts[0].args[0])
    facts[0].args[2]
    k = int(facts[1].args[1])

    n_p_list = sylow2.num_sylow(p, k)
    if len(n_p_list) == 1:
        conclusions.append(false())
    return conclusions


rule_out_normalizer_of_intersection_order = HyperTheorem(
    in_facts,
    _rule_out_normalizer_of_intersection_order_rule,
    "rule_out_normalizer_of_intersection_order",
)


DEFAULT_THEOREMS: List[Union[Theorem, HyperTheorem]] = [
    sylow_theorem,
    single_sylow_not_simple,
    simple_not_simple,
    alternating_order,
    embed_in_An,
    lagrange,
    divides_contradiction,
    alternating_simple,
    subgroup_index,
    coset_action,
    simple_group_action,
    count_order_pk_elements,
    counting_contradiction,
    multiple_sylows,
    possible_max_intersections,
    intersection_of_sylows,
    normalizer_sylow_intersection,
    normalizer_everything_implies_normal,
    normal_subgroup_to_not_simple,
    rule_out_max_intersections,
    rule_out_normalizer_of_intersection_order,
]

DEFAULT_THEOREM_DICT: Dict[str, Union[Theorem, HyperTheorem]] = {
    "sylow": sylow_theorem,
    "not_simple": single_sylow_not_simple,
    "simple_not_simple": simple_not_simple,
    "alternating_order": alternating_order,
    "embed_An": embed_in_An,
    "lagrange": lagrange,
    "divides_contradiction": divides_contradiction,
    "alternating_simple": alternating_simple,
    "subgroup_index": subgroup_index,
    "coset_action": coset_action,
    "simple_group_action": simple_group_action,
    "count_order_pk_elements": count_order_pk_elements,
    "counting_cont": counting_contradiction,
    "multiple_sylows": multiple_sylows,
    "possible_max_intersections": possible_max_intersections,
    "intersection_of_sylows": intersection_of_sylows,
    "normalizer_sylow_intersection": normalizer_sylow_intersection,
    "normalizer_everything_implies_normal": normalizer_everything_implies_normal,
    "normal_subgroup_to_not_simple": normal_subgroup_to_not_simple,
    "rule_out_max_intersections": rule_out_max_intersections,
    "rule_out_normalizer_of_intersection_order": (
        rule_out_normalizer_of_intersection_order
    ),
}
