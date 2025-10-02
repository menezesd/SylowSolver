"""auto2.py

Lightweight theorem-proving engine used by the Sylow solver. This
module contains Fact/Disjunction classes and a small proof search
engine used by `auto_test2` and other helpers.
"""

import math
import sylow2
from core import (
    Fact,
    Disjunction,
    Theorem,
    HyperTheorem,
    Proof_environment,
)


# given a list of facts and the input structure to a theorem, output all possible tuples of input facts
# (is this #P-hard?)

# input_struc is the structure of the input that the theorem takes
# takes the form of a list of facts
# facts is the universe of facts available to be matched
# returns a list of (fact lists), one for each matching combination
# (this could make the data structures rather large.  might be better to instead return lists of fact labels?)
# (a more compact data structure could take the form of a tree)


# if new_facts is not None, then only look for matches containing new_facts
def match_facts_to_theorem(thm_facts, facts, new_facts=None):

    if new_facts is None:
        new_facts = facts  # just assume every fact is new

    cur_matches = [
        []
    ]  # the current list of (lists of facts which match the first i theorem hypotheses)
    # list of (matching dicts) corresponding to the lists in cur_matches
    dicts = [{}]
    uses_new_list = [False]
    # build a dictionary consisting of all the matches to each theorem hypothesis
    for i in range(0, len(thm_facts)):
        new_cur_matches = []
        new_dicts = []
        new_uses_new_list = []
        for match, match_dict, uses_new in zip(cur_matches, dicts, uses_new_list):
            new_fact_matches, new_fact_dicts = match_facts_to_template(
                thm_facts[i], facts, init_match_dict=match_dict
            )
            for new_match, new_dict in zip(new_fact_matches, new_fact_dicts):
                new_cur_matches.append(list(match) + [new_match])
                new_dicts.append(dict(new_dict))
                new_uses_new_list.append(uses_new or (new_match in new_facts))
        cur_matches = new_cur_matches
        dicts = new_dicts
        uses_new_list = new_uses_new_list

    ret = []
    for match, uses_new_fact in zip(cur_matches, uses_new_list):
        if uses_new_fact:
            ret.append(match)
    return ret


# find all facts that match a given template structure
# also returns the associated matching dict
# optional argument init_match_dict gives literals corresponding to a subset of arguments in template
# not necessarily as efficient as possible
def match_facts_to_template(template, facts, init_match_dict=None):
    init_match_dict = {} if init_match_dict is None else init_match_dict
    matches = []
    dicts = []
    template_name = template.name
    template_args = template.args

    for fact in facts:
        if fact.name != template_name:
            continue
        if len(fact.args) != len(template_args):
            continue
        # length and name match
        match_dict = dict(init_match_dict)  # make a copy

        match = True
        for arg_pair in zip(template_args, fact.args):
            temp_arg = arg_pair[0]
            fact_arg = arg_pair[1]

            if temp_arg[0] == "*":
                if temp_arg[1:] != fact_arg:
                    match = False
                    break

            if temp_arg not in match_dict:
                match_dict[temp_arg] = fact_arg
            elif match_dict[temp_arg] != fact_arg:
                match = False
                break
        if match:
            matches.append(fact)
            dicts.append(dict(match_dict))
    return [matches, dicts]


def auto_solve(pf_envir):

    # Allow more iterations for deep searches (raise during diagnostics)
    MAX_ITERATIONS = 1000

    thm_matches = (
        {}
    )  # dict mapping theorems in the environment to lists of fact matches
    for thm in pf_envir.theorems:
        thm_matches[thm] = match_facts_to_theorem(thm.facts, pf_envir.facts)

    for _ in range(0, MAX_ITERATIONS):
        # pick one of the matches according to some procedure
        # "breadth-first" approach
        # should remove things once they're already applied

        # for dis in pf_envir.disjunctions:
        encountered_match = False  # check if we're out of matches

        new_facts = []

        for thm in thm_matches:

            #           print("new thm")
            for match in list(thm_matches[thm]):
                #               print("   new match")
                encountered_match = True  # did we actually do anything with the match?
                #                print("   about to apply ", thm.name)
                #               for f in match:
                #                   f.do_print()
                #                print("   applied")

                #              if(len(facts_from_theorem) > 0): encountered_match = True

                if facts_from_theorem := pf_envir.apply_thm(
                    thm, match
                ):  # sometimes the theorem match might be invalid. FIX?
                    # FIX move encountered_match here
                    new_facts += facts_from_theorem

                    # print("----- new facts -----")
                    # for fact in facts_from_theorem:
                    #    fact.do_print()
                    # print("---------------------")

                thm_matches[thm].remove(match)  # prevent reapplying theorems

        if not encountered_match:
            break  # failed

        for thm in pf_envir.theorems:
            thm_matches[thm] += match_facts_to_theorem(
                thm.facts, pf_envir.facts, new_facts
            )

        if pf_envir.goal_achieved:
            pf_envir.print_relevant_facts()
            print("SUCCESS")
            return True
        else:
            pass
        #  print("******************************************")
        # pf_envir.exec_command("display")
        # print("******************************************")
    #           print("next iteration")

    pf_envir.print_relevant_facts()
    print("FAILURE")
    return False  # surpassed max iterations


################################### FACT GENERATORS ######################################


# G is a group
def group(G):
    return Fact("group", [G])


# the order of G is n
def order(G, n):
    return Fact("order", [G, n])


# the order of a sylow p-subgroup of G is pk
def sylow_p_order(G, p, pk):
    return Fact("sylow_order", [G, p, pk])


# P is a sylow p-subgroup of G
def sylow_p_subgroup(P, p, G):
    return Fact("sylow_p_subgroup", [P, p, G])


# A is the alternating group on n letters
def alternating_group(A, n):
    return Fact("alternating_group", [A, n])


# the number of sylow p-subgroups of G is n
def num_sylow(p, G, n):
    return Fact("num_sylow", [p, G, n])


# G is simple
def simple(G):
    return Fact("simple", [G])


# G is not simple
def not_simple(G):
    return Fact("not_simple", [G])


# H is a subgroup of G
def subgroup(H, G):
    return Fact("subgroup", [H, G])


# m divides n
def divides(m, n):
    return Fact("divides", [m, n])


# a false statement
def false():
    return Fact("false", [])


# H's index in G is n
def index(G, H, n):
    return Fact("index", [G, H, n])


# G acts transitively on a set of size n
def transitive_action(G, n):
    return Fact("transitive_action", [G, n])


# number of elements of order p^k for some k>0 is at least N
def order_pk_lower_bound(G, p, N):
    return Fact("order_pk_lower_bound", [G, p, N])


# G has more than one sylow p subgroup
def more_than_one_sylow(p, G):
    return Fact("more_than_one_sylow", [p, G])


# the intersection of A and B is C
def intersection(A, B, C):
    return Fact("intersection", [A, B, C])


# N_G(H) = K
def normalizer(G, H, K):
    return Fact("normalizer", [G, H, K])


# the order of H is at least n
def order_lower_bound(H, n):
    return Fact("order_lower_bound", [H, n])


# the maximum intersection of two distinct sylow p-subgroups of G is m
def max_sylow_intersection(G, p, m):
    return Fact("max_sylow_intersection", [G, p, m])


# H is a proper subgroup of G
# for us, a proper subgroup is neither trivial, nor all of G
def proper_subgroup(H, G):
    return Fact("proper_subgroup", [H, G])


# H is a normal subgroup of G
def normal(H, G):
    return Fact("normal", [H, G])


# T is the normalizer of intersection for two sylow-p subgroups of G
def normalizer_of_sylow_intersection(p, G, T):
    return Fact("normalizer_of_sylow_intersection", [p, G, T])


def OR(f1, f2):
    return Disjunction([f1, f2])


####################################### THEOREMS #######################################


# sylow's theorem

in_facts = [group("G"), order("G", "n")]


def rule_sylow(facts):
    conclusions = []
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
            # conclusions.append(Fact("int_lit", [n_p]))
            dis_facts.append(Fact("num_sylow", [str(p), group_name, str(n_p)]))
        if len(dis_facts) == 1:
            conclusions.append(dis_facts[0])  # minor optimization
        else:
            dis = Disjunction(dis_facts)
            conclusions.append(dis)
    return conclusions


sylow_theorem = HyperTheorem(in_facts, rule_sylow, "sylow")


# single sylow subgroup
in_facts = [
    Fact("sylow_p_subgroup", ["H", "p", "G"]),
    Fact("num_sylow", ["p", "G", "*1"]),
    Fact("order", ["G", "n"]),
]


def rule_single_sylow_not_simple(facts):
    conclusions = []
    G = facts[0].args[2]
    p = int(facts[0].args[1])
    n = int(facts[2].args[1])  # take off the asterisk
    p_power = True
    while n != 1:
        if n % p != 0:
            p_power = False
            break
        n = n // p
    if not p_power:
        conclusions = [Fact("not_simple", [G])]
    return conclusions


single_sylow_not_simple = HyperTheorem(
    in_facts, rule_single_sylow_not_simple, "single_sylow_normal"
)

# simple + not_simple = false
in_facts = [Fact("simple", ["G"]), Fact("not_simple", ["G"])]
out_facts = [Fact("false", [])]
simple_not_simple = Theorem(in_facts, out_facts, "not_simple")

# embed into A_n
in_facts = [Fact("num_sylow", ["p", "G", "n_p"]), Fact("simple", ["G"])]


def rule_embed_in_An(facts):
    # print("applying embed in An")
    conclusions = []
    n_p = int(facts[0].args[2])
    G = facts[0].args[1]
    if n_p > 1:
        # conclusions = [Fact("subgroup", [G, '?alt']), Fact("alternating_group", ['?alt', str(n_p)]) ]
        conclusions = [subgroup(G, "?alt"), alternating_group("?alt", str(n_p))]
    return conclusions


embed_in_An = HyperTheorem(in_facts, rule_embed_in_An, "embed_An")


in_facts = [alternating_group("A", "n")]


def rule_alternating_order(facts):
    A = facts[0].args[0]
    n = int(facts[0].args[1])

    if n > 1000:  # huge factorial computions are extremely slow/impossible
        # Ugly, but it works.  Other approaches?
        return []

    if n == 1:
        order_val = 1
    else:
        order_val = math.factorial(n) // 2
    conclusions = [Fact("order", [A, str(order_val)])]
    return conclusions


alternating_order = HyperTheorem(in_facts, rule_alternating_order, "alternating_order")

# order of a subgroup divides the order of the group
in_facts = [
    Fact("subgroup", ["H", "G"]),
    Fact("order", ["H", "n"]),
    Fact("order", ["G", "m"]),
]
out_facts = [Fact("divides", ["n", "m"])]
lagrange = Theorem(in_facts, out_facts, "lagrange")

# check if m divides n
in_facts = [Fact("divides", ["m", "n"])]


def rule_divides_contradiction(facts):
    m = int(facts[0].args[0])
    n = int(facts[0].args[1])
    conclusions = []
    if n % m != 0:
        conclusions.append(Fact("false", []))
    return conclusions


divides_contradiction = HyperTheorem(
    in_facts, rule_divides_contradiction, "divides_contradiction"
)

# an alternating group of order n > 5 is simple
in_facts = [alternating_group("A", "n")]


def rule_alternating_simple(facts):

    #   print("in alternating order")

    conclusions = []  # needing this is annoying
    n = int(facts[0].args[1])
    if n >= 5:
        A = facts[0].args[0]  # this step is also annoying
        conclusions = [simple(A)]
    return conclusions


alternating_simple = HyperTheorem(
    in_facts, rule_alternating_simple, "alternating_simple"
)

# index of a subgroup
in_facts = [subgroup("H", "G"), order("H", "m"), order("G", "n")]


def rule_subgroup_index(facts):
    conclusions = []
    m = int(facts[1].args[1])
    n = int(facts[2].args[1])
    H = facts[0].args[0]
    G = facts[0].args[1]
    if n % m == 0:
        i = str(n // m)
        conclusions = [index(G, H, i)]
    return conclusions


subgroup_index = HyperTheorem(in_facts, rule_subgroup_index, "subgroup_index")

# G acts transitively on the cosets of H
in_facts = [index("G", "H", "n")]
out_facts = [transitive_action("G", "n")]
coset_action = Theorem(in_facts, out_facts, "coset_action")

######
in_facts = [transitive_action("G", "n"), simple("G")]


def rule_simple_group_action(facts):
    conclusions = []
    n = int(facts[0].args[1])
    if n > 1:
        conclusions = [subgroup("G", "?alt"), alternating_group("?alt", str(n))]
    return conclusions


simple_group_action = HyperTheorem(in_facts, rule_simple_group_action, "subgroup_index")

# counting elements of order p^k
in_facts = [
    sylow_p_subgroup("P", "p", "G"),
    num_sylow("p", "G", "n_p"),
    order("P", "pk"),
]


def rule_count_order_pk_elements(facts):
    G = facts[0].args[2]
    p = int(facts[0].args[1])
    _P = facts[0].args[0]
    n_p = int(facts[1].args[2])
    if (pk := int(facts[2].args[1])) == p:  # P is cylic of prime order
        lower_bound = (p - 1) * n_p
    else:  # not cyclic of prime order
        if n_p == 1:
            lower_bound = pk - 1
        else:
            lower_bound = pk  # probably not optimal
    conclusions = [order_pk_lower_bound(G, str(p), str(lower_bound))]
    return conclusions


count_order_pk_elements = HyperTheorem(
    in_facts, rule_count_order_pk_elements, "count_order_pk_elements"
)

# getting a contradiction by counting
# really should be varargs
in_facts = [
    order_pk_lower_bound("G", "p1", "N1"),
    order_pk_lower_bound("G", "p2", "N2"),
    order("G", "n"),
]


def rule_counting_contradiction(facts):
    # print("COUNTING")
    conclusions = []
    p1 = int(facts[0].args[1])
    p2 = int(facts[1].args[1])
    N1 = int(facts[0].args[2])
    N2 = int(facts[1].args[2])
    n = int(facts[2].args[1])
    if p1 == p2:
        return []

    if N1 + N2 + 1 > n:  # too many elements
        return [false()]
    else:
        return conclusions


counting_contradiction = HyperTheorem(
    in_facts, rule_counting_contradiction, "counting_contradiction"
)

########################### NORMALIZER OF INTERSECTION #########################

# more than one sylow?
in_facts = [num_sylow("p", "G", "n_p")]


def rule_multiple_sylows(facts):
    conclusions = []
    n_p = int(facts[0].args[2])
    p = facts[0].args[0]
    G = facts[0].args[1]
    if n_p > 1:
        conclusions = [more_than_one_sylow(p, G)]
    return conclusions


multiple_sylows = HyperTheorem(in_facts, rule_multiple_sylows, "multiple_sylows")

# possible maximal sylow intersections
in_facts = [more_than_one_sylow("p", "G"), sylow_p_order("G", "p", "pk")]


def rule_possible_max_intersections(facts):
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
    in_facts, rule_possible_max_intersections, "possible_max_intersections"
)

# If p^k is the maximum sylow intersection, then there are two sylow p-subgroups
# intersecting in a subgroup of size p^k
in_facts = [max_sylow_intersection("G", "p", "p^k")]
out_facts = [
    sylow_p_subgroup("?P", "p", "G"),
    sylow_p_subgroup("?Q", "p", "G"),
    intersection("?P", "?Q", "?R"),
    order("?R", "p^k"),
]
intersection_of_sylows = Theorem(in_facts, out_facts, "intersection_of_sylows")


# normalizer of sylow intersection
# SYLOW ORDER THING IS UGLY
# FOR NOW, only when l = k-1 !!!!!
in_facts = [
    sylow_p_subgroup("P", "p", "G"),
    sylow_p_subgroup("Q", "p", "G"),
    intersection("P", "Q", "R"),
    order("R", "p^l"),
    sylow_p_order("G", "p", "p^k"),
    order("G", "n"),
]


def rule_normalizer_sylow_intersection(facts):
    conclusions = []
    pl = int(facts[3].args[1])
    pk = int(facts[4].args[2])
    p = int(facts[0].args[1])
    n = int(facts[5].args[1])
    G = facts[0].args[2]
    R = facts[3].args[0]
    if pk == pl * p:
        conclusions.append(normalizer(G, R, "?T"))
        conclusions.append(subgroup("?T", G))
        # conclusions.append( group('?T') ) #not really the right place -- subgroups should always be groups. This potentailly slows things down a lot!!
        conclusions.append(normalizer_of_sylow_intersection(str(p), G, "?T"))
        #       conclusions.append( more_than_one_sylow('p', '?T')) #normalizer must contain at least two sylow subgroups

        possible_order_facts = []
        for d in sylow2.divisors(n):
            if (d % pk == 0) and (d > pk):
                possible_order_facts.append(order("?T", str(d)))

        conclusions.append(Disjunction(possible_order_facts))

    return conclusions


normalizer_sylow_intersection = HyperTheorem(
    in_facts, rule_normalizer_sylow_intersection, "normalizer_sylow_intersection"
)

# if the normalizer of intersection is all of G, we're done
# could break this up, and not worry about group orders
in_facts = [normalizer("G", "H", "X"), order("G", "n"), order("X", "n")]
out_facts = [normal("H", "G")]
normalizer_everything_implies_normal = Theorem(
    in_facts, out_facts, "normalizer_everything_implies_normal"
)

in_facts = [normal("H", "G"), order("H", "h"), order("G", "g")]


def rule_normal_subgroup_to_not_simple(facts):
    conclusions = []
    h = int(facts[1].args[1])
    g = int(facts[2].args[1])
    G = facts[0].args[1]
    _H = facts[0].args[0]
    if 1 < h and h < g:
        conclusions.append(not_simple(G))
    return conclusions


normal_subgroup_to_not_simple = HyperTheorem(
    in_facts, rule_normal_subgroup_to_not_simple, "normal_subgroup_to_not_simple"
)

# in_facts = [num_sylow('p', 'G', '*1'), more_than_one_sylow('p','G')]
# out_facts = [false()]
# multi_sylow_single_sylow_cont = Theorem(in_facts, out_facts, "multi_sylow_single_sylow_cont")


# narrow down the possible max intersections
in_facts = [
    num_sylow("p", "G", "np"),
    max_sylow_intersection("G", "p", "p^l"),
    sylow_p_order("G", "p", "p^k"),
]


def rule_rule_out_max_intersections(facts):
    conclusions = []
    _p = int(facts[0].args[0])
    np = int(facts[0].args[2])
    pl = int(facts[1].args[2])
    pk = int(facts[2].args[2])
    # n_p cong 1 mod p^k/p^l
    if np % (pk // pl) != 1:
        conclusions.append(false())
    return conclusions


rule_out_max_intersections = HyperTheorem(
    in_facts, rule_rule_out_max_intersections, "rule_out_max_intersections"
)

in_facts = [normalizer_of_sylow_intersection("p", "G", "T"), order("T", "k")]


def rule_rule_out_normalizer_of_intersection_order(facts):
    conclusions = []
    p = int(facts[0].args[0])
    _T = facts[0].args[2]
    k = int(facts[1].args[1])

    n_p_list = sylow2.num_sylow(p, k)
    if len(n_p_list) == 1:  # sylow p-subgroup of T forced to be normal
        conclusions.append(false())
    return conclusions


rule_out_normalizer_of_intersection_order = HyperTheorem(
    in_facts,
    rule_rule_out_normalizer_of_intersection_order,
    "rule_out_normalizer_of_intersection_order",
)

# in_facts = [order('G', 'n')]
# out_facts = [false()]
# def rule(facts):
#    conclusions = []
#   n = int(facts[0].args[1])
#   if(n == 18):
#       conclusions = [false()]
#   return conclusions
#
# eighteen_bad = HyperTheorem(in_facts, rule, "eighteen_bad")

thm_list = [
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
    #          multi_sylow_single_sylow_cont,
    rule_out_max_intersections,
    rule_out_normalizer_of_intersection_order,
    #          eighteen_bad #REMOVE TEST!!!!!!!!!!!!!
]

thm_names = {
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
    "rule_out_normalizer_of_intersection_order": rule_out_normalizer_of_intersection_order,
    #           "eighteen_bad" : eighteen_bad #REMOVE
    #           "multi_sylow_single_sylow_cont" : multi_sylow_single_sylow_cont
}


########################################## TESTING #####################################################
def test1():

    # subgroup_trans theorem
    facts = [Fact("subgroup", ["A", "B"]), Fact("subgroup", ["B", "C"])]
    conclusions = [Fact("subgroup", ["A", "C"])]
    subgroup_trans = Theorem(facts, conclusions, "subgroup_trans")

    fact2 = Fact("subgroup", ["X", "Y"])
    fact3 = Fact("subgroup", ["X", "Z"])
    d1 = Fact("subgroup", ["Y", "A"])
    d2 = Fact("subgroup", ["Z", "A"])
    dis = Disjunction([d1, d2])

    facts = [fact2, fact3, dis]
    theorems = [subgroup_trans]
    theorem_names = {"subgroup_trans": subgroup_trans}
    goal = Fact("subgroup", ["X", "A"])

    pf_envir = Proof_environment(facts, theorems, theorem_names, goal)

    _running = True
    # while(running != False):
    #        cmd = input()
    #        running = pf_envir.exec_command(cmd)
    pf_envir.exec_command("apply subgroup_trans F1 F4")
    pf_envir.exec_command("display")
    pf_envir.exec_command("apply subgroup_trans F0 F3")
    if pf_envir.goal_achieved:
        print("DONE")


def test2():

    fact1 = Fact("group", ["G"])
    fact2 = Fact("order", ["G", "6"])
    fact3 = Fact("simple", ["G"])
    facts = [fact1, fact2, fact3]

    goal = Fact("false", [])

    pf_envir = Proof_environment(facts, thm_list, thm_names, goal)

    running = True
    while running:
        cmd = input()
        running = pf_envir.exec_command(cmd)


def matching_test():
    def foo(first, second, third):
        return Fact("foo", [first, second, third])

    def _bar(a, b, c):
        return Fact("bar", [a, b, c])

    _template = foo("W", "X", "W")
    # facts = [foo('A','B','C'), foo('D','C','D'), foo('C','A','A'), foo('A','C','A'), bar('x','y','x'), bar('x','x','x'), bar('x','x','u')]
    facts = [foo("A", "B", "C"), foo("D", "E", "F")]
    thm_facts = [foo("X", "Y", "Z"), foo("X", "Y", "Z")]

    matches = match_facts_to_theorem(thm_facts, facts, [foo("A", "B", "C")])

    # matching_test: intentionally quiet; use fact.do_print() in a debugger if needed
    for match in matches:
        for fact in match:
            # fact.do_print()
            pass


#   matches,dicts = match_facts_to_template(template, facts)
#    for match in matches:
#       match.do_print()
#    print(dicts)


def auto_test():
    facts = [Fact("subgroup", ["A", "B"]), Fact("subgroup", ["B", "C"])]
    conclusions = [Fact("subgroup", ["A", "C"])]
    subgroup_trans = Theorem(facts, conclusions, "subgroup_trans")

    fact1 = Fact("subgroup", ["X", "Y"])
    fact2 = Fact("subgroup", ["Y", "Z"])
    fact3 = Fact("subgroup", ["Z", "A"])
    fact4 = Fact("subgroup", ["A", "B"])
    fact5 = Fact("subgroup", ["B", "C"])
    fact6 = Fact("subgroup", ["C", "D"])
    fact7 = Fact("subgroup", ["D", "E"])
    fact8 = Fact("subgroup", ["E", "F"])

    facts = [fact4, fact7, fact1, fact3, fact2, fact6, fact5, fact8]
    theorems = [subgroup_trans]
    theorem_names = {"subgroup_trans": subgroup_trans}
    goal = Fact("subgroup", ["X", "F"])

    pf_envir = Proof_environment(facts, theorems, theorem_names, goal)

    auto_solve(pf_envir)


# There are two pieces of test code currently in play: 'test' in the list of facts, as well as a dummy order 18 is bad theorem
# remove them one at a time, and be done
def auto_test2():
    # uses module-level thm_list and thm_names

    while True:
        _order = input("Enter a group order: ")
        fact1 = Fact("group", ["G"])
        fact2 = Fact("order", ["G", _order])
        fact3 = Fact("simple", ["G"])

        #     test = max_sylow_intersection('G','3','3')

        facts = [fact1, fact2, fact3]
        goal = Fact("false", [])

        pf_envir = Proof_environment(facts, thm_list, thm_names, goal)

        auto_solve(pf_envir)


def easy_dis_test():
    def _subgroup_local(A, B):
        return Fact("subgroup", [A, B])

    def _or_local(f1, f2):
        return Disjunction([f1, f2])

    facts = [Fact("subgroup", ["A", "B"]), Fact("subgroup", ["B", "C"])]
    conclusions = [Fact("subgroup", ["A", "C"])]
    subgroup_trans = Theorem(facts, conclusions, "subgroup_trans")

    facts = [
        _or_local(_subgroup_local("A", "B"), _subgroup_local("A", "X")),
        _subgroup_local("B", "D"),
        _subgroup_local("X", "D"),
    ]
    theorems = [subgroup_trans]
    theorem_names = {"subgroup_trans": subgroup_trans}
    goal = subgroup("A", "D")

    pf_envir = Proof_environment(facts, theorems, theorem_names, goal)
    auto_solve(pf_envir)


def auto_dis_test():
    def _subgroup_local(A, B):
        return Fact("subgroup", [A, B])

    def _or_local(f1, f2):
        return Disjunction([f1, f2])

    facts = [Fact("subgroup", ["A", "B"]), Fact("subgroup", ["B", "C"])]
    conclusions = [Fact("subgroup", ["A", "C"])]
    subgroup_trans = Theorem(facts, conclusions, "subgroup_trans")

    facts = [
        _or_local(_subgroup_local("A", "B"), _subgroup_local("C", "D")),
        _or_local(_subgroup_local("B", "F"), _subgroup_local("D", "F")),
        _subgroup_local("B", "D"),
        _subgroup_local("D", "B"),
        _subgroup_local("X", "A"),
        _subgroup_local("X", "C"),
    ]

    theorems = [subgroup_trans]
    theorem_names = {"subgroup_trans": subgroup_trans}
    goal = subgroup("X", "F")

    pf_envir = Proof_environment(facts, theorems, theorem_names, goal)
    auto_solve(pf_envir)


def alternating_test():
    # uses module-level thm_list and thm_names
    #    thm_list = [embed_in_An]
    #   thm_names = ["embed_in_An", embed_in_An]
    fact1 = Fact("simple", ["G"])
    fact2 = Fact("num_sylow", ["3", "G", "4"])
    fact3 = Fact("order", ["G", "12"])
    goal = Fact("false", [])

    pf_envir = Proof_environment([fact1, fact2, fact3], thm_list, thm_names, goal)
    auto_solve(pf_envir)


def order_counting_test():
    # uses module-level thm_list and thm_names

    fact1 = group("G")
    fact2 = order("G", "30")
    #    fact3 = OR(not_simple('G'), false())
    #    fact4 = OR(simple('G'), false())
    fact5 = sylow_p_subgroup("P5", "5", "G")
    fact6 = sylow_p_subgroup("P3", "3", "G")
    fact7 = order("P5", "5")
    fact8 = order("P3", "3")
    fact9 = simple("G")

    # fact3 and fact4 were placeholder variables in the original test; omit them here
    fact_list = [fact1, fact2, fact5, fact6, fact7, fact8, fact9]
    #    fact_list = [fact3,fact4]
    pf_envir = Proof_environment(fact_list, thm_list, thm_names, false())
    auto_solve(pf_envir)

    # Problem seems to occur when we have
    # (A or B), (C or D).  A -> Goal, C -> Goal, (B,D)->Goal


# def hard_disjunction_test():
#    def test_fact(A,B):
#        return Fact("fact", [A,B])


def find_hard_orders(in_file):
    # uses module-level thm_list and thm_names

    with open(in_file, encoding="utf-8") as f:
        for n in f:
            facts = [group("G"), simple("G"), order("G", n)]
            pf_envir = Proof_environment(facts, thm_list, thm_names, false())
            if auto_solve(pf_envir):
                print(n, " : SUCCESS")
            else:
                print(n, " : FAILURE")


# def normalizer_test():
#    global thm_list
#    global thm_names
#
#    theorem_names = copy.copy(thm_names)

#    in_facts = [order('G','*18')]
#    out_facts = [false()]
# eighteen_bad = new Theorem()
#    theorem_names.append()
#    pf_envir = Proof_environment(facts,theorems,theorem_names, goal)
#    auto_solve(pf_envir)


# find_hard_orders('interesting_10000.txt')


if __name__ == "__main__":
    # run the interactive test loop when executed as a script
    auto_test2()
