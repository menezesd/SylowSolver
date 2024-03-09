import itertools
import math
import sylow2


class Fact:

    # depth is the number of nested cases in which the fact has been shown
    def __init__(self, name, args, dependencies=None, label=None, dis_ancestors=None):
        dependencies = [] if dependencies is None else dependencies
        dis_ancestors = [] if dis_ancestors is None else dis_ancestors
        self.name = name
        self.args = args
        self.dependencies = (
            dependencies  # the facts needed to conclude this fact, list of fact labels
        )

        self.useful = False  # was this fact used to conclude the goal

        self.dis_ancestors = (
            set()
        )  # set of disjunction facts needed to conclude this fact (anywhere in ancestry)
        # each entry is of the form (Disjunction_label, disjunction_index)

        self.conc_thm = None  # the theorem that was used to conclude this Fact
        self.label = label

    def do_print(self):
        print(
            self.label,
            " : ",
            self.name,
            " ",
            self.args,
            " :: ",
            self.dependencies,
            " :: ",
            self.dis_ancestors,
        )

    def do_nice_print(self):
        print(self.label, " : ", self.name, " ", self.args)
        if self.conc_thm != None:
            print(
                "    by thm ",
                self.conc_thm.name,
                " applied to facts ",
                *self.dependencies
            )
        else:
            print("    by hypothesis")
        if self.dis_ancestors != set():
            print("    Disjunctions in history: ", *self.dis_ancestors)
        print()

    def equals(self, fact):
        if self.name != fact.name:
            return False
        if self.args != fact.args:
            return False
        return True

    def copy(self):
        return Fact(self.name, list(self.args), self.depth)

    # returns a normal form for the fact structure
    # useful for matching facts to theorem arguments
    # the structure of a fact is uniquely specified by the name and number of arguments
    # TEST THIS!!!


#   def normal_form(self):

#        return self.name + str(len(args))


# an OR of facts
class Disjunction:

    def __init__(self, facts, dependencies=None, label=None, dis_ancestors=None):
        dependencies = [] if dependencies is None else dependencies
        dis_ancestors = [] if dis_ancestors is None else dis_ancestors
        self.facts = facts
        self.dependencies = dependencies
        self.dis_ancestors = set()
        self.label = label

        self.useful = False

    def do_print(self):
        facts = self.facts
        print(self.label, ":")
        for i in range(0, len(facts)):
            facts[i].do_print()
            if i != len(facts) - 1:
                print("    OR")

    def do_nice_print(self):
        facts = self.facts
        print(self.label, ":")
        for i in range(0, len(facts)):
            facts[i].do_print()
            if i != len(facts) - 1:
                print("    OR")
        if self.conc_thm != None:
            print(
                "    by thm ",
                self.conc_thm.name,
                " applied to facts ",
                *self.dependencies
            )
        else:
            print("    by hypothesis")
        if self.dis_ancestors != set():
            print("    Disjunctions in history: ", *self.dis_ancestors)
        print()


# theorem specified by:
# list of placeholders
# list of facts using placeholders
# list of conclusions using placeholders

# for example:
# symbols:     G, H, I
# facts:       subgroup H G, subgroup I H
# conclusions: subgroup I G


class Theorem:

    def __init__(self, facts, conclusions, name):
        self.facts = facts
        self.conclusions = conclusions
        self.name = name


class HyperTheorem:

    # rule is a function that takes in series of facts with structure 'facts' and ouputs a list of facts
    def __init__(self, facts, rule, name):
        self.facts = facts
        self.rule = rule
        self.name = name
        self.multi_args = False  # can the theorem take multiple arguments?


class Proof_environment:

    # begin with a list of facts
    # list of facts grows as theorems are applied
    # theorems is the set of theorems in the environment
    # theorem_names_dict is a dictionary of theorem names
    # goal is the fact to be proven
    def __init__(self, facts, theorems, theorem_name_dict, goal):

        self.ordered_fact_list = []  # list of facts labels in the order that they appear

        self.facts = []
        self.theorems = theorems
        self.theorem_name_dict = theorem_name_dict
        self.disjunctions = []

        self.goal = goal
        # goal should not already be achieved (probably should check it though)
        self.goal_achieved = False
        self.goal_dis_combos = []
        #       self.goal_label = None

        # fact_labels maps labels to facts
        # makes it easier to refer to a specific fact
        self.fact_labels = {}
        self.cur_fact_num = 0

        # the set of additional assumptions describing the current state of the environment
        # a new assumption is added whenever case is called

        self.add_new_facts(facts)
        self.symbol_set = set()  # the set of all symbols currently in the environment

        # TEST TEST
        #       print("Second Test")
        #        for fact in facts: #TEST
        #            fact.do_print()
        #            print(type(fact))
        #            print()

        for fact in self.facts:
            for sym in fact.args:
                self.symbol_set.add(sym)

    def new_label(self, letter="F"):
        label = letter + str(self.cur_fact_num)
        self.cur_fact_num += 1
        return label

    # has the goal been achieved yet
    # goal_fact is a new copy of goal used for the update
    def update_goal_achieved(self, goal_fact):

        full_dis_set = set(D for D, i in set.union(*(self.goal_dis_combos)))

        dis_labels = set(D for D in full_dis_set)  # prevent duplicates
        #       print("labels")
        #        print(dis_labels)
        #        print("end labels")
        #        print()

        #       dis_labels = set([D for D,i in goal_fact.dis_ancestors]) #prevent duplicates
        L = [(D, len(self.fact_labels[D].facts)) for D in dis_labels]
        #       print("L: ")
        #        print(L)
        #        print()
        X = []
        for D, l in L:
            X.append([(D, i) for i in range(0, l)])
        S = list(itertools.product(*X))
        S = set(frozenset(u) for u in S)

        #        print("S")
        #        print(S)
        #        print()

        # all we need to do is check that for each guy in S, some guy in frozen_dis_combos is a subset
        frozen_dis_combos = set(frozenset(d) for d in self.goal_dis_combos)
        # if frozen_dis_combos.issuperset(S): #SET UP SO NO CASTING
        #    self.goal_achieved = True
        for s in S:
            found_implication = False
            for dtuple in frozen_dis_combos:
                if dtuple.issubset(s):
                    found_implication = True
                    continue
            if not found_implication:
                return

        # if we made it
        self.goal_achieved = True

    #   def check_goal_achieved(self, goal_fact):
    #        dis_labels = set([D for D,i in goal_disjunction_dependencies])
    #        L = [(D,len(self.fact_labels[D].facts)) for D in dis_labels] #size of each disjunction in terms of number of facts
    #
    #        X = [] #list of lists of disjunction facts e.g. [ [(D1,1),(D1,2)], [(D2,1),(D2,2),(D2,3)] ]
    #        for D, l in L:
    #            X.append([(D,i) for i in range(0,l)])

    #        S = list(itertools.product(*X))
    #        S = set(frozenset(u) for u in S) #set of all tuples of disjunctions that need to be checked
    #        frozen_dis_combos = set(frozenset(d) for d in self.goal_dis_combos)

    # mark a given fact, and all of its ancestors as useful
    def update_useful(self, fact):
        if fact.useful:
            return  # already marked
        fact.useful = True
        for pred_lbl in fact.dependencies:
            self.update_useful(self.fact_labels[pred_lbl])

    def add_new_facts(self, new_facts):
        for fact in new_facts:

            if isinstance(fact, Fact):

                #               new_label = 'F'+str(self.cur_fact_num)
                new_label = self.new_label()
                self.fact_labels[new_label] = fact
                fact.label = new_label

                self.facts.append(fact)
                if fact.equals(self.goal):  # we have a new instance of our goal
                    #                   print("HERE")
                    self.goal_dis_combos.append(fact.dis_ancestors)
                    self.update_goal_achieved(fact)
                    # self.goal_label = fact.label
                    # UPDATE WIN CONDITION

                    self.update_useful(fact)

            if isinstance(fact, Disjunction):
                #               new_label = 'D'+str(self.cur_fact_num)
                new_label = self.new_label(letter="D")
                self.fact_labels[new_label] = fact
                fact.label = new_label
                self.disjunctions.append(fact)

                for i in range(0, len(fact.facts)):
                    sub_fact = fact.facts[i]
                    sub_fact.dependencies = [
                        fact.label
                    ]  # a subfact of a disjunction depends on the disjunction
                    sub_fact.dis_ancestors = set(fact.dis_ancestors)
                    sub_fact.dis_ancestors.add((fact.label, i))

                self.add_new_facts(fact.facts)

            self.ordered_fact_list.append(new_label)  # add the new label

    #         self.cur_fact_num += 1

    def apply_std_thm(self, thm, facts):
        valid = True
        if len(facts) != len(thm.facts):
            valid = False
        matching = {}
        for pair in zip(facts, thm.facts):
            in_fact = pair[0]
            thm_fact = pair[1]
            if in_fact.name != thm_fact.name:
                valid = False
            if len(in_fact.args) != len(thm_fact.args):
                valid = False
            for arg_pair in zip(in_fact.args, thm_fact.args):
                in_arg = arg_pair[0]
                thm_arg = arg_pair[1]

                # added
                if thm_arg[0] == "*":
                    if in_arg != thm_arg[1:]:
                        print("exact match expected")
                        valid = False
                    continue  # don't bother updating the matching dict

                if thm_arg in matching:
                    if matching[thm_arg] != in_arg:
                        valid = False
                else:
                    matching[thm_arg] = in_arg

        if not valid:
            #           print("invalid application of theorem")
            return False

        conclusions = []
        for conc in thm.conclusions:

            # print("---- new conc -----")
            # conc.do_print()
            # print("----- end new conc ----")

            # new_fact_args = [ matching[x] for x in conc.args ]
            new_fact_args = []
            for x in conc.args:
                if x[0] != "?":
                    new_fact_args.append(matching[x])
                else:
                    new_fact_args.append(x)

            new_fact = Fact(conc.name, new_fact_args)
            conclusions.append(new_fact)

        return conclusions

    # apply a theorem or hypertheorem, then add the new facts to the environment
    # returns False if the theorem application was invalid
    def apply_thm(self, thm, facts):

        # check to make sure that we're never applying two facts from the same disjunction
        used_disjunction_facts = set.union(*[f.dis_ancestors for f in facts])
        used_disjunction_dict = dict(used_disjunction_facts)
        valid = True
        for d, i in used_disjunction_facts:
            if used_disjunction_dict[d] != i:
                valid = False
        if not valid:
            # print("Invalid use of disjunction facts")
            return False

        if isinstance(thm, Theorem):
            new_facts = self.apply_std_thm(thm, facts)
        if isinstance(thm, HyperTheorem):
            new_facts = thm.rule(facts)
        if new_facts is False:
            print("error applying theorem")
            return

        new_dis_ancestors = set.union(*[fact.dis_ancestors for fact in facts])
        dependency_labels = [fact.label for fact in facts]
        for new_fact in new_facts:
            # update the immediate dependencies for the concluded fact
            new_fact.dependencies = dependency_labels
            new_fact.conc_thm = thm
            # union of all the disjunction ancestors of all its predecessors
            new_fact.dis_ancestors = new_dis_ancestors

        self.process_new_facts(new_facts)  # replace any ?'s
        self.add_new_facts(new_facts)

        for f in list(new_facts):
            if isinstance(f, Disjunction):
                new_facts += f.facts  # add in the facts from disjunctions

        return new_facts

    # look for any ? symbols in the list of facts, and generate symbols for them
    # replace the question marks in the list of facts
    def process_new_facts(self, new_facts):
        sym_dict = {}

        # first break up the disjunctions into their component facts
        simple_fact_list = []
        for fact in new_facts:
            if isinstance(fact, Fact):
                simple_fact_list.append(fact)
            elif isinstance(fact, Disjunction):
                simple_fact_list += fact.facts
            else:
                print("not Fact or Disjunction")

        for fact in simple_fact_list:
            args = fact.args
            for i in range(0, len(args)):

                if (sym := args[i]) is None:
                    print("error")
                    fact.do_print()
                    self.exec_command("display")

                if sym[0] == "?":
                    # print("question mark detected")
                    if sym not in sym_dict:
                        new_symbol = self.generate_new_symbol()
                        # print("new_symbol: ", new_symbol)
                        sym_dict[sym] = new_symbol
                    args[i] = sym_dict[sym]

        # print("--------------Testing------------")
        # for fact in simple_fact_list:
        #    fact.do_print()
        # print("--------------Done Testing -------")

    # produce a new symbol
    # a symbol is a string consisting of an uppercase letter followed by a sequence of digits
    def generate_new_symbol(self):
        try:
            while True:
                self.cur_suffix
                suffix = ""
                if self.cur_suffix != 0:
                    suffix = str(self.cur_suffix)
                new_symbol = self.cur_letter + suffix
                if self.cur_letter == "Z":
                    self.cur_letter = "A"
                    self.cur_suffix += 1
                else:
                    # increment cur_letter
                    self.cur_letter = chr(ord(self.cur_letter) + 1)
                if new_symbol not in self.symbol_set:
                    if new_symbol is None:
                        print("error: returning None")
                    return new_symbol
        except AttributeError:  # slightly unusual structure
            self.cur_letter = "A"
            self.cur_suffix = 0
            return self.generate_new_symbol()

    # enter into case mode using a particular disjunction
    # def enter_cases(self, dis):

    #        self.case_chain.append(dis) #keep a list of all cases being performed
    #        self.solved_cases.append([]) # for each disjunction in cases, keep track of which indices have been solved (IN GENERAL SHOULD LOOK THIS UP)

    # add new fact to the list of facts
    #        self.cur_indices.append(0)

    #    def advance_cases(self):

    def print_relevant_facts(self):
        for fact_lbl in self.ordered_fact_list:
            fact = self.fact_labels[fact_lbl]
            if fact.useful:
                fact.do_nice_print()

    # print facts together with their labels
    def print_facts(self):

        for lbl in self.fact_labels:
            fact = self.fact_labels[lbl]
            fact.do_print()
            print()

    def exec_command(self, cmd):
        cmd_list = cmd.split()
        cmd_name = cmd_list[0]
        cmd_args = cmd_list[1:]

        if cmd_name == "apply":
            thm_name = cmd_args[0]
            if thm_name in self.theorem_name_dict:
                thm = self.theorem_name_dict[thm_name]
            else:
                print("theorem name not recognized")
                return
            thm_args = cmd_args[1:]  # list of fact labels
            in_facts = [
                self.fact_labels[lbl] for lbl in thm_args
            ]  # the corresponding list of facts
            self.apply_thm(thm, in_facts)
            return

        # case disjunction index

        # an easier-to-implement version of case
        # all or nothing: either prove the result by iterating through some cases, or fail
        if cmd_name == "cases":

            print("DEPRECATED")
            return

            if self.case_depth >= 1:
                print("only one level of cases supported")
                return

            lbl = cmd_args[0]
            dis = self.fact_labels[lbl]
            if type(dis) != Disjunction:
                print("not a disjunction")
                return

            self.start_cases(dis)
            return

        if cmd_name == "conclude":

            print("DEPRECATED")
            return

            conclusion_lbl = cmd_args[0]
            conclusion = self.fact_labels[conclusion_lbl]
            if not conclusion.equals(self.goal):
                print("conclusion is not the goal")
                return

            if self.case_depth == 0:  # not in any cases
                print("goal achieved")

            if self.case_depth > 0:
                done = self.case_solved()
                if done:
                    print("goal achieved")

            return

        if cmd_name == "display":
            self.print_facts()
            return

        if cmd_name == "exit":
            return False

        print("Unkown Command")

    def start_cases(self, dis):
        self.num_cases = len(dis.facts)  # how many cases to deal with
        self.solved_cases = 0  # how many cases have been solved
        self.case_depth += 1
        self.case_dis = dis
        self.case_fact = (dis.facts[self.solved_cases]).copy()
        self.add_new_facts([self.case_fact])

    # called when a new case has been verified to be solved
    # return True if all cases have been exhausted
    def case_solved(self):
        self.solved_cases += 1
        self.remove_facts_by_depth(self.case_depth)
        if self.solved_cases == self.num_cases:
            done = True
            self.case_depth -= 1
        else:
            done = False
            self.case_fact = ((self.case_dis).facts[self.solved_cases]).copy()
            self.add_new_facts([self.case_fact])
        return done

    # remove facts at a particular depth
    def remove_facts_by_depth(self, D):
        fact_labels = self.fact_labels
        for lbl in dict(fact_labels):  # copy first, slightly annoying
            fact = fact_labels[lbl]
            if fact.depth == D:
                self.remove_fact(lbl)

    def remove_fact(self, lbl):
        fact = self.fact_labels[lbl]
        self.facts.remove(fact)
        del self.fact_labels[lbl]

    # print a log describing how a fact was reached

    def print_derivation(self, fact_label, derived_fact_labels=None):
        if derived_fact_labels is None:
            derived_fact_labels = set()
        # backtrack through the depency graph
        # mark the goal with a depth of 0 (0 is the deepest - we're measuring from the bottom of the ocean)
        # the depth of any other fact is

        fact = self.fact_labels[fact_label]
        if fact.dependencies != []:  # the fact was not an assumption
            thm = fact.conc_thm
            thm_name = thm.name

            # make sure all the hypotheses have been proven
            for label in fact.dependencies:
                if label not in derived_fact_labels:
                    self.print_derivation(label, derived_fact_labels)

            print("Applying theorem ", thm_name, " to ",
                  fact.dependencies, " we have: ")
            fact.do_print()
            print()

            derived_fact_labels.add(fact_label)

        else:
            print("By assumption we have: ")
            fact.do_print()
            print()
            derived_fact_labels.add(fact_label)


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

    MAX_ITERATIONS = 30

    thm_matches = {}  # dict mapping theorems in the environment to lists of fact matches
    for thm in pf_envir.theorems:
        thm_matches[thm] = match_facts_to_theorem(thm.facts, pf_envir.facts)

    for i in range(0, MAX_ITERATIONS):

        print("iteration: ", i)
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

                if facts_from_theorem := pf_envir.apply_thm(thm, match):  # sometimes the theorem match might be invalid. FIX?
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
            #           print("DONE!")
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


def rule(facts):
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


sylow_theorem = HyperTheorem(in_facts, rule, "sylow")


# single sylow subgroup
in_facts = [
    Fact("sylow_p_subgroup", ["H", "p", "G"]),
    Fact("num_sylow", ["p", "G", "*1"]),
    Fact("order", ["G", "n"]),
]


def rule(facts):
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


single_sylow_not_simple = HyperTheorem(in_facts, rule, "single_sylow_normal")

# simple + not_simple = false
in_facts = [Fact("simple", ["G"]), Fact("not_simple", ["G"])]
out_facts = [Fact("false", [])]
simple_not_simple = Theorem(in_facts, out_facts, "not_simple")

# embed into A_n
in_facts = [Fact("num_sylow", ["p", "G", "n_p"]), Fact("simple", ["G"])]


def rule(facts):
    # print("applying embed in An")
    conclusions = []
    n_p = int(facts[0].args[2])
    G = facts[0].args[1]
    if n_p > 1:
        # conclusions = [Fact("subgroup", [G, '?alt']), Fact("alternating_group", ['?alt', str(n_p)]) ]
        conclusions = [subgroup(G, "?alt"),
                       alternating_group("?alt", str(n_p))]
    return conclusions


embed_in_An = HyperTheorem(in_facts, rule, "embed_An")


in_facts = [alternating_group("A", "n")]


def rule(facts):
    A = facts[0].args[0]
    n = int(facts[0].args[1])

    if n > 1000:  # huge factorial computions are extremely slow/impossible
        # Ugly, but it works.  Other approaches?
        return []

    if n == 1:
        order = 1
    else:
        order = math.factorial(n) // 2
    conclusions = [Fact("order", [A, str(order)])]
    return conclusions


alternating_order = HyperTheorem(in_facts, rule, "alternating_order")

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


def rule(facts):
    m = int(facts[0].args[0])
    n = int(facts[0].args[1])
    conclusions = []
    if n % m != 0:
        conclusions.append(Fact("false", []))
    return conclusions


divides_contradiction = HyperTheorem(in_facts, rule, "divides_contradiction")

# an alternating group of order n > 5 is simple
in_facts = [alternating_group("A", "n")]


def rule(facts):

    #   print("in alternating order")

    conclusions = []  # needing this is annoying
    n = int(facts[0].args[1])
    if n >= 5:
        A = facts[0].args[0]  # this step is also annoying
        conclusions = [simple(A)]
    return conclusions


alternating_simple = HyperTheorem(in_facts, rule, "alternating_simple")

# index of a subgroup
in_facts = [subgroup("H", "G"), order("H", "m"), order("G", "n")]


def rule(facts):
    conclusions = []
    m = int(facts[1].args[1])
    n = int(facts[2].args[1])
    H = facts[0].args[0]
    G = facts[0].args[1]
    if n % m == 0:
        i = str(n // m)
        conclusions = [index(G, H, i)]
    return conclusions


subgroup_index = HyperTheorem(in_facts, rule, "subgroup_index")

# G acts transitively on the cosets of H
in_facts = [index("G", "H", "n")]
out_facts = [transitive_action("G", "n")]
coset_action = Theorem(in_facts, out_facts, "coset_action")

######
in_facts = [transitive_action("G", "n"), simple("G")]


def rule(facts):
    conclusions = []
    n = int(facts[0].args[1])
    if n > 1:
        conclusions = [subgroup("G", "?alt"),
                       alternating_group("?alt", str(n))]
    return conclusions


simple_group_action = HyperTheorem(in_facts, rule, "subgroup_index")

# counting elements of order p^k
in_facts = [
    sylow_p_subgroup("P", "p", "G"),
    num_sylow("p", "G", "n_p"),
    order("P", "pk"),
]


def rule(facts):
    G = facts[0].args[2]
    p = int(facts[0].args[1])
    P = facts[0].args[0]
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
    in_facts, rule, "count_order_pk_elements")

# getting a contradiction by counting
# really should be varargs
in_facts = [
    order_pk_lower_bound("G", "p1", "N1"),
    order_pk_lower_bound("G", "p2", "N2"),
    order("G", "n"),
]


def rule(facts):
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


counting_contradiction = HyperTheorem(in_facts, rule, "counting_contradiction")

########################### NORMALIZER OF INTERSECTION #########################

# more than one sylow?
in_facts = [num_sylow("p", "G", "n_p")]


def rule(facts):
    conclusions = []
    n_p = int(facts[0].args[2])
    p = facts[0].args[0]
    G = facts[0].args[1]
    if n_p > 1:
        conclusions = [more_than_one_sylow(p, G)]
    return conclusions


multiple_sylows = HyperTheorem(in_facts, rule, "multiple_sylows")

# possible maximal sylow intersections
in_facts = [more_than_one_sylow("p", "G"), sylow_p_order("G", "p", "pk")]


def rule(facts):
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
    in_facts, rule, "possible_max_intersections")

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


def rule(facts):
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
    in_facts, rule, "normalizer_sylow_intersection"
)

# if the normalizer of intersection is all of G, we're done
# could break this up, and not worry about group orders
in_facts = [normalizer("G", "H", "X"), order("G", "n"), order("X", "n")]
out_facts = [normal("H", "G")]
normalizer_everything_implies_normal = Theorem(
    in_facts, out_facts, "normalizer_everything_implies_normal"
)

in_facts = [normal("H", "G"), order("H", "h"), order("G", "g")]


def rule(facts):
    conclusions = []
    h = int(facts[1].args[1])
    g = int(facts[2].args[1])
    G = facts[0].args[1]
    H = facts[0].args[0]
    if 1 < h and h < g:
        conclusions.append(not_simple(G))
    return conclusions


normal_subgroup_to_not_simple = HyperTheorem(
    in_facts, rule, "normal_subgroup_to_not_simple"
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


def rule(facts):
    conclusions = []
    p = int(facts[0].args[0])
    np = int(facts[0].args[2])
    pl = int(facts[1].args[2])
    pk = int(facts[2].args[2])
    # n_p cong 1 mod p^k/p^l
    if np % (pk // pl) != 1:
        conclusions.append(false())
    return conclusions


rule_out_max_intersections = HyperTheorem(
    in_facts, rule, "rule_out_max_intersections")

in_facts = [normalizer_of_sylow_intersection("p", "G", "T"), order("T", "k")]


def rule(facts):
    conclusions = []
    p = int(facts[0].args[0])
    T = facts[0].args[2]
    k = int(facts[1].args[1])

    n_p_list = sylow2.num_sylow(p, k)
    if len(n_p_list) == 1:  # sylow p-subgroup of T forced to be normal
        conclusions.append(false())
        print("p: ", p, " :: k: ", k)
    return conclusions


rule_out_normalizer_of_intersection_order = HyperTheorem(
    in_facts, rule, "rule_out_normalizer_of_intersection_order"
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

    running = True
    # while(running != False):
    #        cmd = input()
    #        running = pf_envir.exec_command(cmd)
    pf_envir.exec_command("apply subgroup_trans F1 F4")
    pf_envir.exec_command("display")
    pf_envir.exec_command("apply subgroup_trans F0 F3")
    if pf_envir.goal_achieved:
        print("DONE")


def test2():

    global thm_list
    global thm_names

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

    def bar(a, b, c):
        return Fact("bar", [a, b, c])

    template = foo("W", "X", "W")
    # facts = [foo('A','B','C'), foo('D','C','D'), foo('C','A','A'), foo('A','C','A'), bar('x','y','x'), bar('x','x','x'), bar('x','x','u')]
    facts = [foo("A", "B", "C"), foo("D", "E", "F")]
    thm_facts = [foo("X", "Y", "Z"), foo("X", "Y", "Z")]

    matches = match_facts_to_theorem(thm_facts, facts, [foo("A", "B", "C")])

    print("in matching_test")
    for match in matches:
        for fact in match:
            fact.do_print()
        print(" ")


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
    global thm_list
    global thm_names

    while True:
        order = input("Enter a group order: ")
        fact1 = Fact("group", ["G"])
        fact2 = Fact("order", ["G", order])
        fact3 = Fact("simple", ["G"])

        #     test = max_sylow_intersection('G','3','3')

        facts = [fact1, fact2, fact3]
        goal = Fact("false", [])

        pf_envir = Proof_environment(facts, thm_list, thm_names, goal)

        auto_solve(pf_envir)


def easy_dis_test():
    def subgroup(A, B):
        return Fact("subgroup", [A, B])

    def OR(f1, f2):
        return Disjunction([f1, f2])

    facts = [Fact("subgroup", ["A", "B"]), Fact("subgroup", ["B", "C"])]
    conclusions = [Fact("subgroup", ["A", "C"])]
    subgroup_trans = Theorem(facts, conclusions, "subgroup_trans")

    facts = [
        OR(subgroup("A", "B"), subgroup("A", "X")),
        #            OR(subgroup('A','B'), subgroup('A','X')),
        subgroup("B", "D"),
        subgroup("X", "D"),
    ]
    theorems = [subgroup_trans]
    theorem_names = {"subgroup_trans": subgroup_trans}
    goal = subgroup("A", "D")

    pf_envir = Proof_environment(facts, theorems, theorem_names, goal)
    auto_solve(pf_envir)


def auto_dis_test():

    def subgroup(A, B):
        return Fact("subgroup", [A, B])

    def OR(f1, f2):
        return Disjunction([f1, f2])

    facts = [Fact("subgroup", ["A", "B"]), Fact("subgroup", ["B", "C"])]
    conclusions = [Fact("subgroup", ["A", "C"])]
    subgroup_trans = Theorem(facts, conclusions, "subgroup_trans")

    facts = [
        OR(subgroup("A", "B"), subgroup("C", "D")),
        OR(subgroup("B", "F"), subgroup("D", "F")),
        subgroup("B", "D"),
        subgroup("D", "B"),
        subgroup("X", "A"),
        subgroup("X", "C"),
    ]

    theorems = [subgroup_trans]
    theorem_names = {"subgroup_trans": subgroup_trans}
    goal = subgroup("X", "F")

    pf_envir = Proof_environment(facts, theorems, theorem_names, goal)
    auto_solve(pf_envir)


def alternating_test():
    global thm_list
    global thm_names
    #    thm_list = [embed_in_An]
    #   thm_names = ["embed_in_An", embed_in_An]
    fact1 = Fact("simple", ["G"])
    fact2 = Fact("num_sylow", ["3", "G", "4"])
    fact3 = Fact("order", ["G", "12"])
    goal = Fact("false", [])

    pf_envir = Proof_environment([fact1, fact2, fact3], thm_list, thm_names, goal)
    auto_solve(pf_envir)


def order_counting_test():
    global thm_list
    global thm_names

    fact1 = group("G")
    fact2 = order("G", "30")
    #    fact3 = OR(not_simple('G'), false())
    #    fact4 = OR(simple('G'), false())
    fact5 = sylow_p_subgroup("P5", "5", "G")
    fact6 = sylow_p_subgroup("P3", "3", "G")
    fact7 = order("P5", "5")
    fact8 = order("P3", "3")
    fact9 = simple("G")

    fact_list = [fact1, fact2, fact3, fact4, fact5, fact6, fact7, fact8, fact9]
    #    fact_list = [fact3,fact4]
    pf_envir = Proof_environment(fact_list, thm_list, thm_names, false())
    auto_solve(pf_envir)

    # Problem seems to occur when we have
    # (A or B), (C or D).  A -> Goal, C -> Goal, (B,D)->Goal


# def hard_disjunction_test():
#    def test_fact(A,B):
#        return Fact("fact", [A,B])


def find_hard_orders(in_file):

    global thm_list
    global thm_names

    with open(in_file, encoding="utf-8") as f:
        for n in f:
            facts = [group("G"), simple("G"), order("G", n)]
            pf_envir = Proof_environment(facts, thm_list, thm_names, false())
            if success := auto_solve(pf_envir):
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
auto_test2()

# auto_test2()
