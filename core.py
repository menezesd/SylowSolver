"""Core data-model classes for the theorem prover.

This module contains the Fact, Disjunction, Theorem, HyperTheorem and
ProofEnvironment classes extracted from `auto2.py` so the prover can be
refactored into smaller modules.
"""


class Fact:
    """A simple fact object: (name, args) with provenance metadata."""

    # depth is the number of nested cases in which the fact has been shown
    def __init__(
        self, name, args, dependencies=None, label=None, dis_ancestors=None, depth=0
    ):
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

        self.depth = depth

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
        if self.conc_thm is not None:
            print(
                "    by thm ",
                self.conc_thm.name,
                " applied to facts ",
                *self.dependencies,
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
        # create a shallow copy preserving metadata
        new_fact = Fact(
            self.name,
            list(self.args),
            list(self.dependencies),
            self.label,
            list(self.dis_ancestors),
            self.depth,
        )
        new_fact.useful = self.useful
        new_fact.conc_thm = self.conc_thm
        return new_fact


class Disjunction:
    """Represents a disjunction of Fact objects.

    Each Disjunction contains a list of Fact instances representing the
    alternatives; Disjunctions track dependencies similar to Fact.
    """

    def __init__(self, facts, dependencies=None, label=None, dis_ancestors=None):
        dependencies = [] if dependencies is None else dependencies
        dis_ancestors = [] if dis_ancestors is None else dis_ancestors
        self.facts = facts
        self.dependencies = dependencies
        self.dis_ancestors = set()
        self.label = label

        self.useful = False
        self.conc_thm = None

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
        if getattr(self, "conc_thm", None) is not None:
            print(
                "    by thm ",
                self.conc_thm.name,
                " applied to facts ",
                *self.dependencies,
            )
        else:
            print("    by hypothesis")
        if self.dis_ancestors != set():
            print("    Disjunctions in history: ", *self.dis_ancestors)
        print()


class Theorem:
    """A declarative theorem: pattern of input facts -> concrete conclusions."""

    def __init__(self, facts, conclusions, name):
        self.facts = facts
        self.conclusions = conclusions
        self.name = name


class HyperTheorem:
    """A theorem backed by a rule function that produces conclusions."""

    # rule is a function that takes in series of facts with structure 'facts' and ouputs a list of facts
    def __init__(self, facts, rule, name):
        self.facts = facts
        self.rule = rule
        self.name = name
        self.multi_args = False  # can the theorem take multiple arguments?


import env as _env

# Re-export ProofEnvironment for backwards compatibility
ProofEnvironment = _env.ProofEnvironment
Proof_environment = _env.Proof_environment
