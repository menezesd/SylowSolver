"""Automated theorem prover for Sylow theory.

This module implements a complete automated proof search system using logical facts,
theorems, and an intelligent search algorithm to prove properties of finite groups.
"""
from __future__ import annotations

import itertools
import math
import sylow2
from collections import deque
from dataclasses import dataclass, field
from typing import List, Set, Tuple, Optional, Dict, Any, Union, Callable

# Constants
MAX_ITERATIONS = 1000
BATCH_SIZE = 8
DEFAULT_LABEL = "F0"


class Predicates:
    """Constants for predicate names used in facts."""
    GROUP = "group"
    ORDER = "order"
    SIMPLE = "simple"
    NOT_SIMPLE = "not_simple"
    SUBGROUP = "subgroup"
    NORMAL = "normal"
    DIVIDES = "divides"
    FALSE = "false"
    SYLOW_ORDER = "sylow_order"
    SYLOW_P_SUBGROUP = "sylow_p_subgroup"
    NUM_SYLOW = "num_sylow"
    ALTERNATING_GROUP = "alternating_group"
    INDEX = "index"
    TRANSITIVE_ACTION = "transitive_action"
    ORDER_PK_LOWER_BOUND = "order_pk_lower_bound"
    MORE_THAN_ONE_SYLOW = "more_than_one_sylow"
    INTERSECTION = "intersection"
    NORMALIZER = "normalizer"
    ORDER_LOWER_BOUND = "order_lower_bound"
    MAX_SYLOW_INTERSECTION = "max_sylow_intersection"
    PROPER_SUBGROUP = "proper_subgroup"
    NORMALIZER_OF_SYLOW_INTERSECTION = "normalizer_of_sylow_intersection"


@dataclass(slots=True)
class Fact:
    """
    Represents a logical fact in the proof system.

    A fact is a predicate with arguments, e.g., "group(G)" or "order(G, 12)".
    Facts can be derived from other facts using theorems.

    Attributes:
        name: The predicate name (e.g., "group", "order")
        args: List of arguments to the predicate
        dependencies: Labels of facts needed to conclude this fact
        label: Unique identifier for this fact
        dis_ancestors: Set of (DisjunctionLabel, index) pairs from ancestry
        conc_thm: The theorem used to conclude this fact, if any
        useful: Whether this fact was used to conclude the goal
    """
    name: str
    args: List[Any]
    dependencies: List[str] = field(default_factory=list)
    label: Optional[str] = None
    dis_ancestors: Set[Tuple[str, int]] = field(default_factory=set)
    conc_thm: Optional[Any] = None  # Type is Theorem but avoid circular import
    useful: bool = False

    def __str__(self) -> str:
        """Detailed string representation for debugging."""
        return (
            f"{self.label} : {self.name} {self.args} :: "
            f"{self.dependencies} :: {self.dis_ancestors}"
        )

    def __repr__(self) -> str:
        """Concise representation for debugging."""
        return f"Fact({self.name!r}, {self.args!r})"

    def print_nice(self) -> None:
        """Print fact in human-readable format."""
        print(f"{self.label} : {self.name} {self.args}")
        if self.conc_thm is not None:
            deps_str = " ".join(str(d) for d in self.dependencies)
            print(f"    by thm {self.conc_thm.name} applied to facts {deps_str}")
        else:
            print("    by hypothesis")
        if self.dis_ancestors:
            anc_str = " ".join(str(a) for a in self.dis_ancestors)
            print(f"    Disjunctions in history: {anc_str}")
        print()

    def __eq__(self, other: object) -> bool:
        """Check structural equality (same name and args)."""
        if not isinstance(other, Fact):
            return NotImplemented
        return self.name == other.name and self.args == other.args

    def __hash__(self) -> int:
        """Hash based on structure for use in sets/dicts."""
        return hash((self.name, tuple(self.args)))

    # Legacy compatibility - kept for backward compatibility with existing code
    def do_print(self) -> None:
        """Print fact. Consider using print(fact) instead."""
        print(self)

    def do_nice_print(self) -> None:
        """Print fact in nice format. Consider using print_nice() instead."""
        self.print_nice()

    def equals(self, fact: 'Fact') -> bool:
        """Check equality. Consider using == instead."""
        return self == fact


@dataclass(frozen=True)
class DisjunctionKey:
    """
    Immutable structural key for efficient disjunction deduplication.

    Uses sorted tuples to create a canonical representation that avoids
    expensive string concatenation while enabling O(1) hash-based lookups.

    Attributes:
        facts_tuple: Sorted tuple of (name, args) pairs
        ancestors_tuple: Sorted tuple of disjunction ancestors
        conc_thm: The concluding theorem, if any
    """
    facts_tuple: Tuple[Tuple[str, Tuple[Any, ...]], ...]
    ancestors_tuple: Tuple[Tuple[str, int], ...]
    conc_thm: Optional[str]

    @staticmethod
    def from_disjunction(facts: List['Fact'], dis_ancestors: Set[Tuple[str, int]],
                        conc_thm: Optional[Any] = None) -> 'DisjunctionKey':
        """Create a DisjunctionKey from disjunction components."""
        # Sort facts by (name, args) for canonical representation
        sorted_facts = tuple(sorted((f.name, tuple(f.args)) for f in facts))

        # Sort ancestors for canonical representation
        sorted_ancestors = tuple(sorted(dis_ancestors)) if dis_ancestors else ()

        # Extract theorem name if present
        thm_name = conc_thm.name if conc_thm and hasattr(conc_thm, 'name') else None

        return DisjunctionKey(sorted_facts, sorted_ancestors, thm_name)


class Disjunction:
    """Represents an OR of multiple facts for case-based reasoning."""

    __slots__ = ('facts', 'dependencies', 'dis_ancestors', 'label', 'conc_thm', 'useful')

    def __init__(
        self,
        facts: List[Fact],
        dependencies: Optional[List[str]] = None,
        label: Optional[str] = None,
        dis_ancestors: Optional[List[Any]] = None,
        conc_thm: Optional[Any] = None
    ):
        self.facts = facts
        self.dependencies = dependencies if dependencies is not None else []
        self.dis_ancestors: Set[Tuple[str, int]] = set()
        self.label = label
        self.conc_thm = conc_thm
        self.useful = False

    def __repr__(self) -> str:
        """Concise representation for debugging."""
        fact_reprs = " OR ".join(repr(f) for f in self.facts)
        return f"Disjunction([{fact_reprs}])"

    def get_key(self) -> DisjunctionKey:
        """Generate structural key for deduplication."""
        return DisjunctionKey.from_disjunction(self.facts, self.dis_ancestors, self.conc_thm)

    def do_print(self) -> None:
        """Print disjunction."""
        print(self.label, ":")
        for i, fact in enumerate(self.facts):
            fact.do_print()
            if i != len(self.facts) - 1:
                print("    OR")

    def do_nice_print(self) -> None:
        """Print disjunction in human-readable format."""
        print(self.label, ":")
        for i, fact in enumerate(self.facts):
            fact.do_print()
            if i != len(self.facts) - 1:
                print("    OR")
        if self.conc_thm is not None:
            print(
                "    by thm ",
                self.conc_thm.name,
                " applied to facts ",
                *self.dependencies
            )
        else:
            print("    by hypothesis")
        if self.dis_ancestors:
            print("    Disjunctions in history: ", *self.dis_ancestors)
        print()


class Theorem:
    """
    Represents a standard logical theorem with premises and conclusions.

    A theorem specifies a pattern: if facts matching the premises exist,
    then the conclusions can be derived.

    Example:
        symbols:     G, H, I
        facts:       subgroup H G, subgroup I H
        conclusions: subgroup I G
    """

    __slots__ = ('facts', 'conclusions', 'name')

    def __init__(self, facts: List[Fact], conclusions: List[Fact], name: str):
        self.facts = facts
        self.conclusions = conclusions
        self.name = name

    def __repr__(self) -> str:
        return f"Theorem({self.name!r})"


class HyperTheorem:
    """
    Represents a computational theorem with a rule function.

    Unlike standard theorems, HyperTheorems use a Python function to compute
    conclusions from premises, allowing for more complex reasoning.
    """

    __slots__ = ('facts', 'rule', 'name', 'multi_args')

    def __init__(self, facts: List[Fact], rule: Any, name: str):
        self.facts = facts
        self.rule = rule
        self.name = name
        self.multi_args = False  # can the theorem take multiple arguments?

    def __repr__(self) -> str:
        return f"HyperTheorem({self.name!r})"


class Proof_environment:
    """
    Central manager for the proof search process.

    Maintains the current state of facts, theorems, and disjunctions,
    and provides methods for applying theorems and tracking goal achievement.
    """

    def __init__(
        self,
        facts: List[Union[Fact, 'Disjunction']],
        theorems: List[Union[Theorem, HyperTheorem]],
        theorem_name_dict: Dict[str, Union[Theorem, HyperTheorem]],
        goal: Fact
    ):
        """
        Initialize a proof environment.

        Args:
            facts: Initial list of facts (hypotheses)
            theorems: List of available theorems
            theorem_name_dict: Dictionary mapping theorem names to theorem objects
            goal: The fact to be proven
        """
        self.ordered_fact_list: List[str] = []  # fact labels in order of appearance
        self.facts: List[Fact] = []
        self.theorems = theorems
        self.theorem_name_dict = theorem_name_dict
        self.disjunctions: List[Disjunction] = []

        # Disjunction deduplication: map DisjunctionKey -> DisjId
        self.disj_labels: Dict[DisjunctionKey, str] = {}

        self.goal = goal
        self.goal_achieved = False
        self.goal_dis_combos: List[Set[Tuple[str, int]]] = []

        # fact_labels maps labels to facts
        self.fact_labels: Dict[str, Union[Fact, Disjunction]] = {}
        self.cur_fact_num = 0

        # Symbol generation state - properly initialized
        self.cur_letter = "A"
        self.cur_suffix = 0

        # The set of all symbols currently in the environment
        self.symbol_set: Set[str] = set()

        self.add_new_facts(facts)

        for fact in self.facts:
            for sym in fact.args:
                self.symbol_set.add(sym)

    def new_label(self, letter="F"):
        label = letter + str(self.cur_fact_num)
        self.cur_fact_num += 1
        return label

    def update_goal_achieved(self, goal_fact: Fact) -> None:
        """
        Check if the goal has been achieved across all disjunction branches.

        For the goal to be achieved, every possible combination of disjunction
        branches must be covered by at least one proven path to the goal.

        Args:
            goal_fact: The fact that matches the goal (used for ancestry tracking)
        """
        # Collect all disjunction labels from goal ancestry
        dis_labels = {D for D, _ in set.union(*(self.goal_dis_combos))}

        # Build list of (disjunction_label, branch_count) pairs
        disj_branch_counts = [
            (label, len(self.fact_labels[label].facts))
            for label in dis_labels
        ]

        # Generate all possible branch combinations
        branch_choices = [
            [(label, i) for i in range(count)]
            for label, count in disj_branch_counts
        ]
        all_combinations = {frozenset(combo) for combo in itertools.product(*branch_choices)}

        # Check that each combination is covered by some proven path
        frozen_dis_combos = {frozenset(d) for d in self.goal_dis_combos}
        for combination in all_combinations:
            if not any(proven.issubset(combination) for proven in frozen_dis_combos):
                return

        self.goal_achieved = True

    # mark a given fact, and all of its ancestors as useful
    def update_useful(self, fact):
        if fact.useful:
            return  # already marked
        fact.useful = True
        for pred_lbl in fact.dependencies:
            self.update_useful(self.fact_labels[pred_lbl])

    def _process_disjunction_subfacts(self, disjunction: Disjunction) -> None:
        """Set up dependencies and ancestors for each sub-fact of a disjunction."""
        for i, sub_fact in enumerate(disjunction.facts):
            sub_fact.dependencies = [disjunction.label]
            sub_fact.dis_ancestors = set(disjunction.dis_ancestors)
            sub_fact.dis_ancestors.add((disjunction.label, i))

    def add_new_facts(self, new_facts: List[Union[Fact, Disjunction]]) -> None:
        """
        Add new facts or disjunctions to the proof environment.

        Args:
            new_facts: List of Facts or Disjunctions to add
        """
        for fact in new_facts:
            if isinstance(fact, Fact):
                new_label = self.new_label()
                self.fact_labels[new_label] = fact
                fact.label = new_label
                self.facts.append(fact)

                if fact == self.goal:
                    self.goal_dis_combos.append(fact.dis_ancestors)
                    self.update_goal_achieved(fact)
                    self.update_useful(fact)

            elif isinstance(fact, Disjunction):
                disj_key = fact.get_key()

                if disj_key in self.disj_labels:
                    # Reuse existing label for duplicate disjunction
                    fact.label = self.disj_labels[disj_key]
                else:
                    # New disjunction
                    new_label = self.new_label(letter="D")
                    self.fact_labels[new_label] = fact
                    fact.label = new_label
                    self.disjunctions.append(fact)
                    self.disj_labels[disj_key] = new_label

                self._process_disjunction_subfacts(fact)
                self.add_new_facts(fact.facts)

            self.ordered_fact_list.append(fact.label)

    def apply_std_thm(
        self, thm: Theorem, facts: List[Fact]
    ) -> Union[List[Fact], bool]:
        """
        Apply a standard theorem to a list of facts.

        Args:
            thm: The theorem to apply
            facts: Facts matching the theorem's premises

        Returns:
            List of conclusion facts if successful, False otherwise
        """
        if len(facts) != len(thm.facts):
            return False

        matching: Dict[str, Any] = {}
        for in_fact, thm_fact in zip(facts, thm.facts):
            if in_fact.name != thm_fact.name:
                return False
            if len(in_fact.args) != len(thm_fact.args):
                return False

            for in_arg, thm_arg in zip(in_fact.args, thm_fact.args):
                # Check for exact match requirement (prefixed with *)
                if isinstance(thm_arg, str) and thm_arg.startswith("*"):
                    if in_arg != thm_arg[1:]:
                        return False
                    continue

                # Check for consistent variable binding
                if thm_arg in matching:
                    if matching[thm_arg] != in_arg:
                        return False
                else:
                    matching[thm_arg] = in_arg

        # Build conclusion facts
        conclusions = []
        for conc in thm.conclusions:
            new_fact_args = [
                arg if isinstance(arg, str) and arg.startswith("?") else matching[arg]
                for arg in conc.args
            ]
            conclusions.append(Fact(conc.name, new_fact_args))

        return conclusions

    def apply_thm(
        self, thm: Union[Theorem, HyperTheorem], facts: List[Fact]
    ) -> Union[List[Union[Fact, Disjunction]], bool]:
        """
        Apply a theorem or hyper-theorem and add conclusions to the environment.

        Args:
            thm: The theorem to apply
            facts: Facts matching the theorem's premises

        Returns:
            List of new facts/disjunctions if successful, False if invalid
        """
        # Validate: no two facts from conflicting disjunction branches
        used_disjunction_facts = set.union(*[f.dis_ancestors for f in facts])
        used_disjunction_dict = dict(used_disjunction_facts)
        for disj_label, branch_idx in used_disjunction_facts:
            if used_disjunction_dict[disj_label] != branch_idx:
                return False

        # Apply the appropriate theorem type
        if isinstance(thm, Theorem):
            new_facts = self.apply_std_thm(thm, facts)
        elif isinstance(thm, HyperTheorem):
            new_facts = thm.rule(facts)
        else:
            return False

        if new_facts is False:
            return False

        # Set up provenance for new facts
        new_dis_ancestors = set.union(*[fact.dis_ancestors for fact in facts])
        dependency_labels = [fact.label for fact in facts]
        for new_fact in new_facts:
            new_fact.dependencies = dependency_labels
            new_fact.conc_thm = thm
            new_fact.dis_ancestors = new_dis_ancestors

        self.process_new_facts(new_facts)
        self.add_new_facts(new_facts)

        # Include disjunction sub-facts in return
        result = list(new_facts)
        for f in new_facts:
            if isinstance(f, Disjunction):
                result.extend(f.facts)

        return result

    def process_new_facts(self, new_facts: List[Union[Fact, Disjunction]]) -> None:
        """
        Replace placeholder symbols (starting with ?) with fresh unique symbols.

        Args:
            new_facts: List of facts/disjunctions to process
        """
        sym_dict: Dict[str, str] = {}

        # Flatten disjunctions into simple facts
        simple_facts: List[Fact] = []
        for fact in new_facts:
            if isinstance(fact, Fact):
                simple_facts.append(fact)
            elif isinstance(fact, Disjunction):
                simple_facts.extend(fact.facts)

        # Replace placeholder symbols
        for fact in simple_facts:
            for i, sym in enumerate(fact.args):
                if sym is None:
                    raise ValueError(f"Null argument in fact: {fact}")
                if isinstance(sym, str) and sym.startswith("?"):
                    if sym not in sym_dict:
                        sym_dict[sym] = self.generate_new_symbol()
                    fact.args[i] = sym_dict[sym]

    def generate_new_symbol(self) -> str:
        """
        Produce a new unique symbol.

        A symbol is a string consisting of an uppercase letter followed by
        an optional sequence of digits (e.g., 'A', 'B', ..., 'Z', 'A1', 'B1', ...).

        Returns:
            A unique symbol not yet in the environment's symbol set.
        """
        while True:
            suffix = "" if self.cur_suffix == 0 else str(self.cur_suffix)
            new_symbol = self.cur_letter + suffix

            # Advance to next letter/suffix
            if self.cur_letter == "Z":
                self.cur_letter = "A"
                self.cur_suffix += 1
            else:
                self.cur_letter = chr(ord(self.cur_letter) + 1)

            if new_symbol not in self.symbol_set:
                self.symbol_set.add(new_symbol)
                return new_symbol

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

    def _cmd_apply(self, args: List[str]) -> None:
        """Apply a theorem to specified facts."""
        if not args:
            print("Usage: apply <theorem_name> <fact_labels...>")
            return
        thm_name = args[0]
        if thm_name not in self.theorem_name_dict:
            print(f"Theorem '{thm_name}' not recognized")
            return
        thm = self.theorem_name_dict[thm_name]
        fact_labels = args[1:]
        facts = [self.fact_labels[lbl] for lbl in fact_labels]
        self.apply_thm(thm, facts)

    def exec_command(self, cmd: str) -> Optional[bool]:
        """
        Execute an interactive command.

        Args:
            cmd: Command string (e.g., "apply sylow F0 F1")

        Returns:
            False to exit, None otherwise
        """
        parts = cmd.split()
        if not parts:
            return None

        cmd_name = parts[0]
        cmd_args = parts[1:]

        commands = {
            "apply": self._cmd_apply,
            "display": lambda _: self.print_facts(),
        }

        if cmd_name == "exit":
            return False

        if cmd_name in commands:
            commands[cmd_name](cmd_args)
        else:
            print(f"Unknown command: {cmd_name}")

        return None

    def print_derivation(
        self, fact_label: str, derived_fact_labels: Optional[Set[str]] = None
    ) -> None:
        """
        Print the derivation tree for a fact.

        Args:
            fact_label: Label of the fact to trace
            derived_fact_labels: Set of already-printed labels (for recursion)
        """
        if derived_fact_labels is None:
            derived_fact_labels = set()

        fact = self.fact_labels[fact_label]

        if fact.dependencies:
            # Recursively print dependencies first
            for label in fact.dependencies:
                if label not in derived_fact_labels:
                    self.print_derivation(label, derived_fact_labels)

            deps_str = ", ".join(fact.dependencies)
            print(f"Applying theorem {fact.conc_thm.name} to [{deps_str}] we have:")
            print(f"  {fact}")
            print()
        else:
            print("By assumption we have:")
            print(f"  {fact}")
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


def match_facts_to_theorem(
    thm_facts: List[Fact],
    facts: List[Fact],
    new_facts: Optional[List[Fact]] = None
) -> List[List[Fact]]:
    """
    Find all fact combinations matching a theorem's premises.

    Args:
        thm_facts: The theorem's premise patterns
        facts: Available facts to match against
        new_facts: If provided, only return matches containing at least one new fact

    Returns:
        List of fact lists, each matching all theorem premises
    """
    if new_facts is None:
        new_facts = facts

    # Track partial matches: (matched_facts, substitution_dict, uses_new_fact)
    cur_matches: List[List[Fact]] = [[]]
    dicts: List[Dict[str, Any]] = [{}]
    uses_new_list: List[bool] = [False]

    for premise in thm_facts:
        new_cur_matches = []
        new_dicts = []
        new_uses_new_list = []

        for match, match_dict, uses_new in zip(cur_matches, dicts, uses_new_list):
            matched_facts, matched_dicts = match_facts_to_template(
                premise, facts, init_match_dict=match_dict
            )
            for new_match, new_dict in zip(matched_facts, matched_dicts):
                new_cur_matches.append(match + [new_match])
                new_dicts.append(new_dict)
                new_uses_new_list.append(uses_new or (new_match in new_facts))

        cur_matches = new_cur_matches
        dicts = new_dicts
        uses_new_list = new_uses_new_list

    # Filter to matches containing at least one new fact
    return [match for match, uses_new in zip(cur_matches, uses_new_list) if uses_new]


def match_facts_to_template(
    template: Fact,
    facts: List[Fact],
    init_match_dict: Optional[Dict[str, Any]] = None
) -> Tuple[List[Fact], List[Dict[str, Any]]]:
    """
    Find all facts matching a template pattern.

    Args:
        template: The pattern to match (may contain variables)
        facts: Available facts to match against
        init_match_dict: Initial variable bindings to respect

    Returns:
        Tuple of (matching_facts, substitution_dicts)
    """
    init_match_dict = init_match_dict or {}
    matches: List[Fact] = []
    dicts: List[Dict[str, Any]] = []

    for fact in facts:
        if fact.name != template.name:
            continue
        if len(fact.args) != len(template.args):
            continue

        match_dict = dict(init_match_dict)
        is_match = True

        for temp_arg, fact_arg in zip(template.args, fact.args):
            # Exact match required (prefixed with *)
            if isinstance(temp_arg, str) and temp_arg.startswith("*"):
                if temp_arg[1:] != fact_arg:
                    is_match = False
                    break
                continue

            # Variable binding
            if temp_arg not in match_dict:
                match_dict[temp_arg] = fact_arg
            elif match_dict[temp_arg] != fact_arg:
                is_match = False
                break

        if is_match:
            matches.append(fact)
            dicts.append(match_dict)

    return matches, dicts


def auto_solve(pf_envir: 'Proof_environment') -> bool:
    """
    Optimized agenda-based proof search using trigger indexing and batching.

    This function attempts to prove the goal in pf_envir by iteratively applying
    theorems to facts until either:
    - The goal is achieved (returns True)
    - The work queue is exhausted (returns False)
    - Maximum iterations are reached (returns False)

    Algorithmic improvements over naive O(theorems × facts) approach:
    1. **Trigger indexing**: Only check theorems relevant to each fact via
       (fact_name, arity) → [(theorem, premise_index)] index
    2. **Agenda-based queue**: Process facts one at a time, adding new facts
       to queue as they're discovered
    3. **Batch processing**: Process BATCH_SIZE facts per iteration to reduce
       loop overhead
    4. **Deque for O(1) operations**: Use collections.deque instead of list
       for O(1) append/popleft
    5. **Processed tracking**: Avoid reprocessing facts with a set

    Args:
        pf_envir: The proof environment containing facts, theorems, and goal

    Returns:
        True if goal was proven, False otherwise
    """
    # Build trigger index: map (fact_name, num_args) -> list of (theorem, premise_index, premises)
    trigger_index: Dict[Tuple[str, int], List[Tuple[Any, int, List[Fact]]]] = {}

    for thm in pf_envir.theorems:
        for i, premise in enumerate(thm.facts):
            key = (premise.name, len(premise.args))
            if key not in trigger_index:
                trigger_index[key] = []
            trigger_index[key].append((thm, i, thm.facts))

    # Initialize work queue with all facts
    work_queue: deque = deque(pf_envir.facts)
    processed_labels: Set[str] = set()  # Track which facts we've already processed

    iteration = 0
    while work_queue and iteration < MAX_ITERATIONS:
        iteration += 1
        print(f"iteration: {iteration}, queue size: {len(work_queue)}")

        # Check if goal achieved
        if pf_envir.goal_achieved:
            pf_envir.print_relevant_facts()
            print("SUCCESS")
            return True

        # Extract a batch of facts to process
        batch = []
        for _ in range(min(BATCH_SIZE, len(work_queue))):
            if not work_queue:
                break
            fact = work_queue.popleft()

            # Skip already processed facts
            if fact.label in processed_labels:
                continue

            batch.append(fact)
            processed_labels.add(fact.label)

        if not batch:
            continue  # All facts in batch were already processed

        # Process each fact in the batch
        for fact in batch:
            # Skip Disjunctions - only process Facts
            if not isinstance(fact, Fact):
                continue

            # Find triggered theorems using the index
            key = (fact.name, len(fact.args))
            triggers = trigger_index.get(key, [])

            for thm, premise_idx, premises in triggers:
                # Try to complete the match starting from this fact
                matches = _match_with_trigger(pf_envir, fact, thm, premise_idx, premises)

                for match in matches:
                    # Apply theorem
                    if new_facts := pf_envir.apply_thm(thm, match):
                        # Add new facts to work queue
                        work_queue.extend(new_facts)

    # Failed to prove goal
    pf_envir.print_relevant_facts()
    print("FAILURE")
    return False


def _match_with_trigger(
    pf_envir: 'Proof_environment',
    new_fact: Fact,
    thm: Any,
    trigger_idx: int,
    premises: List[Fact]
) -> List[List[Fact]]:
    """
    Try to complete a theorem match given that new_fact matches premise at trigger_idx.

    This implements incremental theorem matching: given that we know new_fact
    unifies with premises[trigger_idx], we try to find matches for all other
    premises to complete the theorem application.

    Args:
        pf_envir: The proof environment with available facts
        new_fact: The newly added fact that triggered this theorem
        thm: The theorem being matched
        trigger_idx: Index of the premise that new_fact matched
        premises: All premises of the theorem

    Returns:
        List of complete matches, where each match is a list of facts
        in the same order as premises
    """
    # Try to unify new_fact with the premise at trigger_idx
    initial_dict = {}
    if not _unify_facts(premises[trigger_idx], new_fact, initial_dict):
        return []

    # Split premises: before trigger, trigger itself, after trigger
    before_premises = premises[:trigger_idx]
    after_premises = premises[trigger_idx + 1:]

    # Match premises before the trigger
    before_matches = [[]]
    before_dicts = [initial_dict.copy()]

    for premise in before_premises:
        new_before_matches = []
        new_before_dicts = []

        for match, dict_so_far in zip(before_matches, before_dicts):
            for candidate in pf_envir.facts:
                new_dict = dict_so_far.copy()
                if _unify_facts(premise, candidate, new_dict):
                    new_before_matches.append(match + [candidate])
                    new_before_dicts.append(new_dict)

        before_matches = new_before_matches
        before_dicts = new_before_dicts

        if not before_matches:
            return []  # Can't match all before premises

    # For each "before" match, try to match "after" premises
    complete_matches = []

    for before_match, dict_after_before in zip(before_matches, before_dicts):
        after_matches = [[]]
        after_dicts = [dict_after_before.copy()]

        for premise in after_premises:
            new_after_matches = []
            new_after_dicts = []

            for match, dict_so_far in zip(after_matches, after_dicts):
                for candidate in pf_envir.facts:
                    new_dict = dict_so_far.copy()
                    if _unify_facts(premise, candidate, new_dict):
                        new_after_matches.append(match + [candidate])
                        new_after_dicts.append(new_dict)

            after_matches = new_after_matches
            after_dicts = new_after_dicts

            if not after_matches:
                break  # Can't match all after premises

        # Reconstruct in premise order: before + [trigger] + after
        for after_match in after_matches:
            complete_matches.append(before_match + [new_fact] + after_match)

    return complete_matches


def _unify_facts(template: Fact, fact: Fact, substitution_dict: Dict[str, Any]) -> bool:
    """
    Try to unify template with fact, updating substitution_dict in place.

    Unification matches a template fact (with variables) against a concrete fact,
    binding variables to values.

    Variable convention (matching original code):
    - All template arguments are treated as variables that can bind to any value
    - Arguments starting with '*' require exact match (e.g., '*1' must match '1')

    Args:
        template: The pattern fact (may contain variables)
        fact: The concrete fact to match against
        substitution_dict: Dictionary mapping variable names to values (modified in place)

    Returns:
        True if unification succeeds (template matches fact), False otherwise

    Example:
        >>> template = Fact("order", ["G", "n"])
        >>> fact = Fact("order", ["group1", "12"])
        >>> subst = {}
        >>> _unify_facts(template, fact, subst)
        True
        >>> subst
        {'G': 'group1', 'n': '12'}
    """
    if template.name != fact.name:
        return False
    if len(template.args) != len(fact.args):
        return False

    for t_arg, f_arg in zip(template.args, fact.args):
        if isinstance(t_arg, str) and t_arg.startswith("*"):
            # Exact match required (strip the '*' prefix)
            if t_arg[1:] != f_arg:
                return False
        elif t_arg in substitution_dict:
            # Variable already bound - must match
            if substitution_dict[t_arg] != f_arg:
                return False
        else:
            # New variable binding
            substitution_dict[t_arg] = f_arg

    return True


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
# Tests are named with test_ prefix for pytest discovery


def test_disjunction_proof() -> None:
    """Test proof with disjunctions using subgroup transitivity."""
    # Define subgroup transitivity theorem
    premises = [Fact("subgroup", ["A", "B"]), Fact("subgroup", ["B", "C"])]
    conclusions = [Fact("subgroup", ["A", "C"])]
    subgroup_trans = Theorem(premises, conclusions, "subgroup_trans")

    # Set up facts with a disjunction
    fact1 = Fact("subgroup", ["X", "Y"])
    fact2 = Fact("subgroup", ["X", "Z"])
    d1 = Fact("subgroup", ["Y", "A"])
    d2 = Fact("subgroup", ["Z", "A"])
    dis = Disjunction([d1, d2])

    facts = [fact1, fact2, dis]
    theorems = [subgroup_trans]
    theorem_dict = {"subgroup_trans": subgroup_trans}
    goal = Fact("subgroup", ["X", "A"])

    pf_envir = Proof_environment(facts, theorems, theorem_dict, goal)
    pf_envir.exec_command("apply subgroup_trans F1 F4")
    pf_envir.exec_command("apply subgroup_trans F0 F3")

    assert pf_envir.goal_achieved, "Should prove X is subgroup of A"


def test_matching() -> None:
    """Test theorem matching logic."""
    def foo(first, second, third):
        return Fact("foo", [first, second, third])

    facts = [foo("A", "B", "C"), foo("D", "E", "F")]
    thm_facts = [foo("X", "Y", "Z"), foo("X", "Y", "Z")]

    matches = match_facts_to_theorem(thm_facts, facts, [foo("A", "B", "C")])

    # Should find matches that include the new fact
    assert len(matches) > 0, "Should find at least one match"


def test_subgroup_transitivity_chain() -> None:
    """Test auto_solve on a chain of subgroup relations."""
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
    theorems = [subgroup_trans]
    theorem_dict = {"subgroup_trans": subgroup_trans}
    goal = Fact("subgroup", ["X", "F"])

    pf_envir = Proof_environment(facts, theorems, theorem_dict, goal)
    result = auto_solve(pf_envir)

    assert result, "Should prove X is subgroup of F through transitivity chain"


def test_simple_disjunction() -> None:
    """Test auto_solve with simple disjunction."""
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
    theorems = [subgroup_trans]
    theorem_dict = {"subgroup_trans": subgroup_trans}
    goal = sub("A", "D")

    pf_envir = Proof_environment(facts, theorems, theorem_dict, goal)
    result = auto_solve(pf_envir)

    assert result, "Should prove A is subgroup of D through either branch"


def test_complex_disjunction() -> None:
    """Test auto_solve with multiple disjunctions."""
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
    theorems = [subgroup_trans]
    theorem_dict = {"subgroup_trans": subgroup_trans}
    goal = sub("X", "F")

    pf_envir = Proof_environment(facts, theorems, theorem_dict, goal)
    result = auto_solve(pf_envir)

    assert result, "Should prove X is subgroup of F through disjunction cases"


def test_alternating_embedding() -> None:
    """Test embedding into alternating group."""
    facts = [
        group("G"),
        simple("G"),
        Fact("num_sylow", ["3", "G", "4"]),
        order("G", "12"),
    ]
    goal = false()

    pf_envir = Proof_environment(facts, thm_list, thm_names, goal)
    result = auto_solve(pf_envir)

    assert result, "Should find contradiction for order 12 simple group"


def test_element_counting() -> None:
    """Test element counting contradictions."""
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

    pf_envir = Proof_environment(facts, thm_list, thm_names, goal)
    result = auto_solve(pf_envir)

    assert result, "Should find contradiction by counting elements"


def find_hard_orders(in_file: str) -> None:
    """Find orders where the prover fails to prove non-simplicity."""
    with open(in_file, encoding="utf-8") as f:
        for n in f:
            n = n.strip()
            if not n:
                continue
            facts = [group("G"), simple("G"), order("G", n)]
            pf_envir = Proof_environment(facts, thm_list, thm_names, false())
            if auto_solve(pf_envir):
                print(f"{n}: SUCCESS")
            else:
                print(f"{n}: FAILURE")


def interactive_test() -> None:
    """Interactive test for manual exploration."""
    while True:
        try:
            n = input("Enter a group order (or 'quit'): ")
            if n.lower() == 'quit':
                break
            facts = [group("G"), simple("G"), order("G", n)]
            pf_envir = Proof_environment(facts, thm_list, thm_names, false())
            auto_solve(pf_envir)
        except KeyboardInterrupt:
            break


if __name__ == "__main__":
    # Run interactive test by default
    interactive_test()
