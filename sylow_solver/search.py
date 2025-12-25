from __future__ import annotations

import itertools
import logging
from collections import deque
from typing import Any, Dict, List, Optional, Set, Tuple, Union, cast

from .config import DEFAULT_CONFIG, SolverConfig
from .facts import Disjunction, DisjunctionKey, Fact
from .theorem_base import HyperTheorem, Theorem


class ProofEnvironment:
    """
    Central manager for the proof search process.

    Maintains the current state of facts, theorems, and disjunctions,
    and provides methods for applying theorems and tracking goal achievement.
    """

    def __init__(
        self,
        facts: List[Union[Fact, Disjunction]],
        theorems: List[Union[Theorem, HyperTheorem]],
        theorem_name_dict: Dict[str, Union[Theorem, HyperTheorem]],
        goal: Fact,
        config: SolverConfig | None = None,
        logger: Optional[logging.Logger] = None,
    ):
        self.ordered_fact_list: List[str] = []  # fact labels in order of appearance
        self.facts: List[Fact] = []
        self.theorems = theorems
        self.theorem_name_dict = theorem_name_dict
        self.disjunctions: List[Disjunction] = []
        self.disj_labels: Dict[DisjunctionKey, str] = {}
        self.goal = goal
        self.goal_achieved = False
        self.goal_dis_combos: List[Set[Tuple[str, int]]] = []
        self.fact_labels: Dict[str, Union[Fact, Disjunction]] = {}
        self.cur_fact_num = 0
        self.cur_letter = "A"
        self.cur_suffix = 0
        self.symbol_set: Set[str] = set()
        self.config = config or DEFAULT_CONFIG
        self.logger = logger or logging.getLogger(__name__)

        self.add_new_facts(facts)

        for fact in self.facts:
            for sym in fact.args:
                self.symbol_set.add(sym)

    def new_label(self, letter: str = "F") -> str:
        label = letter + str(self.cur_fact_num)
        self.cur_fact_num += 1
        return label

    def update_goal_achieved(self, goal_fact: Fact) -> None:
        """
        Check if the goal has been achieved across all disjunction branches.
        """
        dis_labels = {D for D, _ in set.union(*(self.goal_dis_combos))}
        disj_branch_counts = []
        for label in dis_labels:
            disjunction = cast(Disjunction, self.fact_labels[label])
            disj_branch_counts.append((label, len(disjunction.facts)))

        branch_choices = [
            [(label, i) for i in range(count)]
            for label, count in disj_branch_counts
        ]
        all_combinations = {frozenset(combo) for combo in itertools.product(*branch_choices)}

        frozen_dis_combos = {frozenset(d) for d in self.goal_dis_combos}
        for combination in all_combinations:
            if not any(proven.issubset(combination) for proven in frozen_dis_combos):
                return

        self.goal_achieved = True

    def update_useful(self, fact: Fact) -> None:
        """Mark a given fact, and all of its ancestors, as useful."""
        if fact.useful:
            return
        fact.useful = True
        for pred_lbl in fact.dependencies:
            ancestor = self.fact_labels[pred_lbl]
            if isinstance(ancestor, Fact):
                self.update_useful(ancestor)

    def _process_disjunction_subfacts(self, disjunction: Disjunction) -> None:
        """Set up dependencies and ancestors for each sub-fact of a disjunction."""
        if disjunction.label is None:
            raise ValueError("Disjunction must have a label before processing subfacts")
        for i, sub_fact in enumerate(disjunction.facts):
            sub_fact.dependencies = [disjunction.label]
            sub_fact.dis_ancestors = set(disjunction.dis_ancestors)
            sub_fact.dis_ancestors.add((disjunction.label, i))

    def add_new_facts(self, new_facts: List[Union[Fact, Disjunction]]) -> None:
        """Add new facts or disjunctions to the proof environment."""
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
                    fact.label = self.disj_labels[disj_key]
                else:
                    new_label = self.new_label(letter="D")
                    self.fact_labels[new_label] = fact
                    fact.label = new_label
                    self.disjunctions.append(fact)
                    self.disj_labels[disj_key] = new_label

                self._process_disjunction_subfacts(fact)
                self.add_new_facts(list(fact.facts))

            if fact.label is None:
                raise ValueError("Fact or disjunction missing label after insertion")
            self.ordered_fact_list.append(fact.label)

    def apply_std_thm(
        self, thm: Theorem, facts: List[Fact]
    ) -> Optional[List[Fact]]:
        """Apply a standard theorem to a list of facts."""
        if len(facts) != len(thm.facts):
            return None

        matching: Dict[str, Any] = {}
        for in_fact, thm_fact in zip(facts, thm.facts):
            if in_fact.name != thm_fact.name:
                return None
            if len(in_fact.args) != len(thm_fact.args):
                return None

            for in_arg, thm_arg in zip(in_fact.args, thm_fact.args):
                if isinstance(thm_arg, str) and thm_arg.startswith("*"):
                    if in_arg != thm_arg[1:]:
                        return None
                    continue

                if thm_arg in matching:
                    if matching[thm_arg] != in_arg:
                        return None
                else:
                    matching[thm_arg] = in_arg

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
    ) -> Optional[List[Union[Fact, Disjunction]]]:
        """Apply a theorem or hyper-theorem and add conclusions to the environment."""
        used_disjunction_facts = set.union(*[f.dis_ancestors for f in facts]) if facts else set()
        used_disjunction_dict = dict(used_disjunction_facts)
        for disj_label, branch_idx in used_disjunction_facts:
            if used_disjunction_dict[disj_label] != branch_idx:
                return None

        if isinstance(thm, Theorem):
            new_facts = self.apply_std_thm(thm, facts)
        elif isinstance(thm, HyperTheorem):
            new_facts = thm.rule(facts)

        if new_facts is None:
            return None

        new_dis_ancestors = set.union(*[fact.dis_ancestors for fact in facts]) if facts else set()
        dependency_labels: List[str] = []
        for fact in facts:
            if fact.label is None:
                raise ValueError("Fact missing label when setting dependencies")
            dependency_labels.append(fact.label)
        for new_fact in new_facts:
            new_fact.dependencies = dependency_labels
            new_fact.conc_thm = thm
            new_fact.dis_ancestors = new_dis_ancestors

        typed_new_facts = cast(List[Union[Fact, Disjunction]], new_facts)
        self.process_new_facts(typed_new_facts)
        self.add_new_facts(list(typed_new_facts))

        result: List[Union[Fact, Disjunction]] = list(typed_new_facts)
        for f in typed_new_facts:
            if isinstance(f, Disjunction):
                result.extend(f.facts)

        return result

    def process_new_facts(self, new_facts: List[Union[Fact, Disjunction]]) -> None:
        """Replace placeholder symbols (starting with ?) with fresh unique symbols."""
        sym_dict: Dict[str, str] = {}

        simple_facts: List[Fact] = []
        for fact in new_facts:
            if isinstance(fact, Fact):
                simple_facts.append(fact)
            elif isinstance(fact, Disjunction):
                simple_facts.extend(fact.facts)

        for fact in simple_facts:
            for i, sym in enumerate(fact.args):
                if sym is None:
                    raise ValueError(f"Null argument in fact: {fact}")
                if isinstance(sym, str) and sym.startswith("?"):
                    if sym not in sym_dict:
                        sym_dict[sym] = self.generate_new_symbol()
                    fact.args[i] = sym_dict[sym]

    def generate_new_symbol(self) -> str:
        """Produce a new unique symbol."""
        while True:
            suffix = "" if self.cur_suffix == 0 else str(self.cur_suffix)
            new_symbol = self.cur_letter + suffix

            if self.cur_letter == "Z":
                self.cur_letter = "A"
                self.cur_suffix += 1
            else:
                self.cur_letter = chr(ord(self.cur_letter) + 1)

            if new_symbol not in self.symbol_set:
                self.symbol_set.add(new_symbol)
                return new_symbol

    def print_relevant_facts(self) -> None:
        for fact_lbl in self.ordered_fact_list:
            fact = self.fact_labels[fact_lbl]
            if isinstance(fact, Fact) and fact.useful:
                fact.do_nice_print()

    def print_facts(self) -> None:
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
        facts_list = [f for f in facts if isinstance(f, Fact)]
        self.apply_thm(thm, facts_list)

    def exec_command(self, cmd: str) -> Optional[bool]:
        """Execute an interactive command."""
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
        """Print the derivation tree for a fact."""
        if derived_fact_labels is None:
            derived_fact_labels = set()

        fact_obj = self.fact_labels[fact_label]
        if not isinstance(fact_obj, Fact):
            return

        if fact_obj.dependencies:
            for label in fact_obj.dependencies:
                if label not in derived_fact_labels:
                    self.print_derivation(label, derived_fact_labels)

            deps_str = ", ".join(fact_obj.dependencies)
            thm_name = fact_obj.conc_thm.name if fact_obj.conc_thm else "unknown"
            print(f"Applying theorem {thm_name} to [{deps_str}] we have:")
            print(f"  {fact_obj}")
            print()
        else:
            print("By assumption we have:")
            print(f"  {fact_obj}")
            print()

        derived_fact_labels.add(fact_label)


def match_facts_to_theorem(
    thm_facts: List[Fact],
    facts: List[Fact],
    new_facts: Optional[List[Fact]] = None
) -> List[List[Fact]]:
    """
    Find all fact combinations matching a theorem's premises.
    """
    if new_facts is None:
        new_facts = facts

    cur_matches: List[List[Fact]] = [[]]
    dicts: List[Dict[str, Any]] = [{}]
    uses_new_list: List[bool] = [False]

    for premise in thm_facts:
        new_cur_matches: List[List[Fact]] = []
        new_dicts: List[Dict[str, Any]] = []
        new_uses_new_list: List[bool] = []

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

    return [match for match, uses_new in zip(cur_matches, uses_new_list) if uses_new]


def match_facts_to_template(
    template: Fact,
    facts: List[Fact],
    init_match_dict: Optional[Dict[str, Any]] = None
) -> Tuple[List[Fact], List[Dict[str, Any]]]:
    """
    Find all facts matching a template pattern.
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
            if isinstance(temp_arg, str) and temp_arg.startswith("*"):
                if temp_arg[1:] != fact_arg:
                    is_match = False
                    break
                continue

            if temp_arg not in match_dict:
                match_dict[temp_arg] = fact_arg
            elif match_dict[temp_arg] != fact_arg:
                is_match = False
                break

        if is_match:
            matches.append(fact)
            dicts.append(match_dict)

    return matches, dicts


def auto_solve(pf_envir: ProofEnvironment) -> bool:
    """
    Optimized agenda-based proof search using trigger indexing and batching.
    """
    config = pf_envir.config

    trigger_index: Dict[Tuple[str, int], List[Tuple[Any, int, List[Fact]]]] = {}

    for thm in pf_envir.theorems:
        for i, premise in enumerate(thm.facts):
            key = (premise.name, len(premise.args))
            trigger_index.setdefault(key, []).append((thm, i, thm.facts))

    work_queue: deque = deque(pf_envir.facts)
    processed_labels: Set[str] = set()

    iteration = 0
    while work_queue and iteration < config.max_iterations:
        iteration += 1
        if config.verbose:
            pf_envir.logger.info("iteration %s, queue size: %s", iteration, len(work_queue))

        if pf_envir.goal_achieved:
            if config.verbose:
                pf_envir.print_relevant_facts()
            pf_envir.logger.info("SUCCESS")
            return True

        batch: List[Fact] = []
        for _ in range(min(config.batch_size, len(work_queue))):
            if not work_queue:
                break
            fact = work_queue.popleft()
            if fact.label is None:
                continue
            if fact.label in processed_labels:
                continue

            batch.append(fact)
            processed_labels.add(fact.label)

        if not batch:
            continue

        for fact in batch:
            key = (fact.name, len(fact.args))
            triggers = trigger_index.get(key, [])

            for thm, premise_idx, premises in triggers:
                matches = _match_with_trigger(pf_envir, fact, thm, premise_idx, premises)

                for match in matches:
                    if new_facts := pf_envir.apply_thm(thm, match):
                        for item in new_facts:
                            if isinstance(item, Fact):
                                work_queue.append(item)
                            elif isinstance(item, Disjunction):
                                work_queue.extend(item.facts)

    if config.verbose:
        pf_envir.print_relevant_facts()
    pf_envir.logger.info("FAILURE")
    return False


def _match_with_trigger(
    pf_envir: ProofEnvironment,
    new_fact: Fact,
    thm: Any,
    trigger_idx: int,
    premises: List[Fact]
) -> List[List[Fact]]:
    """Try to complete a theorem match given that new_fact matches premise at trigger_idx."""
    initial_dict: Dict[str, Any] = {}
    if not _unify_facts(premises[trigger_idx], new_fact, initial_dict):
        return []

    before_premises = premises[:trigger_idx]
    after_premises = premises[trigger_idx + 1:]

    before_matches: List[List[Fact]] = [[]]
    before_dicts: List[Dict[str, Any]] = [initial_dict.copy()]

    for premise in before_premises:
        new_before_matches: List[List[Fact]] = []
        new_before_dicts: List[Dict[str, Any]] = []

        for match, dict_so_far in zip(before_matches, before_dicts):
            for candidate in pf_envir.facts:
                new_dict = dict_so_far.copy()
                if _unify_facts(premise, candidate, new_dict):
                    new_before_matches.append(match + [candidate])
                    new_before_dicts.append(new_dict)

        before_matches = new_before_matches
        before_dicts = new_before_dicts

        if not before_matches:
            return []

    complete_matches: List[List[Fact]] = []

    for before_match, dict_after_before in zip(before_matches, before_dicts):
        after_matches: List[List[Fact]] = [[]]
        after_dicts: List[Dict[str, Any]] = [dict_after_before.copy()]

        for premise in after_premises:
            new_after_matches: List[List[Fact]] = []
            new_after_dicts: List[Dict[str, Any]] = []

            for match, dict_so_far in zip(after_matches, after_dicts):
                for candidate in pf_envir.facts:
                    new_dict = dict_so_far.copy()
                    if _unify_facts(premise, candidate, new_dict):
                        new_after_matches.append(match + [candidate])
                        new_after_dicts.append(new_dict)

            after_matches = new_after_matches
            after_dicts = new_after_dicts

            if not after_matches:
                break

        for after_match in after_matches:
            complete_matches.append(before_match + [new_fact] + after_match)

    return complete_matches


def _unify_facts(template: Fact, fact: Fact, substitution_dict: Dict[str, Any]) -> bool:
    """
    Try to unify template with fact, updating substitution_dict in place.
    """
    if template.name != fact.name:
        return False
    if len(template.args) != len(fact.args):
        return False

    for t_arg, f_arg in zip(template.args, fact.args):
        if isinstance(t_arg, str) and t_arg.startswith("*"):
            if t_arg[1:] != f_arg:
                return False
        elif t_arg in substitution_dict:
            if substitution_dict[t_arg] != f_arg:
                return False
        else:
            substitution_dict[t_arg] = f_arg

    return True


# Keep compatibility with the original name
Proof_environment = ProofEnvironment
