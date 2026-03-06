from __future__ import annotations

import itertools
import logging
from collections import deque
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple, Union, cast

from .config import DEFAULT_CONFIG, OutputMode, SolverConfig
from .facts import Disjunction, DisjunctionKey, Fact
from .proof_tree import DisjMeta, infer_disj_meta, render_clean, render_tree
from .substitution import Substitution
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
        self.facts_by_key: Dict[Tuple[str, int], List[Fact]] = {}
        self.theorems = theorems
        self.theorem_name_dict = theorem_name_dict
        self.disjunctions: List[Disjunction] = []
        self.disj_labels: Dict[DisjunctionKey, str] = {}
        self.goal = goal
        self.goal_achieved = False
        self.goal_dis_combos: List[FrozenSet[Tuple[str, int]]] = []
        self.goal_dis_combo_set: Set[FrozenSet[Tuple[str, int]]] = set()
        self.fact_labels: Dict[str, Union[Fact, Disjunction]] = {}
        self.disj_meta: Dict[str, DisjMeta] = {}
        self.disj_branch_counts: Dict[str, int] = {}
        self._combo_cache: Dict[Tuple[Tuple[str, int], ...], Set[FrozenSet[Tuple[str, int]]]] = {}
        self.cur_fact_num = 0
        self.cur_letter = "A"
        self.cur_suffix = 0
        self.symbol_set: Set[str] = set()
        self.symbol_queue: List[str] = []
        self.config = config or DEFAULT_CONFIG
        self.logger = logger or logging.getLogger(__name__)

        self.add_new_facts(facts)

        for fact in self.facts:
            for sym in fact.args:
                self.symbol_set.add(sym)
            self._index_fact(fact)

    def new_label(self, letter: str = "F") -> str:
        label = letter + str(self.cur_fact_num)
        self.cur_fact_num += 1
        return label

    def update_goal_achieved(self, goal_fact: Fact) -> None:
        """
        Check if the goal has been achieved across all disjunction branches.
        """
        if self.goal_achieved:
            return
        if not self.goal_dis_combos:
            return
        dis_labels = {label for combo in self.goal_dis_combos for label, _ in combo}
        if not dis_labels:
            self.goal_achieved = True
            return

        disj_branch_counts: List[Tuple[str, int]] = []
        for label in dis_labels:
            count = self.disj_branch_counts.get(label)
            if count is None:
                disjunction = cast(Disjunction, self.fact_labels[label])
                count = len(disjunction.facts)
                self.disj_branch_counts[label] = count
            disj_branch_counts.append((label, count))
        disj_branch_counts.sort(key=lambda pair: pair[0])

        cache_key = tuple(disj_branch_counts)
        all_combinations = self._combo_cache.get(cache_key)
        if all_combinations is None:
            branch_choices = [[(label, i) for i in range(count)] for label, count in disj_branch_counts]
            all_combinations = {frozenset(combo) for combo in itertools.product(*branch_choices)}
            self._combo_cache[cache_key] = all_combinations
        for combination in all_combinations:
            if not any(proven.issubset(combination) for proven in self.goal_dis_combo_set):
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
                self._index_fact(fact)
                for sym in fact.args:
                    if isinstance(sym, str):
                        self.symbol_set.add(sym)

                if fact == self.goal:
                    combo = frozenset(fact.dis_ancestors)
                    if combo not in self.goal_dis_combo_set:
                        self.goal_dis_combo_set.add(combo)
                        self.goal_dis_combos.append(combo)
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
                    self.disj_meta[new_label] = infer_disj_meta(fact)
                    self.disj_branch_counts[new_label] = len(fact.facts)

                self._process_disjunction_subfacts(fact)
                self.add_new_facts(list(fact.facts))

            if fact.label is None:
                raise ValueError("Fact or disjunction missing label after insertion")
            self.ordered_fact_list.append(fact.label)

    def _index_fact(self, fact: Fact) -> None:
        key = (fact.name, len(fact.args))
        self.facts_by_key.setdefault(key, []).append(fact)

    def apply_std_thm(self, thm: Theorem, facts: List[Fact]) -> Optional[List[Fact]]:
        """Apply a standard theorem to a list of facts."""
        if len(facts) != len(thm.facts):
            return None

        matching = Substitution.empty()
        for in_fact, thm_fact in zip(facts, thm.facts):
            if not _unify_facts(thm_fact, in_fact, matching):
                return None

        conclusions = []
        for conc in thm.conclusions:
            new_fact_args = [_substitute_arg(arg, matching) for arg in conc.args]
            conclusions.append(Fact(conc.name, new_fact_args))

        return conclusions

    def apply_thm(
        self, thm: Union[Theorem, HyperTheorem], facts: List[Fact]
    ) -> Optional[List[Union[Fact, Disjunction]]]:
        """Apply a theorem or hyper-theorem and add conclusions to the environment."""
        used_disjunction_facts = set.union(*[f.dis_ancestors for f in facts]) if facts else set()
        if len(used_disjunction_facts) != len({d for d, _ in used_disjunction_facts}):
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
        if not self.symbol_queue:
            self.symbol_queue = self._batch_generate_symbols(64)
        new_symbol = self.symbol_queue.pop()
        self.symbol_set.add(new_symbol)
        return new_symbol

    def _batch_generate_symbols(self, count: int) -> List[str]:
        """Precompute a batch of symbols to reduce loop overhead."""
        generated: List[str] = []
        while len(generated) < count:
            suffix = "" if self.cur_suffix == 0 else str(self.cur_suffix)
            candidate = self.cur_letter + suffix

            if self.cur_letter == "Z":
                self.cur_letter = "A"
                self.cur_suffix += 1
            else:
                self.cur_letter = chr(ord(self.cur_letter) + 1)

            if candidate in self.symbol_set:
                continue
            generated.append(candidate)
        generated.reverse()
        return generated

    def print_relevant_facts(self) -> None:
        for fact_lbl in self.ordered_fact_list:
            fact = self.fact_labels[fact_lbl]
            if isinstance(fact, Fact) and fact.useful:
                fact.do_nice_print()

    def render_proof(self) -> List[str]:
        """Render proof based on configured output mode."""
        mode = self.config.output_mode
        if mode == OutputMode.CLASSIC:
            lines = []
            for fact_lbl in self.ordered_fact_list:
                fact = self.fact_labels[fact_lbl]
                if isinstance(fact, Fact) and fact.useful:
                    lines.append(str(fact))
            return lines
        elif mode == OutputMode.TREE:
            return render_tree(self.facts, self.disjunctions, self.disj_meta)
        else:  # CLEAN
            return render_clean(self.facts, self.disjunctions, self.disj_meta)

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
    thm_facts: List[Fact], facts: List[Fact], new_facts: Optional[List[Fact]] = None
) -> List[List[Fact]]:
    """
    Find all fact combinations matching a theorem's premises.
    """
    if new_facts is None:
        new_facts = facts

    cur_matches: List[List[Fact]] = [[]]
    dicts: List[Substitution] = [Substitution.empty()]
    uses_new_list: List[bool] = [False]

    for premise in thm_facts:
        new_cur_matches: List[List[Fact]] = []
        new_dicts: List[Substitution] = []
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
    template: Fact, facts: List[Fact], init_match_dict: Optional[Substitution] = None
) -> Tuple[List[Fact], List[Substitution]]:
    """
    Find all facts matching a template pattern.
    """
    init_match_dict = init_match_dict or Substitution.empty()
    matches: List[Fact] = []
    dicts: List[Substitution] = []

    for fact in facts:
        match_dict = init_match_dict.copy()
        if _unify_facts(template, fact, match_dict):
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
            for line in pf_envir.render_proof():
                print(line)
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

    for line in pf_envir.render_proof():
        print(line)
    pf_envir.logger.info("FAILURE")
    return False


def _match_with_trigger(
    pf_envir: ProofEnvironment, new_fact: Fact, thm: Any, trigger_idx: int, premises: List[Fact]
) -> List[List[Fact]]:
    """Try to complete a theorem match given that new_fact matches premise at trigger_idx."""
    initial_dict = Substitution.empty()
    if not _unify_facts(premises[trigger_idx], new_fact, initial_dict):
        return []

    before_premises = premises[:trigger_idx]
    after_premises = premises[trigger_idx + 1 :]

    before_matches: List[List[Fact]] = [[]]
    before_dicts: List[Substitution] = [initial_dict.copy()]

    for premise in before_premises:
        new_before_matches: List[List[Fact]] = []
        new_before_dicts: List[Substitution] = []

        for match, dict_so_far in zip(before_matches, before_dicts):
            for candidate in pf_envir.facts_by_key.get((premise.name, len(premise.args)), []):
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
        after_dicts: List[Substitution] = [dict_after_before.copy()]

        for premise in after_premises:
            new_after_matches: List[List[Fact]] = []
            new_after_dicts: List[Substitution] = []

            for match, dict_so_far in zip(after_matches, after_dicts):
                for candidate in pf_envir.facts_by_key.get((premise.name, len(premise.args)), []):
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


def _substitute_arg(arg: Any, substitution: Substitution) -> Any:
    """Apply a theorem substitution to one argument."""
    if isinstance(arg, str) and arg.startswith("?"):
        return arg
    if isinstance(arg, str) and arg in substitution:
        return substitution[arg]
    return arg


def _unify_facts(template: Fact, fact: Fact, substitution: Substitution) -> bool:
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
        elif t_arg in substitution:
            if substitution[t_arg] != f_arg:
                return False
        else:
            substitution.insert(t_arg, f_arg)

    return True


# Keep compatibility with the original name
Proof_environment = ProofEnvironment
