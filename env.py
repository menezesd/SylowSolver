"""Proof environment implementation.

This module provides the ProofEnvironment class which depends on the
data-model classes defined in `core.py`.
"""

import itertools
from core import Fact, Disjunction, Theorem, HyperTheorem


class ProofEnvironment:
    """Proof environment maintaining facts, theorems, and search state."""

    def __init__(self, facts, theorems, theorem_name_dict, goal):
        # Optional path to write structured JSON-lines diagnostics for
        # update_goal_achieved. If None, diagnostics are printed to stdout
        # as before. This is used during parity debugging to produce
        # machine-readable dumps that avoid huge stdout logs.
        self.diagnostic_json_path = None

        self.ordered_fact_list = []
        self.facts = []
        self.theorems = theorems
        self.theorem_name_dict = theorem_name_dict
        self.disjunctions = []

        self.goal = goal
        self.goal_achieved = False
        self.goal_dis_combos = []

        self.fact_labels = {}
        self.cur_fact_num = 0
        # initialize attributes used for generating new symbol names
        # set sensible defaults so generate_new_symbol can always run
        self.cur_letter = "A"
        self.cur_suffix = 0
        self.case_depth = 0
        self.num_cases = 0
        self.solved_cases = 0
        self.case_dis = None
        self.case_fact = None

        self.add_new_facts(facts)
        self.symbol_set = set()

        for fact in self.facts:
            for sym in fact.args:
                self.symbol_set.add(sym)

    def new_label(self, letter="F"):
        label = letter + str(self.cur_fact_num)
        self.cur_fact_num += 1
        return label

    def _canonical_disjunction_signature(self, disj):
        # Build a canonical string for the disjunction: sort alternative
        # fact signatures (name + args) to avoid depending on insertion order.
        sigs = []
        for f in disj.facts:
            try:
                args = ",".join(map(str, f.args))
            except (TypeError, AttributeError):
                args = ""
            sigs.append(f.name + ":" + args)
        sigs.sort()
        # Include provenance to disambiguate distinct instances that may
        # have identical alternative signatures: include the concluding
        # theorem name (if present) and a sorted list of immediate
        # ancestor disjunction labels (so two identical-looking disjunctions
        # produced by different contexts differ).
        prov = []
        try:
            thm = getattr(disj, "conc_thm", None)
            if thm is not None:
                # thm may be an object or a string; handle both
                thm_name = getattr(thm, "name", None) or str(thm)
                prov.append("thm:" + thm_name)
        except AttributeError:
            pass
        try:
            anc = getattr(disj, "dis_ancestors", None)
            if anc:
                # anc is a set of (label,idx) tuples
                anc_labels = sorted({a for (a, _) in anc})
                prov.append("anc:" + ",".join(map(str, anc_labels)))
        except AttributeError:
            pass

        if prov:
            return "|".join(sigs) + "::" + "|".join(prov)
        return "|".join(sigs)

    def new_disjunction_label(self, disj, prefix="D"):
        # Deterministically derive a numeric-ish label from the canonical
        # signature so both Python and Haskell produce the same label for
        # logically identical disjunctions regardless of registration order.
        import hashlib

        canon = self._canonical_disjunction_signature(disj)
        h = hashlib.sha1(canon.encode("utf-8")).hexdigest()
        # Take first 10 hex chars -> integer, reduce to 6 digits for brevity
        num = int(h[:10], 16) % 1000000
        label = prefix + str(num)

        # Ensure uniqueness within current environment; if collision with
        # a different disjunction signature, perturb deterministically.
        probe = 0
        while label in self.fact_labels:
            # If the existing label maps to a disjunction with identical
            # signature, reuse it. Otherwise, perturb by incrementing probe.
            existing = self.fact_labels.get(label)
            # existing for disjunctions stored in fact_labels may be a Fact
            # -- for disjunction labels we expect them to be stored too. If
            # the existing entry isn't a Disjunction or signatures differ,
            # continue probing.
            try:
                if hasattr(existing, "facts"):
                    if self._canonical_disjunction_signature(existing) == canon:
                        return label
            except AttributeError:
                pass
            probe += 1
            label = prefix + str((num + probe) % 1000000)

        return label

    def update_goal_achieved(self, _goal_fact):

        # Reconstruct the set of disjunction labels referenced by observed
        # goal-disjunction combos and compute the Cartesian product of their
        # alternatives. Then check whether every full assignment is implied
        # by at least one observed goal combo. Instrumentation below helps
        # diagnose cases where the Python and Haskell runs differ.
        if not self.goal_dis_combos:
            return

        full_dis_set = set(D for D, i in set.union(*(self.goal_dis_combos)))

        dis_labels = set(D for D in full_dis_set)  # prevent duplicates
        L = [(D, len(self.fact_labels[D].facts)) for D in dis_labels]
        X = []
        for D, l in L:
            X.append([(D, i) for i in range(0, l)])
        S = list(itertools.product(*X))
        S = set(frozenset(u) for u in S)

        frozen_dis_combos = set(frozenset(d) for d in self.goal_dis_combos)

        # When requested, write structured JSON-lines diagnostics instead of
        # printing large DEBUG blobs to stdout.

        # For richer diagnostics: for each full assignment, list which observed
        # goal combos cover it, and for each covering observed combo list the
        # concrete producer signatures (fact name and args) so we can do a
        # label-agnostic comparison with the Haskell run.
        combo_coverings = []  # list of (full_combo, [covering_observed_combos])
        for s in S:
            covered_by = []
            for dtuple in frozen_dis_combos:
                if dtuple.issubset(s):
                    covered_by.append(dtuple)
            combo_coverings.append((s, covered_by))

        # Emit either pretty stdout debug lines (legacy) or a structured
        # JSON-lines file (recommended for automated diffs).
        if self.diagnostic_json_path:
            import json

            try:
                with open(self.diagnostic_json_path, "a", encoding="utf-8") as fh:
                    # Build disjunction signatures: for each D label include
                    # a list of alternative fact signatures (name, args) and
                    # the canonical signature string used to derive the D label.
                    # The canonical string includes provenance (concluding theorem
                    # and disjunction ancestors) and is useful for label-agnostic
                    # comparison between Python and Haskell runs.
                    disjunction_signatures = []
                    for D, l in L:
                        sigs = []
                        canon = None
                        if D in self.fact_labels:
                            # collect alternative fact signatures
                            for f in self.fact_labels[D].facts:
                                try:
                                    sigs.append((f.name, list(f.args)))
                                except (AttributeError, TypeError):
                                    sigs.append((f.name, []))
                            # also compute canonical signature string from the
                            # Disjunction object so downstream tools can match on it
                            try:
                                disj_obj = self.fact_labels[D]
                                canon = self._canonical_disjunction_signature(disj_obj)
                            except (KeyError, AttributeError, TypeError):
                                canon = None
                        disjunction_signatures.append([D, sigs, canon])

                    # Emit goal_dis_combos in a deterministic order: sort each combo
                    # (list of (label,idx)) and then sort the list of combos by their
                    # JSON representation so order does not depend on discovery timing.
                    goal_combos_sorted = [sorted(list(d)) for d in frozen_dis_combos]
                    try:
                        goal_combos_sorted = sorted(goal_combos_sorted, key=json.dumps)
                    except (TypeError, ValueError):
                        # If sorting fails, leave the list in its current order.
                        pass
                    header = {
                        "goal_dis_combos": goal_combos_sorted,
                        "disjunctionSizes": L,
                        "disjunctionSignatures": disjunction_signatures,
                        "allPossibleCombos": len(S),
                    }
                    fh.write(json.dumps({"type": "header", "data": header}) + "\n")
                    for idx, (full_combo, covered_by) in enumerate(combo_coverings):
                        entry = {
                            "full_combo": sorted(list(full_combo)),
                            "covered_by": [[sorted(list(x)) for x in covered_by]],
                            "producers": [],
                        }
                        # collect producers for each covering observed combo
                        for cov in covered_by:
                            producers = []
                            for dlabel, i in cov:
                                if dlabel in self.fact_labels and i < len(
                                    self.fact_labels[dlabel].facts
                                ):
                                    f = self.fact_labels[dlabel].facts[i]
                                    producers.append((f.name, tuple(f.args)))
                                else:
                                    producers.append((None, None))
                            entry["producers"].append(producers)
                        fh.write(
                            json.dumps({"type": "combo", "index": idx, "data": entry})
                            + "\n"
                        )
            except (OSError, IOError, TypeError):
                # Fall back to stdout prints if file write fails
                pass
        else:
            try:
                # Print first 200 combos to avoid enormous logs in pathological cases
                for idx, (full_combo, covered_by) in enumerate(combo_coverings):
                    if idx >= 200:
                        break
                    # print(f"fullCombo #{idx}: {sorted(list(full_combo))}")
                    # print(f"coveredBy: { [sorted(list(x)) for x in covered_by] }")
                    # For each covering observed combo, print its producers (fact label -> (name,args))
                    for cov in covered_by:
                        producers = []
                        for dlabel, i in cov:
                            if dlabel in self.fact_labels and i < len(
                                self.fact_labels[dlabel].facts
                            ):
                                f = self.fact_labels[dlabel].facts[i]
                                producers.append((dlabel, f.name, tuple(f.args)))
                            else:
                                producers.append((dlabel, None, None))
                        # print(f"producers for {sorted(list(cov))} -> {producers}")
            except OSError:
                pass

        # Now decide if all full combos are covered
        for full_combo, covered_by in combo_coverings:
            if not covered_by:
                print("DEBUG allCovered = False")
                return

        print("DEBUG allCovered = True")
        self.goal_achieved = True

    def update_useful(self, fact):
        if fact.useful:
            return
        fact.useful = True
        for pred_lbl in fact.dependencies:
            self.update_useful(self.fact_labels[pred_lbl])

    def add_new_facts(self, new_facts):
        for fact in new_facts:

            if isinstance(fact, Fact):
                new_label = self.new_label()
                self.fact_labels[new_label] = fact
                fact.label = new_label

                self.facts.append(fact)
                if fact.equals(self.goal):
                    self.goal_dis_combos.append(fact.dis_ancestors)
                    # Print signature-mapped ancestors for parity with Haskell
                    try:
                        sigs = []
                        for dlabel, idx in fact.dis_ancestors:
                            if dlabel in self.fact_labels and idx < len(
                                self.fact_labels[dlabel].facts
                            ):
                                f = self.fact_labels[dlabel].facts[idx]
                                sigs.append(((dlabel, idx), (f.name, tuple(f.args))))
                            else:
                                sigs.append(((dlabel, idx), None))
                    except (KeyError, IndexError, AttributeError):
                        sigs = []
                    self.update_goal_achieved(fact)
                    self.update_useful(fact)

            if isinstance(fact, Disjunction):
                # Use deterministic disjunction labels derived from canonical signature
                new_label = self.new_disjunction_label(fact, prefix="D")
                self.fact_labels[new_label] = fact
                fact.label = new_label
                self.disjunctions.append(fact)

                for i in range(0, len(fact.facts)):
                    sub_fact = fact.facts[i]
                    sub_fact.dependencies = [fact.label]
                    sub_fact.dis_ancestors = set(fact.dis_ancestors)
                    sub_fact.dis_ancestors.add((fact.label, i))

                self.add_new_facts(fact.facts)

            self.ordered_fact_list.append(new_label)

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

                if thm_arg[0] == "*":
                    if in_arg != thm_arg[1:]:
                        print("exact match expected")
                        valid = False
                    continue

                if thm_arg in matching:
                    if matching[thm_arg] != in_arg:
                        valid = False
                else:
                    matching[thm_arg] = in_arg

        if not valid:
            return False

        conclusions = []
        for conc in thm.conclusions:
            new_fact_args = []
            for x in conc.args:
                if x[0] != "?":
                    new_fact_args.append(matching[x])
                else:
                    new_fact_args.append(x)

            new_fact = Fact(conc.name, new_fact_args)
            conclusions.append(new_fact)

        return conclusions

    def apply_thm(self, thm, facts):
        new_facts = None
        used_disjunction_facts = set.union(*[f.dis_ancestors for f in facts])
        used_disjunction_dict = dict(used_disjunction_facts)
        valid = True
        for d, i in used_disjunction_facts:
            if used_disjunction_dict[d] != i:
                valid = False
        if not valid:
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
            new_fact.dependencies = dependency_labels
            new_fact.conc_thm = thm
            new_fact.dis_ancestors = new_dis_ancestors

        self.process_new_facts(new_facts)
        self.add_new_facts(new_facts)

        for f in list(new_facts):
            if isinstance(f, Disjunction):
                new_facts += f.facts

        return new_facts

    def process_new_facts(self, new_facts):
        sym_dict = {}

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
                    if sym not in sym_dict:
                        new_symbol = self.generate_new_symbol()
                        sym_dict[sym] = new_symbol
                    args[i] = sym_dict[sym]

    def generate_new_symbol(self):
        try:
            while True:
                cur_suffix = self.cur_suffix
                suffix = ""
                if cur_suffix != 0:
                    suffix = str(cur_suffix)
                new_symbol = self.cur_letter + suffix
                if self.cur_letter == "Z":
                    self.cur_letter = "A"
                    self.cur_suffix += 1
                else:
                    self.cur_letter = chr(ord(self.cur_letter) + 1)
                if new_symbol not in self.symbol_set:
                    if new_symbol is None:
                        print("error: returning None")
                    return new_symbol
        except AttributeError:
            self.cur_letter = "A"
            self.cur_suffix = 0
            return self.generate_new_symbol()

    def start_cases(self, dis):
        self.num_cases = len(dis.facts)
        self.solved_cases = 0
        self.case_depth += 1
        self.case_dis = dis
        self.case_fact = (dis.facts[self.solved_cases]).copy()
        self.add_new_facts([self.case_fact])

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

    def remove_facts_by_depth(self, D):
        fact_labels = self.fact_labels
        for lbl in dict(fact_labels):
            fact = fact_labels[lbl]
            if fact.depth == D:
                self.remove_fact(lbl)

    def remove_fact(self, lbl):
        fact = self.fact_labels[lbl]
        self.facts.remove(fact)
        del self.fact_labels[lbl]

    def print_derivation(self, fact_label, derived_fact_labels=None):
        if derived_fact_labels is None:
            derived_fact_labels = set()

        fact = self.fact_labels[fact_label]
        if fact.dependencies != []:
            thm = fact.conc_thm
            thm_name = thm.name

            for label in fact.dependencies:
                if label not in derived_fact_labels:
                    self.print_derivation(label, derived_fact_labels)

            print(
                "Applying theorem ", thm_name, " to ", fact.dependencies, " we have: "
            )
            fact.do_print()
            print()

            derived_fact_labels.add(fact_label)

        else:
            print("By assumption we have: ")
            fact.do_print()
            print()
            derived_fact_labels.add(fact_label)

    def print_relevant_facts(self):
        for fact_lbl in self.ordered_fact_list:
            fact = self.fact_labels[fact_lbl]
            if fact.useful:
                fact.do_nice_print()

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
            thm_args = cmd_args[1:]
            in_facts = [self.fact_labels[lbl] for lbl in thm_args]
            self.apply_thm(thm, in_facts)
            return

        if cmd_name == "cases":
            print("DEPRECATED")
            return

        if cmd_name == "conclude":
            print("DEPRECATED")
            return

        if cmd_name == "display":
            self.print_facts()
            return

        if cmd_name == "exit":
            return False

        print("Unkown Command")


# Backwards compatible alias
Proof_environment = ProofEnvironment
