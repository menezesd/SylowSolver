from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, List, Optional, Set, Tuple


@dataclass(eq=False)
class Fact:
    """Represents a logical fact used by the solver."""

    name: str
    args: List[Any]
    dependencies: List[str] = field(default_factory=list)
    label: Optional[str] = None
    dis_ancestors: Set[Tuple[str, int]] = field(default_factory=set)
    conc_thm: Optional[Any] = None  # Type is Theorem/HyperTheorem but avoid circular import
    useful: bool = False

    def __str__(self) -> str:
        return (
            f"{self.label} : {self.name} {self.args} :: "
            f"{self.dependencies} :: {self.dis_ancestors}"
        )

    def __repr__(self) -> str:
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
        if not isinstance(other, Fact):
            return NotImplemented
        return self.name == other.name and self.args == other.args

    def __hash__(self) -> int:
        return hash((self.name, tuple(self.args)))

    # Legacy helpers kept for compatibility
    def do_print(self) -> None:
        print(self)

    def do_nice_print(self) -> None:
        self.print_nice()

    def equals(self, fact: "Fact") -> bool:
        return self == fact


@dataclass(frozen=True)
class DisjunctionKey:
    """Immutable structural key for efficient disjunction deduplication."""

    facts_tuple: Tuple[Tuple[str, Tuple[Any, ...]], ...]
    ancestors_tuple: Tuple[Tuple[str, int], ...]
    conc_thm: Optional[str]

    @staticmethod
    def from_disjunction(
        facts: List[Fact], dis_ancestors: Set[Tuple[str, int]], conc_thm: Optional[Any] = None
    ) -> "DisjunctionKey":
        sorted_facts = tuple(sorted((f.name, tuple(f.args)) for f in facts))
        sorted_ancestors = tuple(sorted(dis_ancestors)) if dis_ancestors else ()
        thm_name = conc_thm.name if conc_thm and hasattr(conc_thm, "name") else None
        return DisjunctionKey(sorted_facts, sorted_ancestors, thm_name)


class Disjunction:
    """Represents a disjunction of facts for case-based reasoning."""

    __slots__ = ("facts", "dependencies", "dis_ancestors", "label", "conc_thm", "useful")

    def __init__(
        self,
        facts: List[Fact],
        dependencies: Optional[List[str]] = None,
        label: Optional[str] = None,
        dis_ancestors: Optional[List[Any]] = None,
        conc_thm: Optional[Any] = None,
    ):
        self.facts = facts
        self.dependencies = dependencies if dependencies is not None else []
        self.dis_ancestors: Set[Tuple[str, int]] = set(dis_ancestors or [])
        self.label = label
        self.conc_thm = conc_thm
        self.useful = False

    def __repr__(self) -> str:
        fact_reprs = " OR ".join(repr(f) for f in self.facts)
        return f"Disjunction([{fact_reprs}])"

    def get_key(self) -> DisjunctionKey:
        return DisjunctionKey.from_disjunction(self.facts, self.dis_ancestors, self.conc_thm)

    def do_print(self) -> None:
        print(self.label, ":")
        for i, fact in enumerate(self.facts):
            fact.do_print()
            if i != len(self.facts) - 1:
                print("    OR")

    def do_nice_print(self) -> None:
        print(self.label, ":")
        for i, fact in enumerate(self.facts):
            fact.do_print()
            if i != len(self.facts) - 1:
                print("    OR")
        if self.conc_thm is not None:
            print("    by thm ", self.conc_thm.name, " applied to facts ", *self.dependencies)
        else:
            print("    by hypothesis")
        if self.dis_ancestors:
            print("    Disjunctions in history: ", *self.dis_ancestors)
        print()
