from typing import Any, List

from .facts import Fact


class Theorem:
    """Represents a standard logical theorem with premises and conclusions."""

    __slots__ = ("facts", "conclusions", "name", "compiled_patterns")

    def __init__(self, facts: List[Fact], conclusions: List[Fact], name: str):
        self.facts = facts
        self.conclusions = conclusions
        self.name = name
        # Precompile argument patterns for faster matching
        self.compiled_patterns = [
            [_compile_arg(arg) for arg in fact.args] for fact in facts
        ]

    def __repr__(self) -> str:
        return f"Theorem({self.name!r})"


class HyperTheorem:
    """Represents a computational theorem with a rule function."""

    __slots__ = ("facts", "rule", "name", "multi_args")

    def __init__(self, facts: List[Fact], rule: Any, name: str):
        self.facts = facts
        self.rule = rule
        self.name = name
        self.multi_args = False

    def __repr__(self) -> str:
        return f"HyperTheorem({self.name!r})"


def _compile_arg(arg: Any) -> tuple[str, Any]:
    if isinstance(arg, str) and arg.startswith("*"):
        return ("star", arg[1:])
    return ("var", arg)
