from __future__ import annotations

from typing import Any, Dict, Iterable, Tuple


class Substitution:
    """Lightweight wrapper around a mapping used during unification."""

    __slots__ = ("_mapping",)

    def __init__(self, initial: Iterable[Tuple[str, Any]] | None = None):
        self._mapping: Dict[str, Any] = dict(initial or {})

    @classmethod
    def empty(cls) -> "Substitution":
        return cls()

    @classmethod
    def singleton(cls, name: str, value: Any) -> "Substitution":
        return cls([(name, value)])

    def copy(self) -> "Substitution":
        return Substitution(self._mapping.items())

    def lookup(self, name: str) -> Any | None:
        return self._mapping.get(name)

    def insert(self, name: str, value: Any) -> None:
        self._mapping[name] = value

    def items(self) -> Iterable[Tuple[str, Any]]:
        return self._mapping.items()

    def __contains__(self, name: str) -> bool:
        return name in self._mapping

    def __getitem__(self, name: str) -> Any:
        return self._mapping[name]

    def __len__(self) -> int:
        return len(self._mapping)

    def __repr__(self) -> str:
        return f"Substitution({self._mapping!r})"
