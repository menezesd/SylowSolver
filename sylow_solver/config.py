from dataclasses import dataclass
from enum import Enum, auto


class OutputMode(Enum):
    """Output mode for proof display."""

    CLASSIC = auto()  # Original verbose output
    CLEAN = auto()  # Cleaner formatting with case labels
    TREE = auto()  # Tree visualization


@dataclass(frozen=True)
class SolverConfig:
    """Configuration options for the proof search."""

    max_iterations: int = 1000
    batch_size: int = 8
    default_label: str = "F0"
    verbose: bool = False
    output_mode: OutputMode = OutputMode.CLEAN


DEFAULT_CONFIG = SolverConfig()
