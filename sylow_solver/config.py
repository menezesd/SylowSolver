from dataclasses import dataclass


@dataclass(frozen=True)
class SolverConfig:
    """Configuration options for the proof search."""

    max_iterations: int = 1000
    batch_size: int = 8
    default_label: str = "F0"
    verbose: bool = False


DEFAULT_CONFIG = SolverConfig()
