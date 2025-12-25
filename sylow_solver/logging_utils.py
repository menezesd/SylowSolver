import logging


def get_logger(name: str = "sylow_solver", level: int = logging.INFO) -> logging.Logger:
    """Return a configured logger with a simple stderr handler."""
    logger = logging.getLogger(name)
    if not logger.handlers:
        handler = logging.StreamHandler()
        formatter = logging.Formatter("%(levelname)s:%(name)s:%(message)s")
        handler.setFormatter(formatter)
        logger.addHandler(handler)
    logger.setLevel(level)
    return logger


def configure_root_logger(level: int = logging.INFO) -> logging.Logger:
    """Configure the root logger if it has no handlers and return it."""
    root = logging.getLogger()
    if not root.handlers:
        handler = logging.StreamHandler()
        formatter = logging.Formatter("%(levelname)s:%(name)s:%(message)s")
        handler.setFormatter(formatter)
        root.addHandler(handler)
    root.setLevel(level)
    return root
