"""Shared helper for the verification scripts."""


def require(condition: bool, detail=None) -> None:
    """Fail loudly if a check does not hold.  Unlike `assert`, this is not removed by `python -O`."""
    if not condition:
        raise AssertionError(detail)
