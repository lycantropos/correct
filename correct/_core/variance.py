from __future__ import annotations

import enum
import typing as t

auto: t.Callable[[], t.Any] = enum.auto


class Variance(enum.IntEnum):
    CONTRAVARIANT: Variance = auto()
    COVARIANT: Variance = auto()
    INVARIANT: Variance = auto()

    def __invert__(self) -> Variance:
        if self is self.COVARIANT:
            return self.CONTRAVARIANT
        elif self is self.CONTRAVARIANT:
            return self.COVARIANT
        else:
            assert self is self.INVARIANT
            return self
