import enum


class Variance(enum.IntEnum):
    CONTRAVARIANT = enum.auto()
    COVARIANT = enum.auto()
    INVARIANT = enum.auto()
