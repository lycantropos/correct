from ._core.hints import Annotation as _Annotation
from ._core.predicates import is_subtype as _is_subtype
from ._core.variance import Variance as _Variance


def is_subtype(left: _Annotation, right: _Annotation) -> bool:
    """
    Checks if annotation is a subtype of another.

    >>> is_subtype(int, int)
    True
    >>> is_subtype(bool, int)  # types are considered invariant by default
    False
    >>> from typing import TypeVar
    >>> CovariantInt = TypeVar('CovariantInt', bound=int, covariant=True)
    >>> is_subtype(bool, CovariantInt)
    True
    >>> is_subtype(int, bool)
    False
    >>> ContravariantBool = TypeVar('ContravariantBool', bound=bool,
    ...                             contravariant=True)
    >>> is_subtype(int, ContravariantBool)
    True
    """
    return _is_subtype(_Variance.INVARIANT, _Variance.INVARIANT, left, right)
