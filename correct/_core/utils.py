import sys
import typing as t
from collections import abc

from .hints import (Annotation,
                    GenericAlias)
from .variance import Variance

if sys.version_info >= (3, 8):
    to_arguments = t.get_args
    to_origin = t.get_origin
else:
    def to_arguments(annotation: Annotation) -> t.Tuple[Annotation, ...]:
        if isinstance(annotation, GenericAlias):
            result = annotation.__args__
            if (result
                    and to_origin(annotation) is abc.Callable
                    and result[0] is not Ellipsis):
                result = (list(result[:-1]), result[-1])
            return result
        return ()


    def to_origin(annotation: Annotation) -> t.Any:
        if isinstance(annotation, GenericAlias):
            return annotation.__origin__
        elif annotation is t.Generic:
            return t.Generic
        else:
            return None


def type_repr(type_: Annotation) -> str:
    return (f'{type_.__module__}.{type_.__qualname__}'
            if isinstance(type_, type)
            else repr(type_))


def type_var_to_variance(value: t.TypeVar) -> Variance:
    assert isinstance(value, t.TypeVar), value
    assert not (value.__contravariant__ and value.__covariant__), (
        'type variables supposed to be non-bivariant'
    )
    return (Variance.CONTRAVARIANT
            if value.__contravariant__
            else (Variance.COVARIANT
                  if value.__covariant__
                  else Variance.INVARIANT))


def unpack_type_var(value: t.TypeVar) -> Annotation:
    assert isinstance(value, t.TypeVar), value
    if value.__bound__:
        return value.__bound__
    elif value.__constraints__:
        return t.Union[value.__constraints__]
    else:
        return t.Any
