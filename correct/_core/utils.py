import sys
import typing as t
from collections import abc

from .hints import (Annotation,
                    GenericAlias)

if sys.version_info >= (3, 8):
    to_arguments = t.get_args
    to_origin = t.get_origin
else:
    def to_arguments(annotation: Annotation) -> t.Tuple[Annotation, ...]:
        if isinstance(annotation, GenericAlias):
            result = annotation.__args__
            if (to_origin(annotation) is abc.Callable
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


def unpack_type_var(annotation: t.TypeVar) -> Annotation:
    assert isinstance(annotation, t.TypeVar), annotation
    if annotation.__bound__:
        return annotation.__bound__
    elif annotation.__constraints__:
        return t.Union[annotation.__constraints__]
    else:
        return t.Any
