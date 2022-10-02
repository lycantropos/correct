import sys
import typing as t
from collections import abc
from functools import singledispatch

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


@singledispatch
def annotation_repr(value: Annotation) -> str:
    return repr(value)


@annotation_repr.register(type)
def _(value: type) -> str:
    return f'{value.__module__}.{value.__qualname__}'


@annotation_repr.register(GenericAlias)
def _(value: GenericAlias) -> str:
    arguments = to_arguments(value)
    return ((f'{value.__module__}.{value._name}'
             f'[{", ".join(map(annotation_repr, arguments))}]')
            if arguments
            else f'{value.__module__}.{value._name}')


@annotation_repr.register(t.TypeVar)
def _(value: t.TypeVar) -> str:
    arguments = [repr(value.__name__)]
    arguments.extend(map(annotation_repr, value.__constraints__))
    if value.__bound__ is not None:
        arguments.append(f'bound={annotation_repr(value.__bound__)}')
    if value.__contravariant__:
        arguments.append('contravariant=True')
    if value.__covariant__:
        arguments.append('covariant=True')
    return f'{type(value).__qualname__}({", ".join(arguments)})'


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
