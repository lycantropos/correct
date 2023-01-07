import sys
import typing as t
from functools import singledispatch

import typing_extensions as te

from .hints import (Annotation,
                    LegacySpecialization,
                    Specialization)
from .variance import Variance

if sys.version_info < (3, 11):
    def to_arguments(annotation: Annotation) -> t.Tuple[Annotation, ...]:
        return (()
                if annotation == t.Tuple[()]
                else te.get_args(annotation))
else:
    to_arguments = te.get_args

to_base = te.get_origin


@singledispatch
def annotation_repr(value: Annotation) -> str:
    return repr(value)


@annotation_repr.register(type)
def _(value: type) -> str:
    return f'{value.__module__}.{value.__qualname__}'


@annotation_repr.register(LegacySpecialization)
@annotation_repr.register(Specialization)
def _(value: t.Union[LegacySpecialization, Specialization]) -> str:
    origin = to_base(value)
    arguments = to_arguments(value)
    assert value._name is not None or origin is t.Union, value
    return (((f'{annotation_repr(t.Optional)}'
              f'[{annotation_repr(arguments[arguments[0] is type(None)])}]')
             if len(arguments) == 2 and type(None) in arguments
             else (f'{annotation_repr(origin)}'
                   f'[{", ".join(map(annotation_repr, arguments))}]'))
            if origin is t.Union
            else ((f'{value.__module__}.{value._name}'
                   f'[{", ".join(map(annotation_repr, arguments))}]')
                  if arguments
                  else f'{value.__module__}.{value._name}'))


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
    return f'{annotation_repr(type(value))}({", ".join(arguments)})'


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
