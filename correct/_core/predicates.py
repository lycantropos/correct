from __future__ import annotations

import sys
import typing as t
from collections import (Counter,
                         abc)
from inspect import isabstract

import typing_extensions as te

from .hints import (Annotation,
                    GenericAlias,
                    LegacySpecialization,
                    LegacyUnionType,
                    Specialization,
                    UnionType)
from .utils import (annotation_repr,
                    to_arguments,
                    to_base,
                    type_var_to_variance,
                    unpack_type_var)
from .variance import Variance


def is_subtype(left: Annotation, right: Annotation) -> bool:
    if isinstance(left, t.TypeVar):
        left, left_variance = unpack_type_var(left), type_var_to_variance(left)
    else:
        left_variance = Variance.INVARIANT
    if isinstance(right, t.TypeVar):
        right, right_variance = (unpack_type_var(right),
                                 type_var_to_variance(right))
    else:
        right_variance = Variance.INVARIANT
    if is_union(left):
        left_arguments = to_arguments(left)
        if is_union(right):
            right_arguments = to_arguments(right)
            return (
                (left_variance is Variance.INVARIANT
                 and all(any((is_subtype(left_argument, right_argument)
                              and is_subtype(right_argument,
                                             left_argument))
                             for right_argument in right_arguments)
                         for left_argument in left_arguments))
                if right_variance is Variance.INVARIANT
                else (
                    (left_variance is not Variance.CONTRAVARIANT
                     and all(any(is_subtype(left_argument,
                                            right_argument)
                                 for right_argument in right_arguments)
                             for left_argument in left_arguments))
                    if right_variance is Variance.COVARIANT
                    else
                    (left_variance is not Variance.COVARIANT
                     and all(any(is_subtype(right_argument,
                                            left_argument)
                                 for right_argument in right_arguments)
                             for left_argument in left_arguments))
                )
            )
        else:
            return (
                (left_variance is Variance.INVARIANT
                 and all((is_subtype(left_argument, right)
                          and is_subtype(right, left_argument))
                         for left_argument in left_arguments))
                if right_variance is Variance.INVARIANT
                else ((left_variance is not Variance.CONTRAVARIANT
                       and all(is_subtype(left_argument, right)
                               for left_argument in left_arguments))
                      if right_variance is Variance.COVARIANT
                      else (left_variance is not Variance.COVARIANT
                            and all(is_subtype(right, left_argument)
                                    for left_argument in left_arguments)))
            )
    elif is_union(right):
        right_arguments = to_arguments(right)
        return ((left_variance is Variance.INVARIANT
                 and any(is_subtype(left, right_argument)
                         for right_argument in right_arguments)
                 and any(is_subtype(right_argument, left)
                         for right_argument in right_arguments))
                if right_variance is Variance.INVARIANT
                else ((left_variance is not Variance.CONTRAVARIANT
                       and any(is_subtype(left, right_argument)
                               for right_argument in right_arguments))
                      if right_variance is Variance.COVARIANT
                      else (left_variance is not Variance.COVARIANT
                            and any(is_subtype(right_argument, left)
                                    for right_argument in right_arguments))))
    elif is_specialization(left):
        left_base, left_arguments = to_base(left), to_arguments(left)
        if not isinstance(left_base, type):
            pass
        elif is_specialization(right):
            right_base, right_arguments = to_base(right), to_arguments(right)
            if not isinstance(right_base, type):
                pass
            elif not (
                    left_variance is Variance.INVARIANT
                    if right_variance is Variance.INVARIANT
                    else (
                            left_variance is not Variance.CONTRAVARIANT
                            if right_variance is Variance.COVARIANT
                            else left_variance is not Variance.COVARIANT
                    )
            ):
                return False
            elif (
                    not (
                            right_base in left_base.mro()
                            and left_base in right_base.mro()
                            if right_variance is Variance.INVARIANT
                            else (
                                    right_base in left_base.mro()
                                    if right_variance is Variance.COVARIANT
                                    else left_base in right_base.mro()
                            )
                    )
                    if isabstract(left_base) and isabstract(right_base)
                    else not (
                            (issubclass(left_base, right_base)
                             and issubclass(right_base, left_base))
                            if right_variance is Variance.INVARIANT
                            else (
                                    issubclass(left_base, right_base)
                                    if right_variance is Variance.COVARIANT
                                    else issubclass(right_base, left_base)
                            )
                    )
            ):
                return False
            elif left_base is tuple:
                if not left_arguments:
                    return (right_variance is Variance.COVARIANT
                            or (len(right_arguments) == 1
                                and right_arguments[0] == ()))
                elif right_base is tuple:
                    if not right_arguments:
                        return right_variance is Variance.CONTRAVARIANT
                    elif (len(left_arguments) == 2
                          and left_arguments[1] is Ellipsis):
                        left_argument = left_arguments[0]
                        if (len(right_arguments) == 2
                                and right_arguments[1] is Ellipsis):
                            right_argument = right_arguments[0]
                            return (
                                (is_subtype(left_argument, right_argument)
                                 and is_subtype(right_argument, left_argument))
                                if right_variance is Variance.INVARIANT
                                else (is_subtype(left_argument, right_argument)
                                      if right_variance is Variance.COVARIANT
                                      else is_subtype(right_argument,
                                                      left_argument))
                            )
                        else:
                            return (
                                all((is_subtype(left_argument, right_argument)
                                     and is_subtype(right_argument,
                                                    left_argument))
                                    for right_argument in right_arguments)
                                if right_variance is Variance.INVARIANT
                                else (
                                    all(is_subtype(left_argument,
                                                   right_argument)
                                        for right_argument in right_arguments)
                                    if right_variance is Variance.COVARIANT
                                    else
                                    all(is_subtype(right_argument,
                                                   left_argument)
                                        for right_argument in right_arguments)
                                )
                            )
                    elif (len(right_arguments) == 2
                          and right_arguments[1] is Ellipsis):
                        right_argument = right_arguments[0]
                        return (
                            all((is_subtype(left_argument, right_argument)
                                 and is_subtype(right_argument, left_argument))
                                for left_argument in left_arguments)
                            if right_variance is Variance.INVARIANT
                            else (all(is_subtype(left_argument, right_argument)
                                      for left_argument in left_arguments)
                                  if right_variance is Variance.COVARIANT
                                  else
                                  all(is_subtype(right_argument, left_argument)
                                      for left_argument in left_arguments))
                        )
                    else:
                        return (
                            (len(left_arguments) == len(right_arguments)
                             and all(map(is_subtype, left_arguments,
                                         right_arguments))
                             and all(map(is_subtype, right_arguments,
                                         left_arguments)))
                            if right_variance is Variance.INVARIANT
                            else (
                                (len(left_arguments) <= len(right_arguments)
                                 and all(map(is_subtype, left_arguments,
                                             right_arguments)))
                                if right_variance is Variance.COVARIANT
                                else
                                (len(left_arguments) >= len(right_arguments)
                                 and all(map(is_subtype, right_arguments,
                                             left_arguments)))
                            )
                        )
                else:
                    assert len(right_arguments) == 1, right
                    right_argument, = right_arguments
                    if (len(left_arguments) == 2
                            and left_arguments[1] is Ellipsis):
                        left_argument = left_arguments[0]
                        return ((is_subtype(left_argument, right_argument)
                                 and is_subtype(right_argument, left_argument))
                                if right_variance is Variance.INVARIANT
                                else (is_subtype(left_argument, right_argument)
                                      if right_variance is Variance.COVARIANT
                                      else is_subtype(right_argument,
                                                      left_argument)))
                    else:
                        return (
                            all((is_subtype(left_argument, right_argument)
                                 and is_subtype(right_argument, left_argument))
                                for left_argument in left_arguments)
                            if right_variance is Variance.INVARIANT
                            else (
                                all(is_subtype(left_argument, right_argument)
                                    for left_argument in left_arguments)
                                if right_variance is Variance.COVARIANT
                                else all(is_subtype(right_argument,
                                                    left_argument)
                                         for left_argument in left_arguments)
                            )
                        )
            elif right_base is tuple:
                if not right_arguments:
                    return right_variance is Variance.CONTRAVARIANT
                elif (len(right_arguments) == 2
                      and right_arguments[1] is Ellipsis):
                    right_argument = right_arguments[0]
                    return (
                        all((is_subtype(left_argument, right_argument)
                             and is_subtype(right_argument, left_argument))
                            for left_argument in left_arguments)
                        if right_variance is Variance.INVARIANT
                        else (all(is_subtype(left_argument, right_argument)
                                  for left_argument in left_arguments)
                              if right_variance is Variance.COVARIANT
                              else all(is_subtype(right_argument,
                                                  left_argument)
                                       for left_argument in left_arguments))
                    )
                else:
                    return (
                        (len(left_arguments) == len(right_arguments)
                         and all(map(is_subtype, left_arguments,
                                     right_arguments))
                         and all(map(is_subtype, right_arguments,
                                     left_arguments)))
                        if right_variance is Variance.INVARIANT
                        else ((len(left_arguments) <= len(right_arguments)
                               and all(map(is_subtype, left_arguments,
                                           right_arguments)))
                              if right_variance is Variance.COVARIANT
                              else (len(left_arguments) >= len(right_arguments)
                                    and all(map(is_subtype, right_arguments,
                                                left_arguments))))
                    )
            else:
                left_arguments = _complete_arguments(left_arguments, left_base)
                right_arguments = _complete_arguments(right_arguments,
                                                      right_base)
                if (len(left_arguments) == len(right_arguments)
                        or (
                                (issubclass(right_base, abc.Mapping)
                                 and len(right_arguments) == 2)
                                if right_variance is Variance.CONTRAVARIANT
                                else (issubclass(left_base, abc.Mapping)
                                      and len(left_arguments) == 2)
                        )
                        or (
                                right_base
                                if right_variance is Variance.CONTRAVARIANT
                                else left_base
                        ) in (abc.AsyncGenerator, abc.Coroutine,
                              abc.Generator)):
                    return (
                        (all(map(is_subtype, left_arguments, right_arguments))
                         and all(map(is_subtype, right_arguments,
                                     left_arguments)))
                        if right_variance is Variance.INVARIANT
                        else (all(map(is_subtype, left_arguments,
                                      right_arguments))
                              if right_variance is Variance.COVARIANT
                              else all(map(is_subtype, right_arguments,
                                           left_arguments)))
                    )
        elif right is t.Any:
            return True
        else:
            if is_generic_alias(right):
                assert not to_arguments(right), right
                right = to_base(right)
            if isinstance(right, type):
                if is_protocol(right):
                    pass
                else:
                    return ((left_variance is Variance.INVARIANT
                             and issubclass(left_base, right)
                             and issubclass(right, left_base))
                            if right_variance is Variance.INVARIANT
                            else ((left_variance is not Variance.CONTRAVARIANT
                                   and issubclass(left_base, right))
                                  if right_variance is Variance.COVARIANT
                                  else (left_variance is not Variance.COVARIANT
                                        and issubclass(right, left_base))))
    elif left is t.Any:
        return True
    else:
        if is_generic_alias(left):
            assert not to_arguments(left), left
            left = to_base(left)
        if isinstance(left, type):
            if is_protocol(left):
                pass
            elif is_specialization(right):
                right_base, right_arguments = (to_base(right),
                                               to_arguments(right))
                if isinstance(right_base, type):
                    if is_protocol(right_base):
                        pass
                    else:
                        return (
                            (left_variance is Variance.INVARIANT
                             and issubclass(left, right_base)
                             and issubclass(right_base, left))
                            if right_variance is Variance.INVARIANT
                            else ((left_variance is not Variance.CONTRAVARIANT
                                   and issubclass(left, right_base))
                                  if right_variance is Variance.COVARIANT
                                  else (left_variance is not Variance.COVARIANT
                                        and issubclass(right_base, left)))
                        )
            elif right is t.Any:
                return True
            else:
                if is_generic_alias(right):
                    assert not to_arguments(right), right
                    right = to_base(right)
                if isinstance(right, type):
                    if is_protocol(right):
                        pass
                    else:
                        return (
                            (left_variance is Variance.INVARIANT
                             and issubclass(left, right)
                             and issubclass(right, left))
                            if right_variance is Variance.INVARIANT
                            else ((left_variance is not Variance.CONTRAVARIANT
                                   and issubclass(left, right))
                                  if right_variance is Variance.COVARIANT
                                  else (left_variance is not Variance.COVARIANT
                                        and issubclass(right, left)))
                        )
    raise TypeError('Unsupported types: '
                    f'"{annotation_repr(left)}", "{annotation_repr(right)}".')


def is_generic_alias(value: t.Any) -> bool:
    return isinstance(value, GenericAlias)


if sys.version_info < (3, 9):
    def is_specialization(value: t.Any) -> bool:
        return (isinstance(value, LegacySpecialization)
                and (to_base(value) is not t.Union
                     if to_arguments(value)
                     else to_base(value) is tuple))
else:
    def is_specialization(value: t.Any) -> bool:
        return isinstance(value, (LegacySpecialization, Specialization))


def is_protocol(value: type,
                _protocol_meta: t.Type = type(te.Protocol)) -> bool:
    return isinstance(value, _protocol_meta)


if sys.version_info < (3, 9):
    def is_union(value: t.Any) -> bool:
        return isinstance(value, LegacyUnionType) and to_base(value) is t.Union
elif sys.version_info < (3, 10):
    def is_union(value: t.Any) -> bool:
        return isinstance(value, LegacyUnionType)
else:
    def is_union(value: t.Any) -> bool:
        return isinstance(value, (LegacyUnionType, UnionType))


def _complete_arguments(arguments: t.Tuple[Annotation, ...],
                        origin: type) -> t.Tuple[Annotation, ...]:
    if origin is Counter:
        assert len(arguments) == 1, arguments
        arguments += (int,)
    elif origin is abc.ItemsView:
        assert len(arguments) == 2, arguments
        arguments = (t.Tuple[arguments],)
    return arguments
