import inspect
import sys
import typing as t
from collections import (Counter,
                         abc)

from .hints import (Annotation,
                    GenericAlias)
from .utils import (to_arguments,
                    to_origin,
                    type_repr,
                    type_var_to_variance,
                    unpack_type_var)
from .variance import Variance

if sys.version_info >= (3, 8):
    Protocol = t.Protocol
else:
    from typing_extensions import Protocol


def _generic_alias_to_variance(value: GenericAlias) -> t.Tuple[Variance, ...]:
    return tuple(Variance.CONTRAVARIANT
                 if parameter.__contravariant__
                 else (Variance.COVARIANT
                       if parameter.__covariant__
                       else Variance.INVARIANT)
                 for parameter in value.__parameters__)


if sys.version_info >= (3, 9):
    def _is_generic_alias(value: t.Any) -> bool:
        return isinstance(value, GenericAlias)
else:
    def _is_generic_alias(value: t.Any) -> bool:
        return (isinstance(value, GenericAlias)
                and hasattr(value, '__parameters__'))


def is_subtype(left: Annotation, right: Annotation) -> bool:
    if isinstance(left, t.TypeVar):
        left = unpack_type_var(left)
    if isinstance(right, t.TypeVar):
        right, right_variance = (unpack_type_var(right),
                                 type_var_to_variance(right))
    else:
        right_variance = Variance.COVARIANT
    left_origin, right_origin = to_origin(left), to_origin(right)
    left_arguments, right_arguments = to_arguments(left), to_arguments(right)
    if left_origin is None:
        assert not left_arguments, left
        if left is t.Any:
            return True
        elif isinstance(left, type):
            if is_protocol(left):
                pass
            elif right_origin is None:
                assert not right_arguments, right
                if right is t.Any:
                    return True
                elif isinstance(right, type):
                    if is_protocol(right):
                        pass
                    else:
                        return ((issubclass(left, right)
                                 and issubclass(right, left))
                                if right_variance is Variance.INVARIANT
                                else (issubclass(left, right)
                                      if right_variance is Variance.COVARIANT
                                      else issubclass(right, left)))
            elif right_origin is t.Union:
                return (any((is_subtype(left, right_argument)
                             and is_subtype(right_argument, left))
                            for right_argument in right_arguments)
                        if right_variance is Variance.INVARIANT
                        else (any(is_subtype(left, right_argument)
                                  for right_argument in right_arguments)
                              if right_variance is Variance.COVARIANT
                              else any(is_subtype(right_argument, left)
                                       for right_argument in right_arguments)))
            elif isinstance(right_origin, type):
                if is_protocol(right_origin):
                    pass
                else:
                    return ((issubclass(left, right_origin)
                             and issubclass(right_origin, left))
                            if right_variance is Variance.INVARIANT
                            else (issubclass(left, right_origin)
                                  if right_variance is Variance.COVARIANT
                                  else issubclass(right_origin, left)))
    elif left_origin is t.Union:
        if right_origin is t.Union:
            left_arguments_set = set(left_arguments)
            right_arguments_set = set(right_arguments)
            common_arguments = left_arguments_set & right_arguments_set
            left_arguments_set.difference_update(common_arguments)
            right_arguments_set.difference_update(common_arguments)
            return (
                all(any((is_subtype(left_argument, right_argument)
                         and is_subtype(right_argument, left_argument))
                        for right_argument in right_arguments_set)
                    for left_argument in left_arguments_set)
                if right_variance is Variance.INVARIANT
                else (all(any(is_subtype(left_argument, right_argument)
                              for right_argument in right_arguments_set)
                          for left_argument in left_arguments_set)
                      if right_variance is Variance.COVARIANT
                      else all(any(is_subtype(right_argument, left_argument)
                                   for right_argument in right_arguments_set)
                               for left_argument in left_arguments_set))
            )
        else:
            return (all((is_subtype(left_argument, right)
                         and is_subtype(right, left_argument))
                        for left_argument in left_arguments)
                    if right_variance is Variance.INVARIANT
                    else (all(is_subtype(left_argument, right)
                              for left_argument in left_arguments)
                          if right_variance is Variance.COVARIANT
                          else all(is_subtype(right, left_argument)
                                   for left_argument in left_arguments)))
    elif not isinstance(left_origin, type):
        pass
    elif right_origin is None:
        assert not right_arguments, right
        if right is t.Any:
            return True
        elif isinstance(right, type):
            if is_protocol(right):
                pass
            else:
                return ((issubclass(left_origin, right)
                         and issubclass(right, left_origin))
                        if right_variance is Variance.INVARIANT
                        else (issubclass(left_origin, right)
                              if right_variance is Variance.COVARIANT
                              else issubclass(right, left_origin)))
    elif right_origin is t.Union:
        return (any(is_subtype(left, right_argument)
                    for right_argument in right_arguments)
                and any(is_subtype(right_argument, left)
                        for right_argument in right_arguments)
                if right_variance is Variance.INVARIANT
                else (any(is_subtype(left, right_argument)
                          for right_argument in right_arguments)
                      if right_variance is Variance.COVARIANT
                      else any(is_subtype(right_argument, left)
                               for right_argument in right_arguments)))
    elif not isinstance(right_origin, type):
        pass
    elif (
            not (
                    right_origin in left_origin.mro()
                    and left_origin in right_origin.mro()
                    if right_variance is Variance.INVARIANT
                    else (
                            right_origin in left_origin.mro()
                            if right_variance is Variance.COVARIANT
                            else left_origin in right_origin.mro()
                    )
            )
            if (inspect.isabstract(left_origin)
                and inspect.isabstract(right_origin))
            else not (
                    (issubclass(left_origin, right_origin)
                     and issubclass(right_origin, left_origin))
                    if right_variance is Variance.INVARIANT
                    else (
                            issubclass(left_origin, right_origin)
                            if right_variance is Variance.COVARIANT
                            else issubclass(right_origin, left_origin)
                    )
            )
    ):
        return False
    elif not (left_arguments and right_arguments):
        return True
    elif left_origin is tuple:
        if len(left_arguments) == 1 and left_arguments[0] == ():
            return (right_variance is Variance.COVARIANT
                    or len(right_arguments) == 1 and right_arguments[0] == ())
        elif right_origin is tuple:
            if len(right_arguments) == 1 and right_arguments[0] == ():
                return right_variance is Variance.CONTRAVARIANT
            elif len(left_arguments) == 2 and left_arguments[1] is Ellipsis:
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
                              else is_subtype(right_argument, left_argument))
                    )
                else:
                    return (
                        all((is_subtype(left_argument, right_argument)
                             and is_subtype(right_argument, left_argument))
                            for right_argument in right_arguments)
                        if right_variance is Variance.INVARIANT
                        else (
                            all(is_subtype(left_argument, right_argument)
                                for right_argument in right_arguments)
                            if right_variance is Variance.COVARIANT
                            else all(is_subtype(right_argument, left_argument)
                                     for right_argument in right_arguments)
                        )
                    )
            elif len(right_arguments) == 2 and right_arguments[1] is Ellipsis:
                right_argument = right_arguments[0]
                return (
                    all((is_subtype(left_argument, right_argument)
                         and is_subtype(right_argument, left_argument))
                        for left_argument in left_arguments)
                    if right_variance is Variance.INVARIANT
                    else (all(is_subtype(left_argument, right_argument)
                              for left_argument in left_arguments)
                          if right_variance is Variance.COVARIANT
                          else all(is_subtype(right_argument, left_argument)
                                   for left_argument in left_arguments))
                )
            else:
                return ((len(left_arguments) == len(right_arguments)
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
                                                left_arguments)))))
        else:
            assert len(right_arguments) == 1, right
            right_argument, = right_arguments
            if len(left_arguments) == 2 and left_arguments[1] is Ellipsis:
                left_argument = left_arguments[0]
                return ((is_subtype(left_argument, right_argument)
                         and is_subtype(right_argument, left_argument))
                        if right_variance is Variance.INVARIANT
                        else (is_subtype(left_argument, right_argument)
                              if right_variance is Variance.COVARIANT
                              else is_subtype(right_argument, left_argument)))
            else:
                return (
                    all((is_subtype(left_argument, right_argument)
                         and is_subtype(right_argument, left_argument))
                        for left_argument in left_arguments)
                    if right_variance is Variance.INVARIANT
                    else (all(is_subtype(left_argument, right_argument)
                              for left_argument in left_arguments)
                          if right_variance is Variance.COVARIANT
                          else all(is_subtype(right_argument, left_argument)
                                   for left_argument in left_arguments))
                )
    elif right_origin is tuple:
        if len(right_arguments) == 1 and right_arguments[0] == ():
            return right_variance is Variance.CONTRAVARIANT
        elif len(right_arguments) == 2 and right_arguments[1] is Ellipsis:
            right_argument = right_arguments[0]
            return (all((is_subtype(left_argument, right_argument)
                         and is_subtype(right_argument, left_argument))
                        for left_argument in left_arguments)
                    if right_variance is Variance.INVARIANT
                    else (all(is_subtype(left_argument, right_argument)
                              for left_argument in left_arguments)
                          if right_variance is Variance.COVARIANT
                          else all(is_subtype(right_argument, left_argument)
                                   for left_argument in left_arguments)))
        else:
            return ((len(left_arguments) == len(right_arguments)
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
                                            left_arguments)))))
    else:
        assert _is_generic_alias(left), left
        assert _is_generic_alias(right), right
        if left_origin is Counter:
            assert len(left_arguments) == 1, left
            left_arguments += (int,)
        if len(left_arguments) == len(right_arguments):
            return (
                (all(map(is_subtype, left_arguments, right_arguments))
                 and all(map(is_subtype, right_arguments, left_arguments)))
                if right_variance is Variance.INVARIANT
                else (
                    all(map(is_subtype, left_arguments, right_arguments))
                    if right_variance is Variance.COVARIANT
                    else all(map(is_subtype, right_arguments, left_arguments))
                )
            )
        elif issubclass(left_origin, abc.Mapping):
            if len(left_arguments) == 2:
                assert len(right_arguments) == 1, right
                left_key_annotation = left_arguments[0]
                right_argument, = right_arguments
                return (
                    (is_subtype(left_key_annotation, right_argument)
                     and is_subtype(right_argument, left_key_annotation))
                    if right_variance is Variance.INVARIANT
                    else (is_subtype(left_key_annotation, right_argument)
                          if right_variance is Variance.COVARIANT
                          else is_subtype(right_argument, left_key_annotation))
                )
        elif left_origin is abc.ItemsView:
            assert len(left_arguments) == 2, left
            assert len(right_arguments) == 1, right
            left_item_annotation: Annotation = t.Tuple[left_arguments]
            right_argument, = right_arguments
            return (
                (is_subtype(left_item_annotation, right_argument)
                 and is_subtype(right_argument, left_item_annotation))
                if right_variance is Variance.INVARIANT
                else (is_subtype(left_item_annotation, right_argument)
                      if right_variance is Variance.COVARIANT
                      else is_subtype(right_argument, left_item_annotation))
            )
        elif left_origin is abc.Coroutine or left_origin is abc.Generator:
            assert len(left_arguments) == 3, left
            assert len(right_arguments) == 1, right
            left_yield_annotation = left_arguments[0]
            right_argument, = right_arguments
            return (
                (is_subtype(left_yield_annotation, right_argument)
                 and is_subtype(right_argument, left_yield_annotation))
                if right_variance is Variance.INVARIANT
                else (is_subtype(left_yield_annotation, right_argument)
                      if right_variance is Variance.COVARIANT
                      else is_subtype(right_argument, left_yield_annotation))
            )
        elif left_origin is abc.AsyncGenerator:
            assert len(right_arguments) == 1, right
            left_yield_annotation = left_arguments[0]
            right_argument, = right_arguments
            return (
                (is_subtype(left_yield_annotation, right_argument)
                 and is_subtype(right_argument, left_yield_annotation))
                if right_variance is Variance.INVARIANT
                else (is_subtype(left_yield_annotation, right_argument)
                      if right_variance is Variance.COVARIANT
                      else is_subtype(right_argument, left_yield_annotation))
            )
    raise TypeError('Unsupported types: '
                    f'"{type_repr(left)}", "{type_repr(right)}".')


def is_protocol(value: type,
                _protocol_meta: t.Type = type(Protocol)) -> bool:
    return isinstance(value, _protocol_meta)
