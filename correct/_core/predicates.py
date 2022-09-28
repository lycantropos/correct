import inspect
import typing as t
from collections import (Counter,
                         abc)

from .hints import (Annotation,
                    GenericAlias,
                    VariadicGenericAlias)
from .utils import (to_arguments,
                    to_origin,
                    type_repr,
                    unpack_type_var)
from .variance import Variance


def _generic_alias_to_variance(value: GenericAlias) -> t.Tuple[Variance, ...]:
    return tuple(Variance.CONTRAVARIANT
                 if parameter.__contravariant__
                 else (Variance.COVARIANT
                       if parameter.__covariant__
                       else Variance.INVARIANT)
                 for parameter in value.__parameters__)


_PARAMETERS_VARIANCE = {
    to_origin(value): _generic_alias_to_variance(value)
    for value in vars(t).values()
    if (isinstance(value, GenericAlias)
        and not isinstance(value, VariadicGenericAlias))
}
assert all(
        isinstance(origin, type) for origin in _PARAMETERS_VARIANCE
), _PARAMETERS_VARIANCE
assert None not in _PARAMETERS_VARIANCE, _PARAMETERS_VARIANCE


def is_subtype(left: Annotation, right: Annotation) -> bool:
    if isinstance(left, t.TypeVar):
        left = unpack_type_var(left)
    if isinstance(right, t.TypeVar):
        right = unpack_type_var(right)
    left_origin, right_origin = to_origin(left), to_origin(right)
    if not (isinstance(left, to_arguments(Annotation))
            and isinstance(right, to_arguments(Annotation))):
        pass
    elif left_origin is None:
        assert not to_arguments(left), left
        if left is t.Any or left is object:
            return True
        elif isinstance(left, type):
            if is_protocol(left):
                pass
            if right_origin is None:
                assert not to_arguments(right), right
                if right is t.Any or right is object:
                    return True
                elif isinstance(right, type):
                    if is_protocol(right):
                        pass
                    else:
                        return issubclass(left, right)
            elif right_origin is t.Union:
                return any(is_subtype(left, right_argument)
                           for right_argument in to_arguments(right))
            elif isinstance(right_origin, type):
                return issubclass(left, right_origin)
    elif left_origin is t.Union:
        if right_origin is t.Union:
            left_arguments_set = set(to_arguments(left))
            right_arguments_set = set(to_arguments(right))
            common_arguments = left_arguments_set & right_arguments_set
            left_arguments_set.difference_update(common_arguments)
            right_arguments_set.difference_update(common_arguments)
            return all(any(is_subtype(left_argument, right_argument)
                           for right_argument in right_arguments_set)
                       for left_argument in left_arguments_set)
        else:
            return all(is_subtype(left_argument, right)
                       for left_argument in to_arguments(left))
    elif right_origin is t.Union:
        return any(is_subtype(left, right_argument)
                   for right_argument in to_arguments(right))
    elif left_origin is tuple:
        if right_origin is None:
            assert not to_arguments(right), right
            if right is t.Any or right is object:
                return True
            elif isinstance(right, type):
                if is_protocol(right):
                    pass
                else:
                    return issubclass(left_origin, right)
        elif right_origin is tuple:
            left_arguments, right_arguments = (to_arguments(left),
                                               to_arguments(right))
            if not (left_arguments and right_arguments):
                return True
            elif (len(left_arguments) == 2
                  and left_arguments[1] is Ellipsis):
                left_argument = left_arguments[0]
                if (len(right_arguments) == 2
                        and right_arguments[1] is Ellipsis):
                    return is_subtype(left_argument, right_arguments[0])
                else:
                    return all(is_subtype(left_argument, right_argument)
                               for right_argument in right_arguments)
            elif (len(right_arguments) == 2
                  and right_arguments[1] is Ellipsis):
                right_argument = right_arguments[0]
                return all(is_subtype(left_argument, right_argument)
                           for left_argument in left_arguments)
            else:
                return all(map(is_subtype, left_arguments, right_arguments))
        elif right_origin in _PARAMETERS_VARIANCE:
            if not issubclass(left_origin, right_origin):
                return False
            left_arguments = to_arguments(left)
            if not left_arguments:
                return True
            right_parameters_variance = _PARAMETERS_VARIANCE[right_origin]
            assert len(right_parameters_variance) == 1, right
            right_arguments = to_arguments(right)
            assert (
                    len(right_arguments) in (0, len(right_parameters_variance))
            ), right
            if not right_arguments:
                return True
            else:
                right_argument, = right_arguments
                if (len(left_arguments) == 2
                        and left_arguments[1] is Ellipsis):
                    left_argument = left_arguments[0]
                    return is_subtype(left_argument, right_argument)
                else:
                    return all(is_subtype(left_argument, right_argument)
                               for left_argument in left_arguments)
    elif left_origin in _PARAMETERS_VARIANCE:
        if right_origin is None:
            assert not to_arguments(right), right
            if right is t.Any or right is object:
                return True
            elif isinstance(right, type):
                if is_protocol(right):
                    pass
                else:
                    return issubclass(left_origin, right)
        elif right_origin is tuple:
            if not issubclass(left_origin, right_origin):
                return False
            left_parameters_variance = _PARAMETERS_VARIANCE[left_origin]
            assert len(left_parameters_variance) == 1, left
            if not left_parameters_variance:
                return True
            left_arguments = to_arguments(left)
            assert (
                    len(left_arguments) in (0, len(left_parameters_variance))
            ), left
            if not left_arguments:
                return True
            else:
                left_argument, = left_arguments
                right_arguments = to_arguments(right)
                if not right_arguments:
                    return True
                elif (len(right_arguments) == 2
                      and right_arguments[1] is Ellipsis):
                    right_argument = right_arguments[0]
                    return is_subtype(left_argument, right_argument)
                else:
                    return all(is_subtype(left_argument, right_argument)
                               for right_argument in right_arguments)
        elif right_origin in _PARAMETERS_VARIANCE:
            if (inspect.isabstract(left_origin)
                    and inspect.isabstract(right_origin)):
                if right_origin not in left_origin.mro():
                    return False
            elif not issubclass(left_origin, right_origin):
                return False
            left_parameters_variance = _PARAMETERS_VARIANCE[left_origin]
            right_parameters_variance = _PARAMETERS_VARIANCE[right_origin]
            assert all(
                    (left_variance is right_variance
                     or left_variance is Variance.INVARIANT)
                    for left_variance, right_variance in zip(
                            left_parameters_variance,
                            right_parameters_variance
                    )
            ), (left, right)
            if not (left_parameters_variance and right_parameters_variance):
                return True
            left_arguments, right_arguments = (to_arguments(left),
                                               to_arguments(right))
            assert (
                    len(left_arguments) in (0, len(left_parameters_variance))
            ), left
            assert (
                    len(right_arguments) in (0, len(right_parameters_variance))
            ), right
            if not (left_arguments and right_arguments):
                return True
            elif (len(left_parameters_variance)
                  == len(right_parameters_variance)):
                return all(
                        (is_subtype(left_argument, right_argument)
                         and is_subtype(left_argument, right_argument))
                        if right_variance is Variance.INVARIANT
                        else (is_subtype(left_argument, right_argument)
                              if right_variance is Variance.COVARIANT
                              else is_subtype(right_argument, left_argument))
                        for left_argument, right_argument, right_variance
                        in zip(left_arguments, right_arguments,
                               right_parameters_variance)
                )
            elif issubclass(left_origin, abc.Mapping):
                if len(left_parameters_variance) == 2:
                    assert len(right_parameters_variance) == 1, right
                    left_key_annotation = left_arguments[0]
                    right_argument, = right_arguments
                    return is_subtype(left_key_annotation, right_argument)
                elif left_origin is Counter:
                    assert len(left_parameters_variance) == 1, left
                    assert len(right_parameters_variance) == 2, right
                    left_arguments += (int,)
                    return all(
                            (is_subtype(left_argument, right_argument)
                             and is_subtype(left_argument, right_argument))
                            if right_variance is Variance.INVARIANT
                            else (is_subtype(left_argument, right_argument)
                                  if right_variance is Variance.COVARIANT
                                  else is_subtype(right_argument,
                                                  left_argument))
                            for left_argument, right_argument, right_variance
                            in zip(left_arguments, right_arguments,
                                   right_parameters_variance)
                    )
            elif left_origin is abc.ItemsView:
                assert len(left_parameters_variance) == 2, left
                assert len(right_parameters_variance) == 1, right
                left_item_annotation: Annotation = t.Tuple[left_arguments]
                right_argument, = right_arguments
                return is_subtype(left_item_annotation, right_argument)
            elif left_origin is abc.Coroutine or left_origin is abc.Generator:
                assert len(left_parameters_variance) == 3, left
                assert len(right_parameters_variance) == 1, right
                left_yield_annotation = left_arguments[0]
                right_argument, = right_arguments
                return is_subtype(left_yield_annotation, right_argument)
            elif left_origin is abc.AsyncGenerator:
                assert len(right_parameters_variance) == 1, right
                left_yield_annotation = left_arguments[0]
                right_argument, = right_arguments
                return is_subtype(left_yield_annotation, right_argument)
    raise TypeError('Unsupported types: '
                    f'"{type_repr(left)}", "{type_repr(right)}".')


def is_protocol(value: type,
                _protocol_meta: t.Type = type(t.Protocol)) -> bool:
    return isinstance(value, _protocol_meta)
