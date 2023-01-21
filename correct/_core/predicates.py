from __future__ import annotations

import enum
import sys
import types
import typing as t
from collections import (Counter,
                         abc)
from functools import partial
from inspect import isabstract

import typing_extensions as te

from .hints import (Annotation,
                    EllipsisType,
                    GenericAlias,
                    LegacySpecialization,
                    LegacyUnionType,
                    Specialization,
                    UnionType)
from .utils import (annotation_repr,
                    to_arguments,
                    to_base,
                    to_variants,
                    type_var_to_variance,
                    unpack_type_var)
from .variance import Variance


def is_subtype(default_left_variance: Variance,
               default_right_variance: Variance,
               left: Annotation, right: Annotation) -> bool:
    if is_type_var(left):
        left, left_variance = unpack_type_var(left), type_var_to_variance(left)
    else:
        left_variance = default_left_variance
    if is_type_var(right):
        right, right_variance = (unpack_type_var(right),
                                 type_var_to_variance(right))
    else:
        right_variance = default_right_variance
    return (left is t.Any or right is t.Any
            or ((left_variance is Variance.INVARIANT
                 and _is_subtype(left, right, left_variance, right_variance)
                 and _is_subtype(right, left, left_variance, right_variance))
                if right_variance is Variance.INVARIANT
                else ((left_variance is not Variance.CONTRAVARIANT
                       and _is_subtype(left, right, left_variance,
                                       right_variance))
                      if right_variance is Variance.COVARIANT
                      else (left_variance is not Variance.COVARIANT
                            and _is_subtype(right, left, ~left_variance,
                                            ~right_variance)))))


class AnnotationKind(enum.IntEnum):
    CONSTANT = enum.auto()
    GENERIC_ALIAS = enum.auto()
    PROTOCOL = enum.auto()
    SELF = enum.auto()
    SPECIALIZATION = enum.auto()
    TYPE = enum.auto()
    UNION = enum.auto()


def _classify(value: Annotation) -> AnnotationKind:
    if value is te.Self:
        return AnnotationKind.SELF
    elif value is t.NoReturn or value is None:
        return AnnotationKind.CONSTANT
    elif is_generic_alias(value):
        return AnnotationKind.GENERIC_ALIAS
    elif is_specialization(value):
        return AnnotationKind.SPECIALIZATION
    elif is_protocol(value):
        return AnnotationKind.PROTOCOL
    elif is_type(value):
        return AnnotationKind.TYPE
    elif is_union(value):
        return AnnotationKind.UNION
    else:
        raise TypeError(f'Unsupported annotation: "{annotation_repr(value)}".')


class FieldKind(enum.IntEnum):
    CLASS_METHOD = enum.auto()
    INSTANCE_METHOD = enum.auto()
    PROPERTY = enum.auto()
    STATIC_METHOD = enum.auto()


def _classify_field(
        value: Annotation
) -> t.Union[AnnotationKind, FieldKind]:
    if isinstance(value, property):
        return FieldKind.PROPERTY
    elif isinstance(value, classmethod):
        return FieldKind.CLASS_METHOD
    elif isinstance(value, staticmethod):
        return FieldKind.STATIC_METHOD
    elif isinstance(value, (types.BuiltinFunctionType, types.BuiltinMethodType,
                            types.ClassMethodDescriptorType,
                            types.FunctionType, types.LambdaType,
                            types.MethodDescriptorType,
                            types.WrapperDescriptorType)):
        return FieldKind.INSTANCE_METHOD
    else:
        return _classify(value)


def _is_field_subtype(left_variance: Variance,
                      right_variance: Variance,
                      left: Annotation,
                      right: Annotation) -> bool:
    from . import signatures

    left_kind, right_kind = _classify_field(left), _classify_field(right)
    if right_kind is FieldKind.CLASS_METHOD:
        if left_kind is not FieldKind.CLASS_METHOD:
            return False
        return signatures.is_subtype_of(
                signatures.from_callable(left.__func__),
                signatures.from_callable(right.__func__),
                partial(is_subtype, left_variance, right_variance)
        )
    elif left_kind is FieldKind.CLASS_METHOD:
        return False
    elif right_kind is FieldKind.STATIC_METHOD:
        if left_kind is not FieldKind.STATIC_METHOD:
            return False
        return signatures.is_subtype_of(
                signatures.from_callable(left.__func__),
                signatures.from_callable(right.__func__),
                partial(is_subtype, left_variance, right_variance)
        )
    elif left_kind is FieldKind.STATIC_METHOD:
        return False
    elif right_kind is FieldKind.INSTANCE_METHOD:
        if left_kind is not FieldKind.INSTANCE_METHOD:
            return False
        return signatures.is_subtype_of(signatures.from_callable(left),
                                        signatures.from_callable(right),
                                        partial(is_subtype, left_variance,
                                                right_variance))
    elif left_kind is FieldKind.INSTANCE_METHOD:
        if right_kind is AnnotationKind.GENERIC_ALIAS:
            return to_base(right) is abc.Callable
        elif right_kind is AnnotationKind.TYPE:
            return right is abc.Callable
        elif right_kind is not AnnotationKind.SPECIALIZATION:
            return False
        if to_base(right) is not abc.Callable:
            return False
        left_signature = signatures.from_callable(left)
        right_annotations, right_returns = to_arguments(right)
        return signatures.is_subtype_of_callable(
                left_signature, right_annotations, right_returns,
                partial(is_subtype, left_variance, right_variance)
        )
    elif right_kind is FieldKind.PROPERTY:
        if left_kind is not FieldKind.PROPERTY:
            return False
        assert left.fget is not None, left
        assert right.fget is not None, right
        if not signatures.is_subtype_of(signatures.from_callable(left.fget),
                                        signatures.from_callable(right.fget),
                                        partial(is_subtype, left_variance,
                                                right_variance)):
            return False
        if right.fset is not None:
            if left.fset is None:
                return False
            elif not signatures.is_subtype_of(
                    signatures.from_callable(left.fset),
                    signatures.from_callable(right.fset),
                    partial(is_subtype, left_variance, right_variance)
            ):
                return False
        if right.fdel is not None:
            if left.fdel is None:
                return False
            elif not signatures.is_subtype_of(
                    signatures.from_callable(left.fdel),
                    signatures.from_callable(right.fdel),
                    partial(is_subtype, left_variance, right_variance)
            ):
                return False
        return True
    elif left_kind is FieldKind.PROPERTY:
        if left.fset is None or left.fdel is None:
            return False
        return signatures.is_subtype_of_callable_returns(
                signatures.from_callable(left.fget), right,
                partial(is_subtype, left_variance, right_variance)
        )
    else:
        assert left_kind not in FieldKind, left_kind
        assert right_kind not in FieldKind, right_kind
        return is_subtype(left_variance, right_variance, left, right)


def _is_subtype(left: Annotation,
                right: Annotation,
                left_variance: Variance,
                right_variance: Variance,
                callable_base: te.TypeAlias = abc.Callable) -> bool:
    left_kind, right_kind = _classify(left), _classify(right)

    if left_kind is AnnotationKind.GENERIC_ALIAS:
        assert not to_arguments(left), left
        left = to_base(left)
        left_kind = _classify(left)
    if right_kind is AnnotationKind.GENERIC_ALIAS:
        assert not to_arguments(right), right
        right = to_base(right)
        right_kind = _classify(right)

    if left_kind is AnnotationKind.UNION:
        left_variants = to_variants(left)
        if right_kind is AnnotationKind.UNION:
            right_variants = to_variants(right)
            return all(any(is_subtype(left_variance, right_variance,
                                      left_variant, right_variant)
                           for right_variant in right_variants)
                       for left_variant in left_variants)
        else:
            return all(is_subtype(left_variance, right_variance, left_variant,
                                  right)
                       for left_variant in left_variants)
    elif right_kind is AnnotationKind.UNION:
        right_variants = to_variants(right)
        return any(is_subtype(left_variance, right_variance, left,
                              right_variant)
                   for right_variant in right_variants)
    elif left_kind is AnnotationKind.CONSTANT:
        return right is object or left is right
    elif right_kind is AnnotationKind.CONSTANT:
        return False
    elif left_kind is AnnotationKind.SELF:
        return right_kind is AnnotationKind.SELF
    elif right_kind is AnnotationKind.SELF:
        return False
    elif left_kind is AnnotationKind.PROTOCOL:
        if right_kind is AnnotationKind.PROTOCOL:
            left_fields, right_fields = (_protocol_to_fields(left),
                                         _protocol_to_fields(right))
            if not (left_fields.keys() <= right_fields.keys()):
                return False
            return all(_is_field_subtype(left_variance, right_variance,
                                         left_field, right_fields[field_name])
                       for field_name, left_field in left_fields.items())
        else:
            return False
    elif right_kind is AnnotationKind.PROTOCOL:
        right_fields = _protocol_to_fields(right)
        for right_field_name, right_field in right_fields.items():
            try:
                left_field = getattr(left, right_field_name)
            except AttributeError:
                return False
            else:
                if not _is_field_subtype(left_variance, right_variance,
                                         left_field, right_field):
                    return False
        return True
    elif left_kind is AnnotationKind.SPECIALIZATION:
        left_base, left_arguments = to_base(left), to_arguments(left)
        if left_base is t.ClassVar:
            if right_kind is not AnnotationKind.SPECIALIZATION:
                return False
            right_base, right_arguments = to_base(right), to_arguments(right)
            return (right_base is t.ClassVar
                    and is_subtype(left_variance, right_variance,
                                   left_arguments[0], right_arguments[0]))
        elif not isinstance(left_base, type):
            pass
        elif right_kind is AnnotationKind.SPECIALIZATION:
            right_base, right_arguments = to_base(right), to_arguments(right)
            if right_base is t.ClassVar:
                return False
            elif not isinstance(right_base, type):
                pass
            elif (
                    right_base not in left_base.mro()
                    if isabstract(left_base) and isabstract(right_base)
                    else not issubclass(left_base, right_base)
            ):
                return False
            elif left_base is tuple:
                if right_base is tuple:
                    if (len(left_arguments) == 2
                            and left_arguments[1] is Ellipsis):
                        return (len(right_arguments) == 2
                                and right_arguments[1] is Ellipsis
                                and is_subtype(left_variance, right_variance,
                                               left_arguments[0],
                                               right_arguments[0]))
                    elif (len(right_arguments) == 2
                          and right_arguments[1] is Ellipsis):
                        right_argument = right_arguments[0]
                        return all(is_subtype(left_variance, right_variance,
                                              left_argument, right_argument)
                                   for left_argument in left_arguments)
                    else:
                        return (len(left_arguments) == len(right_arguments)
                                and
                                all(is_subtype(left_variance, right_variance,
                                               left_argument, right_argument)
                                    for left_argument, right_argument
                                    in zip(left_arguments, right_arguments)))
                else:
                    assert len(right_arguments) == 1, right
                    right_argument, = right_arguments
                    if (len(left_arguments) == 2
                            and left_arguments[1] is Ellipsis):
                        return is_subtype(left_variance, right_variance,
                                          left_arguments[0], right_argument)
                    else:
                        return all(is_subtype(left_variance, right_variance,
                                              left_argument, right_argument)
                                   for left_argument in left_arguments)
            elif left_base is type:
                assert len(left_arguments) == 1, left
                left_argument, = left_arguments
                if right_base is callable_base:
                    assert len(right_arguments) == 2, right
                    right_annotations, right_returns = right_arguments
                    if not is_subtype(left_variance, right_variance,
                                      left_argument, right_returns):
                        return False
                    elif right_annotations is Ellipsis:
                        return True
                    elif isinstance(left_argument, type):
                        from . import signatures
                        return signatures.is_subtype_of_callable_annotations(
                                signatures.from_callable(left_argument),
                                right_annotations,
                                partial(is_subtype, left_variance,
                                        right_variance)
                        )
                elif right_base is type:
                    assert len(right_arguments) == 1, right
                    right_argument, = right_arguments
                    return is_subtype(left_variance, right_variance,
                                      left_argument, right_argument)
            elif left_base is callable_base:
                assert len(left_arguments) == 2, left
                left_annotations, left_returns = left_arguments
                if right_base is callable_base:
                    assert len(right_arguments) == 2, right
                    right_annotations, right_returns = right_arguments
                    return _is_callable_subtype(
                            left_annotations, left_returns, right_annotations,
                            right_returns, left_variance, right_variance
                    )
                elif right_base is type:
                    return False
            else:
                left_arguments = _complete_arguments(left_arguments, left_base)
                right_arguments = _complete_arguments(right_arguments,
                                                      right_base)
                if (len(left_arguments) == len(right_arguments)
                        or (issubclass(left_base, abc.Mapping)
                            and len(left_arguments) == 2)
                        or left_base in (abc.AsyncGenerator, abc.Coroutine,
                                         abc.Generator)):
                    return all(is_subtype(left_variance, right_variance,
                                          left_argument, right_argument)
                               for left_argument, right_argument
                               in zip(left_arguments, right_arguments))
        elif isinstance(right, type):
            return issubclass(left_base, right)
    else:
        assert left_kind is AnnotationKind.TYPE, left_kind
        if right_kind is AnnotationKind.SPECIALIZATION:
            right_base, right_arguments = to_base(right), to_arguments(right)
            if right_base is t.ClassVar:
                return False
            elif not isinstance(right_base, type):
                pass
            elif right_base is callable_base:
                if issubclass(left, right_base):
                    return True
                assert len(right_arguments) == 2, right
                right_annotations, right_returns = right_arguments
                if not is_subtype(left_variance, right_variance, left,
                                  right_returns):
                    return False
                elif right_annotations is Ellipsis:
                    return True
                else:
                    from . import signatures
                    return signatures.is_subtype_of_callable_annotations(
                            signatures.from_callable(left), right_annotations,
                            partial(is_subtype, left_variance, right_variance)
                    )
            elif right_base is type:
                assert len(right_arguments) == 1, right
                right_argument, = right_arguments
                return is_subtype(left_variance, right_variance, left,
                                  right_argument)
            else:
                return issubclass(left, right_base)
        else:
            assert right_kind is AnnotationKind.TYPE, right_kind
            return issubclass(left, right)
    raise TypeError('Unsupported types: '
                    f'"{annotation_repr(left)}", "{annotation_repr(right)}".')


def _is_callable_subtype(
        left_annotations: t.Union[t.Sequence[Annotation], EllipsisType],
        left_returns: Annotation,
        right_annotations: t.Union[t.Sequence[Annotation], EllipsisType],
        right_returns: Annotation,
        left_variance: Variance,
        right_variance: Variance
) -> bool:
    if not is_subtype(left_variance, right_variance, left_returns,
                      right_returns):
        return False
    elif right_annotations is Ellipsis:
        return True
    elif left_annotations is Ellipsis:
        return False
    else:
        assert isinstance(left_annotations, abc.Sequence), left_annotations
        assert isinstance(right_annotations, abc.Sequence), right_annotations
        return (len(left_annotations) == len(right_annotations)
                and all(is_subtype(left_variance, right_variance,
                                   right_annotation, left_annotation)
                        for left_annotation, right_annotation
                        in zip(left_annotations, right_annotations)))


if sys.version_info < (3, 9):
    def is_generic_alias(value: t.Any) -> bool:
        return (isinstance(value, GenericAlias)
                and hasattr(value, '__getitem_inner__'))
else:
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
        return (isinstance(value, (LegacySpecialization, Specialization))
                and (to_base(value) is not t.Union
                     if to_arguments(value)
                     else to_base(value) is tuple))


def is_protocol(value: t.Any,
                _protocol_meta: t.Type[t.Any] = type(te.Protocol)) -> bool:
    return isinstance(value, _protocol_meta)


def is_type(value: t.Any) -> bool:
    return isinstance(value, type) and not is_protocol(value)


is_type_var = t.TypeVar.__instancecheck__

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


def _protocol_to_fields(
        value: t.Type[t.Any],
        fields_names_to_skip: t.Container[str] = frozenset(
                {'__abstractmethods__', '__annotations__', '__weakref__',
                 '_is_protocol', '_is_runtime_protocol', '__dict__',
                 '__args__', '__slots__', '__next_in_mro__', '__parameters__',
                 '__origin__', '__orig_bases__', '__extra__', '__tree_hash__',
                 '__doc__', '__subclasshook__', '__init__', '__new__',
                 '__module__', '_MutableMapping__marker', '_gorg'}
        )
) -> t.Dict[str, Annotation]:
    assert is_protocol(value), value
    result: t.Dict[str, Annotation] = {}
    for base in value.__mro__[:-1]:
        if base.__name__ in ('Protocol', 'Generic'):
            assert base in (te.Protocol, t.Generic), base
            continue
        result.update((name, content)
                      for name, content in vars(base).items()
                      if (not name.startswith('_abc_')
                          and name not in fields_names_to_skip))
        result.update(te.get_type_hints(base))
    return result
