import typing as _t

from paradigm.base import (OptionalParameter as _OptionalParameter,
                           OverloadedSignature as _OverloadedSignature,
                           ParameterKind as _ParameterKind,
                           PlainSignature as _PlainSignature,
                           RequiredParameter as _RequiredParameter,
                           signature_from_callable as _signature_from_callable)

from .hints import Annotation as _Annotation

_Parameter = _t.Union[_OptionalParameter, _RequiredParameter]
_Signature = _t.Union[_OverloadedSignature, _PlainSignature]


def from_callable(value: _t.Callable[..., _t.Any],
                  none_type: _t.Type[None] = type(None)) -> _Signature:
    return (_PlainSignature(returns=None)
            if value is none_type
            else _signature_from_callable(value))


def is_subtype_of(
        left: _Signature,
        right: _Signature,
        is_subtype: _t.Callable[[_Annotation, _Annotation], bool]
) -> bool:
    if isinstance(left, _OverloadedSignature):
        return all(is_subtype_of(signature, right, is_subtype)
                   for signature in left.signatures)
    else:
        assert isinstance(left, _PlainSignature), left
        if isinstance(right, _OverloadedSignature):
            return any(is_subtype_of(left, signature, is_subtype)
                       for signature in right.signatures)
        else:
            assert isinstance(right, _PlainSignature), right
            if not is_subtype(left.returns, right.returns):
                return False
            left_variadic_positional = next(
                    (parameter
                     for parameter in left.parameters
                     if parameter.kind is _ParameterKind.VARIADIC_POSITIONAL),
                    None
            )
            right_variadic_positional = next(
                    (parameter
                     for parameter in right.parameters
                     if parameter.kind is _ParameterKind.VARIADIC_POSITIONAL),
                    None
            )
            if right_variadic_positional is not None:
                if (
                        left_variadic_positional is None
                        or not is_subtype(right_variadic_positional.annotation,
                                          left_variadic_positional.annotation)
                ):
                    return False
            left_variadic_keyword = next(
                    (parameter
                     for parameter in left.parameters
                     if parameter.kind is _ParameterKind.VARIADIC_KEYWORD),
                    None
            )
            right_variadic_keyword = next(
                    (parameter
                     for parameter in right.parameters
                     if parameter.kind is _ParameterKind.VARIADIC_KEYWORD),
                    None
            )
            if right_variadic_keyword is not None:
                if (
                        left_variadic_keyword is None
                        or not is_subtype(right_variadic_keyword.annotation,
                                          left_variadic_keyword.annotation)
                ):
                    return False
            left_parameters_by_name = {
                parameter.name: parameter for parameter in left.parameters
            }
            right_parameters_by_name = {
                parameter.name: parameter for parameter in right.parameters
            }
            left_parameters_by_kind = _to_parameters_by_kind(left.parameters)
            right_parameters_by_kind = _to_parameters_by_kind(right.parameters)
            left_positionals_only = left_parameters_by_kind[
                _ParameterKind.POSITIONAL_ONLY
            ]
            left_positionals_or_keywords = left_parameters_by_kind[
                _ParameterKind.POSITIONAL_OR_KEYWORD
            ]
            right_positionals_only = right_parameters_by_kind[
                _ParameterKind.POSITIONAL_ONLY
            ]
            if len(left_positionals_only) > len(right_positionals_only):
                return False
            elif len(right_positionals_only) > (
                    len(left_positionals_only)
                    + len(left_positionals_or_keywords)
            ):
                left_positionals = [*left_positionals_only,
                                    *left_positionals_or_keywords]
                if (sum(isinstance(parameter, _OptionalParameter)
                        for parameter
                        in right_positionals_only[:len(left_positionals)])
                        > sum(isinstance(parameter, _OptionalParameter)
                              for parameter in left_positionals)):
                    return False
                if left_variadic_positional is None:
                    return False
                if not all(
                        is_subtype(right_parameter.annotation,
                                   left_parameter.annotation)
                        for left_parameter, right_parameter
                        in zip(left_positionals,
                               right_positionals_only[:len(left_positionals)])
                ) or not all(
                        is_subtype(right_parameter.annotation,
                                   left_variadic_positional.annotation)
                        for right_parameter
                        in right_positionals_only[len(left_positionals):]
                ):
                    return False
                if left_variadic_keyword is None:
                    assert right_variadic_keyword is None
                    for right_parameter in right_parameters_by_kind[
                        _ParameterKind.POSITIONAL_OR_KEYWORD
                    ]:
                        try:
                            left_parameter = left_parameters_by_name[
                                right_parameter.name
                            ]
                        except KeyError:
                            return False
                        else:
                            if (left_parameter.kind
                                    is not _ParameterKind.KEYWORD_ONLY):
                                return False
                            if not isinstance(left_parameter,
                                              _OptionalParameter):
                                return False
                            if not is_subtype(right_parameter.annotation,
                                              left_parameter.annotation):
                                return False
            else:
                left_positionals = [*left_positionals_only,
                                    *left_positionals_or_keywords]
                start_left_positionals, rest_left_positionals = (
                    left_positionals[:len(right_positionals_only)],
                    left_positionals[len(right_positionals_only):]
                )
                assert all(
                        parameter.kind is _ParameterKind.POSITIONAL_OR_KEYWORD
                        for parameter in rest_left_positionals
                ), left
                if (sum(isinstance(parameter, _OptionalParameter)
                        for parameter in right_positionals_only)
                        > sum(isinstance(parameter, _OptionalParameter)
                              for parameter in start_left_positionals)):
                    return False
                if not all(is_subtype(right_parameter.annotation,
                                      left_parameter.annotation)
                           for left_parameter, right_parameter
                           in zip(start_left_positionals,
                                  right_positionals_only)):
                    return False
                right_positionals_or_keywords = right_parameters_by_kind[
                    _ParameterKind.POSITIONAL_OR_KEYWORD
                ]
                if (len(right_positionals_or_keywords)
                        > len(rest_left_positionals)):
                    if left_variadic_positional is None:
                        return False
                    start_right_positionals_or_keywords = (
                        right_positionals_or_keywords
                        [:len(rest_left_positionals)]
                    )
                    if not all(
                            is_subtype(right_parameter.annotation,
                                       left_parameter.annotation)
                            for left_parameter, right_parameter
                            in zip(rest_left_positionals,
                                   start_right_positionals_or_keywords)
                    ):
                        return False
                    rest_right_positionals_or_keywords = (
                        right_positionals_or_keywords
                        [len(rest_left_positionals):]
                    )
                    if not all(is_subtype(right_parameter.annotation,
                                          left_variadic_positional.annotation)
                               for right_parameter
                               in rest_right_positionals_or_keywords):
                        return False
                    for right_parameter in rest_right_positionals_or_keywords:
                        try:
                            left_parameter = left_parameters_by_name[
                                right_parameter.name
                            ]
                        except KeyError:
                            if left_variadic_keyword is None:
                                return False
                            if not is_subtype(
                                    right_parameter.annotation,
                                    left_variadic_keyword.annotation
                            ):
                                return False
                        else:
                            if (left_parameter.kind
                                    is not _ParameterKind.KEYWORD_ONLY):
                                return False
                            if not isinstance(left_parameter,
                                              _OptionalParameter):
                                return False
                else:
                    start_rest_left_positionals = (
                        rest_left_positionals
                        [:len(right_positionals_or_keywords)]
                    )
                    if not all(is_subtype(right_parameter.annotation,
                                          left_parameter.annotation)
                               for left_parameter, right_parameter
                               in zip(start_rest_left_positionals,
                                      right_positionals_or_keywords)):
                        return False
                    rest_rest_left_positionals = (
                        rest_left_positionals
                        [len(right_positionals_or_keywords):]
                    )
                    if not all(
                            isinstance(parameter, _OptionalParameter)
                            for parameter in rest_rest_left_positionals
                    ):
                        return False
            if right_variadic_keyword is None:
                if not all(
                        (right_parameters_by_name[left_parameter.name].kind
                         is _ParameterKind.KEYWORD_ONLY)
                        if left_parameter.name in right_parameters_by_name
                        else isinstance(left_parameter, _OptionalParameter)
                        for left_parameter in left_parameters_by_kind[
                            _ParameterKind.KEYWORD_ONLY
                        ]
                ):
                    return False
            if left_variadic_keyword is None:
                for right_parameter in right_parameters_by_kind[
                    _ParameterKind.KEYWORD_ONLY
                ]:
                    try:
                        left_parameter = left_parameters_by_name[
                            right_parameter.name
                        ]
                    except KeyError:
                        return False
                    else:
                        if left_parameter.kind not in (
                                _ParameterKind.KEYWORD_ONLY,
                                _ParameterKind.POSITIONAL_OR_KEYWORD
                        ):
                            return False
                        if (isinstance(right_parameter, _OptionalParameter)
                                and not isinstance(left_parameter,
                                                   _OptionalParameter)):
                            return False
            return True


def is_subtype_of_callable(
        left_signature: _Signature,
        right_annotations: _t.Sequence[_Annotation],
        right_returns: _Annotation,
        is_subtype: _t.Callable[[_Annotation, _Annotation], bool]
) -> bool:
    if isinstance(left_signature, _OverloadedSignature):
        return any(is_subtype(signature.returns, right_returns)
                   and _is_plain_signature_subtype(signature,
                                                   right_annotations,
                                                   is_subtype)
                   for signature in left_signature.signatures)
    else:
        return (is_subtype(left_signature.returns, right_returns)
                and _is_plain_signature_subtype(left_signature,
                                                right_annotations,
                                                is_subtype))


def is_subtype_of_callable_annotations(
        left_signature: _Signature,
        right_annotations: _t.Sequence[_Annotation],
        is_subtype: _t.Callable[[_Annotation, _Annotation], bool]
) -> bool:
    if isinstance(left_signature, _OverloadedSignature):
        return any(_is_plain_signature_subtype(signature, right_annotations,
                                               is_subtype)
                   for signature in left_signature.signatures)
    else:
        return _is_plain_signature_subtype(left_signature, right_annotations,
                                           is_subtype)


def is_subtype_of_callable_returns(
        left_signature: _Signature,
        right_returns: _t.Sequence[_Annotation],
        is_subtype: _t.Callable[[_Annotation, _Annotation], bool]
) -> bool:
    if isinstance(left_signature, _OverloadedSignature):
        return any(is_subtype(signature.returns, right_returns)
                   for signature in left_signature.signatures)
    else:
        return is_subtype(left_signature.returns, right_returns)


def _is_plain_signature_subtype(
        left_signature: _PlainSignature,
        right_annotations: _t.Sequence[_Annotation],
        is_subtype: _t.Callable[[_Annotation, _Annotation], bool]
) -> bool:
    if not all(parameter.kind is not _ParameterKind.KEYWORD_ONLY
               or isinstance(parameter, _OptionalParameter)
               for parameter in left_signature.parameters):
        return False
    left_positionals = [
        parameter
        for parameter in left_signature.parameters
        if (parameter.kind is _ParameterKind.POSITIONAL_ONLY
            or parameter.kind is _ParameterKind.POSITIONAL_OR_KEYWORD)
    ]
    if len(left_positionals) < len(right_annotations):
        left_variadic_positional_annotation = next(
                (parameter.annotation
                 for parameter in left_signature.parameters
                 if parameter.kind is _ParameterKind.VARIADIC_POSITIONAL),
                None
        )
        return (left_variadic_positional_annotation is not None
                and all(is_subtype(annotation,
                                   left_variadic_positional_annotation)
                        for annotation
                        in right_annotations[len(left_positionals):]))
    left_annotations, left_extra_parameters = (
        [parameter.annotation
         for parameter in left_positionals[:len(right_annotations)]],
        left_positionals[len(right_annotations):]
    )
    return (all(isinstance(parameter, _OptionalParameter)
                for parameter in left_extra_parameters)
            and all(map(is_subtype, right_annotations, left_annotations)))


def _to_parameters_by_kind(
        parameters: _t.Iterable[_Parameter]
) -> _t.Mapping[_ParameterKind, _t.Sequence[_Parameter]]:
    result: _t.Dict[_ParameterKind, _t.List[_Parameter]] = {
        kind: [] for kind in _ParameterKind
    }
    for parameter in parameters:
        result[parameter.kind].append(parameter)
    return result
