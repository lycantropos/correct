import sys
import typing
from functools import partial
from itertools import repeat

from hypothesis import strategies
from hypothesis.strategies import SearchStrategy

from correct._core.utils import to_base
from correct.hints import Annotation
from tests.utils import SpecialGenericAlias

special_generic_aliases_values = [
    candidate
    for candidate in vars(typing).values()
    if (isinstance(candidate, SpecialGenericAlias)
        and candidate is not typing.Callable)
]
special_generic_aliases = strategies.sampled_from(
        special_generic_aliases_values
)


def pass_to_generic_alias(
        arguments: SearchStrategy[Annotation],
        alias: SpecialGenericAlias
) -> SearchStrategy[Annotation]:
    parameters_count = special_generic_alias_to_parameters_count(alias)
    return (strategies.builds(alias.__getitem__,
                              strategies.tuples(*repeat(arguments,
                                                        parameters_count)))
            if parameters_count
            else arguments)


def nest_annotations(
        base: SearchStrategy[Annotation]
) -> SearchStrategy[Annotation]:
    return (special_generic_aliases.flatmap(partial(pass_to_generic_alias,
                                                    base))
            | strategies.builds(typing.Optional.__getitem__, base)
            | strategies.builds(typing.Union.__getitem__,
                                (strategies.lists(base,
                                                  min_size=1,
                                                  max_size=5)
                                 .map(tuple)))
            | strategies.builds(typing.Tuple.__getitem__,
                                strategies.tuples(base,
                                                  strategies.just(Ellipsis)))
            | strategies.builds(typing.Tuple.__getitem__,
                                (strategies.lists(base,
                                                  max_size=5)
                                 .map(tuple))))


if sys.version_info >= (3, 9):
    def special_generic_alias_to_parameters_count(
            value: SpecialGenericAlias
    ) -> int:
        return value._nparams
else:
    def special_generic_alias_to_parameters_count(
            value: SpecialGenericAlias
    ) -> int:
        return len(value.__parameters__)

special_generic_aliases_origins_values = {
    to_base(alias) for alias in special_generic_aliases_values
}


def is_not_special_generic_alias_origin(value: type) -> bool:
    return value not in special_generic_aliases_origins_values


plain_static_annotations = strategies.recursive(
        strategies.from_type(type).filter(is_not_special_generic_alias_origin),
        nest_annotations
)
type_variables_names = strategies.text()


def to_variable_annotations(
        static_annotations: SearchStrategy[Annotation]
) -> SearchStrategy[Annotation]:
    return (strategies.builds(typing.TypeVar, type_variables_names,
                              bound=static_annotations)
            | strategies.builds(typing.TypeVar, type_variables_names,
                                bound=static_annotations,
                                contravariant=strategies.booleans())
            | strategies.builds(typing.TypeVar, type_variables_names,
                                bound=static_annotations,
                                covariant=strategies.booleans()))


plain_annotations = strategies.recursive(
        plain_static_annotations
        | to_variable_annotations(plain_static_annotations),
        nest_annotations,
        max_leaves=3
)
annotations = strategies.recursive(
        plain_annotations
        | special_generic_aliases
        | to_variable_annotations(special_generic_aliases),
        nest_annotations,
        max_leaves=3
)
