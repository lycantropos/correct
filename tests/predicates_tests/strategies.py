import sys
import typing
from itertools import repeat

from hypothesis import strategies
from hypothesis.strategies import SearchStrategy

from correct._core.utils import to_origin
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


def nest_annotations(
        base: SearchStrategy[Annotation]
) -> SearchStrategy[Annotation]:
    return special_generic_aliases.flatmap(
            lambda alias: strategies.builds(
                    alias.__getitem__,
                    strategies.tuples(
                            *repeat(
                                    base,
                                    special_generic_alias_to_parameters_count(
                                            alias
                                    )
                            )
                    )
            )
            if special_generic_alias_to_parameters_count(alias)
            else base
    )


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

annotations = strategies.recursive(
        strategies.from_type(type) | special_generic_aliases,
        nest_annotations
)
annotations |= strategies.builds(typing.Union.__getitem__,
                                 (strategies.lists(annotations,
                                                   min_size=1)
                                  .map(tuple)))
special_generic_aliases_origins_values = {
    to_origin(alias) for alias in special_generic_aliases_values
}
plain_annotations = strategies.recursive(
        strategies.from_type(type).filter(
                lambda type_:
                type_ not in special_generic_aliases_origins_values
        ),
        nest_annotations
)
plain_annotations |= strategies.builds(typing.Union.__getitem__,
                                       (strategies.lists(plain_annotations,
                                                         min_size=1)
                                        .map(tuple)))
