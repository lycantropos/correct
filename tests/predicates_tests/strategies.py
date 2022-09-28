import sys
import typing
from itertools import repeat

from hypothesis import strategies
from hypothesis.strategies import SearchStrategy

from correct.hints import Annotation
from tests.utils import SpecialGenericAlias

special_generic_aliases = strategies.sampled_from(
        [candidate
         for candidate in vars(typing).values()
         if isinstance(candidate, SpecialGenericAlias)]
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
            else base | strategies.just(alias)
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
