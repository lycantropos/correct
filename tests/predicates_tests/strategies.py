import typing
from itertools import repeat

from hypothesis import strategies
from hypothesis.strategies import SearchStrategy

from correct.hints import Annotation
from tests.utils import GenericAlias

plain_generic_aliases = strategies.sampled_from(
        [candidate
         for candidate in vars(typing).values()
         if (isinstance(candidate, GenericAlias)
             and hasattr(candidate, '__parameters__'))]
)


def nest_annotations(
        base: SearchStrategy[Annotation]
) -> SearchStrategy[Annotation]:
    return plain_generic_aliases.flatmap(
            lambda alias: strategies.builds(
                    alias.__getitem__,
                    strategies.tuples(*repeat(base, len(alias.__parameters__)))
            )
            if alias.__parameters__
            else base | strategies.just(alias)
    )


annotations = strategies.recursive(
        strategies.from_type(type) | plain_generic_aliases,
        nest_annotations
)
