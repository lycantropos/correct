from hypothesis import given

from correct.hints import Annotation
from correct.predicates import is_subtype
from . import strategies


@given(strategies.annotations, strategies.annotations)
def test_basic(first: Annotation, second: Annotation) -> None:
    result = is_subtype(first, second)

    assert isinstance(result, bool)


@given(strategies.annotations)
def test_reflexivity(annotation: Annotation) -> None:
    assert is_subtype(annotation, annotation)
