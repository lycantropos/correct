import typing as t

from hypothesis import given

from correct.hints import Annotation
from correct.predicates import is_subtype
from tests.utils import implication
from . import strategies


@given(strategies.annotations, strategies.annotations)
def test_basic(first: Annotation, second: Annotation) -> None:
    result = is_subtype(first, second)

    assert isinstance(result, bool)


@given(strategies.annotations)
def test_minimal_element(annotation: Annotation) -> None:
    assert is_subtype(t.Any, annotation)


@given(strategies.annotations)
def test_maximal_element(annotation: Annotation) -> None:
    assert is_subtype(annotation, t.Any)


@given(strategies.annotations)
def test_reflexivity(annotation: Annotation) -> None:
    assert is_subtype(annotation, annotation)


@given(strategies.plain_annotations, strategies.plain_annotations,
       strategies.plain_annotations)
def test_transitivity(first: Annotation,
                      second: Annotation,
                      third: Annotation) -> None:
    assert implication(is_subtype(first, second) and is_subtype(second, third),
                       is_subtype(first, third))
