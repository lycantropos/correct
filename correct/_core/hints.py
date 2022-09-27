import sys
from typing import (Any,
                    List,
                    Tuple,
                    TypeVar,
                    Union)

if sys.version_info >= (3, 9):
    from types import GenericAlias
else:
    GenericAlias: Any = type(List)
VariadicGenericAlias = type(Tuple)
assert issubclass(VariadicGenericAlias, GenericAlias)
SpecialForm = type(Any)
Annotation: Any = Union[type, GenericAlias, SpecialForm, TypeVar]
