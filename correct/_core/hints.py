import sys
import types
from typing import (Any,
                    List,
                    TypeVar,
                    Union)

GenericAlias: Any = type(List)
_T = TypeVar('_T')
LegacySpecialization: Any = type(List[_T])
del _T
if sys.version_info < (3, 9):
    Specialization: Any = LegacySpecialization
else:
    Specialization: Any = types.GenericAlias
SpecialForm = type(Any)
SpecialGenericAlias = type(List)
Annotation: Any = Union[
    type, GenericAlias, LegacySpecialization, SpecialForm, Specialization,
    TypeVar
]
