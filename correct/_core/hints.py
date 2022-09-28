from typing import (Any,
                    List,
                    TypeVar,
                    Union)

_T = TypeVar('_T')
GenericAlias: Any = type(List[_T])
del _T
SpecialForm = type(Any)
SpecialGenericAlias = type(List)
Annotation: Any = Union[type, GenericAlias, SpecialForm, TypeVar]
