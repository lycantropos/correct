import sys
import types
import typing as t

GenericAlias: t.Any = type(t.List)
_T = t.TypeVar('_T')
LegacySpecialization: t.Any = type(t.List[_T])
del _T
if sys.version_info < (3, 9):
    Specialization: t.Any = LegacySpecialization
else:
    Specialization: t.Any = types.GenericAlias
LegacyUnionType: t.Any = type(t.Union[float, int])
if sys.version_info < (3, 10):
    UnionType: t.Any = LegacyUnionType
else:
    UnionType: t.Any = types.UnionType
SpecialForm = type(t.Any)
Annotation: t.Any = t.Union[
    type, GenericAlias, LegacySpecialization, SpecialForm, Specialization,
    t.TypeVar
]
EllipsisType: t.Any
if sys.version_info < (3, 10):
    EllipsisType = type(Ellipsis)
else:
    EllipsisType = types.EllipsisType
