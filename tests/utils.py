from correct._core.hints import SpecialGenericAlias as _SpecialGenericAlias

SpecialGenericAlias = _SpecialGenericAlias


def implication(antecedent: bool, consequent: bool) -> bool:
    return not antecedent or consequent
