from correct._core.hints import GenericAlias as _GenericAlias

GenericAlias = _GenericAlias


def implication(antecedent: bool, consequent: bool) -> bool:
    return not antecedent or consequent
