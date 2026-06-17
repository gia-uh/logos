from logos.expr import Expr

_axioms: dict[str, Expr] = {}

def register_axiom(name: str, stmt: Expr) -> None:
    if name in _axioms:
        raise ValueError(f"Axiom '{name}' already registered")
    _axioms[name] = stmt

def get_all_axioms() -> dict[str, Expr]:
    return dict(_axioms)

def clear_axioms() -> None:
    _axioms.clear()
