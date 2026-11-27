from logos.expr import (
    Expr, Lit, Var, Add, Sub, Mul, Div, Mod, Neg, Pow, Len, Nth, Sorted,
    Eq, Neq, Lt, Le, Gt, Ge, And, Or, Not, Implies,
    ForallNode, ExistsNode, App, CaseExpr,
)

def normalize_order(expr: Expr) -> Expr:
    """Rewrite ``>``, ``>=`` and ``!=`` into the portable core forms."""
    match expr:
        case Gt(left, right):
            return Lt(normalize_order(right), normalize_order(left))
        case Ge(left, right):
            return Le(normalize_order(right), normalize_order(left))
        case Neq(left, right):
            return Not(Eq(normalize_order(left), normalize_order(right)))
        case Add(left, right) | Sub(left, right) | Mul(left, right) | Div(left, right) | Eq(left, right) | Le(left, right) | Lt(left, right) | And(left, right) | Or(left, right) | Implies(left, right):
            return type(expr)(normalize_order(left), normalize_order(right))
        case Neg(operand) | Not(operand):
            return type(expr)(normalize_order(operand))
        case Pow(base, exponent):
            return Pow(normalize_order(base), normalize_order(exponent))
        case ForallNode(var, body):
            return ForallNode(var, normalize_order(body))
        case ExistsNode(var, body):
            return ExistsNode(var, normalize_order(body))
        case App(name, args, symbol):
            return App(name, [normalize_order(arg) for arg in args], symbol)
        case CaseExpr(branches):
            return CaseExpr([(normalize_order(cond), normalize_order(value)) for cond, value in branches])
        case Len(seq):
            return Len(normalize_order(seq))
        case Nth(seq, index):
            return Nth(normalize_order(seq), normalize_order(index))
        case Sorted(seq):
            return Sorted(normalize_order(seq))
        case _:
            return expr


def structural_eq(a: Expr, b: Expr) -> bool:
    if type(a) is not type(b):
        return False
    match a, b:
        case Lit(v1), Lit(v2):           return v1 == v2
        case Var(n1, t1), Var(n2, t2):   return n1 == n2 and t1 is t2
        case Add(l1,r1), Add(l2,r2):     return structural_eq(l1,l2) and structural_eq(r1,r2)
        case Sub(l1,r1), Sub(l2,r2):     return structural_eq(l1,l2) and structural_eq(r1,r2)
        case Mul(l1,r1), Mul(l2,r2):     return structural_eq(l1,l2) and structural_eq(r1,r2)
        case Div(l1,r1), Div(l2,r2):     return structural_eq(l1,l2) and structural_eq(r1,r2)
        case Len(s1),    Len(s2):        return structural_eq(s1, s2)
        case Nth(s1,i1), Nth(s2,i2):     return structural_eq(s1,s2) and structural_eq(i1,i2)
        case Sorted(s1), Sorted(s2):     return structural_eq(s1, s2)
        case Mod(l1,r1), Mod(l2,r2):     return structural_eq(l1,l2) and structural_eq(r1,r2)
        case Neg(o1),    Neg(o2):         return structural_eq(o1, o2)
        case Pow(b1,e1), Pow(b2,e2):     return structural_eq(b1,b2) and structural_eq(e1,e2)
        case Eq(l1,r1),  Eq(l2,r2):      return structural_eq(l1,l2) and structural_eq(r1,r2)
        case Neq(l1,r1), Neq(l2,r2):    return structural_eq(l1,l2) and structural_eq(r1,r2)
        case Lt(l1,r1),  Lt(l2,r2):      return structural_eq(l1,l2) and structural_eq(r1,r2)
        case Le(l1,r1),  Le(l2,r2):      return structural_eq(l1,l2) and structural_eq(r1,r2)
        case Gt(l1,r1),  Gt(l2,r2):      return structural_eq(l1,l2) and structural_eq(r1,r2)
        case Ge(l1,r1),  Ge(l2,r2):      return structural_eq(l1,l2) and structural_eq(r1,r2)
        case And(l1,r1), And(l2,r2):     return structural_eq(l1,l2) and structural_eq(r1,r2)
        case Or(l1,r1),  Or(l2,r2):      return structural_eq(l1,l2) and structural_eq(r1,r2)
        case Not(o1),    Not(o2):         return structural_eq(o1, o2)
        case Implies(a1,c1), Implies(a2,c2): return structural_eq(a1,a2) and structural_eq(c1,c2)
        case ForallNode(v1,b1), ForallNode(v2,b2):
            return structural_eq(v1,v2) and structural_eq(b1,b2)
        case ExistsNode(v1,b1), ExistsNode(v2,b2):
            return structural_eq(v1,v2) and structural_eq(b1,b2)
        case App(f1,args1), App(f2,args2):
            return f1 == f2 and len(args1)==len(args2) and all(structural_eq(a,b) for a,b in zip(args1,args2))
        case CaseExpr(branches1), CaseExpr(branches2):
            return (len(branches1) == len(branches2) and
                    all(structural_eq(c1, c2) and structural_eq(v1, v2)
                        for (c1, v1), (c2, v2) in zip(branches1, branches2)))
        case _:
            return False

def substitute(expr: Expr, var: Var, val: Expr) -> Expr:
    """Replace all free occurrences of `var` in `expr` with `val`."""
    match expr:
        case Var(name, _) if name == var.name:
            return val
        case Var():
            return expr
        case Lit():
            return expr
        case ForallNode(v, body):
            if v.name == var.name:
                return expr  # var is bound here; stop
            return ForallNode(v, substitute(body, var, val))
        case ExistsNode(v, body):
            if v.name == var.name:
                return expr
            return ExistsNode(v, substitute(body, var, val))
        case App(name, args, symbol):
            return App(name, [substitute(a, var, val) for a in args], symbol)
        case CaseExpr(branches):
            new_branches = [(substitute(cond, var, val), substitute(result, var, val))
                            for cond, result in branches]
            return CaseExpr(new_branches)
        case _:
            # For all binary/unary nodes: recurse on children
            cls = type(expr)
            fields = [getattr(expr, f) for f in expr.__dataclass_fields__]
            new_fields = [substitute(f, var, val) if isinstance(f, Expr) else f for f in fields]
            return cls(*new_fields)

def free_symbol_ids(expr: Expr) -> set[int]:
    match expr:
        case Var():
            return {id(expr)}
        case Lit():
            return set()
        case ForallNode(var, body) | ExistsNode(var, body):
            return free_symbol_ids(body) - {id(var)}
        case App(_, args):
            return set().union(*(free_symbol_ids(arg) for arg in args))
        case CaseExpr(branches):
            return set().union(*(free_symbol_ids(part) for branch in branches for part in branch))
        case _:
            fields = (getattr(expr, name) for name in expr.__dataclass_fields__)
            return set().union(*(free_symbol_ids(field) for field in fields if isinstance(field, Expr)))


def substitute_symbols(expr: Expr, replacements: dict[int, Expr]) -> Expr:
    """Substitute by object identity, dropping mappings for shadowed binders."""
    match expr:
        case Var():
            return replacements.get(id(expr), expr)
        case Lit():
            return expr
        case ForallNode(var, body) | ExistsNode(var, body):
            remaining = {key: value for key, value in replacements.items() if key != id(var)}
            if any(id(var) in free_symbol_ids(value) for value in remaining.values()):
                fresh = Var(var.name, var.type)
                remaining[id(var)] = fresh
                var = fresh
            return type(expr)(var, substitute_symbols(body, remaining))
        case App(name, args, symbol):
            return App(name, [substitute_symbols(arg, replacements) for arg in args], symbol)
        case CaseExpr(branches):
            return CaseExpr([
                (substitute_symbols(cond, replacements), substitute_symbols(value, replacements))
                for cond, value in branches
            ])
        case _:
            fields = (getattr(expr, name) for name in expr.__dataclass_fields__)
            return type(expr)(*(substitute_symbols(field, replacements)
                                if isinstance(field, Expr) else field for field in fields))


def try_unify(pattern: Expr, target: Expr, flex_vars: set) -> "dict | None":
    """Match pattern against target with flex_vars as unifiable variables.
    Returns substitution dict (possibly empty) or None on failure."""
    if isinstance(pattern, Var) and pattern.name in flex_vars:
        return {pattern.name: target}
    if type(pattern) is not type(target):
        return None
    match pattern, target:
        case Lit(v1), Lit(v2):
            return {} if v1 == v2 else None
        case Var(n1, t1), Var(n2, t2):
            return {} if n1 == n2 and t1 is t2 else None
        case App(f1, args1), App(f2, args2):
            if f1 != f2 or len(args1) != len(args2):
                return None
            return _merge_subs([try_unify(a, b, flex_vars) for a, b in zip(args1, args2)])
        case CaseExpr(branches1), CaseExpr(branches2):
            if len(branches1) != len(branches2):
                return None
            subs = []
            for (c1, v1), (c2, v2) in zip(branches1, branches2):
                subs.extend([try_unify(c1, c2, flex_vars), try_unify(v1, v2, flex_vars)])
            return _merge_subs(subs)
        case _:
            cls = type(pattern)
            if not hasattr(cls, "__dataclass_fields__"):
                return None
            subs = []
            for fname in cls.__dataclass_fields__:
                pf = getattr(pattern, fname)
                tf = getattr(target, fname)
                if isinstance(pf, Expr):
                    subs.append(try_unify(pf, tf, flex_vars))
                elif pf != tf:
                    return None
            return _merge_subs(subs)


def _merge_subs(subs: list) -> "dict | None":
    result: dict = {}
    for sub in subs:
        if sub is None:
            return None
        for k, v in sub.items():
            if k in result and not structural_eq(result[k], v):
                return None
            result[k] = v
    return result


def free_vars(expr: Expr) -> set[str]:
    match expr:
        case Var(name, _):    return {name}
        case Lit():           return set()
        case ForallNode(v,b): return free_vars(b) - {v.name}
        case ExistsNode(v,b): return free_vars(b) - {v.name}
        case App(_, args):    return set().union(*(free_vars(a) for a in args))
        case CaseExpr(branches):
            result = set()
            for cond, val in branches:
                result |= free_vars(cond) | free_vars(val)
            return result
        case _:
            result = set()
            for f in expr.__dataclass_fields__:
                val = getattr(expr, f)
                if isinstance(val, Expr):
                    result |= free_vars(val)
            return result
