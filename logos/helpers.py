from logos.expr import (
    Expr, Lit, Var, Add, Sub, Mul, Div, Mod, Neg, Pow,
    Eq, Neq, Lt, Le, Gt, Ge, And, Or, Not, Implies,
    ForallNode, ExistsNode, App, CaseExpr,
)

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
        case App(name, args):
            return App(name, [substitute(a, var, val) for a in args])
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
