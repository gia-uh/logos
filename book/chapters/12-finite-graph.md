---
theme: book
title: A Finite Graph You Can Audit
stem: finite-graph
---

# A Finite Graph You Can Audit

A graph is a set of vertices and a relation on them. The relation can be written as a table, and a table can be written as a disjunction. That is the whole representation used in this chapter: five vertices, five directed edges, and one order on the vertices. The order is not decoration. It is an invariant that every edge must respect, and the invariant composes along a path.

The result is small enough to read in one page and strong enough to rule out cycles. It is also a deliberate limit: the chapter builds one concrete finite relation, not a graph library. There is no reachability operator, no generic graph kernel and no claim that an arbitrary graph can be checked this way.

## Before you start

**Prerequisites.** Chapters 4 and 6: `p.assume`, `p.cases`, `p.linear`, `p.order`, `p.apply`, `p.negate` and transparent definitions.

**Outcomes.** You will encode a finite relation as a disjunction, prove a structural invariant by exhaustive cases, derive two consequences of that invariant, and compose it along a path of two edges.

## The graph is a finite table

The vertices are $0, 1, 2, 3, 4$. The directed edges are

$$0 \to 1,\quad 0 \to 2,\quad 1 \to 3,\quad 2 \to 3,\quad 3 \to 4.$$

The edge relation is a definition whose body is exactly that table. Each disjunct is one row. The right-associated shape is not mathematically important; it keeps the case analysis in the order the rows are written.

```python {run}
import logos
from logos import Int


@logos.definition
def edge(u: Int, v: Int):
    """The five directed edges of the finite graph on 0, 1, 2, 3 and 4."""
    return (
        ((u == 0) & (v == 1))
        | (((u == 0) & (v == 2))
           | (((u == 1) & (v == 3))
              | (((u == 2) & (v == 3))
                 | ((u == 3) & (v == 4)))))
    )
```

Calling `edge(0, 1)` with symbolic arguments builds an application node. The checker can unfold the definition to the table. Calling it with ordinary integers runs the Python body, which is why the same name can be used as a predicate and as a test.

A graph is finite here because the table names every edge. There is no quantifier over an unknown adjacency relation. If a row is missing, the graph is a different graph, and the checker will not invent the missing edge.

## The order is an invariant

The vertices are already ordered as integers. The first structural lemma says that every row of the table respects that order.

$$\operatorname{edge}(u,v) \Rightarrow u < v.$$

The proof is exhaustive case analysis. Each branch receives one conjunction $u = a \land v = b$; linear arithmetic turns it into $u < v$. The helper `close` keeps the five branches from repeating the same two lines.

```python {run continue}
@logos.theorem
def every_edge_goes_up(u: Int, v: Int):
    """Every edge goes from a lower vertex to a higher one."""
    return edge(u, v) >> (u < v)


@every_edge_goes_up.proof
def prove_every_edge(p, u, v):
    """Open each row of the table and close it with linear arithmetic."""
    e = p.assume(edge(u, v))

    def close(branch, pair):
        branch.finish(p.linear(u < v, using=[pair.left(), pair.right()]))

    with p.cases(e) as c1:
        with c1.left() as e1:
            close(c1, e1)
        with c1.right() as rest1:
            with p.cases(rest1) as c2:
                with c2.left() as e2:
                    close(c2, e2)
                with c2.right() as rest2:
                    with p.cases(rest2) as c3:
                        with c3.left() as e3:
                            close(c3, e3)
                        with c3.right() as rest3:
                            with p.cases(rest3) as c4:
                                with c4.left() as e4:
                                    close(c4, e4)
                                with c4.right() as e5:
                                    close(c4, e5)
                            c3.finish(c4.result)
                    c2.finish(c3.result)
            c1.finish(c2.result)
    return c1.result
```

Read the nesting from the inside out. `p.cases(e)` splits the first row from the remaining four. The right branch is itself a disjunction, so it is split again. At the last branch, `e5` is the conjunction $u = 3 \land v = 4$. `close` projects both equalities and asks `p.linear` for $u < v$.

The checker does not know that this graph is acyclic. It only knows the five rows. The conclusion is true because every row was checked, not because the graph was given a special status.

## Consequences of the invariant

Two familiar facts follow without another case analysis.

A vertex has no edge to itself. If it did, the invariant would say $u < u$, which is false.

```python {run continue}
@logos.theorem
def no_self_loop(u: Int):
    """No vertex has an edge to itself."""
    return ~edge(u, u)


@no_self_loop.proof
def prove_no_self_loop(p, u):
    """The invariant would give u < u."""
    with p.negate() as suppose:
        up = p.apply(every_edge_goes_up, u, u, suppose.assumption)
        clash = p.order("lt_irrefl", u)
        suppose.finish(p.not_elim(clash, up))
    return suppose.result
```

Two opposite edges cannot both belong to the graph. The first gives $u < v$, the second gives $v < u$, and linear arithmetic finds the contradiction.

```python {run continue}
@logos.theorem
def no_two_cycle(u: Int, v: Int):
    """Two opposite edges cannot both belong to the graph."""
    return ~(edge(u, v) & edge(v, u))


@no_two_cycle.proof
def prove_no_two_cycle(p, u, v):
    """The two edges force opposite strict inequalities."""
    with p.negate() as suppose:
        both = suppose.assumption
        up = p.apply(every_edge_goes_up, u, v, both.left())
        down = p.apply(every_edge_goes_up, v, u, both.right())
        clash = p.linear(False, using=[up, down])
        suppose.finish(clash)
    return suppose.result
```

Neither proof repeats the table. Both cite `every_edge_goes_up` by name, so a change to the table invalidates the lemma and, through it, the consequences.

## The invariant composes along a path

An edge is one step. A path of two edges is two steps, and the order invariant survives the composition: if $u < v$ and $v < w$, then $u < w$. This is the checked order law `lt_trans`, not a new graph rule.

```python {run continue}
@logos.theorem
def every_two_step_path_goes_up(u: Int, v: Int, w: Int):
    """Two edges in sequence still go from a lower vertex to a higher one."""
    return (edge(u, v) & edge(v, w)) >> (u < w)


@every_two_step_path_goes_up.proof
def prove_two_step(p, u, v, w):
    """Apply the edge invariant twice and compose the strict inequalities."""
    e = p.assume(edge(u, v) & edge(v, w))
    first = p.apply(every_edge_goes_up, u, v, e.left())
    second = p.apply(every_edge_goes_up, v, w, e.right())
    return p.order("lt_trans", u, v, w, using=[first, second])
```

The composition is the reason a cycle cannot hide behind a longer path. Each step raises the vertex, and a finite order cannot rise forever. The chapter proves the two-step case; the same argument repeats for any finite number of steps, but the book does not add a general path quantifier to the logic.

Check the four theorems.

```python {run continue}
for theorem in (
    every_edge_goes_up,
    no_self_loop,
    no_two_cycle,
    every_two_step_path_goes_up,
):
    theorem.check()
    print(f"{theorem.name}: {theorem.certified}")
```

The output is four receipts from the checker. Each certificate cites only transparent definitions, case analysis, linear arithmetic and the order laws; there is no custom axiom and no graph-specific primitive.

## When a step fails

Add a descending row to the table:

```python
| ((u == 3) & (v == 1))
```

The graph then has the edge $3 \to 1$. The statement `every_edge_goes_up` is false, and the proof fails in the last branch. The diagnostic names the branch and the arithmetic obligation:

```text
Theorem 'every_edge_goes_up': linear arithmetic could not derive the goal from these facts
  expected goal: u < v
  hypotheses in scope:
    case3: u = 3 & v = 1
  failing source: branch.finish(p.linear(u < v, using=[pair.left(), pair.right()]))
```

The message does not say that graph theory is incomplete. It says that the facts $u = 3$ and $v = 1$ do not imply $u < v$. Remove the row and the same proof closes every branch again. This is the practical difference between a checked invariant and a table that merely looks acyclic.

## Exit exercise

Add the edge $0 \to 4$ to the table. Prove that `every_edge_goes_up` still holds, then state and prove

$$\neg(\operatorname{edge}(0,4) \land \operatorname{edge}(4,0)).$$

The second proof should not reopen the table. It should apply the first lemma twice, exactly as `no_two_cycle` does. If you find yourself writing another five-way case split, the invariant is doing less work than it should.

As a second exercise, remove the edge $2 \to 3$. Which of the four theorems still hold? Check each one. The structural lemmas are about the table as written; changing the table changes the subject, and the checker will tell you which proofs no longer apply.
