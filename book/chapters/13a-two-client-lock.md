---
theme: book
title: Can Two Clients Hold the Lock?
stem: two-client-lock
---

# Can Two Clients Hold the Lock?

The lock starts free. A acquires it and enters its critical section. B tries
to acquire it while A is still inside. There is no enabled acquisition for B,
so the model has no B step at that point. A releases the lock, and now B can
acquire it.

What would you have to show to rule out both clients being inside after
*any* sequence of steps, including sequences that keep handing the lock back
and forth?

**Prerequisites.** Implication and conjunction from the first proof chapters.

**Outcomes.** Declare a finite model, choose an inductive invariant, check
its three obligations, and replay a run that exposes an incorrect guard.

## Every state and every reachable state

A state records A's location, B's location and the lock owner. Either
location can be idle or critical. The owner can be free, A or B.
Those independent choices give exactly twelve tuples. In particular,
`("critical", "critical", "B")` is a state and it violates mutual
exclusion. Whether we can get there is a separate question about the steps
from the initial state.

```python {run}
from itertools import product
from pathlib import Path

from logos import LogosProofError
from logos.domains.transition_systems import FiniteTransitionSystem

idle, critical, free = "idle", "critical", "free"
locations = (idle, critical)
universe = tuple(product(locations, locations, (free, "A", "B")))
start = (idle, idle, free)
a_inside = (critical, idle, "A")
b_inside = (idle, critical, "B")
both_inside = (critical, critical, "B")

def mutually_exclusive(state):
    a, b, owner = state
    return (a, b) != (critical, critical)

print("Candidate states:", len(universe))
print("Both inside is a candidate:", both_inside in universe)
```

Take one atomic step at a time. Acquire requires the acting client to be
idle and the owner to be free. Release requires that client to be critical
and to own the lock. A step updates the acting client's location and the
owner, leaving the other client's location alone. Enumerating every source
tuple under each guard gives the entire named relation. A false guard
contributes no edge.

```python {run continue}
def declare_lock(*, allow_occupied=False):
    edges = {}
    for index, client in enumerate(("A", "B")):
        acquire, release = [], []
        for source in universe:
            location, owner = source[index], source[2]
            if location == idle and (owner == free or (client == "B" and allow_occupied)):
                target = list(source)
                target[index], target[2] = critical, client
                acquire.append((source, tuple(target)))
            if location == critical and owner == client:
                target = list(source)
                target[index], target[2] = idle, free
                release.append((source, tuple(target)))
        edges[f"{client}.acquire"] = acquire
        edges[f"{client}.release"] = release
    return FiniteTransitionSystem(universe, (start,), edges, mutually_exclusive)

lock = declare_lock()
for name, edges in lock.transitions.items():
    print(name, len(edges), "edges")
```

## Choose a set that the steps preserve

Start with three states. When the lock is free, both clients are idle.
When one owns the lock, just that client is critical. Try `A.acquire` from
each of these three states. Which ones have an edge under that name?
Which candidate state would you miss if you only checked `A.acquire`?

```python {run continue}
invariant = (start, a_inside, b_inside)
certificate = Path("two-client-lock.logos")
lock.export_safety(invariant, certificate)
lock.verify_safety(invariant, certificate)
print("Exact lock certificate verified.")
```

Write $S$ for the twelve tuples, $I$ for the chosen set, $S_0$ for
the singleton initial set, $E_t$ for the edges of each named transition
$t$, and $P$ for the mutual exclusion predicate. The certificate checks
the following conjunction, expanded over the finite tables.

1. For every $s\in S$, $s\in S_0\Rightarrow s\in I$.
2. For each transition $t$ and each $(s,u)\in E_t$,
   $s\in I\Rightarrow u\in I$. If a source has several successors under
   one name, there is a separate obligation for each successor.
3. For every $s\in S$, $s\in I\Rightarrow P(s)$.

A true table entry at index $i$ becomes $i=i$. A false entry becomes
$\neg(i=i)$. The Rust checker checks each implication using reflexivity
for a true conclusion or contradiction with a false antecedent. It
checks the assembled conjunction with zero custom axioms. Its target
also carries a SHA-256 fingerprint of the ordered universe, initial and
safety tables, and all named edge tables. `verify_safety` reconstructs
the target from the model and invariant and rejects mismatches before
replaying the evidence. The Rust checker reads the certificate. The
Python declaration supplies the finite tables, including the values of
the predicate on all twelve tuples.

To use these facts, take any finite run $s_0,\ldots,s_n$ that starts in
$S_0$ and follows a named edge at each step. By obligation 1, $s_0$ is in
$I$. If $s_k$ is in $I$, obligation 2 for the actual edge
$(s_k,s_{k+1})$ puts $s_{k+1}$ in $I$. Induction on the run length puts
$s_n$ in $I$, and obligation 3 gives $P(s_n)$. The same argument applies
to each finite prefix of an infinite run. The certificate checks the
finite premises of this argument. The induction on runs is the
mathematical argument connecting them to reachability.

These are steps of an abstract protocol. A real lock would need a
separate argument that its initial machine states and interleavings
map to this model. If a real acquisition checks the owner and updates
the lock in separate instructions, the abstract atomic edge needs
justification. This proof also does not say that B eventually acquires.

## When a step fails

Remove the free-owner requirement from B's acquire guard. B can now
overwrite A's ownership while A stays critical. Try the same trace with
both tables.

```python {run continue}
trace = (("A.acquire", a_inside), ("B.acquire", both_inside))
mutant = declare_lock(allow_occupied=True)
print("Mutant ends in violation:", mutant.replay_violation(start, trace))
try:
    lock.replay_violation(start, trace)
except ValueError as error:
    print("Correct model rejects:", error)

try:
    mutant.export_safety(invariant, Path("invalid-lock.logos"))
except LogosProofError as error:
    print(error)
```

`replay_violation` checks the start, each named edge and the final
predicate. Two acquisitions are enough to violate safety and one
cannot do so from the initial tuple. A failed closure obligation alone
says the proposed set is inadequate. Here the replay separately shows
that the mutated protocol is unsafe. If no certificate or legal
violating run has been established, the result is inconclusive.

The [standalone lock example](https://github.com/gia-uh/logos/blob/main/examples/two_client_lock.py)
exports the same model, verifies a saved certificate against it and
replays this trace.

## Exit exercise

Add an atomic `A.handoff` step from `a_inside` to `b_inside`. Keep the
four original relations and the initial state. Is the same invariant
enough? Fill in `handoff_edges` in this block and run it. To test the
obligation, try adding a second successor `both_inside` from the same
source.

```python
handoff_edges = []  # Add the edge and then try the second successor.
handoff = FiniteTransitionSystem(
    universe, (start,), {**lock.transitions, "A.handoff": handoff_edges},
    mutually_exclusive,
)
path = Path("handoff-exercise.logos")
handoff.export_safety(invariant, path)
handoff.verify_safety(invariant, path)
```

## Instructor solution

The new edge ends at `b_inside`, which already belongs to the chosen set.
The extra successor would leave the set even though the first successor
is safe.

```python {run continue}
def with_handoff(edges):
    return FiniteTransitionSystem(
        universe, (start,), {**lock.transitions, "A.handoff": edges},
        mutually_exclusive,
    )

handoff = with_handoff([(a_inside, b_inside)])
path = Path("handoff-solution.logos")
handoff.export_safety(invariant, path)
handoff.verify_safety(invariant, path)
print("Handoff solution certificate verified.")

try:
    with_handoff([(a_inside, b_inside), (a_inside, both_inside)]).export_safety(
        invariant, Path("invalid-handoff.logos"),
    )
except LogosProofError as error:
    print(error)
```
