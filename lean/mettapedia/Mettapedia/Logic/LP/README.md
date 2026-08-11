# LP Kernel

A *logic program* answers a query by searching for a proof: you give it facts and
rules ("`grandparent(X,Z)` if `parent(X,Y)` and `parent(Y,Z)`") and ask "who are
the grandparents?", and the engine *derives* the answers. This directory is the
verified core of that idea and the canonical executable runtime being extended
to host pinned PeTTa's Prolog sources directly. It is built in Lean 4 so that
local mechanism guarantees are *proven*, not just tested.

Two pillars make a logic-programming engine trustworthy, and both are formalized
here with proofs:

- **Unification** — the algorithm that decides whether two terms (say `f(X, b)`
  and `f(a, Y)`) can be made syntactically equal, and finds the *most general* way
  to do so (here `X := a`, `Y := b`). This kernel proves the Martelli-Montanari
  algorithm correct *and complete*: if a unifier exists at all, the algorithm finds
  one (assumption-free completeness).
- **Meaning vs. search** — a program has a *declarative* meaning (its least
  Herbrand model, the smallest set of facts consistent with the rules, built as a
  least fixpoint of the immediate-consequence operator `T_P` via Tarski's theorem)
  and an *operational* behaviour (SLD resolution, the actual proof search). The
  kernel ties the two together and ships an executable, fuel-bounded search.

Everything in this directory builds with zero `sorry`s.

Import via `Mettapedia.Logic.LP` ([LP.lean](../LP.lean)).

## Build

```bash
# from repository root
lake build Mettapedia.Logic.LP
```

## Modules

### Core

| Module | What it does |
|--------|-------------|
| [Core.lean](Core.lean) | Terms, atoms, clauses, knowledge bases |
| [Substitution.lean](Substitution.lean) | Substitution application and composition |
| [Matching.lean](Matching.lean) | One-way pattern matching |
| [Semantics.lean](Semantics.lean) | $T_P$ operator, Herbrand interpretations, least Herbrand model |

### Unification

| Module | What it does |
|--------|-------------|
| [Unification.lean](Unification.lean) | Fuel-bounded unification algorithm |
| [UnificationMGU.lean](UnificationMGU.lean) | Most general unifier properties |
| [UnificationComplete.lean](UnificationComplete.lean) | Assumption-free completeness: semantic unifiability implies algorithmic success |

### SLD resolution

| Module | What it does |
|--------|-------------|
| [SLD.lean](SLD.lean) | SLD derivation relation |
| [SLDCompute.lean](SLDCompute.lean) | Executable SLD search with fuel |
| [SLDAll.lean](SLDAll.lean) | All-solutions SLD (collecting all answer substitutions) |
| [SLDCompletenessKit.lean](SLDCompletenessKit.lean) | Completeness infrastructure: SLD finds all LHM members |
| [SLDCompletenessCanaries.lean](SLDCompletenessCanaries.lean) | Canary theorems exercising completeness |
| [UnificationCompletenessCanaries.lean](UnificationCompletenessCanaries.lean) | Canary theorems exercising unification completeness |

### Executable Prolog runtime

| Module | What it does |
|--------|-------------|
| [StandardizeApart.lean](StandardizeApart.lean) | Typed activation scopes and variable-disjoint clause copies |
| [RuntimeTerm.lean](RuntimeTerm.lean) | Checked rational-term heap, destructive bindings, trail, and exact rollback |
| [RuntimeUnification.lean](RuntimeUnification.lean) | Resumable transactional graph unification with cycle-pair memoization |
| [RuntimeMaterialize.lean](RuntimeMaterialize.lean) | Checked allocation of source queries and standardized clauses into the graph heap |
| [RuntimeQuery.lean](RuntimeQuery.lean) | Demand-driven source-order DFS, clause retry, resumable answers, cleanup, and predicate-scoped cut |
| [RuntimeQueryConservation.lean](RuntimeQueryConservation.lean) | Generic conservation certificate for query opening, shared-machine steps, and finite pull prefixes across language representations |

The runtime modules operate on the same `Core.lean` terms, atoms, clauses, and
programs as the LP kernel. They are one implementation, not a PeTTa-specific
compiler or a second semantic machine. The current executable boundary is the
pure static-clause fragment with cut; dynamic predicates, the source loader,
exceptions, attributed variables, and the built-ins required by PeTTa remain
explicitly incomplete. Runtime regressions exercise exact observable behavior,
while reusable Lean theorems state local heap, rollback, materialization, and
control properties. SWI compatibility is tracked separately in the
[hash-pinned provenance manifest](../Prolog/SWI/SWI_PROVENANCE.json).

### Fragments and extensions

| Module | What it does |
|--------|-------------|
| [FunctionFree.lean](FunctionFree.lean) | Function-free fragment with finite evaluation guarantees |
| [FunctionFreeEvaluation.lean](FunctionFreeEvaluation.lean) | Evaluation in the function-free fragment |
| [FunctionFreePeTTa.lean](FunctionFreePeTTa.lean) | PeTTa-specific function-free specialization |
| [RangeRestriction.lean](RangeRestriction.lean) | Range-restricted clauses and unit-KB LHM characterization |
| [MMMeasure.lean](MMMeasure.lean) | Term-size measure for well-founded recursion |
| [Stratification.lean](Stratification.lean) | Stratified fixpoint semantics for normal programs with negation-as-failure (per-stratum `OrderHom.lfp`) |
| [NormalGrounding.lean](NormalGrounding.lean) | First-order normal (ProbLog-style) clauses grounded and evaluated via the stratified semantics |
| [PrologInstance.lean](PrologInstance.lean) | A concrete `LPSignature` showing the kernel models standard Prolog (function symbols, compound terms, recursion) |

### Bridges

| Module | What it does |
|--------|-------------|
| [MeTTaILBridge.lean](MeTTaILBridge.lean) | `DeclReduces` implies LHM membership |
| [WorldModelBridge.lean](WorldModelBridge.lean) | LP knowledge base as PLN world-model instance |
| [PathMapBridge.lean](PathMapBridge.lean) | PathMap lattice operations as LP queries |
| [OSLFBridge.lean](OSLFBridge.lean) | OSLF language instance for LP |
| [CertifyingDatalogBridge.lean](CertifyingDatalogBridge.lean) | Bridge to certifying Datalog evaluation |
| [Provenance.lean](Provenance.lean) | Derivation provenance tracking |

### ATP / chainer

| Module | What it does |
|--------|-------------|
| [PropositionalChainer.lean](PropositionalChainer.lean) | Propositional forward/backward chainer |
| [BackwardViaForward.lean](BackwardViaForward.lean) | Backward chaining compiled to forward saturation (Magic-Sets-style demand transformation) |
| [PropositionalConnectionChainer.lean](PropositionalConnectionChainer.lean) | Propositional connection tableau with DFS and witness completeness |
| [FirstOrderConnectionTrace.lean](FirstOrderConnectionTrace.lean) | First-order connection traces with substitutions |

## Related

- [PeTTa layer](../../Languages/MeTTa/PeTTa) — evaluation, effects, OSLF instance
- [Prolog layer](../Prolog) — goal language, cut, ISO conformance

## Formalization status

All `.lean` files in this directory are `sorry`-free. The headline results are
proven, not assumed: unification correctness and assumption-free completeness
(`UnificationMGU.lean`, `UnificationComplete.lean`), monotonicity of `T_P` and the
least-Herbrand-model construction via `OrderHom.lfp` / Tarski (`Semantics.lean`),
and the SLD completeness kit (`SLDCompletenessKit.lean`), with canary theorems
exercising both completeness lanes.

**Trusted base.** There are no source-level `axiom` declarations in this directory
(a source grep, *not* a per-theorem `#print axioms` audit — definitions and proofs
built on Mathlib may inherit standard Mathlib axioms such as `propext`,
`Quot.sound`, and `Classical.choice` transitively; the `T_P` operator is
`noncomputable` and uses Mathlib's order-theoretic fixpoint machinery). Nothing in
this directory uses `native_decide`, so no `.lean` file here enlarges the trusted
base via compile-time evaluation.

## References

- M. H. van Emden & R. A. Kowalski, "The Semantics of Predicate Logic as a Programming Language," [*Journal of the ACM* 23(4), 1976, pp. 733-742](https://dl.acm.org/doi/10.1145/321978.321991) — the `T_P` operator and the least-Herbrand-model fixpoint semantics.
- John W. Lloyd, [*Foundations of Logic Programming*](https://link.springer.com/book/10.1007/978-3-642-83189-8) (Springer, 2nd ed. 1987) — the standard reference for Herbrand models, SLD resolution, and the Datalog/function-free fragment.
- Alberto Martelli & Ugo Montanari, "An Efficient Unification Algorithm," [*ACM Transactions on Programming Languages and Systems* 4(2), 1982, pp. 258-282](https://dl.acm.org/doi/10.1145/357162.357169) — the unification algorithm formalized in `Unification.lean`.

---
*Status updated 2026-08-04; executable-runtime scope is intentionally partial.*
