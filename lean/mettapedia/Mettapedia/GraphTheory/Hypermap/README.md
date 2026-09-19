# Hypermap theory and its rotation-system adapters

Use the smallest layer needed by a consumer:

| Module | Mathematical content |
| --- | --- |
| `Basic` | Three permutations, their cancellation law, Euler defect, forgetful map from rotation systems |
| `Connectivity` | Component count, redundant generators, rotation/edge reachability dictionary |
| `Euler` | Euler inequality, parity, genus and its relation to planarity |
| `GenusAdditivity` | Arithmetic of gluing counts and disjoint unions |
| `Patch` | Border-ring hypotheses; derived counting, genus and planarity laws |
| `Jordan.Curve` | Equivalence of hypermap planarity and the combinatorial Jordan property |

The generic theory follows the hypermap approach of the Coq fourcolor
development. Its existing Lean proofs use this repository's permutation
machinery; this is not an import of the classical Four-Colour proof.

## Representation boundaries

`ofRotationSystem` forgets labels and the chosen outer dart. It is not an
equivalence with arbitrary hypermaps. In particular, displayed vertex labels
correspond to node orbits only when the vertex map is onto and each vertex
fiber is one rotation cycle. Edge involutivity and the absence of fixed points
are additional restrictions not imposed on general hypermaps.

`ofRotationSystem_reachable_iff` and `compCount_ofRotationSystem` identify the
three-generator hypermap connectivity with rotation/edge connectivity without
assuming vertex cyclicity. The further identification with connectedness of
the displayed primal graph does require cyclicity.

The sign convention is explicit: `eulerDefect` is minus twice genus.
Other modules' nonnegative Euler defects must be transported by a proved
identity, not identified by name.

## Existing consumers and remaining integration

`FourColor.GoertzelV24ConnectedMapEulerBound` now derives its connected-map
Euler inequality from `Hypermap.eulerLhs_le_eulerRhs`. Its presentation-neutral
walk lifting is also used by `GoertzelV24StellarDualStructure`, replacing a
second walk induction while preserving the old theorem interfaces.

The ring-patching theorems have a nondegenerate consumer in `PatchExample`.
Applying them to a route cut still requires constructing the actual `Patch`
data. Neither a general hypermap theorem nor an example supplies that adapter.
Similarly, a categorical composition law alone does not supply finite-state
coverage, replacement soundness, or the route's generating-base audit.

Some generic foundations still live under `FourColor`. Extract them when a
specific dependency requires it, preserving public APIs and rebuilding the
consumers; directory names alone are not a reason for a mass migration.
