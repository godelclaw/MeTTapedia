# Generic coloring theory and compositional research

The maintained library contains reusable finite-graph coloring theory and
compositional algebra. It does not establish the Four-Color Theorem.
Route-specific work on `goertzel/proofs` is a separate development.

## Maintained mathematics

`FourColor` imports `FourColor.Curriculum.Actual`: coloring and clique
obstructions, minimal and incidence-critical graphs, support transport,
finite degree and edge bounds, and explicit small-graph structure and witness
theorems. These are generic graph results; the small-graph classifications
are not a certified planar base case for the compositional Four-Color proof.

`FourColor.IntegrationCore` adds the triangulation and boundary-chain
interfaces and `FourColor.Algebra.BlockerTheorem`. The latter proves why
naive run-completion XOR additivity fails: the common run cancels, leaving
the complementary interior arcs. This counterexample delimits that model;
it does not refute every compositional proof route.

The maintained target includes both roots. Use the enclosing MeTTapedia
package and its pinned dependencies:

```sh
cd ../mettapedia
lake build FourColorCore
```

The integration validation record is
[`../mettapedia/artifacts/integration-20261028/validation.json`](../mettapedia/artifacts/integration-20261028/validation.json).
It distinguishes current-source checks from imported artifact checks and
records an admission-dependency audit of the maintained coloring roots.

## Historical research and exercises

Other files retain older proof attempts, teaching exercises and documentation
in their original locations. They are not certified by the maintained target.
The standalone Lake configuration and old status documents are historical;
the enclosing package is the qualified integration build entry point.

[`Curriculum/README.md`](Curriculum/README.md) distinguishes the maintained
subject library from incomplete exercise sheets. Unfinished exercises and
legacy research are retained as WIP, without a claim that all their theorems
have been proved or migrated.
