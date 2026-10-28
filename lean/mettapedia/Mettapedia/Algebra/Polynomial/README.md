# Polynomial certificate mathematics

These modules state why a polynomial refutation certificate is sound. They do
not trust the search program that found it, and contain no fixed Krenn support
census or generated case tree.

| Module | Content |
|---|---|
| `Certificate.UnitCombination` | Extend a selected family by zero; a unit combination excludes a common zero |
| `Certificate.Sparse` | Evaluation and soundness of sparse integer-coefficient certificates |
| `Certificate.CoordinateSplit` | Exhaustive zero/invertible coordinate branches and sound refutation trees |
| `Certificate.EquationSplit` | Restriction and extension of common zeros through equation-system splits |
| `Certificate.BinomialRelations` | Exponent balance and cancellation of active signed relation chains |
| `Certificate.Multilinear` | Four sound multilinear elimination rules and a finite postorder trace checker |
| `Certificate.Transversal` | Cofactor elimination of a transversal term |
| `LaurentMonomial` | Integer exponent composition and normalization from an integer right inverse |

The original certificate reflection, carrier splitting, lattice combination
and multilinear trace modules supply the generic mathematics extracted here.
Their problem-specific data and assembly remain with the search corpus.

The algebraic hypotheses are attached to each theorem. In particular the
multilinear trace's integer-coefficient contradiction rule uses a characteristic
zero field; Laurent normalization does not assume the existence of roots.

Import `Mettapedia.Algebra.Polynomial` for the family. The matching family's
`GHZ.AxiomAudit` imports this umbrella and checks its transitive axioms too.
