# GHZ weighted matching equations

This family studies three-color weighted perfect-matching equations and their
characteristic-two and fermionic variants. General matching mathematics stays
in the parent `Matching` family; polynomial certificate semantics live in
`Algebra/Polynomial`.

## Claim boundary

`GHZ.Configuration.isGHZ` requires nonzero constant-color amplitudes and zero
mixed-color amplitudes. `GHZ.OfficialBridge` relates these equations to the
normalized official statement in `MonochromaticQuantumGraph.EqSystemN`.

The arbitrary-size complex Krenn–Gu conjecture remains open. The conditional
reductions retain their structural hypotheses, including the descent and
six-vertex obligations. They do not turn those obligations into assumptions
hidden in a definition. `GHZ.Configuration.conjecture_iff_descent_and_baseSix` makes the strength
of the descent formulation explicit.

Characteristic-two and fermionic obstructions are separate unconditional
results under their stated algebraic hypotheses. The four-vertex construction
is a genuine positive example. The eight-vertex example in
`Matching.ServabilityCounterexamples` refutes a proposed lower bound from two
disjoint matchings; it does not refute the Krenn–Gu conjecture.

## Semantic homes

The historical import names below refer to the standalone search development.
They are not additional copies of the library implementations on main.

| Historical source | Library home relative to `Matching/` |
|---|---|
| `lib/Amplitude` | `GHZ/Configurations` (GHZ predicates only) |
| `lib/MatchingParity`, `GraphMatchingBridge` | `Pairing`, `GraphBridge` |
| `lib/MatchingBridge`, `LocalCancellation` | `PermutationBridge`, `LocalCancellation` |
| `lib/CapIncidence`, `EvenCycle` | `CapIncidence`, `EvenCycle` |
| `lib/MixedColouring` | `FourthMatching` |
| `lib/OrbitNormalization` | `../OrbitNormalization` |
| `lib/Gauge`, `ColourPerMatching`, `MatchingSum` | `GHZ/Gauge`, `ColorPerMatching`, `MatchingSum` (GHZ consequences only) |
| `lib/FourVertices` | `GHZ/FourVertexConstruction` (GHZ construction only) |
| `lib/CycleSolution`, `CycleCoordinates`, `SixCycle` | `GHZ/TwoColorCycle`, `CycleCoordinates`, `SixCycle` |
| `lib/FourVertexRank`, `Covector`, `PurePartner` | `GHZ/FourVertexRank`, `Covectors`, `PurePartner` |
| `lib/FanStructure`, `Degenerate`, `SingleFlip` | `GHZ/StarStructure`, `Degenerate`, `SingleFlip` |
| `lib/Separation`, `LiveDegree`, `MinimalSupport`, `HardCase` | same names under `GHZ/` |
| `lib/MainTheorem` | `GHZ/ConditionalThreeRegularity` |
| `lib/NoCancellation`, `StarNormalForm` | same names under `GHZ/` |
| `lib/TightCut`, `UniformRigidity` | same names under `GHZ/` (GHZ consequences only) |
| `lib/CharTwo*` | `GHZ/CharacteristicTwo/` |
| `lib/Fermi*` | `GHZ/Fermionic/` |
| `lib/TripleOrbits` | `TripleOrbitClassification` |
| `GeneralOfficialBridge`, `OfficialKrennDefinitions` | `GHZ/OfficialBridge`, `OfficialDefinitions` |
| `OfficialConditional`, `OfficialCharTwo`, `OfficialPfaffian`, `OfficialScenarios` | `GHZ/Conditional`, `CharacteristicTwo/OfficialBridge`, `Pfaffian`, `Scenarios` |
| `KrennFactorization`, `KrennCounterexamples` | `GraphFactorization`, `ServabilityCounterexamples` |
| `KrennRank` (first two graph lemmas) | `GraphServability` |
| `DimensionMonotonicity` | `GHZ/ColorRestriction` |
| `KrennDoilyPotential`, `KrennDoilyVertexStars`, `KrennC6PotentialTargets` | `SixVertexPotential`, `SixVertexStars`, `SixCyclePotential` |
| `KrennSyzygies` (color multiplicities) | `ThreePairColorProfiles` |

The eight historical wrapper modules reuse existing implementations. The
same-named amplitude, gauge, four-vertex and tight-cut files extend those
foundations with GHZ consequences; their generic parts are not copied.
Graph-backed finite edge sets retain an explicit equivalence with Mathlib's
perfect-matching subgraphs in `GraphFactorization`.

The fixed support tables, case connectors and generated certificate trees
remain a separate search corpus. A finite branch refutation establishes no
coverage beyond its explicit assembly hypotheses.

## Qualification

From `lean/mettapedia`:

```sh
lake build Mettapedia.Combinatorics.Matching.GHZ
lake build Mettapedia.Combinatorics.Matching.GHZ.AxiomAudit
```

`AxiomAudit` imports the promoted families together and enumerates their compiled
module declaration tables. It checks every theorem and safe kernel declaration,
including private helpers, against `propext`, `Classical.choice` and `Quot.sound`.
Generated execution helpers are counted separately; they cannot justify a trusted
proof. The audit rejects admissions and also checks selected public endpoints
explicitly. Source coverage and aggregate build qualification are
reported separately by `scripts/check_library_sanity.sh`.
