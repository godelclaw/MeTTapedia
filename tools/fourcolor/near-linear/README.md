# Near-linear Four Colour catalogue bridges

The configuration files are unmodified inputs from
[near-linear-4ct/reducible-configurations](https://github.com/near-linear-4ct/reducible-configurations),
pinned to `c2ce7a96e35256201526e2abb51a39d04a588b53`.
Their MIT notice is retained in [LICENSE](LICENSE); [sources.json](sources.json)
and [five-sources.json](five-sources.json) record the individual hashes. The associated paper is
[The Four Color Theorem with Linearly Many Reducible Configurations and Near-Linear Time Coloring](https://arxiv.org/abs/2603.24880).

The Lean bridge identifies `D0000` and `D0001` with the existing diamond
configurations 1 and 2. It checks all source rows, complete adjacency,
prescribed internal degrees, every cyclic neighbour list and ordered boundary
alignment. A boundary-triangle insertion between the two source presentations
commutes with the existing reference insertion. Their repair laws reuse the
shared profile certificate and the general boundary-split theorem.

The repair conclusion produces an actual graph colouring compatible with any
supplied Kempe-closed exterior trace relation containing the initial proper
trace. The second entry's repaired witness also has a compatible GSLT insertion
history. This history records construction choices; it does not compute the
exterior Kempe recolourings.

From the repository root, source fidelity can be replayed with:

```sh
python3 tools/fourcolor/near-linear/audit_diamond_sources.py
```

From `lean/fourcolor-classical`, the kernel and dependency audit is:

```sh
lake build MettapediaFourColor.NearLinearDiamondAudit
```

The audit covers 23 roots and excludes all original configuration certificates
and complete Four Colour endpoints. The shared finite profile is retained.
See [diamond-source-audit.json](diamond-source-audit.json) and
[diamond-measurements.json](diamond-measurements.json).

These two entries were already covered by the existing mathematics. The bridge
adds no catalogue compression credit and changes neither the 633 coverage
entries nor the 629 original certificate dependencies in the complete assembly.
It does not verify the rest of the new catalogue, its geometric supply theorem,
its simultaneous repairs or its near-linear running time.

## A five-entry repair family

One retained classical certificate now supplies the repair contracts for five
entries from the repeated nine-vertex core. Arrows below transfer repair:

```text
           D0604 = classical configuration 225
              /           |           \
           D0464        D0465        D3202
              \           /
                  D0370
```

The actual graph construction runs in the opposite direction. Each step
inserts a vertex in a boundary triangle, replacing one boundary edge by two
edges while retaining their joint colouring relation. The general theorem
`BoundaryTriangleRepair.repair` restricts a repaired upper colouring to a
proper colouring of the lower graph. It applies to any graph and boundary
tail satisfying its repair premise; the five catalogue instances check the
complete graph isomorphisms, cyclic neighbour orders and ordered boundaries.
The five source inputs and prescribed internal degrees are checked separately.

`NearLinearFiveBase.reference_repair` proves that the existing configuration-225
rank certificate covers the whole proper fourteen-port domain after colour
permutations. This retains that finite certificate and adds one kernel-checked
mask comparison. `NearLinearFiveRepair` then supplies all five repair contracts
using the same split-and-reconstruction law. No independent rank certificate
is needed for the four lower entries. Their rings have lengths 12 and 13;
the upper ring has length 14.

`NearLinearFiveGSLT.coloring_square` proves that both insertion orders from
`D0370` to `D0604` produce the same complete colouring, including both newly
inserted vertices. `compatible_histories` starts with one actual repaired
`D0370` witness and supplies both GSLT histories with that common endpoint.
This is commutation for a fixed starting colouring; it does not equate the
results of independent Kempe repairs or extract exterior Kempe moves.

Replay source fidelity from the repository root:

```sh
python3 tools/fourcolor/near-linear/audit_five_sources.py
```

With the audited reference artifacts and configuration-family dependencies
prepared as in the [package guide](../../../lean/fourcolor-classical/README.md),
run from `lean/fourcolor-classical`:

```sh
lake build kernelNearLinearFamily
```

The six-module replay includes `NearLinearFiveAudit`. It excludes all complete
Four Colour endpoints and every original rank certificate except configuration
225. See [five-source-audit.json](five-source-audit.json) and
[five-measurements.json](five-measurements.json) for exact hashes and costs.

This is shared local repair reasoning for a finite five-entry family. It
changes neither the 633 coverage entries nor the 629 original certificate
dependencies of the complete classical assembly. The geometric occurrence,
strict smaller-map construction and reconstruction against an actual exterior
remain to be connected for this family. Recognition, coverage, coordinated
batch repairs and the newer algorithm's running time are separate obligations.

## Recognizing a diamond through an overlap

`OverlappingPentagonalSectors` isolates the cyclic mechanism suggested by
[Figure 11](https://arxiv.org/html/2603.24880v1#S8.F11). In the dual cubic map,
two views anchored at an actual edge read the same pentagonal face from
consecutive boundary darts. Its neighbouring faces have cyclic positions

```text
first centre -> second centre -> B -> D -> A -> first centre
```

One view reads `A` and `D` backwards; the other reads `B` and `D` forwards.
Five-step closure proves that the two readings of `D` are the same dart,
so every observation of it agrees. If `A`, `B` and `D` are pentagonal too,
the shared face and these three neighbours supply the existing diamond
occurrence. The two centre-face lengths and the rest of the graph are
unrestricted. The corresponding positions differ on a six-cycle; the
pentagonal hypothesis has mathematical content.

The theorem `strict_reduction` consumes the existing geometric recognition
and joint diamond repair. In a connected bridgeless spherical cubic map
with minimum face length five, cyclic edge connectivity at least five and
two-sided faces, it replaces twelve vertices by four, preserves the smaller
map's class, and reconstructs a source colouring from a smaller colouring.
`not_in_minimal` derives the ambient conditions from minimality.

This is a local recognition law for an already proved reduction, with no
new rank certificate. It is not a decoding of the complete Figure 11
cartwheels, a classification of degree-eight zero-charge pairs, or a proof
that every such pair has these readings. The all-flat supply theorem still
requires that classification and its residual cases. No classical coverage
entry or complete-assembly certificate dependency is removed here.

With the existing geometric dependencies prepared, run from
`lean/fourcolor-classical`:

```sh
lake build kernelOverlapSupply
```

The dependency audit checks nine roots, requires the geometric reduction
consumer, and excludes complete colouring endpoints and original catalogue
rank certificates. The joint diamond profile certificate is still retained
by that consumer. See [overlap-measurements.json](overlap-measurements.json).

## Coverage assembly and remaining local obligations

The [formal coverage assembly](../../../lean/fourcolor-classical/README.md#conditional-flat-neighbourhood-coverage-assembly)
now separates the radius and case argument from the still-open geometric
classification. `LocalCoverageAssembly.radius_twelve` composes three local
supply laws, transporting one complete supported occurrence through every
change of centre. `eight_of_overlap` further decomposes the degree-eight law
into classification, a specified second centre in an exceptional occurrence,
and a joint closing argument for both occurrences.

The concrete consumer runs on the actual quotient-face dual and excludes
the already certified pentagonal-overlap outcome from a minimal
counterexample. Other outcomes remain explicit residual witnesses. The
charge input has not yet been identified with the full source discharging
calculation. The source exceptional pattern is now decoded as described
below, while its supply from flatness remains open. The proof does not
assume that every pair of flat cartwheels is a diamond.

The [obligation record](coverage-obligations.json) lists the exact open fields
and their source references. The [measurement record](coverage-measurements.json)
records the kernel replay and dependency audit. From the prepared classical
package, replay with `lake build kernelFlatCoverage`. No classical coverage
or certificate dependency is removed by this conditional assembly.

## The exceptional overlap and the D1774 core

The exact `getX` function from the pinned primary
[computer checks](https://github.com/near-linear-4ct/computer-checks/tree/6cb85666ce89cf8bd813132e4c5dd56053e367a5)
encodes Figure 12: seventeen vertices, cyclic neighbour lists with explicit
gaps, and prescribed degrees. The unaltered excerpt and `D1774.conf` are
retained with hashes in [exception-sources.json](exception-sources.json).
The shared [MIT notice](LICENSE) applies to both source repositories.

`ExceptionalPattern.Occurrence` reads that data into an actual simple graph
with a vertex rotation, preserving every listed edge, prescribed degree and
known cyclic step. Gaps impose no step. Vertex collisions are permitted at
this stage and remain an explicit geometric obligation.

The next-centre field is now proved for this source pattern. Source vertex
14 has degree eight and lies within two edges of vertex 0. If a second
exceptional occurrence is centred at that actual vertex, the cyclic word
around its centre forces the neighbour two positions before any degree-seven
neighbour to have degree five. The first occurrence fixes the intervening
dart. Triangular face closure supplies the additional edge, so the two
occurrences force the corner used in Figure 13.

```text
first exact X occurrence
        |
specified second degree-eight centre within distance two
        |
second X occurrence at that same vertex
        |
shared rotation forces the extra degree-five corner
        |
all 13 D1774 core edges and all 8 prescribed degrees
        |
full boundary occurrence and compatible repair [OPEN]
```

`ExceptionalCore.coreHom` transports all core edges; `core_degrees` proves
the prescribed ambient degrees. Their entire support lies within radius
three of the first centre. `JointReading` retains both source occurrences,
their alignment, and the core's exact realization, so their cyclic-order
information remains available for boundary reconstruction. All retained
observations, including the second source occurrence, lie within radius four;
the support used by the scaffold includes them all.
`overlap_supply` instantiates the existing
degree-eight scaffold with these joint readings: its next-centre and joint
core-reading fields are proved, while classification remains a hypothesis.
It does **not** instantiate the scaffold with certified reductions. Moving
from a core reading to the full eleven-port occurrence requires collision
and inducedness analysis, boundary completion with cyclic order, and a colouring-repair
contract. The zero-charge classification and actual-dual bridge also remain
open. No coverage or certificate dependency is removed here.

Replay the independent source comparison and the Lean proof audit with:

```sh
python3 tools/fourcolor/near-linear/audit_exception_sources.py
```

From the prepared classical package:

```sh
lake build kernelExceptionalOverlap
```

See [exception-source-audit.json](exception-source-audit.json) and
[exception-measurements.json](exception-measurements.json). The dependency
audit excludes complete Four Colour endpoints and original catalogue rank
certificates; the source data are decoded and checked in Lean.
