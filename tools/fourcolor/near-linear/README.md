# Near-linear Four Colour catalogue bridges

## Coordinated repair of both critical-chain boundaries

[`StripChainRepair`](../../../lean/fourcolor-classical/MettapediaFourColor/StripChainRepair.lean)
completes the two fixed-boundary obstructions described below. Both inputs
reach genuine complete source colourings, compatible at all eleven ordered
ports with a colouring of the same exterior. The theorem assumes that
exterior's trace predicate is Kempe closed and contains the initial trace.
It also proves that the repaired boundary trace differs from the initial
one, since the initial trace admits no full source extension.

Eleven finite stages retain forty single-component and fourteen paired-component
source contracts. Seven stages now use the arbitrary-width
[`KempeBalancedBlock`](../../../lean/fourcolor-classical/MettapediaFourColor/KempeBalancedBlock.lean)
law. Only stages 5, 6, 7 and 10 retain the joint partner-exclusion computation.
No interior-colouring table or all-boundaries closure table is stored.

For a noncrossing perfect matching on `2k` active ports, consider a consecutive
block of `k` ports. Either it contains a matched adjacent pair, or every port
is paired with its reverse coordinate. In the second case the entire matching
is fixed. The repair consumer can therefore switch any specified finite batch
of those components while retaining the original exterior. Ear and batch
continuations can themselves invoke previously proved repairs.

The seven consumers have six, eight or ten active ports. Their cyclic
coordinates, ear contracts and rigid-case continuations are checked separately.
Cyclic order on triples transports noncrossing by a general lemma. The finite
source-extension contracts remain; this replaces matching-selection searches,
not complete source-reducibility certificates.

```
fixed-boundary forced-chain obstruction
                 |
      retain partners in one matching
                 |
    one or two compatible component switches
                 |
        earlier stage OR full reconstruction
                 |
    source and same exterior agree at every port
```

Replay with `lake build kernelStripChainRepair`. The
[kernel receipt](strip-chain-repair-measurements.json) records source size,
checking cost and the dependency audit, including the general selection law. The
[independent verifier](audit_strip_chain_repair.py) reads the Lean stage
data and checks all 201 stage matching layouts and the terminal source
reconstructions. It also tests the general dichotomy on all 2,055 noncrossing
matchings through sixteen ports; its [receipt](strip-chain-repair-audit.json)
retains the source pin and hashes.

This closes the two specified input repairs. It is not a uniform theorem
for every forced chain, nor a physical recolouring-history bound. Geometric
occurrence supply, strict ambient reduction and universal coverage remain
separate obligations. No catalogue entry or complete-assembly certificate
is removed by this result.

## A shared forced chain in two minimal boundary obstructions

[`StripCriticalChain`](../../../lean/fourcolor-classical/MettapediaFourColor/StripCriticalChain.lean)
proves that each of the D0099 boundaries `12211121113` and `12333313331`
extends after **any nonempty set of core vertices is deleted**, but neither
extends to the complete source while its eleven boundary colours stay fixed.
In particular, all eight seven-vertex views have actual colourings. Their
independently chosen witnesses cannot be glued into a complete colouring.

One shared argument explains the failure. A pinned colour propagates
through a path to vertex 4. Together with the colour forced at vertex 0,
it forces vertex 1, which then forces adjacent vertices 2 and 3 to agree.
The path propagation lemma works for arbitrary length and colour type.
The two source consumers use their decoded adjacency and boundary lists;
the sixteen single-deletion cases reuse the symbolic triangle joins.
No table of interior colouring witnesses is stored.

This rules out local existence as a sufficient gluing criterion, even
when every proper core restriction is checked. Composition with witnesses
that agree on overlaps remains valid. The fixed-boundary obstruction does
not prevent a repair that changes the boundary through the exterior.

Replay with `lake build kernelStripCriticalChain`. The
[kernel receipt](strip-critical-chain-measurements.json) records the
seven-root dependency audit and checking cost. The
[independent verifier](audit_strip_critical_chain.py) checks the two
boundaries directly against the source graph and records a separate
[program experiment](strip-critical-chain-audit.json):

- All 502 one-hole inputs forcing core vertices 5 and 7 to the same colour
  can remove every adjacent equal-singleton conflict using at most two
  components of one retained matching. Every individual switch leaves
  some source colouring with at most one hole.
- Of all 964 one-hole inputs with such an adjacent conflict anywhere in
  the core, 962 admit this one-query release. The other two remain explicit
  exceptions to that assertion.
- All 4,912 one-hole-or-complete inputs without such a conflict reach a
  complete source colouring in the finite matching game without recreating
  one. The successive closure layers finish after eight queries.

These repair experiments are not Lean theorems. They allow a fresh
adversarial noncrossing matching at each query and retain a common
matching for the selected pair of components. Successive partial
colourings need not form a physical history of one chosen interior
witness. No full-source repair certificate, strict ambient reduction,
geometric supply or catalogue deletion is added by this milestone.

## A choice-count obstruction and a composed escape

[`StripChoiceBarrier`](../../../lean/fourcolor-classical/MettapediaFourColor/StripChoiceBarrier.lean)
isolates a failed progress measure. The D0099 input `11212321221` admits
seven possible positions for one omitted core vertex, but no complete
source colouring. For each colour query there is a noncrossing matching
such that every subset of its component switches either decreases that
number or returns to the same boundary up to palette permutation.
Consequently, arbitrary-length histories that never decrease the number
of available hole positions cannot escape these responses.

The available positions mean actual proper induced-source colourings,
with all eleven boundary colours fixed. The negative result is an
**abstract matching-game obstruction**: the three adverse responses have
not been realized together by one exterior graph. It does not establish
an obstruction to every physical recolouring policy.

[`StripChoiceEscape`](../../../lean/fourcolor-classical/MettapediaFourColor/StripChoiceEscape.lean)
repairs the same input while allowing choices to decrease:

```
11212321221  -------> full source colouring
     |
11212331321  -------> full source colouring
     |
     +---- 11212113121 ----> full source colouring
     |
     +---- 12323111231 ----> full source colouring
```

Every continuation retains the same Kempe-closed exterior predicate.
The graph consumer reconstructs all eight core vertices and an exterior
colouring agreeing at every ordered port. Its exterior-closure hypothesis
is explicit. These are existence and compatibility results; the diagram
does not count physical recolouring steps or prescribe a history of one
chosen interior witness.

The four local laws reuse
[`KempeAnchorSelection`](../../../lean/fourcolor-classical/MettapediaFourColor/KempeAnchorSelection.lean),
which supports any boundary width and any number of retained anchors.
The partners all belong to one matching. When no successful single
component exists, the theorem selects two components jointly and composes
their continuation. Here four anchors suffice, with ten single-component
and fourteen paired-component contracts. Full source witnesses come from
the existing symbolic triangle joins; no interior-colouring table is stored.

Replay with `lake build kernelStripChoiceBarrier`. The
[kernel receipt](strip-choice-measurements.json) separates the finite
contracts, dependency audit and checking cost. The
[independent verifier](audit_strip_choice.py) checks all 48 distinct
subsets of the adverse responses and all 75 noncrossing matching layouts
across the four repair stages against the decoded source graph; its
[receipt](strip-choice-audit.json) records the source and proof hashes.

This rules out a greedy measure and supplies its input with a successful
alternative. It does not complete the last-hole continuation for the
earlier difficult inputs, a general D0099 repair, a strict ambient
reduction or geometric supply. Catalogue and complete-assembly dependency
counts are unchanged.

## Two-stage progress for the four difficult partial-colouring inputs

[`StripTwoPhaseProgress`](../../../lean/fourcolor-classical/MettapediaFourColor/StripTwoPhaseProgress.lean)
proves that each of `12311221133`, `12311331133`, `12312332133` and
`12313223133` lies in the Kempe co-closure of source colourings with at most
one omitted core vertex. The result holds for **every Kempe-closed exterior
predicate containing the input**. It does not assume a successful
continuation or choose an independently favourable exterior.

```
four difficult boundary inputs
              |
       first matching query
              |
       +------+----------------+
       |                       |
  one-hole witness     five intermediate forms
                               |
                     fresh matching query
                     in the SAME exterior
                               |
                        one-hole witness
```

Both stages reuse the general retained-matching anchor theorem. Single
chords are selected by interval exclusion; when necessary, two anchor
components are switched using their shared matching. The proof retains
41 single-chord contracts and five paired-anchor contracts across nine
stages. Two initial inputs share the same intermediate continuation.
These finite contracts remain proof obligations; this is not a case-free
source-repair theorem.

[`StripPuncturedExtension`](../../../lean/fourcolor-classical/MettapediaFourColor/StripPuncturedExtension.lean)
extends the six triangle-elimination joins to arbitrary boundary colours
and arbitrary omitted core vertices. Its equivalence theorem reconstructs
all retained source colours from common witnesses on the shared edges.
No table of interior colourings is stored.

[`StripTwoPhaseReconstruction`](../../../lean/fourcolor-classical/MettapediaFourColor/StripTwoPhaseReconstruction.lean)
returns an actual exterior colouring and a colouring of the induced source
minus one vertex, agreeing at all eleven ports after trace alignment. The
previous planar disk supplies a concrete consumer whose closure premise
is discharged by its checked rotation. The general consumer leaves exterior
closure explicit, so it can also consume other proved disk occurrences.

Replay with `lake build kernelStripTwoPhase`. The
[kernel receipt](strip-two-phase-measurements.json) records thirteen audit
roots, standard axioms only, and approximately 28 seconds for four modules
including imports. The [independent verifier](audit_strip_two_phase.py)
checks all 201 matching layouts across the nine stages and reconstructs a
partial source witness for every terminal contract. Its
[receipt](strip-two-phase-audit.json) also confirms that all four initial
words require exactly two holes.

This gives partial progress beyond the fixed-pair obstruction: a plateau
can be followed by a different matching query that removes a hole.
**One hole remains to be restored.** The two stages count abstract matching
queries, not physical component switches; the theorem does not give a
physical recolouring-history length bound. No strict ambient reduction,
geometric supply, universal coverage or catalogue deletion is established.

## Fixed-pair obstruction in the spherical coverage example

[`StripSpherePhase`](../../../lean/fourcolor-classical/MettapediaFourColor/StripSpherePhase.lean)
and [`StripSphereGeometry`](../../../lean/fourcolor-classical/MettapediaFourColor/StripSphereGeometry.lean)
transfer the phase obstruction below to the existing 162-vertex
closing-triangle sphere. Lean proves that the ambient rotation is planar
and triangular, every degree lies between five and seven, and deleting the
eight D0099 core vertices leaves exactly the stated 154-vertex induced
exterior. The source reading is injective and preserves every source edge
and every complete core star.

One proper exterior colouring realizes the same six initial boundary
route profiles as the smaller disk. The existing general phase theorem
therefore proves, without a new endpoint classification, that **every
fixed-pair history leaves at least two necessary core omissions**. This
allows arbitrary phase length, interior recolouring and choices of omitted
vertices. Equal and reversed colour pairs are included.

Two actual component switches nevertheless reconstruct a proper colouring
of all 162 vertices:

```
initial exterior      switch (0,2)      switch (1,2)
       2 holes  ---------------->  2  ---------------->  0
                   47 vertices          69 vertices     |
                                               full reconstruction
```

Both switches are connected, saturated bichromatic components in the
same exterior, composed as a proof-relevant GSLT history. Lean also proves
that no history of length less than two reconstructs the ambient graph,
so the exhibited two-step history is shortest. The exact minimum-hole
counts before and after the first switch additionally have independent
program checks; Lean supplies their lower bounds and the final colouring.

The [independent replay](audit_strip_sphere_phase.py) checks the pinned
sphere construction, all Lean graph and colouring literals, the three
degree-seven centres' zero final charges and all 1,817 nonobstructing short
cycles of lengths three through five. Those charge and short-cycle checks
remain **program evidence**, separate from the Lean results. No whole flat
ball or minimal-counterexample claim is made. This is a colourable test
map satisfying the tested local coverage hypotheses.

Replay with `lake build kernelStripSphere`, and independently with
`python3 tools/fourcolor/near-linear/audit_strip_sphere_phase.py --catalogue CATALOGUE/D`.
The [kernel receipt](strip-sphere-phase-measurements.json),
[program receipt](strip-sphere-phase-audit.json) and
[fixture](strip-sphere-phase-example.json) retain the exact evidence and
costs. The proof reuses the previous five small conflict shapes and stores
two explicit component witnesses; it imports neither a complete Four
Colour theorem nor a large repair table.

The earlier degree-three caveat has thus been removed for these explicit
geometric conditions. Strict decrease of the minimum hole count in a
single fixed-pair phase still fails. A general law for selecting successful
mixed-pair continuations remains open, together with geometric supply,
strict ambient reduction and universal coverage. The result removes no
catalogue entry or original certificate dependency.

## A physical limit of fixed-pair progress, with a successful mixed-pair repair

[`StripPhaseObstruction`](../../../lean/fourcolor-classical/MettapediaFourColor/StripPhaseObstruction.lean)
resolves a limitation of the preceding abstract matching tests: **one
actual exterior simultaneously prevents strict hole-count progress for
every fixed colour pair**. The exterior has 23 vertices and eleven ordered
ports attached to the eight-vertex D0099 core. Initially, at least two core
vertices must be left uncoloured, and two suffice. After any number of
switches of any one fixed vertex-colour pair, at least two omissions are
still necessary, even allowing arbitrary recolouring of the core and
arbitrary choices of omitted vertices.

The general [phase boundary theorem](../../../lean/mettapedia/Mettapedia/GraphTheory/Kempe/PhaseBoundary.lean)
uses initial bichromatic routes to retain the common choice at linked
ports. It applies at arbitrary graph, palette and boundary size, and at
arbitrary phase length. The source consumer needs only the specified port
colours and routes; it is not restricted to this literal exterior. Five
small list-colouring obstructions suffice: every allowed endpoint contains
two disjoint uncolourable pieces. Finite checks cover 48 normal forms,
with at most five vertices in a checked piece.

This exterior nevertheless has a **three-switch repair**, using different
pairs in succession. Lean checks each entire component, constructs the
proof-relevant GSLT history, and supplies the final colouring of all 31
vertices. It also checks the exact original core edges and complete stars.

```
initial exterior    switch (0,1)    switch (0,2)    switch (0,3)
       2 holes  ---------->  2  ---------->  2  ---------->  0
                                                            |
                                                 full reconstruction
```

Lean proves the lower bounds at the first three states, the initial
two-hole witness and the final reconstruction. The independent program
also checks the upper bounds at the intermediate states, so that the
displayed minimum-hole counts are exact. It finds no one- or two-switch
repair on this exterior. That shortest-history assertion is program
validation, separate from the Lean three-switch construction.

[`StripPhaseDisk`](../../../lean/fourcolor-classical/MettapediaFourColor/StripPhaseDisk.lean)
proves planarity of the exterior rotation, the simple ordered boundary,
and Kempe closure of its actual graph trace, using the existing disk Euler
and planar closure theorems. The independent program checks that gluing the
source gives a triangulated sphere; that whole-graph embedding has not
been separately certified in this module. Its minimum degree is three.
Thus this example **does not establish failure under the stronger
minimal-counterexample hypotheses**.

Replay with `lake build kernelStripPhase`. The
[kernel receipt](strip-phase-measurements.json) records 19 audit roots,
standard axioms only, and about 54 frontend seconds for three modules
including imports. No complete Four Colour theorem or large repair table
is used. The [program receipt](strip-phase-audit.json),
[fixture](strip-phase-example.json) and [verifier](audit_strip_phase.py)
retain the independent checks, including all 80 batches of switches on
both complementary vertex-colour pairs with one fixed XOR difference.
That stronger batch result is currently program evidence only.

The failed assertion is universal strict decrease of the minimum number
of holes in one fixed-pair phase on arbitrary planar exteriors. The
successful history shows why a continuation may need to change colour
pairs and temporarily keep the same number of holes. A structural law
justifying such continuations for all inputs remains open, as do geometric
supply, strict ambient reduction and universal coverage. No catalogue entry
or original certificate dependency is removed.

## Coordinated repairs retain one exterior matching

[`recover_stable`](../../../lean/fourcolor-classical/MettapediaFourColor/KempeChromogramMatching.lean)
now retains the decoded matching after accepted colour changes. Its chords
can be switched again while preserving the original chromogram. This
reuses the classical freedom to switch unions of components, using
Gonthier/Emery's general chord and flip theorems.

[`two_anchor_coclosure`](../../../lean/fourcolor-classical/MettapediaFourColor/KempeRetainedMatching.lean)
works at arbitrary boundary width. It either chooses a successful single
chord or switches the components through two specified anchors. Interval
exclusion proves that the remaining partner choices admit a continuation.
Both switches keep the original matching; continuations retain the same
Kempe-closed exterior predicate and may themselves be composed repairs.

[`StripCoupledRepair.source_repair`](../../../lean/fourcolor-classical/MettapediaFourColor/StripCoupledRepair.lean)
uses this law for the nonextending D0099 inputs `11111112223` and
`11111112322`. Their respective anchors are (0,1) and (0,2), after fixing
edge colour 3. If no single chord extends, only three partner pairs in the
first input and one in the second need a joint repair. Symbolic terminal
relations supply common colours for the three holes from the theorem
below; the exact restoration contract reconstructs the complete source.

```
one original exterior matching
              |
     +--------+---------+
     |                  |
single chord       two anchor components
     |             using that SAME matching
     +--------+---------+
              |
       joint restoration
              |
     complete source colouring
```

Replay with `lake build kernelRetainedMatching`. The
[kernel receipt](retained-matching-measurements.json) records fourteen audit
roots, standard axioms only, and about 18 seconds for four modules including
imports. The source retains twelve single-pair contracts, four double-partner
contracts and finite interval checks over partner choices. No full matching
layout or source-colouring table is stored in the Lean proof.

The [independent program](audit_retained_matching.py) checks all 42 matching
layouts for each input. Single chords suffice on 35 and 41 layouts;
the remaining 7 and 1 require the paired branch. On those layouts every
single chord fails, while the two selected components succeed together.
This explains why discarding the first matching between moves can lose a
successful repair.

The same program tests a limitation: input `12311221133` has two holes,
and each colour pair admits an adverse matching for which **every subset**
of component switches still requires at least two holes. All 40 subsets
are checked against the full source. This refutes universal strict decrease
by a single retained-matching batch in that abstract model; it does not
construct one physical exterior realizing all three adverse responses.

Full source repair, cross-colour continuation, geometric supply and strict
ambient reduction remain open. The endpoint preserves an exterior
predicate; no explicit ambient recolouring history or runtime bound is
extracted. No catalogue entry or original certificate is removed.

## Three holes suffice, can be necessary, and leave connected Kempe fibres

[`StripPartialColouring.sharp_three_holes`](../../../lean/fourcolor-classical/MettapediaFourColor/StripPartialColouring.lean)
proves a sharp bound for D0099. For every boundary assignment, omitting
core vertices 0, 2 and 5 leaves a constructively colourable path. Five
choices, each avoiding at most three colours, colour the retained core;
a proper boundary gives a colouring of the actual induced source graph.

One explicit proper boundary forces an omission in each of three disjoint
pieces: two monochromatic forced edges and a triangle with only two
available colours. The lower bound applies to every choice of omitted
vertices and every interior recolouring while that boundary stays fixed.
Thus a universal one-hole or two-hole partial-colouring contract is false
for this source.

```
arbitrary proper boundary
          |
omit core vertices 0, 2, 5
          |
colour retained path 3--1--4--6--7
          |
change path choices by Kempe moves, boundary fixed
          |
restore 0, 2, 5 with their joint constraints      [CONDITIONAL]
          |
colour the complete decoded source
```

[`StripSpineFibre.fibres_connected`](../../../lean/fourcolor-classical/MettapediaFourColor/StripSpineFibre.lean)
reuses the general forest fibre theorem: any two proper colourings of
this partial source with the same boundary are connected by actual Kempe
moves avoiding that boundary. The first greedy choices need not be frozen.
`fill_iff` gives the exact restoration condition, including the shared
inequality between missing vertices 2 and 5. `reconstruct` consumes that
condition and builds a genuine full-source colouring. Its satisfiability,
possibly after compatible exterior repair, is still the main obligation.

Replay with `lake build kernelStripPartial`. The
[kernel receipt](strip-partial-measurements.json) records seventeen audit
roots, standard axioms only, and about 15 seconds for three modules,
including imports. No stored source-colouring table is used. Source
adjacency, list and coordinate checks remain small finite obligations.
This is a result about one source and all its boundary assignments, not
an unbounded family of graph reductions.

The [independent program](audit_strip_partial.py) checks all 7,381 canonical
inputs. Their minimum numbers of holes are 0, 1, 2 and 3 on respectively
1,587, 4,289, 1,441 and 64 inputs. It also tests the proposed progress
measure: every three-hole input admits a guaranteed decrease in one
adaptive chord exchange in the abstract matching game. But even two such
exchanges do not guarantee a strict decrease for every one-hole or
two-hole input. These counts are **program evidence**, not Lean theorems;
the adverse responses have not been realized together in one physical
exterior. The failed short-horizon rule does not rule out longer repairs.

No catalogue entry or original certificate is removed. Complete source
repair, strict ambient reduction and geometric supply remain open.

## One exterior-matching theorem supports seven majority consumers

[`KempeChromogramMatching.recover`](../../../lean/fourcolor-classical/MettapediaFourColor/KempeChromogramMatching.lean)
recovers a noncrossing matching from any accepted chromogram, at arbitrary
boundary width. Switching one of its active chords retains that same
chromogram. The proof reuses the general chord scan, disjointness and
flip theorems from Gonthier/Emery's `FourColor.Bulk.Chords`; it consumes no
bulk reducibility data. The resulting `majority_coclosure` theorem permits
already composed repairs as continuations and retains the same arbitrary
Kempe-closed exterior throughout.

[`StripCriticalRepair.source_repair`](../../../lean/fourcolor-classical/MettapediaFourColor/StripCriticalRepair.lean)
applies this theorem to five nonextending D0099 inputs:

| Input edge trace | Active ports | Consecutive majority block size |
| --- | ---: | ---: |
| `12322212313` | 6 | 4 |
| `12322223131` | 8 | 5 |
| `12323211232` | 8 | 5 |
| `12323321221` | 8 | 5 |
| `12332132221` | 8 | 5 |

More than half the active ports lie in the chosen block, so some chord
lies inside it; a shortest such chord is adjacent. Every adjacent pair
in the block has a checked symbolic source extension. The proof therefore
reconstructs a colouring of the complete decoded source graph for the
chord provided by the actual exterior. No exterior matching layouts or
full source colourings are tabulated in the Lean proof. Source-coordinate,
cyclic-order and terminal-relation checks remain finite.

The two majority inputs in the three-form guard below now use this same
bridge. Their previous finite inverse-layout definitions and checks have
been removed. The dependency audit excludes those checks, earlier stored
colourings, interval search and the complete Four Colour theorem.

Replay with `lake build kernelChromogramMatching`. The
[kernel receipt](chromogram-matching-measurements.json) records twelve
audit roots, standard axioms only, and about 30 seconds for five modules
including imports. The [independent program](audit_critical_majority.py)
checks the five repairs and finds that, together with the 1,587 direct
inputs, their anchor closure reaches all 7,381 canonical inputs in 53
rounds. **That full continuation is program evidence only.** A structural
progress argument and its Lean proof remain open. This step establishes
neither full source reducibility nor geometric supply or strict ambient
reduction, and removes no catalogue entry.

## A boundary-dependent repair with three segment forms

[`StripSymbolicRepair.guarded_repair`](../../../lean/fourcolor-classical/MettapediaFourColor/StripSymbolicRepair.lean)
repairs every D0099 boundary of the form

```
(0, 1, 0, 1, 3, x, y, z, 1, 0, 1)
x in {0,2};  (y,z) in {(0,3),(3,0)};  x != y
```

There are three normalized forms. The guard forces the first interior ear
to colour 2 and leaves colour 1 available at its adjacent interior vertex.
It retains boundary vertex 2, whose loss caused the response obstruction
below. Two forms use an anchor exchange followed, when needed, by the same
majority-block law. The third can require one extra anchor exchange before
joining that majority repair. Directly extending answers stop earlier.

```
two forms    -> anchor ----------------> majority -> source colouring
third form   -> anchor -> extra anchor -> majority -> source colouring
```

The [source reconstruction theorem](../../../lean/fourcolor-classical/MettapediaFourColor/StripSourceExtension.lean)
works for arbitrary boundary colours: a proper boundary and an inhabited
terminal relation reconstruct a colouring of the complete decoded graph.
The repair re-evaluates those symbolic relations after each update. Its
dependency audit excludes the earlier stored colouring witnesses and both
earlier source-repair proofs. No new colouring-witness table is added.

[`KempeChordExchange.coclosure_of_answers`](../../../lean/fourcolor-classical/MettapediaFourColor/KempeChordComposition.lean)
composes proved continuations at any boundary length. It follows the
structural chord-cover theorem and retains the same arbitrary Kempe-closed
exterior. Both majority consumers reuse the convex-block theorem and the
arbitrary-width matching recovery above. Source-domain and terminal-relation
checks remain explicit; the independent program additionally cross-checks
the five possible matching layouts for each of their two inputs.

Replay with `lake build kernelSymbolicStrip`. The
[kernel receipt](symbolic-strip-measurements.json) records sixteen audited
roots and standard axioms only; replay times include imports.
The [independent replay](audit_symbolic_strip.py) checks all three guard
forms, the possible anchor replies, both majority blocks and reconstructed
source colourings. These are three boundary forms of one configuration,
not a complete repair of that configuration or a geometric supply theorem.
No catalogue dependency or net whole-proof saving is credited.

## Exact current relations can forget the response to a repair

[`StripResponseSummary.terminal_iff`](../../../lean/fourcolor-classical/MettapediaFourColor/StripResponseSummary.lean)
proves exact ear elimination for arbitrary boundary colours of D0099.
Six binary joins retain common interior witnesses and every surviving
edge constraint. Their terminal relation is inhabited exactly when the
internal colouring constraints have a solution. Source adjacency and all
boundary attachments are checked against the complete decoded graph.

The same module proves `not_update_congruence`: two boundary colourings
have identical evaluated relations at all six stages, yet the same
boundary update makes one extend to the full source and the other fail.
They differ only at boundary vertex 2, with indices starting at zero.

```
input edge trace       all six retained relations     after the same update
11121232111            equal                          12121232121: extends
12221232111            equal                          11221232121: cannot extend
```

The update adds colour 3 on boundary vertices 2 through 9. On the edge
trace it switches precisely edges 1 and 9. Both inputs support the same
noncrossing matching layout, and `same_chord_update` proves that switching
this whole chord preserves each input's own chromogram. No particular
physical exterior realizing the matching is constructed. The extending
answer reuses an existing complete source colouring; the failure is
proved from the empty terminal relation, including trace normalization.
There is no new colouring-witness payload.

This distinguishes two contracts for an interface: preserving extension
at its current input, and preserving the response to future operations.
The first does not imply the second. The obstruction concerns evaluated
retained relations; the raw messages before intersection already differ.
It does not rule out keeping the boundary observations, symbolic relation
expressions, or another sufficient summary. In particular, the uniform
elimination theorem remains available after a boundary update.

Replay with `lake build kernelStripResponse`. The
[kernel receipt](strip-response-measurements.json) records fourteen audited
roots, standard axioms only, and about 10.2 seconds including imports.
The [independent replay](audit_strip_response.py) compares exact ear
elimination with a separate source-colouring search and checks the whole
chord update. The result removes no catalogue dependency and establishes
neither full source reducibility nor geometric supply.

## Two repair stages compose through the same exterior

[`StripTwoRoundRepair.source_repair`](../../../lean/fourcolor-classical/MettapediaFourColor/StripTwoRoundRepair.lean)
proves `KempeCoclosure` for the D0099 input `11121232111`. A first anchor
exchange has five possible partners: four answers have direct source
colourings, and the fifth is exactly the second input already handled by
the majority-block theorem. That theorem supplies the second repair.
The same arbitrary Kempe-closed exterior predicate is retained throughout;
terminal witnesses are colourings of the complete decoded source graph.
Four additional witnesses use 76 flat colour bytes.

The missing inverse bridge is supplied for both earlier majority inputs.
[`KempeFiniteDecoder.mem_parses`](../../../lean/fourcolor-classical/MettapediaFourColor/KempeFiniteDecoder.lean)
proves the accepted-parser specification by induction at arbitrary width.
A finite check then shows that each selected input has five accepted
chromograms, all represented by five checked noncrossing matching layouts.
Consequently `majority_coclosure` consumes the existing structural majority
law for whichever chromogram the exterior supplies. The inverse cover is
source-specific; no general decoder or compact scaling of enumeration is
asserted. Neither `coversRec`, interval search nor a bulk repair table occurs
in the new proof dependencies.

The [independent program](audit_two_round_repair.py) also tests a potential
progress measure: the cardinalities of the exact relations retained during
core elimination. For this input they are

```
initial:       2 3 2 1 1 0 0
intermediate:  2 3 2 0 0 0 0
                         |
               existing majority repair
                         |
                 genuine colouring
```

For each of the three choices of fixed colour, one explicit noncrossing
matching makes every single-chord answer nonextending and componentwise
no larger than the initial profile. These eleven answers rule out a
strictly improving potential that is monotone in those cardinalities, for
this abstract one-chord response game. The three matchings are independent
responses; no one physical exterior realizing all three is constructed.
The result does not obstruct history-dependent or multi-component repair.
In fact the Lean composition repairs this very input despite the temporary
loss of choices.

The full 7,381-input census grants all 1,587 direct extensions and all 349
first-round majority repairs as terminal seeds. Even then, each of eight
simple progress measures fails on some remaining inputs, allowing adaptive
choice of any single chord. The [receipt](two-round-repair-audit.json)
records the measures and exact counts. These profile results are program
evidence, independently cross-checked by source colouring search and exact
ear elimination; they are not Lean theorems.

Replay the source proofs with `lake build kernelTwoRoundRepair`. The
[kernel receipt](two-round-repair-measurements.json) records nine audited
roots and about 10.3 seconds of frontend time including imports. The
complete D0099 closure, a uniform continuation argument, geometric supply
and strict ambient reduction remain open. No catalogue entry, original
certificate dependency or whole-proof runtime saving is credited.

## Majority blocks give a structural adaptive repair law

[`exists_adjacent_majority`](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/Compositional/NoncrossingMatchingEar.lean)
proves a sufficient condition at arbitrary boundary length: a convex block
containing more than half the active ports contains a matched adjacent pair
in every noncrossing perfect matching. The proof has two parts. Injectivity
prevents every block port from pairing outside the block; a shortest chord
inside the block then has adjacent endpoints. The existing adjacent-pair
theorem now reuses the same localized argument.

[`KempeMajorityRepair.answer`](../../../lean/fourcolor-classical/MettapediaFourColor/KempeMajorityRepair.lean)
removes the inactive ports, retains the actual component matching and chooses
one of the successful adjacent pairs in that block. Its terminal witness
matches the original chromogram. The active ordering and its noncrossing
property are explicit hypotheses.

[`StripMajorityRepair.source_repair`](../../../lean/fourcolor-classical/MettapediaFourColor/StripMajorityRepair.lean)
applies this one law to both earlier D0099 inputs. Each uses four consecutive
ports among six active ports, with successful repairs on the three intervening
pairs. The existing colouring witnesses are reused. The new proof depends on
neither interval recursion nor the two previous interval rejection checks.
It retains finite source, coordinate and witness checks; no net check-count
or runtime saving is claimed. Replay with `lake build kernelMajorityRepair`;
the [receipt](majority-repair-measurements.json) records ten audited roots.

The [independent program](audit_majority_repair.py) replaces every adjacent-chord
interval query by a run of successful pairs of length at least half the active
boundary. On D0099 the resulting closure is unchanged:

| Rules available | Canonical source inputs repaired |
| --- | ---: |
| Anchor rule | 1,993 / 7,381 |
| Majority-block rule | 2,251 / 7,381 |
| Both rules | 7,381 / 7,381 |

Both rules together close in fourteen rounds. A two-phase strategy also
closes: just one majority round adds 349 inputs to the 1,587 directly
extending inputs; seventeen anchor rounds then reach all 7,381. This
establishes the sufficiency of that order in the finite program, not a bound
for the complete colouring algorithm. Each input's initial extension is
independently checked by search and exact ear elimination.

A replayable seed test reduces the 349 new inputs to five sufficient inputs,
each requiring one majority step. Removing any one of those five prevents
full anchor closure for that particular set; no globally minimal seed count
is claimed. Using five seeds takes fifty-three anchor rounds, and the anchor
mechanism still has 162,382 candidate implications before deduplication.
Neither those five source repairs nor the full closure is Lean-certified
here, so this finding does not establish a compact proof.

The [program receipt](majority-repair-audit.json) additionally checks the
equivalence of the successful-run test and hitting every noncrossing matching
for every subset of cyclic adjacent pairs through fourteen active ports.
The unbounded Lean theorem proves sufficiency only; it does not use this
enumeration or assert the general converse.

The unresolved task is a structural progress argument explaining the source
closure and its extension to families. The complete 7,381-input result remains
program evidence. No new occurrence supply, strict reduction, catalogue entry
removal or original certificate replacement is established.

## Adaptive chord choice uses noncrossing geometry

[`KempeIntervalMatching`](../../../lean/fourcolor-classical/MettapediaFourColor/KempeIntervalMatching.lean)
proves an interval exclusion rule at arbitrary boundary length. If the
unsuccessful pair choices cannot form a noncrossing matching, any supplied
noncrossing exterior matching contains a successful chord. An active first
port splits its interval at its partner; fixed ports are skipped. The proof
uses that both resulting intervals remain closed under the same matching.

[`KempeIntervalRepair.answer`](../../../lean/fourcolor-classical/MettapediaFourColor/KempeIntervalRepair.lean)
then switches that one whole chord and retains the original chromogram.
The successful terminal predicate can contain an actual graph colouring.
This permits choosing a chord after inspecting its connections; it does not
require one predetermined anchor to work for every matching.

[`StripIntervalRepair.source_repair`](../../../lean/fourcolor-classical/MettapediaFourColor/StripIntervalRepair.lean)
certifies two exact D0099 input words against every supplied noncrossing
matching with the appropriate fixed ports. Four full source colourings per
word, 152 flat bytes in total, witness the successful choices. Three explicit
noncrossing matchings show that no one anchor covers the certified choices.
A crossing matching avoids all four successful pairs, so the geometry is
essential. These are matching-parametrized source repairs; no complete source
repair, new occurrence supply or strict ambient reduction is claimed.
Replay with `lake build kernelIntervalRepair`; the
[kernel receipt](adaptive-chords-measurements.json) records twelve audited roots.

The independent [policy comparison](audit_adaptive_chords.py) exposes work
hidden in the earlier two-round result:

| Allowed response | Source closure alone | Two parent closures | Source closure using parents |
| --- | ---: | ---: | ---: |
| One predetermined anchor | 1,993 | 1,572 / 1,525 | 2,037 |
| Partner-counting Hall obstruction | 6,181 | 1,715 / 1,609 | 6,181 |
| One adaptively chosen chord | 7,381 | 6,328 / 3,147 | 7,381 |
| One or two jointly chosen chords | 7,381 | 6,328 / 3,557 | 7,381 |

All counts are program evidence over 7,381 canonical input classes. The
adaptive single-chord interval test is cross-checked against explicit
noncrossing matching enumeration. Computing its parent sets takes 22 and
24 rounds; the direct source closes in 11 rounds. The two-chord version
takes 11 and 9 parent rounds before its final two source rounds. A short
final continuation therefore does not establish total proof compression.

The same [program receipt](adaptive-chords-audit.json) tests nonadaptive
parent selection from fixed subsets of observed boundary edges. Every
four-edge seam pattern is ambiguous; no subset of eight or fewer edges
always selects a winning parent. Exactly one nine-edge subset suffices.
This result concerns the computed parent winning sets, with direct source
inputs excluded. It does not bound adaptive inspection, symbolic summaries,
other strategies, or compositional proofs in general.

The remaining task is to derive shared structural conditions that make the
interval test reject, and to connect broader repair domains to strict
reduction and geometric supply. The full game closures are not Lean-certified
here, and no catalogue or certificate dependency is removed.

## A uniform fan law transfers repairs through two exact parents

[`KempeBoundaryFan`](../../../lean/fourcolor-classical/MettapediaFourColor/KempeBoundaryFan.lean)
proves a repair transport law for a two-triangle boundary fan. Replace the
middle vertex of a boundary path by a new vertex adjacent to all three old
path vertices; the old middle vertex becomes internal. The two old edge
colours and the two new ones have the same sum, and corresponding edges
have different colours. This complete joint relation is exactly the
composition of the existing split, rotation and merge relations.

The transport preserves arbitrary Kempe-closed exterior predicates.
[`BoundaryFanRepair.trace_exact`](../../../lean/fourcolor-classical/MettapediaFourColor/BoundaryFanRepair.lean)
proves both directions on actual graph colourings. A successful parent
repair therefore reconstructs the grown graph against the same exterior.
The law has no boundary-length bound and adds no matching table.

[`StripParentFan`](../../../lean/fourcolor-classical/MettapediaFourColor/StripParentFan.lean)
checks the complete graph and ordered boundary of D0099 at both ends.
Each gives a different eighteen-vertex parent. Neither parent is identified
with D0092 merely because their internal graph shapes agree.
[`StripParentFanExample.source_repair`](../../../lean/fourcolor-classical/MettapediaFourColor/StripParentFanExample.lean)
supplies one successful input through each parent. Each uses the uniform
chord-exchange theorem and two full parent colourings; the four witnesses
occupy 72 flat bytes. Replay with `lake build kernelBoundaryFan`.
The [kernel receipt](strip-parent-fan-measurements.json) records the audit
and module costs.

The independent [program replay](audit_strip_parent_fan.py) compares DFS
extension with exact ear elimination for every canonical boundary word.
Its [receipt](strip-parent-fan-audit.json) reports 1,053 and 3,824 surviving
abstract inputs in the two parent repair games. Direct source extension
and transport from both winning parent sets cover 6,777 of 7,381 source
classes; two further repair rounds give 7,305 and then 7,381. These closure
counts are program evidence, not a Lean proof of full source reducibility
or a demonstration of certificate compression. Abstract survivors do not
exhibit unrepairable physical exteriors.

The kernel results certify the general transport and two concrete repairs.
A compact strategy covering every source input remains open, as do ambient
embedding, occurrence supply and strict reduction for this new consumer.
No catalogue entry or original configuration certificate is removed.

## A fixed boundary replacement can fail before coverage is considered

[`BoundaryReplacementObstruction.obstruction`](../../../lean/fourcolor-classical/MettapediaFourColor/BoundaryReplacementObstruction.lean)
proves a limitation for the exact six-port D0000 graph. Take any feasible
conjunction of equalities and inequalities on noncrossing boundary diagonals.
There is a proper boundary colouring satisfying that conjunction which does
not extend into D0000. Consequently, these constraints cannot by themselves
guarantee reconstruction for every colouring of a fixed replacement.

The proof covers every noncrossing diagonal set with one of fourteen
triangulations. Palette symmetry fixes the first two colours. Fifteen
nonextension witnesses, stored in ninety bytes, cover all feasible diagonal
signatures. The graph edges are checked against the decoded catalogue source;
nonextension concerns actual graph colourings. Replay with
`lake build kernelBoundaryReplacement`. The eight-root audit admits only
standard axioms and excludes the complete Four Colour theorem and bulk repair
tables. The module replay takes 17.345 seconds in the recorded run; its audit
takes 2.390 seconds. See the [kernel receipt](boundary-replacements-measurements.json).

The independent [program replay](audit_boundary_replacements.py) tests larger
patches against the same universal fixed-boundary contract. It enumerates
proper boundary words up to palette permutation and compares DFS extension
with exact two-port ear elimination on every word. Two replacement classes
are tested: feasible mixed equality/inequality constraints on noncrossing
diagonals, and simple triangulated disks with exactly one interior vertex.

| Source | Proper word orbits | Nonextending orbits | Boundary triangulations | One-interior-vertex disks |
| --- | ---: | ---: | ---: | ---: |
| D0000 | 31 | 15 | 14 | 84 |
| D0092 | 7,381 | 6,078 | 4,862 | 75,582 |
| D0063 | 2,461 | 1,839 | 1,430 | 19,448 |
| D0099 | 7,381 | 5,794 | 4,862 | 75,582 |

No candidate in either class satisfies the contract for these four sources.
A positive control finds the expected eight-to-seven-vertex reduction of a
wheel with an extra vertex in one triangular face. The
[program receipt](boundary-replacements-audit.json) records exact counts and
source hashes. Only the six-port noncrossing-constraint result is Lean proved;
the larger searches and the one-interior-vertex class are program evidence.

This rejects the stated fixed-boundary mechanisms, not compositional proofs.
It does not exclude a compatible choice of exterior colouring, coordinated
exterior Kempe recolouring, larger replacement gadgets, or a theorem using
stronger ambient hypotheses. The next repair obligation must account for such
choices. Coverage remains a separate open obligation, and no catalogue entry
or original certificate is removed here.

## Structural anchors preserve repairs, but their number can grow

The general Lean law
[`TriangleAnchors`](../../../lean/mettapedia/Mettapedia/GraphTheory/Kempe/TriangleAnchors.lean)
uses an injective elimination rank whose later neighbours form a clique
and a proper structural three-colouring. Deleting one structural colour
class leaves a forest. The structural colours are separate from the
physical colours being repaired. Retaining the physical colours on that
class makes the existing joint forest guard exact for complete Kempe
histories, with the whole exterior fixed.

[`TriangleStripAnchors`](../../../lean/fourcolor-classical/MettapediaFourColor/TriangleStripAnchors.lean)
checks this contract on the complete decoded internal graphs of D0092,
D0063 and D0099. Each uses two anchors: source labels 12 and 14 for D0092
and D0063, and 13 and 18 for D0099. One theorem applies to every exact
induced occurrence in an arbitrary finite ambient graph. Extra core edges
cannot be discarded by the occurrence hypothesis. The theorem preserves
and reconstructs physical histories; it does not assert that a useful
guarded move or a smaller-map reduction exists.

The same method has a precise limitation.
[`TriangleStripWidth.anchors_required`](../../../lean/mettapedia/Mettapedia/GraphTheory/Kempe/TriangleStripWidth.lean)
proves that for the graph on indices `0..3*k-1` joining indices at distance
one or two, every cycle-breaking set has at least `k` vertices. Each of
the disjoint triples `(3*i, 3*i+1, 3*i+2)` is a triangle and must meet the
set. A reverse-index elimination rank and colouring modulo three also
certify the positive forest construction at every length. Thus there is
no constant anchor bound for this method on all triangle strips. This
does not bound the size of symbolic relation expressions or proofs and
does not refute other compositional repair methods.

The independent [inventory replay](audit_triangle_anchors.py) checks the
rank, colouring and acyclicity certificates for all 666 previously
recognized source constructions. Their smallest structural colour-class
sizes are 1 (16 sources), 2 (318), 3 (324) and 4 (8). These counts concern
this construction, not minimum feedback sets or certified reducibility.
Deleting any one vertex still leaves a cycle in each of the three Lean
consumers, providing a negative control for the two-anchor claim.
See the [program receipt](triangle-anchors-audit.json) and
[kernel measurements](triangle-anchors-measurements.json).

No coverage entry or original reducibility certificate is removed.
Remaining obligations are successful guarded repair choices, strict
reduction, and geometric supply for the closing-flat-triangle branch.

## A closing triangle needs more than the five-triangle family

The [replay](audit_closing_triangle_strips.py) checks a 162-vertex spherical
triangulation with a facial triangle of three flat degree-seven centres.
Every vertex has degree 5–7. All 1,817 cycles of length three through five
satisfy the checked nonobstruction conditions. The joint radius-two ball
has 33 vertices.

None of the nine catalogue configurations with the unlabelled D0092 core
and prescribed degrees at most seven occurs in that ball. The seven earlier
named configurations and the tested wheel, diamond and chain recognizers
also fail there. The absence check compares two independent matchers at
every oriented edge in both orientations, excluding even noninjective core
readings. This is a program-checked counterexample to that **specified
inventory's** coverage claim, not to general compositional coverage or to
a statement requiring a whole ball to be flat.

The same ball contains an exact [D0099 occurrence](D0099.conf): eight core
vertices, eleven ordered boundary ports, and six facial triangles attached
in a strip. Complete core stars, degrees, cyclic order and injectivity are
checked. Removing one end ear leaves the unlabelled D0092 core graph, but
that adjacency map does not preserve its prescribed degrees or boundary
semantics. No colouring repair transfers from this fact alone.

The [catalogue audit](closing-triangle-strip-audit.json) pins all 8,200
input files and recognizes 666 configurations of degree at most seven
whose cores are triangle strips. Recognition checks that each triangle
introduces one new vertex along the preceding edge and that the resulting
construction has exactly the source core's edges. The available core sizes
range from four to thirteen vertices. These are source constructions;
their common reducibility theorem is not established here.

A separate [bounded discovery run](closing-triangle-strip-discovery.json)
samples 1,791 related spherical maps across thirty seeded flip sequences.
It finds 33 flat closing triangles: the simple recognizers cover 23 and
exact source occurrences cover the other ten. This census has no claim of
exhaustiveness or independent random sampling. It supports investigating
variable-length strips while the fixed five-triangle candidate has a
checked failure. No Lean theorem, coverage entry or complete-proof
dependency is removed by these experiments.

The D0099 source is from Yuta Inoue's MIT-licensed
[catalogue revision](https://github.com/near-linear-4ct/reducible-configurations/tree/c2ce7a96e35256201526e2abb51a39d04a588b53),
with the licence retained in [LICENSE](LICENSE). The
[fixture](closing-triangle-strip-example.json) records the complete input
content digest and legal flip history. Replays take a checkout of that
revision's `D` directory:

```sh
python3 tools/fourcolor/near-linear/audit_closing_triangle_strips.py --catalogue CATALOGUE_D
python3 tools/fourcolor/near-linear/probe_closing_triangle_strips.py --catalogue CATALOGUE_D
```

## A repair must reach outside radius two

[LocalRepairRadius](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/LocalRepairRadius.lean)
checks a proper colouring of a 155-vertex exterior obtained by deleting
seven vertices from an explicit 162-vertex graph. No full colouring agrees
with that exterior outside the radius-two neighbourhood of the deleted
core. This rules out arbitrary recolouring confined to that neighbourhood,
regardless of which Kempe commands are chosen or how long they run.

The proof has two branching choices, three contradictory leaves and 81
local triangle deductions. It checks the literal graph and initial
colouring, and proves that every reconstruction changes a vertex farther
than two edges from every deleted vertex. The separate full colouring in
that module keeps all vertices outside radius three fixed.

| Allowed neighbourhood | Total vertices, including the seven deleted | Full endpoint keeping its exterior fixed |
| --- | ---: | --- |
| Radius two | 35 | Impossible |
| Radius three | 57 | Full reconstruction after two checked physical switches |

[LocalRepairHistory](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/LocalRepairHistory.lean)
now supplies an actual history for the same starting colouring. One switch
uses colours 0/2 on seven vertices; the other uses 0/3 on three vertices.
Both complete components lie within radius three, and no edge connects
their supports. Every intermediate colouring fixes the farther exterior.
The endpoint reconstructs all seven deleted vertices.

The reusable [separated-chain law](../../../lean/mettapedia/Mettapedia/GraphTheory/Kempe/SeparatedChains.lean)
proves that connected, saturated supports with no common vertex or
connecting edge remain actual components after either switch. The two
physical switches commute, even when their colour pairs overlap. Both
orders in this fixture have checked two-step GSLT histories reaching the
same full colouring. Chain lengths and the ambient graph are unrestricted
in the generic theorem. Reuse invokes that theorem; no repair search is
repeated. The finite consumer supplies just the two chains and seven core
colours in addition to the existing graph and starting colouring.

The [history replay](local-repair-history-audit.json) checks both orders
against the full spherical exterior. This proves a successful enlarged
repair for one supplied colouring, not a universal radius-three bound.
Geometry guaranteeing usable supports, or a successful alternative when
they interact, remains open. The [history receipt](local-repair-history-measurements.json)
records the new proof costs and dependency audit.

The [independent replay](local-repair-radius-audit.json) identifies the Lean
graph with the existing spherical D0092 occurrence. Its degrees are 5–7,
the three selected centres have zero charge, and all 1,815 short cycles
satisfy the checked separation conditions. These geometric facts remain
program evidence, separate from the Lean endpoint obstruction.

The replay also checks a [modified exterior](three-switch-strong-example.json)
requiring exactly three physical switches. Complete source stars and cyclic
orders, degrees 5–7 and the short-cycle conditions are preserved. Exhaustive
search through depth two visits 24 and 378 new complete-colouring classes
modulo global palette permutations; none extends. The supplied three-switch
history reconstructs a full colouring. This lower bound is program checked.
The original centres now have charges `-4,0,-2`, so it does not refute a
two-switch claim under stronger flatness assumptions.

These results constrain fixed locality and step-count contracts. They do
not establish unbounded lower bounds, failure of adaptive larger-region
repair, or impossibility of a compact compositional proof. Other initial
colourings and selected pieces remain possible. Coverage and
complete-proof dependency counts are unchanged. The
[receipt](local-repair-radius-measurements.json) records proof costs and scope.

```sh
python3 tools/fourcolor/near-linear/audit_local_repair_radius.py
python3 tools/fourcolor/near-linear/audit_local_repair_history.py
cd lean/mettapedia
lake build Mettapedia.GraphTheory.FourColor.LocalRepairRadiusAudit
lake build Mettapedia.GraphTheory.FourColor.LocalRepairHistoryAudit
```

## Physical repair counts survive clique attachments

[CliquePhysicalLift](../../../lean/mettapedia/Mettapedia/GraphTheory/Kempe/CliquePhysicalLift.lean)
proves that a hidden patch attached only along a retained clique cannot
merge distinct retained two-colour components. Each retained component
switch lifts to one actual switch; a whole GSLT history lifts with exactly
the same length. The initial full colouring is supplied. The patch's size,
interior graph and colouring-fibre connectivity are unrestricted.

[CoreCliqueRepair](../../../lean/fourcolor-classical/MettapediaFourColor/CoreCliqueRepair.lean)
consumes this law for both core-profile boundary words. Starting from any
proper colouring of a clique-attached enlargement whose retained
eleven-port colouring is one of those two words, one or two switches produce an exterior colouring
and a matching D0092 source colouring. Two switches remain necessary for
the second word. Exact occurrence, source-star and exterior-coverage data
then reconstruct the whole ambient colouring, restoring seven vertices.
Graph isomorphisms transport both actual components and switch counts.
The existing icosahedral cap provides a second checked consumer: its nine
hidden vertices add no switches to any retained physical history.

This is a structural repair theorem for an explicit attachment class. It
does not show that arbitrary exteriors decompose into clique attachments,
or establish occurrence supply in minimal counterexamples. The clique
hypothesis is essential to the component argument; general attachments
can join distinct retained components.

The independent [hidden-exterior test](hidden-exterior-probe.json) checks
all 6,606 compatible colouring/exterior pairs among simple eleven-port
disk triangulations with one additional vertex and the two fixed words,
and 1,500 seeded trials with 2–32 additional vertices. Every tested case
repairs within three physical switches. The larger trials may repeat
graphs and are not an exhaustive census. All histories are replayed on
actual components and checked against full ambient colourings; no general
three-switch theorem follows. The [receipt](core-clique-repair-measurements.json)
separates these program observations from the Lean theorem and costs.
Coverage and complete-assembly dependency counts are unchanged.

```sh
python3 tools/fourcolor/near-linear/probe_hidden_exterior.py
cd lean/fourcolor-classical
lake build MettapediaFourColor.CoreCliqueRepairAudit
```

## One boundary requires a change of colour pair

[CorePairChangeObstruction](../../../lean/fourcolor-classical/MettapediaFourColor/CorePairChangeObstruction.lean)
proves that the D0092 boundary word `01021312321` cannot extend after any
pointwise selection of swaps in a single colour pair. Six short arguments
use source triangles and adjacency; the 45 required source incidences are
decoded and checked once. There is no table of possible endpoints.

[CorePairHistoryObstruction](../../../lean/fourcolor-classical/MettapediaFourColor/CorePairHistoryObstruction.lean)
combines this with the generic fixed-pair history theorem. On any exterior
carrying this word, every finite history using one fixed pair fails to
reach an extendible boundary. There is no bound on exterior size, and the
negative result requires no planarity hypothesis. Pullback along a source
graph homomorphism gives the same lower bound for ambient reconstruction.

The earlier actual spherical example supplies the positive counterpart:
its two physical switches, first using colours 1/3 and then 0/3, reach a
full colouring. `optimal_reconstruction` proves that this history is
shortest on that example. The seven-root audit excludes repair tables and
the complete Four Colour theorem; it also checks that the universal
obstruction has no dependency on the example's exterior geometry.

The [exterior probe](pair-preparation-probe.json) separately enumerates all
4,862 triangulations of the eleven-port polygon. The two fixed initial
words give 399 proper colouring/exterior pairs. Actual component search
finds repairs of length at most three in each, with 14 requiring three.
The fixed two-switch recipe above succeeds on only 12 of the 199 exteriors
compatible with its input. These are bounded program results; exteriors
with additional vertices are outside this test.

This rules out fixed-pair repair for this word and motivates adaptive pair
selection. It does not rule out mixed-pair compositional repair, establish
a general three-switch bound, or supply occurrences. Counts remain 633
coverage entries, 629 original certificates and 336 replaced member checks.
The [measurement receipt](core-pair-history-measurements.json) records
scope, dependencies and costs. The source obstruction checks in about four
seconds; reuse applies its theorem without repeating discovery.

```sh
python3 tools/fourcolor/near-linear/probe_pair_preparation.py
cd lean/fourcolor-classical
lake build MettapediaFourColor.CorePairHistoryAudit
```

## Core lists preserve extension but lose a physical repair choice

[The core-profile counterexample](../../../lean/fourcolor-classical/MettapediaFourColor/CoreProfileSwitchObstruction.lean)
uses two colourings of the same eleven-vertex exterior in an
[eighteen-vertex spherical triangulation](../../../lean/fourcolor-classical/MettapediaFourColor/CoreProfileSwitchGeometry.lean).
The full D0092 core reading and the exact induced exterior are checked.
The two colourings give identical available colours at each of the seven
core vertices, hence the same joint relation of internal assignments.
`extension_iff_relation` proves that this relation is sufficient for
reconstructing a colouring when the exterior is held fixed.

The same rooted operation behaves differently:

```text
same seven core lists; swap colours 0 and 3 at boundary vertex 2
             /                                      \
    component {2,4}                             component {2}
             |                                      |
    full colouring exists                  adjacent core vertices
                                           both forced to colour 0
```

`no_deterministic_quotient` consumes the shared GSLT nonfactorization
criterion: the updated core profile cannot be computed from the old
profile alone. Even whether the result extends is undetermined by that
summary. This is a concrete source-patch instance of the distinction
between static extension data and physical repair dynamics. It does not
supersede the earlier, different obstruction for current boundary words
and component partitions in `KempeBoundaryObservation`.

There is a constructive repair. In the second colouring, switching colours
1 and 3 on the component `{4,5,6}` yields the first colouring. The successful
0/3 switch then applies. [The preparation theorem](../../../lean/fourcolor-classical/MettapediaFourColor/CoreProfilePreparedRepair.lean)
composes the actual component witnesses through the existing GSLT history
type and reconstructs the full colouring. The two inputs use one and two
physical steps respectively; no repair search is repeated on application.

These are two specified colourings, not arbitrary-exterior reducibility
or a geometric supply theorem. The example is not asserted to satisfy
minimal-counterexample connectivity restrictions. No catalogue entry or
original certificate is removed, and no impossibility of a richer
compositional proof is claimed. The [receipt](core-profile-switch-measurements.json)
records the small finite fixture, dependency audit and build costs.

```sh
python3 tools/fourcolor/near-linear/audit_core_profile_switch.py
cd lean/fourcolor-classical
lake build MettapediaFourColor.CoreProfileSwitchAudit
```

## A composed repair covers all eight three-run choices

[ThreeBlockRepairTransfer](../../../lean/fourcolor-classical/MettapediaFourColor/ThreeBlockRepairTransfer.lean)
proves repair for every Boolean triple in `ThreeBlockCore.word`. Two words
extend directly, two reuse the original seed theorem up to colour symmetry,
and the other four use three shared decisions. The extension contains six
direct source witnesses, eight references to existing checked seed states,
and 52 checked matching answers, encoded in 651 bytes.

[Repair composition](../../../lean/fourcolor-classical/MettapediaFourColor/KempeRepairComposition.lean)
retains the same exterior predicate when an answer invokes an earlier
repair. The old strategy is not copied, and applications use the checked
theorem without rerunning discovery. The new rank bounds three additional
abstract rounds before a leaf; it is not a physical switch-count bound.

```text
actual induced exterior + any of the eight joint boundary choices
                              |
             direct extension / old seed / three new decisions
                              |
                  compatible source and exterior witnesses
                              |
                  reconstruct all seven deleted vertices
```

[The uniform consumer](../../../lean/fourcolor-classical/MettapediaFourColor/ThreeBlockFamilyReconstruction.lean)
uses the ambient geometry theorem below. It retains the complete joint
boundary relation and reconstructs a genuine colouring for any exterior
size. The full cyclic source occurrence and the initial three-run boundary
class remain hypotheses; exterior planarity is derived.

[One explicit 18-vertex sphere](../../../lean/fourcolor-classical/MettapediaFourColor/ThreeBlockFamilyExample.lean)
realizes both new trace classes on its 11-vertex exterior. Neither initial
colouring extends while fixed. `changed_reconstruction` obtains a complete
ambient colouring and proves that its selected exterior differs somewhere
from the initial one. This example does not satisfy all possible
minimal-counterexample restrictions, nor supply a physical switch history.

This closes the immediate repair gap for the eight-word family. It does
not prove full D0092 reducibility or occurrence supply. A separate program
inventory finds 7,381 proper eleven-edge trace classes modulo colour
permutation, of which 1,303 extend directly; the family theorem does not
classify the rest. No coverage entry or original configuration certificate
is removed. The [discovery record](three-block-repair-transfer-discovery.json)
is untrusted program evidence; the
[measurement receipt](three-block-family-measurements.json) records the
Lean audit and costs.

```sh
python3 tools/fourcolor/near-linear/generate_three_block_repair_transfer.py \
  --output ThreeBlockRepairTransferData.lean --report three-block-transfer.json
cd lean/fourcolor-classical
lake build MettapediaFourColor.ThreeBlockFamilyAudit
```

## Ambient geometry now supplies the complete deletion contract

[ThreeBlockExteriorPlanar](../../../lean/fourcolor-classical/MettapediaFourColor/ThreeBlockExteriorPlanar.lean)
proves that an injective full D0092 core reading in a connected planar
triangular rotation supplies a connected planar exterior, with the ordered
eleven-port facial boundary and triangular remaining faces. These exterior
properties are conclusions. The ambient graph has no size bound.

The argument preserves actual graph darts. An affected retained face step
must belong to the specified boundary; every other triangular face survives
unchanged. Every surviving neighbour of the deleted core is a boundary
port, so the retained boundary connects all attachments. A bijection with
source darts counts exactly seven vertices and 29 edges removed. The
Gonthier/Emery Euler formulas then establish exterior planarity.

```text
connected planar triangulation + injective full cyclic core reading
                              |
                delete seven vertices and 29 edges
                              |
      connected planar exterior + ordered eleven-port boundary
                              |
               closed joint boundary colouring relation
                              |
      existing seed repair -> compatible ambient colouring
```

`repair_of_ambient` consumes this geometry in the existing compact seed
repair. It reconstructs every deleted vertex and agrees with the chosen
repaired exterior on every retained vertex. It still requires an initial
exterior colouring in the specified seed class. The geometry and closure
theorems themselves have no colouring or repair premise.

[The concrete source cone](../../../lean/fourcolor-classical/MettapediaFourColor/ThreeBlockExteriorPlanarExample.lean)
has 19 vertices and 51 edges; the theorem supplies its 12-vertex, 22-edge
exterior. This checks that the geometric hypotheses are inhabited. It
does not assert that this example supplies the specified seed colouring.

The remaining local obligation is repair for the other necessary boundary
classes. Occurrence supply and universal coverage remain separate open
obligations. No new repair table is added, and no catalogue removal or
whole-proof kernel saving is credited. The
[receipt](three-block-exterior-measurements.json) records the dependency
audit and module costs.

```sh
cd lean/fourcolor-classical
lake build MettapediaFourColor.ThreeBlockExteriorAudit
```

### Bounded test of repair reuse

[The transfer probe](probe_three_block_seed_transfer.py) reads the existing
41 checked seed states, pinned by their source hash. It adds no repair
records. Of the eight symbolic three-run boundary words, two extend
directly and two are colour permutations of the seed. Four remain outside
both sets, representing two edge-trace classes modulo colour permutation.

For each remaining class and each fixed edge colour, the probe tests every
noncrossing matching and every subset of whole chords. Each fixed colour
has a matching for which no answer reaches direct extension or a retained
seed state. The first failed matching for fixed colour 1 exposes the same
four-state set for both classes. None of those four states has a one-round
transfer into the accepted set. Direct extension is checked independently
by relational elimination and backtracking over the seven core vertices.

These are bounded program results. A failed unsigned matching has not been
realized by a planar exterior; the result does not rule out a longer or
differently chosen mixed-pair repair. It identifies a limitation of immediate
reuse, not an obstruction to D0092 reducibility or compact composition.
The [record](three-block-seed-transfer-probe.json) includes failed matchings
and all their answer traces.

```sh
python3 tools/fourcolor/near-linear/probe_three_block_seed_transfer.py \
  --output three-block-seed-transfer-probe.json
```

## Uniform boundary and complete stars after core deletion

[ThreeBlockDiskDeletion](../../../lean/fourcolor-classical/MettapediaFourColor/ThreeBlockDiskDeletion.lean)
derives the ordered eleven-port facial boundary after deleting D0092's seven
core vertices. Its input is an injective graph reading preserving every
cyclic core turn in a triangular ambient rotation. There is no bound on
ambient size. The rotation acts on the actual induced exterior graph:
at each retained vertex it skips the deleted neighbours and takes the
first retained successor. The source's eleven short fan arcs prove that
these successors follow the original port order.

[ThreeBlockDiskStars](../../../lean/fourcolor-classical/MettapediaFourColor/ThreeBlockDiskStars.lean)
proves that the same core reading has no extra ambient neighbours when
vertex rotations are cyclic. Each source row is closed under rotation;
every ambient dart at that vertex lies in the same orbit, so it must
already belong to the row. Complete core stars are a conclusion here.

```text
injective source + complete cyclic core turns + triangular faces
                              |
                  delete seven core vertices
                              |
       actual induced graph + exact ordered facial boundary
                              |
       planar exterior + triangular remaining faces
                              |
              existing seed repair and reconstruction
```

[The reconstruction consumer](../../../lean/fourcolor-classical/MettapediaFourColor/ThreeBlockDiskReconstruction.lean)
uses these results to discharge exterior coverage, complete stars, vertex
cyclicity, boundary order and boundary distinctness. It also derives the
exact seven-vertex decrease using the existing counting theorem. Exterior
planarity, triangular remaining faces and the specified initial seed
colouring are explicit inputs of this intermediate consumer. The newer
ambient theorem above supplies both exterior geometry inputs. This remains
one source shape, not full D0092 reducibility or a new coverage theorem.

A 19-vertex source cone supplies a checked instance of the complete core
reading and triangular rotation. It tests the orientation and inhabited
geometric contract; it does not supply a seed colouring. The source's 23
inner triangles and eleven fans are checked against the pinned D0092 rows.
No new colouring table or repair strategy is added. The repair consumer
retains the existing compact seed strategy and Gonthier/Emery Kempe theory.

```sh
cd lean/fourcolor-classical
lake build MettapediaFourColor.ThreeBlockDiskAudit
```

The [receipt](three-block-disk-measurements.json) separates the uniform
theorems, small checked source instance, remaining hypotheses and build
costs. Catalogue counts remain 633 coverage entries and 629 original
certificates, with 336 member checks replaced in the complete assembly.

## An actual exterior disk and source reconstruct the ambient graph

[The retained exterior](../../../lean/fourcolor-classical/MettapediaFourColor/ResidualExteriorDiskGeometry.lean)
now satisfies the planar disk contract in Lean: 155 vertices, 451 edges,
297 triangular faces and one ordered eleven-edge boundary. Complete
adjacency, cyclic neighbour rows and a spanning tour connect the compact
rotation data to the existing graph. The general
[row rotation](../../../lean/fourcolor-classical/MettapediaFourColor/GraphRotationRows.lean)
and [Euler](../../../lean/fourcolor-classical/MettapediaFourColor/GraphDiskEuler.lean)
lemmas establish vertex cyclicity and planarity without a table of all
dart-pair orbit relations. The Euler argument reuses Gonthier/Emery.

[The colouring consumer](../../../lean/fourcolor-classical/MettapediaFourColor/ResidualExteriorRepair.lean)
proves two complementary facts. Keeping the initial exterior colouring
fixed cannot colour the ambient graph. The joint seed repair nevertheless
supplies compatible genuine source and exterior colourings; the same
ambient colouring restricts to both of them. All seven deleted vertices
are filled, and every retained exterior vertex keeps the chosen repaired
colour. No geometry, closure or successful repair premise remains for this
particular 162-vertex graph.

```text
exact exterior graph + cyclic rows + local faces + Euler balance
                              |
                  planar joint boundary relation
                              |
                   existing compact seed repair
                              |
              one source + one compatible exterior
                              |
                one complete ambient colouring
```

The new input is 155 packed neighbour rows and a spanning tour, not a
colouring table. The previously checked 1,707-byte seed strategy and the
existing initial exterior colouring are reused. This proves one actual
consumer of the size-independent disk theorem. It is not a uniform
patch-deletion supplier, complete D0092 reducibility, or universal coverage;
it does not claim a physical Kempe-switch sequence from the initial
colouring to the selected exterior witness.

The [measurement receipt](residual-exterior-repair-measurements.json)
records local build costs, exact source and artifact hashes, and the
dependency audit. No complete Four Colour theorem or large repair table
is used. The complete classical proof retains 633 coverage entries and
629 original configuration certificates; 336 member checks are replaced.

```sh
python3 tools/fourcolor/near-linear/generate_exterior_disk_data.py
cd lean/fourcolor-classical
lake build MettapediaFourColor.ResidualExteriorAudit
```

## Planar exterior geometry supplies the joint repair relation

[PlanarGraphBoundaryClosure](../../../lean/fourcolor-classical/MettapediaFourColor/PlanarGraphBoundaryClosure.lean)
proves that a finite planar vertex graph with a duplicate-free facial dart
boundary and triangular remaining faces has a Kempe-closed joint boundary
observation. Vertex rotation orbits must coincide with actual vertices.
The mirrored dual preserves the forward port order, and both directions
of the colouring correspondence retain every boundary colour.

This uses the Gonthier/Emery Kempe theorem, without using a complete Four
Colour existence theorem. The argument is uniform in exterior size and
boundary length; it generates no new repair table.

[The reconstruction consumer](../../../lean/fourcolor-classical/MettapediaFourColor/ResidualSeedPlanarReconstruction.lean)
discharges the closure premise of the compact eleven-port seed repair from
these geometric hypotheses. Complete source stars and exterior coverage
then give an actual colouring of the ambient graph, agreeing with the
repaired exterior. Supply of the disk geometry after deletion, other seed
classes and universal coverage remain open.

The [punctured-rotation diagnostic](planar-exterior-disk-audit.json) checks
the retained example: 155 vertices, 451 edges, 297 triangular faces and one
eleven-edge boundary in the source port order. It verifies connectedness,
the Euler equation and equality with the existing Lean graph and ordered
ports. That receipt records the earlier program diagnostic. The separate
Lean instance and its colouring consumer are certified above.

```sh
python3 tools/fourcolor/near-linear/audit_planar_exterior_disk.py
cd lean/fourcolor-classical
lake build MettapediaFourColor.PlanarGraphBoundaryAudit
```

The [measurement receipt](planar-boundary-closure-measurements.json) records
the six-root dependency audit and local build costs. Coverage entries,
original certificate dependencies and replaced member checks remain
633 / 629 / 336.

## A compact mixed-pair repair for the retained D0092 seed

[The checked strategy](../../../lean/fourcolor-classical/MettapediaFourColor/ResidualSeedRepairChecked.lean)
repairs the boundary word `(1,3,2,3,1,0,3,0,2,0,2)` against every Kempe-closed
exterior that contains its edge trace. Direct extension of this word is
impossible, as `seed_not_direct` proves from the symbolic three-run core law.
The strategy can change colour pairs and retains the complete joint exterior
relation at each step. The failed fixed-pair preparation below is therefore
not an obstruction to all compatible repairs of this seed.

```text
actual noncrossing physical exterior
                |
     Kempe-closed joint observation
                |
    7 decisions / 161 matching cases
                |
  34 genuine complete source colourings
                |
  source and exterior share one whole trace
```

The generator's initial strategy has 674 reachable states and 3,157 matching
cases. Sharing lower-rank answers reduces these to 41 states and 161 cases.
The encoded records occupy 1,707 bytes; the complete Lean data module is
5,129 bytes. The module checking every answer and terminal witness built in
15 seconds in the recorded run. These are local costs, not measured savings
in the complete classical proof. Applications use the proved theorem without
repeating the discovery search.

[The witness consumers](../../../lean/fourcolor-classical/MettapediaFourColor/ResidualSeedRepairReconstruction.lean)
separate two representations. `physical_exterior` derives closure from
cubic open-tangle geometry and noncrossing physical component pairings, then
returns actual source and exterior colourings with equal complete traces.
`whole_repair` uses exact source stars, exterior coverage and colour alignment
to reconstruct the entire embedded graph. Its explicit closure hypothesis
is supplied by the planar disk bridge above when the exterior satisfies
that bridge's geometric hypotheses.

Only this seed and its retained dependency closure are certified. This is
not complete D0092 reducibility, an unbounded family of source reductions,
proof of occurrence supply, or a bound of five individual Kempe switches.
The rank bound applies to abstract matching rounds, each of which may change
several components. Other boundary classes, recognition of the exterior
disk after deletion and universal coverage remain open. Catalogue counts
remain 633 / 629.

```sh
python3 tools/fourcolor/near-linear/generate_residual_seed_repair.py \
  --output ResidualSeedRepairData.lean --report residual-seed-discovery.json
cd lean/fourcolor-classical
lake build MettapediaFourColor.ResidualSeedRepairAudit
```

The [discovery receipt](residual-seed-repair-discovery.json) is untrusted
program evidence; [measurements](residual-seed-repair-measurements.json)
record the separate kernel audit, consumers, costs and unchanged ledger.

## An extra changed port defeats the fixed preparation strategy

[PortPreparationObstruction](../../../lean/fourcolor-classical/MettapediaFourColor/PortPreparationObstruction.lean)
tests the proposed extension of the free-port repair: switch the entire
one/two component through port two, then finish with zero/two switches.
That component can also contain port four. The resulting two active
boundary runs have four possible joint choices, and none extends into
D0092. Five forced core colours prove this directly. The general
`no_tail_phase` theorem rules out every finite following zero/two history,
uniformly in the exterior size.

[The concrete consumer](../../../lean/fourcolor-classical/MettapediaFourColor/PortPreparationObstructionExample.lean)
uses the existing 155-vertex exterior. Its preparing component has 52
vertices and changes exactly ports two and four. A one/three path from
port one to port six survives, so retaining that path alone does not
justify the proposed finishing operation. `failed_whole_preparation`
proves that no endpoint of the restricted history extends to the actual
162-vertex ambient graph.

The same input admits a different two-step repair: switch the two-vertex
zero/two component at port five, then the singleton one/two component at
port eight. `alternative_repair` proves both physical component switches
and a complete ambient colouring agreeing with their result.

The [independent replay](port-preparation-obstruction-audit.json) verifies
the pinned sphere, source stars and cyclic order, residual connectivity,
and absence of an immediate one-switch repair. It also matches the Lean
graph, colouring and component literals to the replayed inputs. The
concrete spherical representation and the exhaustive one-step census are
program evidence; the arbitrary-length phase obstruction, actual component
switches and ambient colourings are kernel checked.

This excludes one fixed preparation strategy. A uniform structural repair
for this boundary class and compact geometric coverage remain open. No catalogue entry or original
certificate is removed by this obstruction.

## A free port supplies a two-step residual repair

[ResidualPortPreparation](../../../lean/fourcolor-classical/MettapediaFourColor/ResidualPortPreparation.lean)
handles a subclass of the remaining D0092 three-run boundary case. Ports
three and six share a one/three component. If port two has no exterior
neighbour of colour one, recolouring that port from two to one joins the
path to port one. The existing spherical separation theorem then forces
the zero/two component through port seven to avoid the first boundary runs.
Switching it gives the displayed proper core assignment and reconstructs
a colouring of the entire ambient graph.

The theorem permits arbitrary exterior size and path length. Its first
move supplies the separator used by the second; neither the final component
observation nor a successful colouring is assumed. The earlier one-step
branches and this supplier combine in `whole_repair_or_neighbor`: the
remaining case must also have a colour-one neighbour at port two.

[The finite consumer](../../../lean/fourcolor-classical/MettapediaFourColor/ResidualPortPreparationExample.lean)
checks the free-port condition and old path on the retained 155-vertex
exterior, then invokes the general preparation law. The concrete spherical
representation and full reconstruction instances are checked separately by
the [program replay](residual-port-preparation-audit.json).

| Sphere vertices | First component | Second component | Successful immediate repairs |
| ---: | ---: | ---: | ---: |
| 162 | 1 | 62 | 0 |
| 3,759 | 1 | 476 | 0 |
| 12,097 | 1 | 1,136 | 0 |

Each replay uses the same two commands and direct seven-vertex core
assignment, without searching for a successful history. The larger spheres
preserve the exact core stars and their cyclic order; a new short-cycle
census is not claimed for them.

The local guard is not universal. A second colouring of the original sphere
has a colour-one neighbour at port two and still has no immediate repair.
Switching the two-vertex component containing port two, followed by the
36-vertex finishing component, repairs it. This is an explicit program
example beyond the singleton supplier, not a proof of that more general
supplier. Universal two-step repair and geometric coverage remain open.
No catalogue entry or original configuration certificate is removed.

Replay `lake build MettapediaFourColor.ResidualPortPreparationAudit` in the
classical package, and from the repository root:

```sh
python3 tools/fourcolor/near-linear/audit_residual_port_preparation.py
```

The [measurement receipt](residual-port-preparation-measurements.json)
separates the parameterized proof, finite consumer and program instances.

## Flat-seven returns and a shared-core test

Two small replay recipes test the proposed continuation through flat
degree-seven centres. Each gives a 162-vertex triangulated sphere of degrees
five through seven containing a facial triangle of three flat sevens.
All cycles of length three through five pass the short-cycle obstruction
test: a three- or four-cycle has an empty side, and a five-cycle has a side
containing at most one vertex. Flat sevens therefore need not form an
acyclic graph under these hypotheses. This does not refute continuation
with additional hypotheses or a separately justified progress measure.

| Recipe | Legal flips | Short cycles checked | Source occurrence | Boundary ports |
|---|---:|---:|---|---:|
| [First return](flat-seven-return-example.json) | 70 | 1,815 | D0092 | 11 |
| [Second return](flat-seven-return-extension-example.json) | 310 | 1,823 | D0063 | 10 |

In the first example, the union of radius-two balls at the three centres
contains no complete-core reading of D0000, D0001, D0004, D0006, D0051,
D0052 or D3009. The second example excludes those same readings and also
D0092 and D0142. All rooted darts and both orientations are tested;
boundary identifications are permitted in the negative search. The simple
diamond, chain and one/two-five wheel profiles are absent in both unions.
These are specified local inventories, not the entire reduction library.
Only the three centres are asserted flat; flatness of their entire
neighbourhoods is not assumed or established.

The positive D0092 and D0063 occurrences retain every source vertex,
ordered boundary edges, full core stars and cyclic order. Their induced
seven-vertex cores lie within radius two, and their full boundaries within
radius three. Their [core correspondence](flat-seven-return-core-map.json)
preserves all eleven internal edges and five internal facial triangles,
with one global reflection. Four prescribed degrees change and the
boundaries have different lengths. This supplies a concrete candidate for
a common family argument; it does **not** establish boundary transport,
colouring repair or a new reduction.

The [verifier](audit_flat_seven_return.py) replays legal flips from the
existing sphere fixture, compares compiled and breadth-first rule matching,
checks all short cycles, and verifies the supplied core map without an
isomorphism search. The [first receipt](flat-seven-return-audit.json) and
[second receipt](flat-seven-return-extension-audit.json) are exact program
checks, not Lean certification. No coverage entry or proof dependency is
removed. Replay from the repository root:

```sh
python3 tools/fourcolor/near-linear/audit_flat_seven_return.py
python3 tools/fourcolor/near-linear/audit_flat_seven_return.py --fixture flat-seven-return-extension-example.json
```

D0063, D0092 and D0142 are copied unchanged from the
[near-linear catalogue](https://github.com/near-linear-4ct/reducible-configurations/tree/c2ce7a96e35256201526e2abb51a39d04a588b53/D)
at revision `c2ce7a96e35256201526e2abb51a39d04a588b53`, under its retained
[MIT licence](LICENSE). The recipes pin their hashes and the existing
discharging-rule revision. These examples concern the flat facial
seven-triangle setting of
[Lemma 8.5](https://arxiv.org/html/2603.24880v1#S8.Thmthm5);
they do not contradict the paper's larger catalogue coverage.

## Boundary choice versus coordinated recolouring

The shared five-triangle core does not justify a fixed boundary-collapse
transfer from D0092 to D0063. Three explicit source colourings exclude all
220 choices of source seam, target rotation and reflection. Each failure
has a short forced-colour explanation and an independent exhaustive check
of the seven target interior vertices. The
[Lean obstruction](../../../lean/fourcolor-classical/MettapediaFourColor/FiveTriangleCollapseObstruction.lean)
certifies one fixed alignment: a genuine source colouring would leave a
target triangle with only two available colours.

Adaptive interior choices fare differently. The
[program audit](five-triangle-collapse-audit.json) enumerates all source
and target colourings with one vertex fixed to colour zero, giving 7,818
and 3,732 distinct edge traces. Every source trace has some successful
collapse and alignment. This assertion concerns interior extension only.

An explicit planar exterior exposes the missing coupling. For one source
colouring, there are 40 distinct proper collapsed traces. Six extend through
a decagon triangulated as a fan, and sixteen extend into D0063, but no trace
does both. The source colouring is held fixed in this test. The glued target
and fan themselves have 414 compatible traces outside this restricted set,
so the obstruction concerns the proposed transport choices, not colourability.

A coordinated recolouring resolves this particular obstruction. Keep one
fixed seam and the same fan exterior, and switch the complete two-vertex
component with colours zero and three in the glued source graph. The new
boundary extends into D0063 while agreeing with that exterior at every
retained vertex. The
[Lean witness](../../../lean/fourcolor-classical/MettapediaFourColor/FiveTriangleJointChoice.lean)
checks the initial and final proper colourings, the complete component, the
exact fan adjacency on both interfaces and the common boundary colours.
The [seven-root audit](five-triangle-collapse-measurements.json) uses only
standard axioms and no configuration rank or repair table.

This is one compatible repair in a specified context. It proves no uniform
family reduction, arbitrary-exterior repair law or geometric coverage.
The next contract must coordinate the retained exterior Kempe components
with recolouring and seam selection. Separate existence of an interior
choice and an exterior choice is insufficient. No catalogue entry or
certificate dependency is removed by this test.

Replay `lake build kernelFiveTriangleCollapse` in the classical package,
and from the repository root run
`python3 tools/fourcolor/near-linear/audit_five_triangle_collapse.py`.
The [fixture](five-triangle-collapse-example.json) stores explicit colouring
witnesses and the one-step repair; its repair search is not replayed.

## A fixed seam can remain blocked through every Kempe history

The next context test rules out a stronger unconditional contract. Attach a
decagon fan to D0092, retaining ten ordered ports and bypassing source boundary
vertex 6. In the displayed colouring every pair of distinct colours has one
connected support. Every whole-component Kempe switch therefore only renames
colours globally. This remains true after any finite number of adaptive switches.

Both orientations of this seam leave target vertices 11, 12 and 14 of D0063
with only two available colours, although they form a triangle. The
[Lean theorem](../../../lean/fourcolor-classical/MettapediaFourColor/FiveTriangleKempeTrap.lean)
proves failure for the existing physical Kempe closure and proof-relevant GSLT
histories. The general
[palette invariant](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/KempePaletteRigidity.lean)
uses six connected pair supports; it does not enumerate recolouring histories.
A different source colouring reconstructs in the very same fan exterior, also
checked in Lean. The obstruction is thus to repair of a prescribed choice while
retaining this seam, not to the existence of compatible colourings.

The [exact program audit](five-triangle-kempe-trap-audit.json) independently
checks a spherical rotation with 18 vertices, 48 edges and 32 triangular faces,
preserving the source core's cyclic stars. The embedding check is not a Lean
planarity theorem. The sphere has a degree-three vertex: this example does not
refute a contract with stronger minimal-counterexample hypotheses. Alternative
seams, rollback and different reductions remain available mechanisms to test.

The [eight-root dependency audit](five-triangle-kempe-trap-measurements.json)
uses only standard axioms and no configuration repair table. No coverage entry
or original certificate dependency is removed. Replay
`lake build kernelFiveTriangleKempeTrap` and
`python3 tools/fourcolor/near-linear/audit_five_triangle_kempe_trap.py`.
The [fixture](five-triangle-kempe-trap-example.json) contains six short walks
and explicit colourings, rather than a table of search histories.

## Removing the old interior permits a uniform fan repair

The whole-source obstruction above does not obstruct the exterior repair
contract used by the reduction machinery. That contract permits the old
interior to be removed before recolouring. Retaining its colouring throughout
would impose an additional restriction.

The [ordered-fan theorem](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/OrderedFanKempe.lean)
proves that any two proper colourings of a fan of any finite length are joined
by genuine Kempe switches. It works for any palette admitting those two
colourings. Align the hub colour, then align successive path vertices by
swapping two colours on a suffix. The hub and the already aligned predecessor
use neither swapped colour. The existing partial-transposition theorem
decomposes each suffix operation into switches of whole connected components.
The resulting witness is a GSLT history; no table of colouring states is used.

The [concrete consumer](../../../lean/fourcolor-classical/MettapediaFourColor/FiveTrianglePuncturedRepair.lean)
identifies the ten retained vertices of the trapped example with the exact
induced fan, including every edge between them. Every proper exterior state
can reach one explicit boundary colouring which reconstructs both the original
source and the target patch. In particular, the previously trapped state can
be repaired on this exterior. Lean also proves that no history keeping the
whole old source can reach that same boundary endpoint. The source has a
degree-three vertex, so it does not satisfy minimum-degree-five hypotheses.

This proves one law for all fan lengths and supplies an actual patch consumer.
It does not extend the law to arbitrary planar exteriors, prove that the
coverage argument supplies fan exteriors, or remove a catalogue dependency.
The concrete reduction retains ten of eighteen vertices; the all-length
theorem concerns recolouring, not an all-length family of patch reductions.
No bound on extracted execution time is claimed.

The [eight-root audit and replay measurements](five-triangle-punctured-measurements.json)
use only standard axioms, with no classical Four Colour theorem or configuration
repair table. The generic proof built in 2.7 seconds; the concrete consumer
replayed in 4.049 seconds and its audit in 3.461 seconds. These are module
measurements, not savings in the complete classical proof. Replay
`lake build Mettapedia.GraphTheory.FourColor.OrderedFanKempe` in the main package
and `lake build kernelFiveTrianglePuncturedRepair` in the classical package.

## Current pair partitions are insufficient for repeated updates

The [boundary observation theorem](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/KempeBoundaryObservation.lean)
separates two requirements for a compressed exterior state. On every graph,
the current boundary colours and all current bichromatic connectivity
relations determine the boundary colours after one rooted Kempe switch.
They do not determine the new connectivity relations needed for later moves.

A four-cycle with three retained ports proves the distinction:

```text
port 0: colour 0 ----- port 1: colour 1
       |                     |
hidden: colour 1 or 3 -- port 2: colour 2
```

Both choices at the hidden vertex are proper and give the same observed
boundary word and all six pair partitions. In each state, the component of
colours 0 and 2 rooted at port 0 is a singleton. Switch it. Both boundary
words become `(2,1,2)`, but the colour-2 ports are connected through colours
2 and 3 precisely when the hidden vertex has colour 3. Consequently no
function of the old summary computes the full new summary for this operation.
A second switch, using colours 2 and 3 at port 0, yields boundary words
`(3,1,2)` and `(3,1,3)`. Lean also rules out computing the boundary word after
these two commands from the initial summary. The proof consumes the existing
GSLT non-factorization criterion.

This is an obstruction to deterministic updating of this particular summary.
It is not an impossibility of compositional repair. The same module certifies
an invisible interior switch joining the two initial states and a two-step
physical history producing the other outcome. A relational summary may retain
both possibilities, but concatenating its transitions requires compatible
concrete witnesses or a proved preparation/lifting law. Existentially choosing
a different hidden witness at each step does not establish such a law.

The [spherical replay](flat-seven-observation-audit.json) finds the same failure
on the complete 155-vertex punctured exteriors of both existing flat-seven
fixtures, with 11 and 10 ports respectively. It checks four actual proper
colourings, the hidden component and both boundary-rooted component switches
in each exterior. Before the switches, all six boundary partitions agree;
afterwards the words still agree and two pair partitions differ. A further
common boundary command produces different boundary words in each example.
The ambient spheres have degrees 5 through 7, three marked flat centres, and no obstructing
short cycles under the existing test. Flatness of an entire surrounding ball
and minimal-counterexample hypotheses are not asserted. These geometric
applications are exact program evidence; the general four-cycle obstruction
is separately kernel checked.

Replay `lake build Mettapedia.GraphTheory.FourColor.KempeBoundaryObservationAudit`
in the main package and
`python3 tools/fourcolor/near-linear/audit_boundary_observation.py` from the
repository root. The [measurement receipt](boundary-observation-measurements.json)
records the eight-root audit and build costs. The
[fixture](flat-seven-observation-example.json) stores one initial exterior
colouring and two rooted commands per case. The shared boundary command is
executed in both states. No table of possible histories is stored. No coverage
entry or original certificate dependency is removed.

## Exact independent elimination with joint repair choices

The [independent lifting theorem](../../../lean/mettapedia/Mettapedia/GraphTheory/Kempe/IndependentLift.lean)
provides a positive alternative to deterministic partition updates. Let `S`
be any finite independent set of hidden vertices in a finite graph, with an
arbitrary colour palette. The retained graph and hidden degrees are unrestricted.
Its interface consists of the retained graph and the joint constraints

```text
for every hidden vertex v:
    some colour is absent from all retained neighbours of v.
```

These constraints characterize extension exactly. A joint operation may switch
any union of components of one colour pair, provided its target still satisfies
all the constraints. Every such history lifts to an actual Kempe history
between the specified full endpoints. Conversely, every actual history projects
to such a joint history. A designated retained boundary can stay fixed through
every physical move. The proof prepares hidden colours, decomposes a proper
partial transposition into actual components, then finishes the hidden colours.
It uses the existing fibration and path-composition theorems. No table of
colouring states or histories occurs in the proof.

The [certified consumers](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/IndependentBoundaryRepair.lean)
include the preceding four-cycle example and a five-vertex star. In the star,
the hidden hub sees leaf colours `(1,1,2,3)`. Changing either first leaf alone
to `0` leaves no colour for the hub. Changing both together to `0` is valid:
the hub changes from `0` to `1`, while the last two leaves stay fixed. Lean
proves both individual extension failures and the joint physical repair.
Thus requiring every retained component to move separately is too restrictive.

The [spherical consumers](independent-repair-audit.json) replay this mechanism
on the two complete punctured exteriors. Each eliminates 33 independent
vertices from a 155-vertex exterior, retaining 122 vertices and 33 availability
constraints of widths 5 through 7. Both starting boundary words fail to extend
to their seven-vertex patches. Two joint operations per example reach words
that reconstruct proper colourings of the entire 162-vertex ambient sphere.
All preparation, component switching, finishing, and final ambient edges are
checked. In the D0092 second operation all 18 selected retained components
have invalid targets individually; the joint target is valid. In the D0063
second operation the same holds for all 28 selected components. Each joint
operation in these fixtures lifts to one full-exterior component switch.
The fixtures store only the initial colouring, the hidden set and two commands.
These geometric applications remain independent program evidence; the generic
law and the four-cycle/star consumers are kernel checked.

This is elimination into a graph **with retained constraints**. It is not a
standalone ordinary Four Colour reduction, and it does not prove all starting
colourings of these exteriors repair. Iterating elimination requires preserving
the accumulated constraints; closure in a compact family is not established.
No catalogue entry or original configuration certificate is removed. The
[measurement receipt](independent-repair-measurements.json) distinguishes these
claims and records the audit and costs.

Replay `lake build Mettapedia.GraphTheory.FourColor.IndependentBoundaryRepairAudit`
in the main package and
`python3 tools/fourcolor/near-linear/audit_independent_repair.py` from the
repository root.

## Adjacent interiors: extension and step lifting separate

The [two-vertex fibre theorem](../../../lean/mettapedia/Mettapedia/GraphTheory/Kempe/TwoVertexFibre.lean)
proves that any two proper colourings of a finite graph agreeing outside two
vertices are connected by Kempe switches avoiding that exterior. The palette
and degrees are unrestricted; the two hidden vertices may be adjacent.
Either one vertex can be recoloured first, or a two-colour interchange repairs
both. This is a uniform proof without a colouring-state table.

Nevertheless, [an exact nine-vertex example](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/AdjacentHiddenObstruction.lean)
shows that connected fibres and extendable targets do not suffice for lifting
moves between different retained colourings. Its core is the triangle `0,1,2`,
with leaves `3,6` at `0`, `4,7` at `1`, and `5,8` at `2`. Hide `0,1` and protect
all six leaves. Both full colourings

```text
vertex:   0 1 2 | 3 4 5 6 7 8
initial:  0 2 1 | 1 0 2 3 3 3
target:   2 1 0 | 1 0 2 3 3 3
```

are proper. In the retained graph, switching colours `0,1` at vertex `2`
produces the target restriction in one component move. Yet every nontrivial
full component at the initial state touches a protected leaf. Consequently
**no history fixing that context reaches any extension of the target**.
Lean proves this by a local transparency invariant and induction on arbitrary
histories. The results refute both single-component and joint-operation
on-image lifting without the independent-set hypothesis.

The same example has a precise repair. Permit only leaf `3` to change
temporarily and switch these actual full components in sequence:

| Colour pair | Component vertices | Colour at leaf 3 afterward |
| --- | --- | --- |
| `0,1` | `2,0,3` | `0` |
| `0,2` | `3` | `2` |
| `1,2` | `1,0,3` | `1` |

This reaches the stated target and restores the entire boundary. The other
five leaves remain fixed throughout. Saturated path witnesses certify all
three physical components; the repair also yields a GSLT history.

Thus repeated elimination needs control of allowed transitions as well as
endpoint extension. Temporarily changing a context vertex must itself be
justified when the patch is placed in a larger graph. The example has
degree-one leaves; it does not establish an obstruction in the stronger
minimal-counterexample geometry, rule out alternative decompositions, or
prove compact compositional Four Colour proofs impossible. No coverage entry
or original certificate dependency is removed.

Replay `lake build Mettapedia.GraphTheory.FourColor.AdjacentHiddenObstructionAudit`.
The [measurement receipt](adjacent-hidden-measurements.json) records eleven
audited roots and costs. No external configuration certificate is used.

## Unbounded cooperation with one uniform repair proof

The [boundary-cooperation family](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/BoundaryCooperation.lean)
replaces each of the preceding six leaves by `r` copies, keeping the same
triangle. It has `3 + 6r` vertices. The reduced command still hides only two
adjacent corners and changes the third by one component switch. Both full
endpoint colourings exist and agree on every boundary leaf.

Lean proves an exact cost for the surrounding cooperation:

```text
fewer than r boundary vertices may change  →  the core cannot move
all r copies of the first leaf may change  →  a physical repair exists
                                             and restores every boundary colour
```

The lower bound uses one untouched representative from each leaf group.
They recover the frozen nine-vertex obstruction. The new general
[history projection theorem](../../../lean/mettapedia/Mettapedia/GraphTheory/Kempe/HomProjection.lean)
shows that a physical history pulls back along any graph homomorphism from a
finite observing graph, with the protected context pulled back as well.
A full component may split, so one full step becomes a sequence of smaller
component switches. This proves the lower bound for arbitrary histories,
including temporary changes to unprotected leaves.

The matching repair has three uniform partial-transposition phases: switch
the first colour pair through the core and first leaf group, recolour that
leaf group, then switch the second core pair. The middle phase decomposes
into separate physical components. No colouring-state or history table is
used, and all widths produce actual GSLT histories. This disproves a constant
bound on the number of cooperating boundary vertices for this contract while
providing a short proof for the entire family. It is not a lower bound on
proof length, interface description size, or the number of structural laws.

The leaves have degree one and core degrees grow with `r`. These examples do
not establish an obstruction under the stronger geometric hypotheses of the
coverage argument. Nor do these repair histories establish a strict graph
reduction or geometric supply theorem. The surrounding graph must permit
any temporary boundary changes. Coverage and certificate counts are unchanged.

Replay `lake build Mettapedia.GraphTheory.FourColor.BoundaryCooperationAudit`.
The [measurement receipt](boundary-cooperation-measurements.json) records the
uniform statements, dependency audit, and verification costs.

## Frozen observers in the actual spherical exteriors

The [frozen-observer theorem](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/FrozenBoundaryObserver.lean)
transports the obstruction into an arbitrary finite graph through a graph
homomorphism and a permutation of the four colour labels. The observer's
leaves need not be leaves of the ambient graph. Injectivity and inducedness
are unnecessary: proper colourings and physical histories pull back along
the homomorphism. Protecting the images of its boundary therefore freezes
the observed core throughout every possible history.

The [independent replay](frozen-observer-audit.json) checks two concrete
applications on the complete 155-vertex punctured exteriors of the existing
162-vertex spherical fixtures. The ambient degrees are five through seven.
Each operation hides two adjacent exterior vertices off the original patch
ports, switches one actual retained component, and has a proper extension
over those two vertices.

| Original patch | Retained component size | Original patch ports changed | Ambient degrees at the observer core |
| --- | --- | --- | --- |
| D0092 | 17 | 4 | `5,5,7` |
| D0063 | 5 | 1 | `5,7,6` |

In both cases the nine observer vertices map to eight distinct exterior
vertices; two observer leaves have the same image. All nine observer edges,
the complete initial colour pattern, the protected boundary images, both
proper exterior endpoints, and the changed observed core are checked. Thus
the target cannot be reached while keeping every unchanged retained vertex
fixed. The replay checks the premises of the universal Lean theorem and
requires no search through recolouring histories. The actual geometric
applications remain program evidence; they are not kernel-certified graph
instances.

Extension over the newly hidden pair is a different obligation from restoring
the original seven-vertex patch. Both selected target words still fail the
latter test. These witnesses refute endpoint-only acceptance of a proposed
fixed-context step; they do not refute the existence of successful choices.
The earlier two-step independent-set repairs still colour both complete
spheres. Whole-ball flatness and minimal-counterexample hypotheses are not
asserted, and no coverage entry is removed.

Replay `lake build Mettapedia.GraphTheory.FourColor.FrozenBoundaryObserverAudit`
and `python3 tools/fourcolor/near-linear/audit_frozen_observer.py`.
The [fixture](frozen-observer-example.json) pins the existing source colourings
and stores only the observer map and reduced command. The
[measurement receipt](frozen-observer-measurements.json) separates the five-root
kernel audit from the concrete program checks.

## Exact guarded repair across an interacting hidden pair

[GuardedLift](../../../lean/mettapedia/Mettapedia/GraphTheory/Kempe/GuardedLift.lean)
repairs the failed endpoint-only contract. For hidden adjacent vertices `u,v`,
let `A_u(C)` and `A_v(C)` be the colours absent from their retained neighbours
in colouring `C`. For a proposed retained partial transposition `σ`, the guard
asks for colours `x,y` before and `x',y'` after such that

```text
x ∈ A_u(C),  y ∈ A_v(C),  x ≠ y
x' ∈ A_u(D), y' ∈ A_v(D), x' ≠ y'
x' = x or σ(x);  y' = y or σ(y).
```

These are local colour conditions, not a hypothesis about an unknown repair
history. The kernel theorem proves that guarded histories are equivalent to
physical Kempe histories for every finite graph, every palette, and every
choice of two hidden vertices. The proof prepares the hidden colours, realizes
a proper partial transposition as actual component switches, and finishes at
the requested extension. The proved two-vertex fibre theorem ensures that
successive witnesses compose.

The general construction applies to larger hidden sets only when the
corresponding fibre-connectivity hypothesis is separately proved. Subsequent
elimination must preserve the generated transition guards; a constrained
interface cannot be silently treated as an ordinary graph.

[GuardedBoundaryRepair](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/GuardedBoundaryRepair.lean)
certifies that the nine-vertex obstruction has neither a guarded step nor a
guarded history with its boundary fixed. Its three-switch repair still passes
through the same interface when the cooperating leaf may temporarily move.

The [concrete replay](transition-guard-audit.json) checks both spherical
exteriors again. It rejects each frozen-observer command and reconstructs
the two successful physical switches that restore the original patch in each
162-vertex sphere. The hidden pair's guard observes six retained neighbours
in D0092 and eight in D0063. Deleting the hidden edge makes both bad commands
pass: independent marginal choices lose exactly the relevant constraint.

The four-colour program checks at most 16 before assignments and four after
choices for each one, with no search through histories. The actual geometry
and reconstruction instances remain program evidence. This result establishes
a faithful interface contract, not a new coverage theorem or a smaller
unavoidable set; no catalogue or certificate saving is credited.

Replay `lake build Mettapedia.GraphTheory.FourColor.GuardedBoundaryRepairAudit`
and `python3 tools/fourcolor/near-linear/audit_transition_guard.py`.
The [measurement receipt](transition-guard-measurements.json) records the
universal theorem and the separate finite applications.

## Arbitrarily many hidden pairs, and the first state-loss obstruction

[PairBlocks](../../../lean/mettapedia/Mettapedia/GraphTheory/Kempe/PairBlocks.lean)
extends the guarded theorem to any number of isolated hidden vertices and
pairs. Block labels must separate all hidden edges, and every nonempty block
must contain at most two vertices. Distinct blocks may share retained
neighbours. One proof establishes connected fibres, factors the transition
guard into local block conditions, and proves exact physical-history
equivalence. All guards observe the same retained colouring and the same
colour transposition; their marginal possibilities are not combined freely.

The [program replay](pair-blocks-audit.json) applies this law to larger hidden
sets in the two spherical exteriors, preserving all original patch ports and
the protected frozen-observer vertices:

| Patch | Hidden vertices | Retained exterior vertices | Pair / singleton guards | Distinct neighbours per guard |
| --- | --- | --- | --- | --- |
| D0092 | 53 | 102 | 23 / 7 | 5–9 |
| D0063 | 52 | 103 | 23 / 6 | 5–10 |

The previous independent deletion hid 33 vertices and retained 122 in each
case. Total guard-neighbour incidences change from 210 and 212 to 206 in each
case. A pair guard, however, retains four before/after colour variables rather
than a single endpoint availability choice. These counts therefore describe
different interfaces, not a certified net reduction in all checking costs.
Both obstructed commands remain rejected, and both successful two-switch
repairs still reconstruct the complete 162-vertex sphere. These geometric
applications remain program checked, not kernel-certified instances.

[HiddenTriangleObstruction](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/HiddenTriangleObstruction.lean)
identifies a limit to extending this theorem. Hiding all three core vertices
of the nine-vertex example makes two distinct physical classes have exactly
the same retained colouring. Their reflexive abstract path cannot lift with
the boundary fixed. Restricting the step relation alone cannot restore a
distinction erased from the state. A larger-block theorem must prove connected
fibres, retain the relevant hidden class, or justify another successful choice.
The example has pendant vertices; minimal-counterexample geometry and a
universal impossibility of compositional proofs are not asserted.

Replay `lake build Mettapedia.GraphTheory.FourColor.PairBlocksAudit` and
`python3 tools/fourcolor/near-linear/audit_pair_blocks.py`. The small
[fixture](pair-blocks-example.json) stores the two partitions. The
[measurement receipt](pair-blocks-measurements.json) records the eight-root
audit and separate consumer checks. No coverage entry or configuration
certificate is removed.

## A facial triangle with two hidden classes in a complete sphere

The [direct witness replay](hidden-triangle-audit.json) places the state-loss
obstruction in the actual D0063 spherical fixture. In its complete proper
162-vertex colouring, hide facial triangle `33,75,76` and keep the other 159
vertices fixed. The allowed hidden colours are respectively `{0,2}`, `{1,2}`
and `{0,1}`. Exactly two proper assignments remain:

```text
(2,1,0)       (0,2,1)
    \         /
     same exterior colouring
     different physical classes with that exterior fixed
```

The sphere has degrees five through seven; the hidden vertices have degrees
`5,5,7`. A homomorphism from the frozen nine-vertex observer verifies the
obstruction without exploring recolouring histories. All observer images
have degree at least five. A second witness occurs at facial triangle
`27,88,129` in the initial punctured exterior.

[FrozenFibreObserver](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/FrozenFibreObserver.lean)
proves the universal consequences of these premises. The retained-colouring
projection has disconnected fibres, and no abstract step relation on that
state space makes it a fibration for the specified physical histories. The
two concrete instances, including the sphere geometry and proper endpoints,
are independently program checked; they are not kernel-certified graph
instances.

This failure concerns lifting between arbitrary specified extensions while
the exterior stays fixed. Both complete-sphere endpoints are already valid
colourings. It does not refute existence of successful compatible choices,
interfaces that retain the hidden class, exterior recolouring, or an
alternative decomposition. Minimal-counterexample hypotheses and global
coverage remain separate obligations.

Replay `lake build Mettapedia.GraphTheory.FourColor.FrozenFibreObserverAudit`
and `python3 tools/fourcolor/near-linear/audit_hidden_triangle.py`. The
[fixture](hidden-triangle-example.json) pins the source reconstruction and
small observer maps. The [receipt](hidden-triangle-measurements.json) records
the two-root audit and the exact scope.

## Uniform repair through arbitrary hidden forests

[ForestFibre](../../../lean/mettapedia/Mettapedia/GraphTheory/Kempe/ForestFibre.lean)
proves that any two full proper colourings agreeing outside an induced forest
are joined by actual Kempe switches that fix the entire exterior. The forest,
ambient graph and palette have unrestricted size. The proof uses leaf
induction with arbitrary allowed colour sets, not a table of forest colourings.

The leaf argument preserves the two specified endpoints. If their colours at
the leaf agree, that colour is fixed and excluded at its neighbour. If they
differ, at least one of those two colours extends every colouring of the
remaining forest, since the leaf has at most one remaining neighbour. A
compatible colour bridge lifts each move. Proper partial transpositions then
decompose into actual component switches in the original ambient graph.

[ForestGuard](../../../lean/mettapedia/Mettapedia/GraphTheory/Kempe/ForestGuard.lean)
represents a joint transition by one old colour and one switch bit per hidden
vertex: eight labels for four colours. Unary constraints check all retained
neighbours at both endpoints; binary constraints check every hidden edge at
both endpoints. Its exact leaf-elimination theorem sends a unary constraint
to the remaining neighbour and reconstructs the removed vertex. Both edge
orientations and one shared assignment are retained. Forest recognition
supplies leaves, and each removal strictly decreases the vertex count.

The [program replay](forest-repair-audit.json) applies these laws to two actual
spherical repair examples:

| Configuration | Hidden vertices | Retained vertices | Hidden edges | Cross-interface edges | Physical switches |
|---|---:|---:|---:|---:|---:|
| D0092 | 74 | 81 | 72 | 281 | 11 |
| D0063 | 74 | 81 | 72 | 283 | 2 |

Each hidden set consists of two induced trees, with maximum hidden degree
three. Both known obstructed commands are rejected. Successful guards are
checked by leaf messages, without enumerating products of tree colourings;
their assignments lift to actual component switches and reconstruct the
complete 162-vertex spherical colouring. The generic theorems are kernel
checked. The concrete geometry and Python executions are program evidence.

The carrier is smaller than in the separated-pair examples, which retained
102 and 103 vertices. The interface still contains all the indicated crossing
edges, and D0092 needs additional preparation and finishing switches. No net
storage or runtime saving is claimed. Eight labels per hidden vertex do not
mean eight states for the whole boundary. The guard evaluator's leaf identity
is proved; the Python implementation is not itself kernel-certified.

The hidden-triangle obstruction explains a limit of this result. A forest
has no lost fixed-exterior physical class; adding a cycle can introduce one.
Retaining vertices that break all hidden cycles permits the forest theorem
to apply to the remainder. Controlling how much information such retained
vertices and their shared exterior require under further composition is a
separate task. No ordinary smaller-map reduction, global geometric coverage
or catalogue saving follows from the forest theorem alone.

Replay `lake build Mettapedia.GraphTheory.FourColor.ForestGuardAudit` and
`python3 tools/fourcolor/near-linear/audit_forest_repair.py`. The
[fixture](forest-repair-example.json) pins the two selected forests; the
[receipt](forest-guard-measurements.json) records the nine-root dependency
audit, costs and scope. The source repair and attribution chain are retained.

## Cycle closure with retained colours

[CycleAnchors](../../../lean/mettapedia/Mettapedia/GraphTheory/Kempe/CycleAnchors.lean)
proves that if deleting a retained set `K` from a hidden region `S` leaves
a forest, any two full proper colourings agreeing on `K` and outside `S`
are connected by actual Kempe switches fixing both. A family of pairwise
unreachable extensions of the same exterior therefore has at most
`q ^ |K|` members for a palette of size `q`. For one retained vertex and
four colours the bound is four, independent of the size of `S`.

This distinguishes classes without declaring different retained colours
unreachable: some can communicate through exact joint forest guards.
`history_iff` proves both projection and reconstruction of entire histories
while the original exterior remains fixed. The retained colours may move;
feasibility and each transition still have to be checked.

The [program replay](cycle-anchors-audit.json) uses the existing complete
162-vertex sphere, whose degrees are five through seven. The frozen triangle
has two feasible retained colours and no transition between them. A six-cycle
around an actual vertex has two feasible retained colours in one class;
their transition reconstructs into two physical component switches and fixes
all 156 vertices outside the cycle. The leaf guard uses fifteen forward
binary comparisons, excluding unary filtering and reconstruction. Independent
enumeration of the two tiny local fibres (two and four full assignments)
agrees with the guarded class partitions. Neither enumeration is used by the
generic kernel proof, and concrete geometry remains program evidence.

This repairs the loss of hidden class information for the stated domain.
The theorem does not bound `|K|` for arbitrary maps, require enumerating all
anchor assignments, produce an ordinary smaller map, establish geometric
coverage or remove a catalogue dependency. The growth of the joint retained
information under composition remains open.

Replay `lake build Mettapedia.GraphTheory.FourColor.CycleAnchorsAudit` and
`python3 tools/fourcolor/near-linear/audit_cycle_anchors.py`. The
[fixture](cycle-anchors-example.json) pins both cycles; the
[receipt](cycle-anchors-measurements.json) records theorem sizes and audits.

## Many cyclic choices without a table of their product

[BlockChoices](../../../lean/mettapedia/Mettapedia/GraphTheory/Kempe/BlockChoices.lean)
constructs proper full colourings from independent choices on separated
hidden blocks. It needs one alternative per block, not one colouring for
every combination. Blocks may share exterior neighbours. Retaining a
cycle-breaking set makes the remaining forest guards factor exactly, and
the resulting histories reconstruct physically. Each factor receives the
same retained before/after colours and the same transposition; independent
existential choices for those shared observations would not suffice.

[FrozenCycleFamily](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/FrozenCycleFamily.lean)
supplies the complementary lower bound. Given `k` separated blocks with
proper alternatives and protected frozen observers, the Boolean construction
produces `2 ^ k` mutually unreachable full colourings of the same exterior.
Any finite summary whose fibres are physically connected needs at least
that many states. The theorem is conditional on explicit observer and
separation data, which the concrete examples below check. It is a lower
bound on state count, not on symbolic description, computation, or proof
length; preserving only the existence of a successful choice is a weaker
contract.

The [program replay](cycle-blocks-audit.json) joins copies of the existing
162-vertex sphere along unaffected triangular faces, matching colours and
reversing boundary orientation. Every resulting rotation system is checked
for connectedness, opposite darts, cyclic vertex stars and Euler
characteristic two. Degrees remain between five and eleven in the joined
examples. Each copy retains one frozen triangle and one repairable six-cycle.

| Copies | Vertices | Physical classes, at least | Feasible joint anchor words | Local anchor states | Crossing-edge constraints | Composed switches |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | 162 | 2 | 4 | 4 | 32 | 2 |
| 2 | 321 | 4 | 16 | 8 | 64 | 5 |
| 3 | 480 | 8 | 64 | 12 | 96 | 8 |
| 4 | 639 | 16 | 256 | 16 | 128 | 10 |

The guards reject every attempted change of a frozen choice. The working
cycle histories compose while fixing the entire exterior of all selected
cycles. Full witnesses for those commands are assembled from local witnesses
and unchanged assignments in the other blocks. No joint colouring table is
enumerated. Independent exhaustive checks are confined to each small cycle.
The generic construction, lower bound and history transport are kernel
checked; joined-sphere geometry and these executions remain program evidence.

Thus exponential class counts are compatible with a compact factored
interface for separated blocks. The retained exterior and crossing edges
still cost space. Edges between hidden blocks require additional joint
constraints; arbitrary interacting compositions, an ordinary smaller-map
reduction and global geometric supply remain open. No catalogue dependency
or whole-proof cost reduction is credited.

Replay `lake build Mettapedia.GraphTheory.FourColor.CycleBlocksAudit` and
`python3 tools/fourcolor/near-linear/audit_cycle_blocks.py`. The
[fixture](cycle-blocks-example.json) pins the sources and gluing faces; the
[receipt](cycle-blocks-measurements.json) records the six-root audit.

## Interacting pieces: keep the joining port choices

[BridgeGuard](../../../lean/mettapedia/Mettapedia/GraphTheory/Kempe/BridgeGuard.lean)
proves exact composition for two pieces joined by one edge. Each piece
retains the labels at its port that have genuine interior witnesses.
The whole constraint problem is solvable exactly when two supported labels
satisfy the joining relation in both orientations. Internal pieces may be
arbitrarily large; neither independent satisfiability nor arbitrary selected
witnesses replace that relation.

For colouring transitions a label consists of the old colour and a Boolean
choice to perform the common transposition. Four colours give at most eight
labels at each port and 64 candidate label pairs across the edge. This
bound concerns the joining check, not all work required to compute messages.
For forest pieces, existing leaf elimination computes the messages and
reconstructs witnesses without enumerating all interior assignments.

The physical consumer constructs a full target colouring from compatible
messages and a proper retained target, and reaches it by actual Kempe
switches fixing the specified exterior. Its hidden-forest hypothesis
supplies the preparatory recolourings; target extension and reachability
are conclusions. It does not assume the independently selected witnesses
already agree across the joining edge.

Two [program consumers](bridge-guard-audit.json) use the existing complete
162-vertex spherical triangulations. Each hides two induced neighbour
cycles, retaining one anchor in each. The remaining paths have exactly one
joining edge. Both examples supply locally valid witnesses that conflict
at that edge and compatible replacements computed through port messages.

| Cycles | Hidden vertices | Independent port colours, before → after | Compatible port colours | Port label pairs checked | Physical switches |
| --- | ---: | --- | --- | ---: | ---: |
| 5 and 6 | 9 | `(2,2) → (2,2)` | `(1,2) → (1,2)` | 8 | 1 |
| 7 and 6 | 11 | `(0,1) → (0,0)` | `(3,1) → (3,0)` | 3 | 2 |

The second repair first prepares the hidden colouring, then changes the
selected anchor through a five-vertex component. The entire exterior of
the two cycles stays fixed. The replay checks every local port label
against the existing leaf evaluator, all reconstructed edges and the
complete physical component supports. It builds no joint colouring table.
Geometry and these executions remain program evidence; the general
composition and physical reconstruction theorems are kernel checked.

This resolves a single-edge interaction, not arbitrary multi-port or cyclic
interaction. It supplies no ordinary smaller-map reduction, geometric
coverage, catalogue replacement or whole-proof cost saving. In particular,
the examples refute combining arbitrary local witnesses; they do not show
that every locally feasible command fails or that compositional repair is
impossible.

Replay `lake build Mettapedia.GraphTheory.FourColor.BridgeGuardAudit` and
`python3 tools/fourcolor/near-linear/audit_bridge_guard.py`. The
[fixture](bridge-guard-example.json) pins both examples and their sources;
the [receipt](bridge-guard-measurements.json) records the three-root audit.

## Two ports in the actual five-triangle cores

[EarGuard](../../../lean/mettapedia/Mettapedia/GraphTheory/Kempe/EarGuard.lean)
removes a vertex with two adjacent neighbours by adding an exact binary
constraint to their edge. The new constraint requires one common colour
for the removed vertex. It retains both orientations of every incident
relation and reconstructs the removed witness. Because inherited relations
are arbitrary, the same law applies at subsequent stages.

[TwoPortCoreElimination](../../../lean/fourcolor-classical/MettapediaFourColor/TwoPortCoreElimination.lean)
checks five such stages in each decoded D0092/D0063 core, the exact remaining
vertex sets, and the terminal edge. Each stage consumes the general law
for arbitrary palettes, unary lists and inherited binary relations. These
operations characterize extension; they do not assert that every boundary
extends or establish arbitrary-exterior reducibility.

Two actual punctured-sphere colourings expose the failure of replacing a
joint message by independent port marginals. In D0063, boundary constraints
force the two ports to colours `0` and `3`, while the removed vertex has
only those two colours available. Either port can be accommodated alone;
both cannot. D0092 gives the same obstruction with colours `1` and `3`.

[TwoPortCoreObstruction](../../../lean/fourcolor-classical/MettapediaFourColor/TwoPortCoreObstruction.lean)
proves that these exact boundary words cannot extend through their decoded
source graphs, using short forced-colour arguments. It also supplies proper
assignments on each source with its first ear omitted, preserving the
boundary and passing both separate port tests. Thus the marginal relaxation
really accepts a false positive. The spherical exterior realizations remain
separately checked program evidence.

The [program replay](two-port-core-audit.json) repairs those same two
counterexample inputs. One specified exterior Kempe component is switched,
then five exact two-port messages construct the seven interior colours in
reverse elimination order. The whole 162-vertex sphere is checked proper.
Each relation has at most 16 colour pairs; no table over boundary words or
joint core colourings is used. An independent finite extension search
cross-checks these two rejected and two accepted words only.

| Source | Ring ports | Eliminations | Exterior switches | Vertices in switched component |
| --- | ---: | ---: | ---: | ---: |
| D0092 | 11 | 5 | 1 | 35 |
| D0063 | 10 | 5 | 1 | 66 |

This uses the same structural calculation for both source cores, including
the correlations that their attachment changes require. A small interface
does not make the exterior component small. The example repairs do not
prove a uniform way to find a successful component, a decreasing repair
potential, or geometric coverage. No catalogue entry or complete-proof
certificate dependency is removed.

Replay `lake build MettapediaFourColor.TwoPortCoreAudit` in the classical
package and `python3 tools/fourcolor/near-linear/audit_two_port_core.py` from
the repository root. The [fixture](two-port-core-example.json) retains the
source pins, compact exterior colourings and explicit repair commands. The
[receipt](two-port-core-measurements.json) distinguishes the generic
two-root audit, source eight-root audit and program executions.

## Shortest repairs can include an unproductive first switch

The original exteriors in `independent-repair-example.json` give a different
test from the marginal counterexamples above. Neither original boundary
extends, and no single actual Kempe component switch makes it extend. A
two-switch repair succeeds in each. The [complete census](two-step-core-audit.json)
includes all six unordered colour pairs and all their components, including
components missing the boundary entirely.

| Source | All initial components | Boundary-changing components | Successful one-switch repairs | Shortest successful history | Distinct exterior vertices touched by displayed repair |
| --- | ---: | ---: | ---: | ---: | ---: |
| D0092 | 30 | 14 | 0 | 2 switches | 2 |
| D0063 | 28 | 13 | 0 | 2 switches | 9 |

For D0092, two successive singleton recolourings suffice. Neither move
alone gives a source extension. A separate three-vertex preparatory switch
leaves the boundary word unchanged but opens four successful next moves.
Consequently the same boundary word can have repair distance two or one.
The current pair partitions distinguish these two states; this is a failure
of the boundary word alone to determine repair distance. The earlier
partition-update obstruction concerns a different, stronger observation.
Silent preparation is an available repair, not necessary on every path.

[ListPropagation](../../../lean/mettapedia/Mettapedia/GraphTheory/Kempe/ListPropagation.lean)
proves that removing colours without support across an actual edge preserves
every proper list colouring. An empty list therefore refutes extension.
[TwoStepCoreProgress](../../../lean/fourcolor-classical/MettapediaFourColor/TwoStepCoreProgress.lean)
uses this common theorem for the two initial words and all 27 boundary-changing
outcomes. Each contradiction uses at most six deductions on the seven-vertex
decoded core. Both repaired source assignments are also kernel checked.
The 5.6 KB source module builds in 8.4 seconds; the generic theorem builds in
1.6 seconds. No table of complete core colourings is used.

The program checks the complete spherical graph, injective source occurrence,
full core stars, cyclic order, actual components and reconstruction of all
162 vertices. These concrete geometric and physical checks remain program
evidence. Lean certifies the 29 boundary rejections and two positive source
assignments; it does not yet certify the spherical component census.

This refutes an immediate one-switch repair guarantee and a strategy requiring
extension feasibility to improve at every physical move. It leaves open finer
progress measures, preparatory moves, successful composite operations, and
uniform coverage. It proves neither that two switches always suffice nor
that compact compositional proofs are impossible. No catalogue entry or
complete-proof dependency is removed.

Replay `lake build MettapediaFourColor.TwoStepCoreAudit` in the classical
package, then from the repository root:

```sh
python3 tools/fourcolor/near-linear/audit_two_step_core.py \
  --check-lean lean/fourcolor-classical/MettapediaFourColor/TwoStepCoreProgress.lean
```

The [fixture](two-step-core-example.json) pins the reused sources and records
only explicit repair commands. The [receipt](two-step-core-measurements.json)
separates the kernel claims, exhaustive one-step program census and bounded
search used to discover the displayed two-step repairs.

## A whole fixed-pair phase is insufficient on the original exteriors

[PairHistory](../../../lean/mettapedia/Mettapedia/GraphTheory/Kempe/PairHistory.lean)
proves a normal form for any finite history of switches using one fixed
colour pair, on any graph and palette. The endpoint is a proper partial
transposition of the initial colouring. If one vertex changes, its whole
original bichromatic component changes. Arbitrarily long repetition is
therefore represented by a subset of the original components meeting the
boundary; components missing the boundary contribute no new boundary word.

The [phase replay](pair-phase-audit.json) exhausts those choices for the same
two original spherical exteriors. D0092 has 40 subsets across the six pairs,
giving 35 distinct boundary words. D0063 has 32 subsets, giving 27 words.
None extends through its source core. Changing the colour pair is necessary
for repair of these inputs; the existing two-switch mixed-pair repairs succeed.

[PairPhaseCore](../../../lean/fourcolor-classical/MettapediaFourColor/PairPhaseCore.lean)
checks all component-mask boundary expressions against the exact decoded
cores. Injective palette renaming reuses the earlier rejection proofs;
only three additional words remain, all rejected by the same four-edge
propagation trace. The source module builds in 6.2 seconds and the general
history module in 1.6 seconds. The component labels' correspondence to the
spherical exteriors remains program evidence, not a kernel-certified embedding.

Lean also checks a D0092 source colouring whose boundary differs from the
initial word at exactly one port. Thus the minimum number of boundary-colour
edits needed for extension is one, although no physical fixed-pair phase
reaches any extension. A repair method requiring this edit distance to
strictly decrease after every phase would stall here. This does not rule
out a finer potential or progress across mixed-pair composite operations.

A bounded deterministic experiment tests 100 distinct nonextendible
colourings, modulo global palette renaming, in the initial Kempe class of
each exterior. In D0092, 60 have a one-switch repair and 40 require two;
in D0063, the counts are 72 and 28. These include the initial colourings.
The samples follow one Kempe walk on each fixed graph. They do not prove a
uniform two-switch bound, cover other Kempe classes or supply geometric coverage.

Replay `lake build MettapediaFourColor.PairPhaseAudit` in the classical
package and, from the repository root:

```sh
python3 tools/fourcolor/near-linear/audit_pair_phase.py \
  --check-lean lean/fourcolor-classical/MettapediaFourColor/PairPhaseCore.lean
```

The [receipt](pair-phase-measurements.json) records the eight-root dependency
audit. The program revalidates the previous source fixtures and generated Lean text;
the bounded sample and the exhaustive phase census are separate evidence.
Complete-proof counts and catalogue dependencies remain unchanged.

## Clique fillings transport complete repair histories

[The clique lifting theorem](../../../lean/mettapedia/Mettapedia/GraphTheory/Kempe/CliqueLift.lean)
handles a finite hidden patch of arbitrary size and internal graph, attached
only along a retained clique. A proper partial transposition on a clique
acts either as the identity or as the full transposition. Applying that
same permutation throughout the hidden patch constructs a proper full
endpoint. The existing component-decomposition theorem realizes this as
physical Kempe switches, preserving any protected retained boundary.

`history_iff` gives exact reachability of retained targets from a specified
full starting colouring. It composes through the existing `LiftsSteps`
interface. It does not require connected hidden fibres and does not claim
that an arbitrary preselected hidden endpoint is reachable. This is a
specialization of clique gluing to colouring dynamics, with no enumeration
of the hidden colouring space.

[The finite consumer](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/CliqueFillAudit.lean)
checks an icosahedron: its nine interior vertices attach along one retained
triangle, every vertex has degree five, and an explicit four-colouring is
proper. Its repair-lifting theorem quantifies over all starting colourings
and retained histories and invokes the general clique theorem. The two
modules build in 1.9 and 2.0 seconds; nine audited roots use standard axioms.

The [source replay](clique-fill-audit.json) uses the same filling in actual
spherical triangulations. D0092 has examples with 99 and 108 vertices;
D0063 has examples with 89 and 98. All have minimum degree five, with exact
source core degrees and cyclic stars preserved. The larger example in each
pair nests one further filling. Two specified physical switches reconstruct
a whole colouring in each case. These examples have separating triangles;
they do not establish the stronger connectivity of a minimal counterexample.

The experiment also refutes a specific proposed progress measure. Count
proper core colourings by their number of conflicting boundary attachments,
ordering the coefficient vector lexicographically from zero conflicts upward.
There are 384 proper core colourings in each source. Across all fixed-pair
phases of each initial small exterior, this vector never increases; equality
only renames the boundary palette. The fillings preserve these choices.
A successful repair must therefore leave this plateau through a worse value.
The displayed first moves reduce the number of one-conflict colourings from
5 to 2 and from 6 to 5 respectively; the second moves reach actual extensions.

This failure concerns that count vector and monotone improvement under
fixed-pair phases. It permits other potentials and nonmonotone combined
operations. The gluing theorem is kernel checked; the counts and larger
spherical examples are separately checked by the replay program. The program
matches its filling incidence and colouring to the Lean consumer and performs
no search for repair commands on replay.

```sh
python3 tools/fourcolor/near-linear/audit_clique_fill.py \
  --output tools/fourcolor/near-linear/clique-fill-audit.json
```

Run `lake build Mettapedia.GraphTheory.FourColor.CliqueFillAudit` in the main
Lean package. The [measurement receipt](clique-fill-measurements.json) records
sizes, timings and scope. No catalogue or complete-proof dependency saving
is credited.

## Preparation survives the stronger connectivity test

The clique-filled examples above have separating triangles. The
[odd-mesh replay](odd-mesh-audit.json) tests the progress question after
excluding those separators as well as the other obstructing short cycles.
An exterior triangle is replaced by an odd triangular mesh. Its colours
use the Klein four group: a lattice point takes the xor of the corner
colours whose barycentric coefficients are odd. Each old exterior edge
becomes an alternating path. Triangulated strips retain the original ring
edges, and every source core star stays unchanged.

For each tested sphere the replay enumerates **every** simple cycle of
length three, four and five, including chorded cycles. It cuts the actual
dual along that cycle, verifies two connected facial shores and counts
off-cycle vertices on both sides. There is no separating three- or
four-cycle and no five-cycle with at least two vertices on each side in
the following examples. Thus they satisfy internal six-connectivity in
the sense used in [the pinned paper, Section 2.2](https://arxiv.org/html/2603.24880v1#S2.SS2).

| Source core | Mesh width | Sphere vertices | Obstructing cycles |
| --- | --- | --- | --- |
| D0092 | 5 | 159 | 0 |
| D0092 | 7 | 278 | 0 |
| D0063 | 5 | 143 | 0 |
| D0063 | 7 | 249 | 0 |

Width three is a negative control: its degree-four strip centres produce
49 and 45 obstructing cycles. Internal six-connectivity for arbitrary
mesh widths is not claimed. These are colourable spheres, not actual
minimal counterexamples to Four Colour.

All initial fixed-pair boundary choices agree with the small exterior.
Consequently none increases the near-extension count vector; the only
equal outcomes are palette renamings. This defeats a requirement of strict
improvement after each fixed-pair phase even with the stronger connectivity.
It does **not** defeat preparation followed by improvement:

| Width-five sphere | Boundary-silent preparation | Following repair | Core extensions |
| --- | --- | --- | --- |
| D0092 | Switch a 10-vertex path using colours 1,3 | Switch a 25-vertex component using 0,3 | 0 → 0 → 1 |
| D0063 | Switch a 9-vertex path using colours 0,3 | Switch a 16-vertex component using 2,3 | 0 → 0 → 1 |

The first step leaves every boundary colour, hence the entire count vector,
unchanged. It changes the next pair's connectivity: in D0092 the boundary
block `{0,2,8,10}` splits into `{0,10}`, `{2}`, `{8}`; in D0063 `{5,7,9}`
splits into `{5}`, `{7,9}`. The second step raises the extension count.
Exact ear elimination reconstructs the seven core colours, and every
ambient edge is checked against the resulting whole colouring. The
[input](odd-mesh-example.json) stores only construction parameters and
these explicit commands; replay does not search for repairs.

[RouteProjection](../../../lean/mettapedia/Mettapedia/GraphTheory/Kempe/RouteProjection.lean)
provides the general transfer law behind the initial obstruction. For any
graph and palette, replace observed edges by paths using their two initial
endpoint colours. Every fixed-pair phase on the larger graph then restricts
to a proper partial transposition of the observed colouring. The theorem
does not require the observed edges themselves to remain. Its paths refer
to the initial colouring, so it deliberately asserts no mixed-pair history
projection: the successful preparation changes those observations.

[OddMeshAudit](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/OddMeshAudit.lean)
checks the exact 21-vertex, width-five triangle mesh, its colouring and six
directed alternating edge routes. Its pairwise nonadjacent corners consume
the general projection theorem. The larger spherical geometry, counts and
two-step repairs remain program evidence, separate from this Lean result.
The [receipt](odd-mesh-measurements.json) records sizes, costs and the
dependency audit.

```sh
python3 tools/fourcolor/near-linear/audit_odd_mesh.py \
  --output tools/fourcolor/near-linear/odd-mesh-audit.json
```

Run `lake build Mettapedia.GraphTheory.FourColor.OddMeshAudit` in the main
Lean package. The open obligation is to supply useful preparations by a
uniform geometric argument, or identify the precise hypotheses under
which that proposed supply fails. These examples prove neither arbitrary
preparation nor a uniform two-switch repair bound. Complete-proof counts
remain 633 coverage entries, 629 original configuration certificates and
336 replaced member-check obligations.

## Detachment enables a second silent preparation

The [detachment replay](component-detach-audit.json) tests the proposed
bound of one boundary-silent component switch followed by an arbitrarily
long fixed-pair phase. It fails on a retained D0092 occurrence in a
162-vertex sphere. The exhaustive census finds no obstructing short cycle:
320 triangles, 480 four-cycles and 1,040 five-cycles. Complete source stars,
prescribed degrees, cyclic order and the ordered eleven-port boundary are
unchanged. Geometry and the following exhaustive failure are program
checks, not Lean theorems about all embedded maps.

None of the initial fixed-pair phases increases the near-extension count
vector. There are exactly 17 boundary-silent components over all six colour
pairs. After each possible single switch, every subsequent fixed-pair
boundary choice still fails to increase that vector. This refutes the
specified **one-component preparation bound**. It does not refute one
simultaneous silent phase, longer preparations, other potentials or a
compact compositional proof.
Indeed, switching two disjoint silent components of colours 1,3 in one
phase, then a 0,3 component, also reconstructs this example. The replay
checks that separate successful phase explicitly.

Two sequential silent preparations succeed. The first removes the only
active exit of a larger region. That region becomes a new silent component,
which can be switched before the final boundary repair:

| History | First silent component | Newly detached component | Final component | Core extensions |
| --- | --- | --- | --- | --- |
| A | Colours 0,2; 2 vertices | Colours 0,1; 21 vertices | Colours 0,3; 67 vertices | 0 → 0 → 0 → 2 |
| B | Colours 0,3; 2 vertices | Colours 0,1; 16 vertices | Colours 0,3; 66 vertices | 0 → 0 → 0 → 2 |

Both histories start from the same full exterior colouring and end with
the same boundary word. They use different first components and different
detached regions. The two preparatory steps retain every boundary colour;
the final step permits reconstruction of a proper colouring of all 162
vertices. No search is needed to replay these supplied successful histories.

[ComponentDetach](../../../lean/mettapedia/Mettapedia/GraphTheory/Kempe/ComponentDetach.lean)
proves the shared law for arbitrary graphs and palettes. Suppose a set uses
colours `a,c`, and all its active exits enter a separate `a,b` component.
If no `b`-coloured vertex of that component is adjacent to the set, switching
it removes the old exits and introduces none. Existing internal paths then
identify a new physical `a,c` component. No bound on either set's size,
planarity assumption or precomputed repair table is needed.

[ComponentDetachExample](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/ComponentDetachExample.lean)
checks both physical histories and whole-graph colouring reconstruction.
It also verifies that the 155-vertex exterior is an induced subgraph of the
162-vertex graph. Colourings are stored as two-bit words, one per state;
the replay checks every data literal against the spherical fixture.
Crucially, the middle component's closure consumes the general detachment
law and observations from **before** the first switch. It is not assumed or
rechecked as an independent saturated component. The
[audit](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/ComponentDetachAudit.lean)
connects these physical histories to the existing proof-relevant GSLT route
type and checks the theorem dependencies. The
[receipt](component-detach-measurements.json) records the finite data and
kernel costs separately from the program census.

```sh
python3 tools/fourcolor/near-linear/audit_component_detach.py \
  --output tools/fourcolor/near-linear/component-detach-audit.json
```

Run `lake build Mettapedia.GraphTheory.FourColor.ComponentDetachAudit` in the
main Lean package. The next missing statement is a supply theorem: under
which geometric or connectivity conditions can useful detachment steps be
found, and what prevents preparation from cycling indefinitely? The two
consumers establish neither a universal preparation bound nor coverage.
Complete-proof counts remain 633 / 629 / 336.

## Odd external boundaries require changing the region

[BoundaryParity](../../../lean/mettapedia/Mettapedia/GraphTheory/Kempe/BoundaryParity.lean)
proves a necessary condition for detachment in every proper four-colouring.
If a region is closed under neighbours of two distinct selected colours,
its external neighbours use only the other two colours. Their induced graph
must therefore be bipartite. An odd closed walk among those neighbours
prevents the region from being an entire Kempe component, regardless of the
length or choice of preparatory recolourings. The theorem applies to arbitrary
graphs and sets; it assumes neither planarity nor finiteness.

A second theorem specifies how an enlargement must respond: a closed
superset must absorb a vertex of every such odd walk. This is a necessary
condition, not an algorithm for choosing compatible enlargements or a proof
that enlargement terminates before reaching protected ports.

The [actual consumer](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/BoundaryParityAudit.lean)
checks two pentagonal neighbour walks in the existing exterior. Neither
singleton can be isolated in any proper four-colouring. Both nevertheless
belong to each of the already verified 21- and 16-vertex detached regions.
The combined theorem proves strict enlargement and physical repair with
whole-graph reconstruction for the same histories. This obstruction therefore
rules out keeping those regions fixed, while the successful larger regions
remain explicit positive evidence.

The [program census](boundary-parity-audit.json) checks all connected,
boundary-disjoint bichromatic regions with one active exit in the retained
162-vertex example. Such a region is a shore of a bridge in its original
two-colour component.

| Outcome | Oriented regions |
| --- | --- |
| One transverse component detaches the region directly | 24 |
| An odd external cycle forbids detachment in every colouring | 233 |
| External graph is bipartite, but neither proposed single switch works | 75 |
| Total | 332 |

Every reported odd obstruction has an explicitly reconstructed and checked
cycle. Bipartite external graphs are independently two-coloured. One tiny
counterexample has both transverse components available away from the ports,
yet either switch creates a new active exit through a facial corner. This
disproves the proposed local supply assertion on the tested source domain.
The full census and spherical geometry are program evidence; the general
theorems and two consumed singleton instances are Lean checked.

```sh
python3 tools/fourcolor/near-linear/audit_boundary_parity.py \
  --output tools/fourcolor/near-linear/boundary-parity-audit.json
```

Run `lake build Mettapedia.GraphTheory.FourColor.BoundaryParityAudit` in the
main Lean package. The [receipt](boundary-parity-measurements.json) records
the short general proof and consumer checks. The next mathematical obligation
is to supply useful changing regions with a justified progress measure.
Neither bipartiteness alone nor the existence of some larger repaired region
establishes that supply. No coverage entries, independent certificates or
member-check obligations are removed here; counts remain 633 / 629 / 336.

## Two detachments compose into a five-vertex preparation

The [cascading repair](cascading-detach-audit.json) reuses the same sphere,
source occurrence and initial colouring. A different choice of starting
region gives a smaller preparation:

| Stage | Physical component | Effect |
| --- | --- | --- |
| First silent switch | Four vertices, colours 1,2 | Removes the only active exit of vertex 43 |
| Second silent switch | Vertex 43, colours 0,1 | Removes a separator from the 0,2 graph |
| Final switch | 53 vertices, colours 0,2 | Produces a boundary word with a genuine core extension |

Both preparatory switches fix all eleven ports. Their combined support has
five vertices, compared with 23 and 18 in the two earlier displayed histories.
The final graph has a verified proper colouring of all 162 vertices. This
does not assert global optimality of the smaller preparation.

[CascadingDetach](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/CascadingDetach.lean)
uses the existing general detachment law twice. The first application derives
the singleton's closure from its old exit. The second derives the final
component's closure because its three old active exit edges all end at that
singleton. Neither newly available component is independently checked for
saturation after its preceding switch. The existing physical-history and
GSLT interfaces compose these operations and retain whole-graph reconstruction.
The [audit](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/CascadingDetachAudit.lean)
requires the final consumer to depend on both the earlier detachment and the
general theorem.

The bounded census explains why local availability is not enough. Among the
24 directly detachable one-exit regions in the original colouring, only six
enable extension after switching the detached region and then performing
one fixed-pair phase. Every boundary outcome of that final phase is checked.
This census concerns the stated three-stage shape, not arbitrary histories.

Region growth is also nonmonotone: a detachable nine-vertex region containing
vertex 8 lies inside an eleven-vertex region whose external neighbours contain
an odd cycle. That larger region cannot be isolated under any four-colouring,
by the general parity theorem. Successful choices therefore require more
than repeatedly enlarging a region or testing whether its boundary is bipartite.
These finite census and geometric observations are program evidence; the
selected physical repair and its five-vertex support are Lean checked.

```sh
python3 tools/fourcolor/near-linear/audit_cascading_detach.py \
  --output tools/fourcolor/near-linear/cascading-detach-audit.json
```

Run `lake build Mettapedia.GraphTheory.FourColor.CascadingDetachAudit` in the
main Lean package. The [receipt](cascading-detach-measurements.json) records
the checks and source sizes. This additional repair establishes no universal
geometric supply, progress bound or new catalogue reduction. Complete-proof
counts remain 633 / 629 / 336.

## Which boundary separation makes the pivot useful?

[ThreeBlockCore](../../../lean/fourcolor-classical/MettapediaFourColor/ThreeBlockCore.lean)
proves a small exact law for the D0092 boundary word
`[1,3,2,3,1,0,3,0,2,0,2]`. Its three connected runs in colours 0,2 are
A = port 2, B = port 5, and C = ports 7–10. If their switch choices are
`a,b,c`, the core extends **if and only if `a = b` and `b ≠ c`**. Necessity
forces colours along actual source edges; sufficiency constructs the source
colouring. This is not an enumeration of every core colouring.

Consequently the required phase is possible exactly when C's component is
distinct from both A's and B's; A and B may share a component. The theorem
`component_choices_iff` states this algebraic observation contract for arbitrary
component labels. It does not establish a planar realization or supply of
those labels. The [consumer and audit](../../../lean/fourcolor-classical/MettapediaFourColor/ThreeBlockCoreAudit.lean)
apply the source rule to the actual cascading repair, retaining its physical
history and all eleven port colours.

This identifies a specific geometric target. A complementary 1,3 path
joining ports 1 and 6 separates C from A and B in a disk. The
[program replay](three-block-core-audit.json) checks all twelve compatible
pairs of noncrossing partitions of these six boundary runs: every partition
with that complementary connection permits the required phase. It also
extracts an actual 1,3 path through pivot 43 in the retained sphere. The
connection is absent before the pivot. The geometric bridge is now proved
under explicit cellular-sphere and source-reading hypotheses, as described
below. Supply of the complementary path remains open.

Merely joining boundary components is insufficient. Another boundary-silent
preparation frees the degree-six pivot 87. Recolouring it merges two 1,2
boundary components, but no subsequent fixed-pair phase extends to the core.
The replay checks every boundary outcome of every such phase; it does not
exclude longer histories that change colour pairs again. Among the three
available singleton pivots after at most one silent component switch on the
retained exterior, only pivot 43 enables the tested final phase.

Four additional bounded samples use the previously checked width-five and
width-seven meshes of D0092 and D0063. Each has useful pivots, and each also
has pivots which merge boundary components without enabling extension in
one final phase. This supplies positive and negative controls, not a
universal occurrence theorem.

```sh
python3 tools/fourcolor/near-linear/audit_three_block_core.py \
  --output tools/fourcolor/near-linear/three-block-core-audit.json
```

Run `lake build MettapediaFourColor.ThreeBlockCoreAudit` in the classical Lean
package. The [measurement receipt](three-block-core-measurements.json)
separates the checked source law from the program's geometric interpretation
and supply census. The next obligation is to derive the useful complementary
connection from a justified source class, or provide an alternative reduction.
No coverage entry, original configuration certificate or existing member
check is removed; counts remain 633 / 629 / 336.

## Complementary paths now yield whole-map reconstruction

[ThreeBlockGeometry](../../../lean/fourcolor-classical/MettapediaFourColor/ThreeBlockGeometry.lean)
proves the previously missing geometric implication. Close an exterior path
from port 1 to port 6 through the fixed source route `1,15,12,13,6`. The
sphere's Euler equation gives a binary face potential for that closed walk.
Seven actual source facial triangles put ports 2 and 5 on the opposite side
from port 7. A vertex-disjoint exterior path preserves that potential, so
neither crossing connection exists. The exterior path may visit additional
boundary vertices, and no vertex-degree or exterior-size bound is assumed.

The hypotheses retain an injective reading of the decoded D0092 source,
source edges, the seven literal facial rotations, cyclic vertex rotations,
connected primal and dual graphs, and Euler's equation. The theorem does not
assume a no-crossing conclusion or an extending colouring.

[ThreeBlockPathRepair](../../../lean/fourcolor-classical/MettapediaFourColor/ThreeBlockPathRepair.lean)
consumes the separator. For the boundary word above, an actual exterior 1,3
path from port 1 to port 6 excludes ports 2 and 5 from the 0,2 component
containing port 7. Switching that physical component changes precisely
ports 7–10. The symbolic core law then reconstructs a compatible source
colouring.

[ThreeBlockReconstruction](../../../lean/fourcolor-classical/MettapediaFourColor/ThreeBlockReconstruction.lean)
glues those witnesses into a colouring of the entire ambient graph when
the exterior covers the complement of the core and the recorded core stars
contain every ambient neighbour. It retains the repaired exterior colouring
literally. The vertex accounting is exact: `|G| = |exterior| + 7`; no
auxiliary vertices are introduced. This is a conditional repair for the
specified boundary class, not an unconditional D0092 reduction or a supply
theorem.

```sh
cd lean/fourcolor-classical
lake build MettapediaFourColor.ThreeBlockGeometryAudit
```

The audit checks the geometry, physical switch, symbolic core and whole-map
consumer together, excluding complete Four Colour endpoints and bulk
colouring certificates. The [measurement receipt](three-block-geometry-measurements.json)
records sizes, checks and retained dependencies.

From the repository root:

```sh
python3 tools/fourcolor/near-linear/audit_three_block_geometry.py
```

The independent [program replay](three-block-geometry-audit.json) checks the
geometric hypotheses on the existing 162-vertex sphere, with a 155-vertex
exterior. Its 26-edge complementary path closes through four core edges;
the resulting 53-vertex switch changes exactly the required four ports and
reconstructs the whole colouring. This concrete rotation-system
instantiation is program evidence; the parameterized geometric and
reconstruction laws are kernel-checked. No new graph fixture is added.

The next research obligation is useful-path supply: derive that connection,
a preparation creating it, or an alternative reduction in a justified
geometric class. The exact boundary class and retained joint choices cannot
be discarded. Coverage and certificate counts remain 633 / 629 / 336.

## Boundary-preserving preparation fails, but a visible repair succeeds

[AnchoredBoundaryExample](../../../lean/mettapedia/Mettapedia/GraphTheory/FourColor/AnchoredBoundaryExample.lean)
gives an exterior with the same nonextending D0092 boundary word in which
every bichromatic component meets a boundary port. Fourteen connected
chains certify this in Lean. The general anchored-chain theorem and the
existing transparency law prove that every finite history preserving all
eleven boundary colours at each step leaves the entire exterior unchanged.
This conclusion has no search-depth bound.

There is only one initial 0,2 component. `phase_global` proves that an
arbitrarily long phase using that pair either swaps every active vertex or
none. Both boundary endpoints fail the symbolic three-run core law.
`no_silent_then_tail_phase` therefore excludes arbitrary boundary-preserving
preparation followed by arbitrary 0,2 finishing. It does not exclude other
finishing pairs or histories with intermediate boundary changes.

The same example has an actual 1,3 component with just three vertices.
Switching it changes port 6 alone, from colour 3 to colour 1. The direct
source assignment in
[VisiblePortRepair](../../../lean/fourcolor-classical/MettapediaFourColor/VisiblePortRepair.lean)
then reconstructs the core. This gives a physical repair of the very example
that obstructs boundary-preserving preparation. The source assignment and
the actual component switch are kernel-checked.

The general `whole_repair_of_isolated_port` consumes this alternative for
any exterior size, through the existing exact core/exterior gluing theorem.
Together with complementary-path repair, `whole_repair_or_residual` leaves
one explicit case for this boundary word: the 1,3 component of port 6 joins
port 3 but not port 1. That case really occurs in the earlier retained
example. A uniform repair for it remains open; no universal supply theorem
has been established.

The [4 KB fixture](anchored-boundary-example.json) is another 162-vertex
triangulated sphere with 155 exterior vertices and the same complete source
core stars. The [program replay](anchored-boundary-audit.json) checks the
ordered source reading, Euler characteristic, minimum degree five, and all
320 triangles, 480 four-cycles and 1,032 five-cycles. None has a prohibited
short-cycle shore. These concrete geometric assertions are program evidence,
separate from the kernel-checked graph, component and source-repair results.
The program also checks reconstruction of a proper whole-map colouring.

```sh
python3 tools/fourcolor/near-linear/audit_anchored_boundary.py
cd lean/fourcolor-classical
lake build MettapediaFourColor.VisiblePortRepairAudit
```

The [measurement receipt](anchored-boundary-measurements.json) separates the
reusable theorems, finite component certificate, geometric program checks
and costs. No colouring table or history search is needed for replay.
Coverage and certificate counts remain 633 / 629 / 336. This is an
obstruction to a specific repair restriction and a certified alternative,
not an impossibility result for compositional Four Colour proofs.

## Existing certified components

The [constructive recognition receipt](seven-pair-recognition-measurements.json)
records a rooted construction of the same shared seven-pair sector.
One actual edge, triangle attachments and a general degree-closing theorem
supply all 31 facial correspondences. The actual consumer takes only the
retained degree test and the surrounding pair hypotheses.

The [independent replay](audit_seven_pair_recognition.py) checks all fourteen
degree-seven rooted edges in each of two triangulated spheres. It recovers
the existing 32-vertex sector and tests retained label identifications on
a nine-vertex bipyramid. These are program checks, separate from the Lean
proof and from the unresolved degree-profile supply theorem. Replay
`lake build kernelSevenPairRecognition`. No catalogue entry, rank certificate
or classical member check is removed by this recognition bridge.

The [seven-pair sector receipt](seven-pair-sector-measurements.json) records
an actual geometric continuation. A shared facial chart with fifteen fixed
degrees forces positive charge if its three marked outer vertices are low.
Consequently, flatness forces a high vertex at one of those same positions.
The minimal-map consumer distinguishes it from both selected centres and
retains its radius-two support, or radius five from the original fan receiver.
Six other chart degrees are unrestricted. The theorem does not assume
that distant chart labels are distinct, and does not assert that the new
vertex differs from every other retained high vertex.

The proof checks 83 outgoing-rule exclusions and eleven incoming-rule maps;
these finite geometric checks remain in its dependency graph. The final
extra unit follows by a shared five/six boundary-degree argument. No
configuration certificate or complete Four Colour theorem is used. The
classification that supplies this profile remains open, and the classical
coverage count is unchanged. Replay `lake build kernelSevenPairSectorData`,
then `lake build kernelSevenPairSector`. The independent input audit is
`python3 tools/fourcolor/near-linear/audit_seven_pair_sector.py`.

The [complete wheel-family receipt](wheel-family-measurements.json) records
kernel certification of every D3009 repair state and input trace. A shared
action checker validates each recolouring once while retaining each
exterior pairing's joint compatibility. The existing boundary-collapse law
then supplies all six ordered two-five variants without new repair tables.
The actual-map consumer proves strict reconstruction and supplies the next
adjacent-seven pair from a shared fan. Broader geometric coverage remains
open; no classical coverage entry is removed by this result.

The [four-triangle geometry](four-triangle-measurements.json) shares one
injectivity and inducedness proof between the distinct D0051 fan and D0052
tripod cores. Both full source files, degree profiles and core facial
intervals are checked; the actual minimal-map consumer is kernel certified.
The [complete source and repair bridge](four-triangle-repair-measurements.json)
now identifies the full ten-port patches with classical configurations 33
and 37, including opposite orientation conventions. One rank-coverage
theorem consumes their existing certificates and supplies full proper-domain
repair. A supplied complete occurrence yields actual strict two-vertex
descent and compatible ambient reconstruction; different boundary labels
may coincide. The [joint boundary completion](facial-boundary-measurements.json)
now derives all source edges and complete positive core stars from four
facial triangles and six degrees. Both complete occurrences and actual
strict reconstruction are connected. A proved reflection of the tripod's
full source aligns its positive geometric completion with its reversed
classical repair. The joint coverage classification remains open. No original
certificate dependency or coverage entry is removed.

The same parameterized seam theorem now serves both earlier three-triangle
chains and both four-triangle layouts. Owners read each exterior port once;
the across-edge triangle law proves agreement at every closing seam. This
retains the joint boundary, while allowing distinct exterior labels to
coincide. Replay `lake build kernelFacialBoundary`, then the migrated
consumers with `lake build kernelChainRecognition` and
`lake build kernelExtendedChain`.
Replay `lake build kernelFourTriangleRepair kernelFourTriangleGeometry`.
Replay the source audit with
`python3 tools/fourcolor/near-linear/audit_four_triangle_sources.py`.

The [shared-fan tripod receipt](rule-fan-tripod-measurements.json) connects
this repair to the actual six-star `[receiver, 5, 5, a, b, 5]`.
For either placement of degrees seven and six at `a,b`, a degree-five
outer tip across `a–b` supplies the tripod. In a minimal counterexample
with a unique high neighbour `q` at the seven, the remaining tip must
have degree six or be exactly `q`. Its identity and radius-three support
are retained. Other free-degree profiles and these two surviving seam
cases still need joint classification. Replay `lake build kernelRuleFanTripod`.
The independent [geometry test](rule-fan-tripod-audit.json) finds both
placements after 83 and 103 legal flips of the existing spherical fixture;
it checks all source core edges, corners and ambient degrees. It does
not assert the full flat-neighbourhood hypothesis. Replay with
`python3 tools/fourcolor/near-linear/audit_rule_fan_tripod.py`.

The [exact high-boundary receipt](punctured-charge-measurements.json)
extends the cyclic rule formula to a high receiver with high neighbours.
Low-edge contributions retain the actual adjacent degree guards; all high
transfers remain signed boundary observations. For the actual retained
flat-seven pair, the first low budget plus its unique high-edge input is
ten. With no other high neighbours at either end, the two low budgets sum
to twenty by cancellation of that same edge. The second centre's additional
high neighbours otherwise remain explicit. The same local rule equivalence
turns a `5–6–6–5` rim segment into the three tripod matches whenever the
intermediate outer tip has degree five, excluding this tip in a minimal map.
Replay `lake build kernelExactCyclicCharge` first, then
`lake build kernelPuncturedCharge`. The concrete Lean instances keep their
exact executable sums symbolic; their numerical values are program evidence.

The [finite boundary audit](punctured-charge-audit.json) compares two source
matchers on 235 low-to-high edges at 47 receivers. In its retained flat
pair, the first low budget is twelve and it exports two units to the second;
the second low budget is nine and it exports one further unit to another
high vertex. Thus the combined low budget is twenty-one, with external
boundary contribution minus one. Only the selected pair is asserted flat;
this fixture does not satisfy the full original flat-ball hypothesis.
Replay `python3 tools/fourcolor/near-linear/audit_punctured_charge.py`.
This establishes exact accounting and a local forbidden pattern, leaving
joint geometric classification and catalogue compression open.

The [joint-rule receipt](joint-tripod-rules-measurements.json) records a
second recognition law: `002_1` and `003_1` on one six-to-seven dart,
together with `002_2` on its rotation-determined adjacent dart, force the
tripod when the adjacent sender has degree six. Their joint contribution
is therefore at most two in a minimal map. The proof constructs the core
from the shared source readings and consumes the complete boundary and
strict reconstruction theorem. Replay `lake build kernelJointTripodRules`.
The [independent replay](joint-tripod-rules-audit.json) exhibits these
matches in the existing sphere. It checks that the shared-fan sender and
both retained seven-centres are flat, while the original receiver has
charge `+3`. Three flat observations do not establish a flat radius-three
ball. Replay `python3 tools/fourcolor/near-linear/audit_joint_tripod_rules.py`.
No new repair table, removed certificate dependency or coverage saving
is claimed. The next classification must retain the forbidden triple
as a joint constraint on actual adjacent readings.

The [seven-pair example](seven-pair-four-triangle-example.json) explains the
choice of these cores. It is a 162-vertex sphere obtained by 1,625 legal
edge flips. Independent matchers agree on all 4,704 rooted rule tests for
the two flat seven-valent centres in both orientations. All 1,819 short
cycles pass the obstruction test. There is no tested diamond, D0004/D0006
chain or one/two-five seven-wheel core in the union of their radius-three
balls. An injective D0052 core occurs within radius two, and D0051 within
radius three. Their complete source images need radii three and four,
respectively. This is a program check of a restricted family inventory,
not a counterexample to universal reducibility or to the stronger
shared-fan/flat-neighbourhood hypotheses. Replay it with
`python3 tools/fourcolor/near-linear/audit_seven_pair_example.py`; see the
[receipt](seven-pair-four-triangle-audit.json).

The [second-fan classification](second-fan-measurements.json) retains the
other side of the same six-star: a flat seven either supplies a new high
neighbour, has the single-five D3009 profile, or has exactly two fives with
one outer five-tip and zero extra charge. The classification is checked
without a repair hypothesis; a separate consumer excludes the single-five
branch using the explicit D3009 repair contract. The
[two-five experiment](two-five-wheel-probe.json) checks all three separations
on the seven-rim wheel. Each closes all 22,144 boundary states in Python;
no new Lean repair or coverage saving follows from that experiment alone.
Replay it with `python3 tools/fourcolor/near-linear/probe_wheel_repair.py --two-fives`.

The [three-triangle chain](../../../lean/fourcolor-classical/MettapediaFourColor/NearLinearChainRepair.lean)
now has a shared repair: `D0006` is exactly classical configuration 7, and
`D0004` inherits its repair through one boundary-triangle subdivision. The
source bridge checks all adjacencies, cyclic stars, degrees and ordered ports.
No separate repair table is introduced for `D0004`.

This target comes from a [whole-neighbourhood example](chain-profile-example.json),
not solely a catalogue shape match. A finite program check finds adjacent
flat centres of degrees eight and seven, with all other neighbours of the
eight-centre of degree at most six. It checks all 461 simple cycles of lengths
three through five and finds no obstructing cycle. Neither of the mixed and
pentagonal diamond cores occurs in the union of the two radius-two balls.
The five-vertex `D0004` interior does occur. Lean verifies its thirteen distinct
source vertices and complete oriented core stars, and consumes its repair in
actual graph reconstruction with explicit exterior-closure and initial-colouring
hypotheses. A subsequent
[actual reduction](../../../lean/fourcolor-classical/MettapediaFourColor/ActualChainReduction.lean)
derives those witnesses from vertex minimality and the actual planar exterior.
Its geometric occurrence contract requires the five complete core stars,
their degrees, distinct core vertices and boundary images outside the core;
boundary images need not be distinct from each other. The example supplies
this contract and a cyclic triangular rotation in Lean. The flatness,
global planarity and short-cycle checks remain program evidence.

Replay source fidelity and the example from the repository root:

```sh
python3 tools/fourcolor/near-linear/audit_chain_sources.py
python3 tools/fourcolor/near-linear/audit_chain_profile.py
```

The package gates are `lake build kernelNearLinearChain kernelChainReduction`. The
[receipt](chain-measurements.json) separates local repair, concrete occurrence,
and conditional reconstruction. The
[actual-reduction receipt](chain-reduction-measurements.json) closes the
initial-colouring and exterior bridge through an existing strict two-vertex
reduction. General occurrence recognition and coverage remain open. The
[source pins](chain-sources.json) retain upstream attribution and the MIT licence.
This step removes no entry or certificate dependency from the complete assembly.


The [rerooted reduction](../../../lean/fourcolor-classical/README.md#changing-the-reduction-edge-removes-a-residual-branch)
now excludes the degree-five second sender in the actual minimal-map
domain. A different edge of the same rule reading exposes the existing
mixed diamond and its strict replacement. This removes one local branch;
the [measurements](rule-pair-residual-measurements.json) retain the unchanged
global coverage and certificate counts.

The latest [paired rule budget](../../../lean/fourcolor-classical/README.md#a-paired-budget-retains-both-sender-choices)
retains both sender degrees, proves the two incoming edges distinct, and
bounds their joint net supply by seven or eight units from below. At a flat
degree-eight receiver the remaining net supply is at most thirteen. The
[measurement record](rule-pair-budget-measurements.json) separates its general
proof, minimal-map consumer, finite instances and open coverage obligations.

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
It does **not** instantiate the scaffold with certified reductions. The
results below supply the actual dual rotation, exclude core collisions and
prove inducedness in the minimal regime. Moving to the full eleven-port
occurrence still requires boundary completion with cyclic order and a
colouring-repair contract. Zero-charge classification and transport of the
published source observations remain open. No coverage or certificate
dependency is removed here.

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


## Facial transport and the collision alternative

`ExceptionalCoreOrientation` checks all eighteen directed core corners
against the full pinned cyclic neighbour rows. Fifteen come directly from
the first exceptional occurrence. The remaining three follow from one
closing corner and the generic facial-triangle rotation law. No boundary
neighbours are removed before testing consecutive turns.

`ExceptionalCoreLocalInjectivity.corner_chain_injective` proves a uniform
rule: consecutive facial corners follow powers of the actual vertex
rotation, and a chain no longer than the ambient degree cannot repeat a
neighbour. Its source consumer proves local injectivity at every D1774 core
vertex, using the prescribed degrees forced by the joint occurrence.

`ExceptionalCoreCollision.source_core_alternative` now has two checked
outcomes for two actual exceptional occurrences aligned at the prescribed
second centre:

```text
actual aligned occurrences
        |
all core edges, degrees and facial corners
        |
local injectivity
        |
        +-- injective orientation-preserving core reading
        |
        +-- nonfacial triangle within radius two of the first centre
```

The finite collision partition leaves only four unordered pairs of core
vertices. Each closes an actual three-edge path. Three cases use the same
central edge: its two facial third vertices have degree eight, whereas the
collided endpoint has degree five. The fourth case uses adjacency to exclude
one facial third vertex and a degree mismatch to exclude the other. The
triangle carries an actual `SimpleGraph.Walk.IsCycle` proof of length three.
The retained source context is essential to these exclusions; the internal
core graph alone does not retain all the necessary observations.

The reusable laws concern facial transport, injective corner chains and
exclusion by the two flanking corners. The four-pair source check remains a
finite obligation. This is a concrete collision alternative, not a general
first-collision theorem for arbitrary patch programs.

No planarity assumption is needed for these laws. The next result supplies
the local-faciality corollary's geometric hypothesis in the actual dual of
a graph-backed minimal Tait counterexample, using an established separator
theorem. The injective branch still needs inducedness, eleven-port ring
completion and the repair contract.

Run `lake build kernelExceptionalEmbedding` with the prepared dependencies.
The source consumer's dependency audit requires both the constructed core
reading and the actual collision argument; it excludes complete Four Colour
endpoints and original catalogue rank certificates. See
[embedding-measurements.json](embedding-measurements.json).
Coverage and certificate counts remain 633 and 629, respectively.

## Collision elimination in the actual minimal dual

`ActualDualRotation` gives the quotient-face dual its actual dart rotation.
It reuses the primal darts, exchanges the vertex and face permutations, and
proves that unique shared edges yield a faithful simple-graph backing.
`MinimalExceptionalEmbedding.graph_eq_coverage_dual` identifies its adjacency
with the graph used by the coverage scaffold. Thus the geometry is not
attached to an unrelated triangulation with a similar graph.

The existing `GoertzelV24MinimalDualTriangleClassification` proves that a
dual triangle cuts off one primal vertex in a graph-backed vertex-minimal
Tait counterexample. This follows from cyclic five-edge-connectivity and
the actual three-edge separator, using the earlier small-cut reconstruction
theory. The new bridge proves that every face incident with an edge at that
cubic vertex is one of its three cyclic face readings. Those three readings
form a facial triangle in the actual dual rotation. Consequently every dual
triangle has one of the two facial orientations.

```text
two aligned actual exceptional occurrences
                  |
       exact core and retained turns
                  |
      injective OR nonfacial triangle
           |                |
           |        singleton-cut classification
           |                |
           |        actual triangle is facial
           |                |
           |          contradiction
           |
   injective eight-vertex core homomorphism
```

`MinimalExceptionalEmbedding.source_core_injective` is the checked source
consumer. It constructs the joint reading, uses the explicit collision
argument, and excludes the collision through the same actual rotation.
The theorem does not assume core injectivity or a full D1774 occurrence.
The uniform actual-dual and facial-triangle laws can be reused by other
patches; the present consumer still uses the D1774 four-pair collision check.
A general first-collision theorem for arbitrary construction programs remains
open.

This result assumes a graph-backed vertex-minimal Tait counterexample and
the two actual exceptional occurrences. The inducedness result below
excludes extra ambient core edges. Supply from the paper's final-charge
classification, the full eleven-port ring, colouring repair and strict
reduction remain open. No catalogue or certificate dependency is removed
from the complete assembly.

Run `lake build kernelExceptionalDual`. The twelve-root audit requires the
actual dual bridge, singleton separator and source collision theorem in the
dependency closure. It admits only `propext`, `Classical.choice` and
`Quot.sound`, and excludes complete Four Colour endpoints and original
catalogue rank certificates. See
[minimal-embedding-measurements.json](minimal-embedding-measurements.json).

## Induced core from facial intervals and short paths

The core has thirteen edges and fifteen distinct unordered nonedges.
Eleven nonedges join vertices with a common core neighbour. The remaining
four pairs have distance three. All eight core stars are consecutive
intervals strictly shorter than the prescribed ambient degree; each retains
at least one exterior neighbour.

`FacialPatchInduced.corner_chain_successor` proves the relevant general
rotation law. If `n` retained consecutive neighbours satisfy `n < degree`,
then a facial corner between retained entries can only join successive
indices. The strict inequality excludes a wraparound corner. Combined with
the actual minimal dual's triangle-faciality theorem, this rules out any
extra edge between two neighbours of a core vertex.

The second law, `FacialPatchInduced.reflects_of_short_paths`, is independent
of rotations and of the catalogue. Suppose an injective graph homomorphism
reflects adjacency between neighbours of each source vertex, all source
vertex pairs have a path of length at most three, and every ambient
four-cycle has a diagonal. Then the entire homomorphism reflects adjacency.
An extra edge across a three-edge source path closes a four-cycle; either
diagonal reduces the claim to the same local reflection law twice.

```text
retained proper neighbour intervals
             +
actual triangles are facial
             |
no extra edge across any two-step core path
             +
actual four-cycles have a diagonal
             |
no extra edge across any three-step core path
             +
kernel-checked core diameter at most three
             |
       exact induced core
```

`ExceptionalCoreInduced.four_cycle_chord` transports the existing minimal
dual four-cycle theorem through the exact adjacency bridge.
`ExceptionalCoreInduced.source_core_induced` consumes that geometry and the
same two aligned source occurrences used for injectivity. It establishes
the exact adjacency equivalence, rather than adding absence of extra edges
as a field. This is a special case of the inducedness task in the paper's
Lemmas 3.1 and 9.2; the source diameter-three fact avoids the five-cycle
case needed for diameter-four configurations.

The finite source checks retain the star bounds, consecutive source edges
and short-path witnesses. The new reusable laws are not a colouring-repair
theorem. The eleven-port completion and conditional reconstruction below
now preserve shared boundary choices and allow boundary identifications.
Compatible repair, strict reduction, final-charge classification and
coverage remain open; counts remain 633/629.

Run `lake build kernelExceptionalInduced`. The nine-root audit requires the
actual source construction and the triangle/four-cycle geometry. Only
standard axioms are allowed, and complete Four Colour endpoints and original
catalogue rank certificates are excluded. See
[induced-measurements.json](induced-measurements.json).

## Eleven-port completion and exact reconstruction

The source core's partial cyclic stars now extend to all eleven ring ports.
For an actual directed edge `d`, triangular closure proves

```text
second endpoint of predecessor(d)
                =
second endpoint of successor(reverse(d)).
```

This is `FacialStarCompletion.across_edge`. Combined with the exact degree
and retained core-star interval, it supplies each of the eight seams around
the core. There is one chosen reading for each ring label; the seam law
proves agreement with every other reading of that label. Two ring labels
occur in three core stars, so their agreement uses two applications of the
same law.

`ExceptionalBoundaryCompletion.row_agrees` identifies every full source
star entry with an actual rotation power. A kernel-checked source edge
classification then constructs a homomorphism of the complete nineteen-vertex
source graph, including the ring edges. The source labels and their order
are retained. `ExceptionalBoundaryOccurrence.full_turn` preserves all full
cyclic core-star steps; `star_covers` proves that every actual incident edge
has a source reading.

No assumption makes the boundary globally injective. The theorem
`ring_outside_core` uses induced core adjacency and injectivity of a full
vertex rotation to exclude capture of a core vertex by a ring label. It
allows distinct ring labels to denote the same exterior vertex.

The general theorem `PatchBoundaryGluing.reconstruct` applies to any graph
patch whose interior map is injective, whose boundary avoids the interior,
and whose incident-edge coverage is complete. Given an actual patch
colouring and an exterior assignment, proper off the interior, agreement
on the entire boundary reconstructs a colouring of the ambient graph while
fixing every exterior vertex.

Its actual consumer is `ExceptionalBoundaryReconstruction.reconstruct`.
The companion `extension_iff` gives the exact contract:

```text
proper exterior assignment extends to the ambient dual
                         iff
the source completion has a colouring with those same eleven observations.
```

The equality is about joint assignments, not independent port possibilities.
If ports have equal ambient images, the common exterior assignment enforces
the corresponding equality of colours. The theorem works for every colour
type and reconstructs a witness; it is not merely a numerical count.

The next obligation is to obtain such a compatible colouring, allowing
justified exterior Kempe changes. No repair rank, strict reduction or
zero-charge supply theorem is established by this equivalence. No global
boundary embedding or general collision theorem for all triangle programs
is asserted. Counts remain 633 coverage entries and 629 original catalogue
certificate dependencies.

Run `lake build kernelExceptionalBoundary`. The fourteen-root dependency
audit requires actual source construction, core injectivity, inducedness,
full incident-edge coverage and reconstruction. It allows only standard
axioms and excludes complete Four Colour endpoints and original catalogue
rank certificates. The source and object hashes, replay times and gate
results are in [boundary-measurements.json](boundary-measurements.json).

## Complete exceptional boundary repair

`ExceptionalRepairCertificate.repair` now proves repair for every proper
zero-sum eleven-port trace. The terminal relation consists of actual colourings
of the complete nineteen-vertex D1774 source. Each terminal witness is checked
against all forty-three edges, including the ring, and its entire ordered trace.

The certificate contains 7,381 trace representatives, including 1,383 terminal
ones. Every nonterminal record supplies a whole-chord mask for each possible
unsigned exterior skeleton. `KempeMaskCertificate.check_sound` proves that
these masks preserve the same signed exterior chromogram. The selected answer
has strictly smaller rank. `KempeIndexedCertificate.sound` performs the common
well-founded argument, quantifying over every Kempe-closed exterior predicate.
Records need not be uniquely identified by their traces.

```text
one proper boundary trace and its actual exterior witness
                         |
       choose complete chords in that same exterior
                         |
              strictly smaller repair rank
                         |
           genuine full source colouring
                         |
       align all ports by one colour translation
                         |
                  reconstruct the map
```

The complete check retains 93,665 unsigned-skeleton cases. It is a finite
repair certificate with a reusable checker and reconstruction law; no
case-free family theorem or catalogue removal is credited. The generator is
untrusted. Its output, all terminal colourings, all rank decreases and the
coverage of all proper inputs are checked by kernel reduction. The full
finite replay took 5,964 seconds; this is verification cost, not an algorithmic
colouring bound. A separate regeneration reproduced both generated files
byte for byte.

`GraphTraceAlignment.align` preserves the whole boundary assignment by one
Klein-group translation. `ExceptionalRepairReconstruction.reconstruct` uses
the earlier actual graph geometry and allows coincident ring images. It still
requires Kempe closure of the actual exterior relation and an initial proper
exterior trace. The finite certificate does not supply those geometric inputs.

Replay with `lake build kernelExceptionalRepair`; after the finite artifacts
are prepared, `kernelExceptionalRepairConsumer` checks alignment,
reconstruction and the twelve-root dependency audit separately. The audit
allows only standard axioms and excludes complete Four Colour endpoints and
original catalogue rank certificates. Counts remain 633 coverage entries and
629 original configuration certificate dependencies.

## Constructed source, local query and valid contraction

`ExceptionalConstruction.program` builds the complete D1774 source with nine
Y operations and eight H operations, interspersed with rotations. The
kernel comparison identifies all three permutations on its eighty-six darts.
The face presentation recovers every source edge, every cyclic star and the
ordered eleven-port ring. `ringTrace_iff` transports actual colouring witnesses
and their complete traces between the literal source and this construction.

The established Gonthier/Werner configuration compiler, as formalized by
Chris Emery, supplies embeddability. Its local recognition query is also
checked exactly. It observes degrees `5, 5, 8, 7, 5, 5, 5, 5` along a specified
branching walk. Matching this list at arbitrary vertices would not suffice:
the dart steps and common starting edge are part of the query.

`KempeRepairContract.reducible_of_repair` proves a general bridge: an
all-proper-trace repair law supplies the coclosure field of every valid
contract on the same perimeter. Its proof derives a proper boundary trace
from an actual contract colouring, using the contract's exclusion from the
ring. D1774 has a checked singleton contract on the edge joining source
vertices 13 and 14 (zero-based labels). Its two darts are off the ring and
lie on distinct nodes.

`ExceptionalConstructionRepair.not_fitted` now excludes a matching local
query in a reference minimal counterexample. The proof consumes the source
construction, exact trace transport, finite joint-chord repair and singleton
contract, then reuses the established query-to-preembedding, contraction,
exterior-closure and patch reconstruction theorems. It uses no complete
Four Colour endpoint or original catalogue rank certificate.

The matching query is now derived from the two actual exceptional occurrences,
as described below. A starting singleton contract colouring is also supplied
directly in the graph-backed minimality regime. The local consumer below now
also establishes exterior embedding and closure in that same domain, without
identifying the two minimality definitions. Zero-charge classification and
occurrence supply remain separate.

Replay with `lake build kernelExceptionalConstruction` after preparing the
finite repair artifacts. Its seventeen-root audit checks the representation,
query compiler and reconstruction dependencies. This establishes source
reducibility and reuse; it removes no coverage entry or existing certificate
dependency. See [construction-measurements.json](construction-measurements.json).

## Actual overlap recognition through compositional query moves

`DualGraphQuery` constructs the exact dual hypermap on the graph's actual darts.
Its face permutation is the given vertex rotation. The general `stepR` and
`stepL` theorems turn directed facial corners into the elementary recognition
moves. `arity_eq_degree` identifies each query observation with the full ambient
degree under vertexwise cyclicity.

`ExceptionalQueryReading.walk` composes those moves through the retained joint
core. The two branches use the same directed starting edge and the same corner
witnesses. `fitted` proves that the resulting eight observations satisfy the
exact query compiled from the D1774 construction. `actual_fitted` instantiates
this theorem at the two aligned exceptional occurrences in the graph-backed
minimal facial dual. The source walk starts at numbered dart 84 and visits
source vertices `16,18,11,14,17,15,12,13` (zero-based labels); those readings are
also kernel checked.

This recognition proof needs no new hypothesis asserting a D1774 occurrence,
core injectivity or distinct ring images. It uses the already retained core
corners and degrees. Under reference minimality of this exact dual hypermap,
`not_minimal` consumes the source construction, finite repair and contraction
chain to exclude the overlap. The graph-backed minimality hypothesis has not
been shown to imply that reference hypothesis. The direct contract-colouring
route below supplies its starting witness without such an implication;
the local exterior consumer below now completes that geometric bridge.

Replay with `lake build kernelExceptionalQuery`. Its nine-root audit retains
the actual corner, degree and reconstruction dependencies, permits only the
standard axioms, and rejects complete Four Colour endpoints and original
configuration rank certificates. The D1774 finite repair certificate remains.
This closes the local query-recognition obligation; coverage remains 633 entries
and the complete assembly retains 629 original configuration certificates.
See [exceptional-query-measurements.json](exceptional-query-measurements.json).

## Initial contract colouring in the actual graph-backed domain

The existing adjacent-pair reduction provides a strict smaller planar cap.
`MinimalSingletonContract.one_zero` uses vertex minimality to colour that cap,
then reconstructs a conserved field on the original graph with exactly one
zero edge. `ConservedContract.of_conserved` integrates the full field into an
actual face assignment. Every edge difference is preserved, including its
zero set, so the result is a genuine contract colouring.

`ContractTransport.ccColoring_push` transports that assignment and its entire
contracted edge list together. `ActualDualContract.map_eq_source_relabel`
identifies all three permutations of the physical source hypermap with those
of the actual dual query map. `singleton_colorable` therefore provides an
initial contract colouring for every selected dart of that exact map, using
graph-backed vertex minimality throughout. `not_colorable` proves the reverse
consumer: a proper colouring there would reconstruct an original Tait colouring.

This closes the starting-witness obligation. The local exterior consumer below
now applies the finite D1774 repair using sufficient local hypotheses, including
treatment of boundary identifications. Classification from final charge,
geometric supply and global coverage remain open.

Replay with `lake build kernelMinimalSingletonContract`. The twelve-root audit
checks 24,706 dependency declarations and permits only standard axioms. It
excludes complete Four Colour endpoints, original configuration ranks, the
D1774 finite repair and the reference minimal contract-colouring theorem.
The new modules add no enumeration or colouring certificate. Coverage remains
633 entries and the complete assembly retains 629 original configuration
certificates. See
[minimal-singleton-contract-measurements.json](minimal-singleton-contract-measurements.json).

## Actual exceptional closing law through local embedding

`ExceptionalLocalRepair.aligned_not_in_minimal` now excludes two aligned actual
X occurrences in a graph-backed vertex-minimal Tait counterexample. It consumes
their full source geometry and the checked D1774 repair, supplying both the
embedding and the initial contract colouring rather than assuming either.

The reusable geometric contract is `FaithfulKernelEmbedding.FaithfulKernel`:
core darts are injected and an ambient edge reversal between their images is
already a source edge reversal. Together with a preembedding, plainness and
cubicity, these two local facts imply injectivity on the complete off-perimeter
disk. Distinct boundary faces need not have distinct ambient images.
`InjectiveEmbeddedRepair.colorable` then composes the actual contract colouring,
exterior Kempe closure and patch reconstruction. These two arguments adapt
Gonthier and Werner's embedding proof as ported by Chris Emery, with its MIT
attribution retained. They factor out the reference consumer's stronger global
Birkhoff-ring and pentagonal hypotheses.

`ExceptionalDartReading` certifies this local contract from the induced core
and complete cyclic stars. It checks the finite source dart positions and star
cycles, but adds no colouring-rank table. `ExceptionalPreembedding` transports
the same reading through the exact Y/H numbering. `LocalPreembedding.of_radius2`
constructs its ring-link paths from the source kernel's radius-two property.
Every observation and every reconstruction stage uses this one map.

The final consumer combines this disk injection with
`ActualDualContract.singleton_colorable`, which comes from the existing strict
smaller planar cap and vertex minimality. `ExceptionalLocalRepair.overlap_supply`
fills the second-centre and joint closing fields of `EightOverlapSupply`.
Its zero-charge classification remains an explicit hypothesis. The low-degree
and degree-seven supply laws, residual cases, charge transport and global
coverage are still open.

After preparing the existing source and finite repair dependencies, run
`lake build kernelInjectiveEmbeddedRepair`, then `lake build kernelExceptionalExterior`. The
29-root audit excludes complete Four Colour endpoints, original catalogue rank
certificates, the reference minimal-contract theorem and the global
`embed_full`/`embed_inj` chain. It permits only standard axioms. The D1774 finite
repair is retained in the final local consumer and absent from the generic and
geometric roots. Coverage remains 633 entries / 629 original configuration
certificate dependencies. See
[exceptional-exterior-measurements.json](exceptional-exterior-measurements.json).

## Actual discharge and a first classification prune

The complete 84 oriented rules (43 rules with their required reflections) are
retained unmodified in [discharging-rules](discharging-rules), pinned to
`d85bfe09e9584d675fdf33a1da61067575ec4883` of
[the discharging-rule repository](https://github.com/near-linear-4ct/discharging-rules).
The MIT notice is in [LICENSE](LICENSE), and individual source hashes are in
[discharging-sources.json](discharging-sources.json).

`NearLinearRuleData` checks the headers, all 638 vertex rows, complete
adjacency, explicit cyclic gaps, degree intervals and marked endpoints. Each
vertex observed by a rule has a path of length at most two from either
endpoint, whose intermediate vertex has prescribed degree at most eight.
Every rule has a prescribed degree-five vertex, and every sender has degree
at most eight.

`NearLinearCharge.Occurrence` interprets these observations in actual graph
darts, retaining all known rotation steps. Occurrences may identify distant
vertices. An applicable rule is counted once, using existence of a reading;
the charge does not count alternate witnesses. Starting charge is
`10 * (6 - degree)`, followed by incoming minus outgoing rule amounts.
This is the mathematical rule semantics, not a proof that the C++ search
implements or exhausts it.

The resulting uniform laws establish:

- No degree-five vertex within radius two means no charge crosses any edge
  incident to the centre. Its final charge equals its initial charge.
- A flat centre of degree seven or eight therefore has a degree-five vertex
  within radius two.
- A rule application retains one degree-five witness close to both endpoints.
- Two distinct flat degree-eight centres require exactly forty units of net
  external charge. Their shared transfers cancel, with the same outside
  vertices retained in the boundary sum.

`ExceptionalFlatCharge.overlap_supply` applies the first prune in the actual
graph-backed minimality domain and reuses the completed exceptional-pair
repair. Classification of the remaining neighbourhoods still has to be
proved. There is no claim here of cartwheel completeness, a smaller catalogue,
new reducibility, or a near-linear running time. The ledger remains 633
coverage entries and 629 original configuration certificate dependencies.

From the repository root:

```sh
python3 tools/fourcolor/near-linear/audit_discharging_sources.py
```

With the exceptional exterior artifacts prepared, from
`lean/fourcolor-classical`, run sequentially:

```sh
lake build kernelNearLinearRuleData
lake build kernelNearLinearCharge
```

See [source fidelity](discharging-source-audit.json) and
[kernel measurements](charge-measurements.json). The charge audit excludes
complete Four Colour endpoints and original configuration rank certificates.
The D1774 finite repair occurs only in the consumer of the existing closing
law; it is absent from the rule and charge proofs.

## Exact rooted matching and a concrete joint-view test

`RuleTraversal` interprets a source construction as flips, vertex rotations
and inverse rotations of an actual graph dart. Its transport theorem uses
one occurrence throughout, including when distinct source vertices share an
ambient image. `RuleTraversalData` certifies all 638 vertex traces for the 84
pinned rules: each trace follows known source transitions, reaches its
advertised vertex, and has length at most seven.

`RuleMatcher.candidate_eq` proves that any rooted occurrence has exactly the
candidate vertex images produced by those traces. `check_iff` then proves
that checking the candidate's complete adjacency, degree bounds and known
cyclic steps is equivalent to `NearLinearCharge.Applies`. Checking succeeds
or fails without searching over vertex assignments. `chargeAt_eq` identifies
the resulting computation with the existing occurrence-based final charge;
`checked_pair_budget` consumes two computed flatness certificates and yields
the exact forty-unit external boundary budget.

The generator is untrusted. Lean checks its output against the original
rule data. The matcher audit forbids reduction certificates, original
configuration certificates and complete Four Colour endpoints. From prepared
rule data, replay with:

```sh
python3 tools/fourcolor/near-linear/generate_rule_traces.py
cd lean/fourcolor-classical
lake build kernelRuleTraversal
lake build kernelRuleMatcher
```

The [measurement record](rule-matcher-measurements.json) separates the finite
traversal-data check from the generic proof and audit.

The [saved flat-pair example](flat-pair-probe.json) is independent program
evidence. Starting with an edge-subdivided icosahedron, 417 legal oriented
edge flips produce a 42-vertex triangulation with adjacent degree-eight
vertices 11 and 18. Both have final charge zero and their net external supply
is forty. The two radius-two balls have 26 vertices each, with 33 in their
union. The `D0001` core image `[38, 39, 36, 27]` lies in that union but neither
individual ball; its full source vertex reading is retained in the report.
Other reducible pieces already occur in the individual balls, so this is not
an example proving that joint inspection is necessary.

Two independent implementations agree on all 20,160 rule/root tests on this
graph: compiled traces and breadth-first dart propagation. They identify 391
rooted rule occurrences. The saved report retains the initial faces, every
edge flip, final faces, source rule revision and actual rule images. Replay
from the repository root:

```sh
python3 tools/fourcolor/near-linear/probe_flat_pairs.py \
  --replay tools/fourcolor/near-linear/flat-pair-probe.json \
  --output /tmp/flat-pair-replay.json
cmp tools/fourcolor/near-linear/flat-pair-probe.json /tmp/flat-pair-replay.json
```

The flat-charge computation and the straddling core reading remain program
evidence. The latter checks complete core stars and ring edges while allowing
boundary identifications; a full embedded occurrence and reconstruction for
that particular core are additional obligations. The rotation and a different
rule-pair consumer in the same graph are certified below. Neither
this example nor the generic matcher establishes cartwheel enumeration
completeness, absence of obstructing cycles, or a charge-to-reduction law for
all flat pairs. The coverage ledger remains 633 entries and 629 original
configuration certificate dependencies.


## Two charge rules force a shared geometric reduction

`RulePairDiamond` gives a structural law for `rule003_2` (index 4) and
`rule004_1` (index 5). The second incoming root is determined by two backward
turns at the first root's receiver. The exact rule matcher proves that both
readings then share the receiver and the same neighbouring vertex.

If the first sender has degree five and the shared neighbour has degree six,
the first reading supplies two consecutive turns at that neighbour and the
second supplies three more. Cyclicity forces the sixth turn. Triangular
closure transfers the resulting corner across the edge, exposing a five–six
edge with a degree-five vertex on each flank. The receiver's degree need not
be eight, and the surrounding graph has no fixed size bound.

```text
rule 003_2: two turns --+--> same six-valent star --> closing corner
rule 004_1: three turns+                                |
                                              mixed diamond
                                                    |
                                          13 removed, 5 added
                                                    |
                                       reconstruct actual colouring
```

`ActualRulePairDiamond` transports this result through the actual facial
dual. Its degree-to-face-length theorem retains the source dart. The existing
mixed-diamond reduction supplies strict descent by eight vertices and
colouring reconstruction. Consequently, in a graph-backed vertex-minimal
counterexample, the checked first rule and the two degree guards force the
aligned second rule check to be false. This is a usable forbidden joint
charge profile; no cartwheel-classification premise is assumed.

The same five-turn path also has a degree-five branch. Cyclicity then
identifies the last outer vertex of the second reading with the first outer
vertex of the first reading. `identified_corner` proves this equality in the
actual graph. With the first sender and other outer corner of degree five, triangular closure
exposes the all-pentagonal diamond. The existing twelve-to-four replacement
again decreases the full map by eight and reconstructs its colouring.

The source rules bound both the shared degree and that other corner's degree
between five and six. `pair_alternatives` therefore gives a complete split
for this aligned pair with a degree-five first sender:

```text
five prescribed turns at the shared vertex
                  |
          +-------+--------+
          |                |
       degree 6         degree 5
          |                |
    closing corner    endpoints identified
          |                |
    mixed diamond     other corner's degree
       13 -> 5          /             \
                       5               6
                  pentagonal        retained
                   12 -> 4          residual
```

`ActualRulePairDiamond.surviving_pair_degrees` discharges both reduction
branches in graph-backed vertex minimality: a surviving pair must have shared
degree five and other-corner degree six. This is a necessary local condition;
it does not assert that the residual is irreducible or occurs in a minimal
counterexample.

`RulePairExample` checks a nonempty instance on the saved 42-vertex graph:
root `25 → 18`, second root `28 → 18`, shared vertex 5 and derived mixed edge
`26 → 5`. The cyclic star at vertex 5 is
`26, 25, 18, 28, 19, 1`. Lean checks vertexwise cyclicity, triangular closure,
both full rule checks and the two degree guards; `has_mixed` consumes the
general structural theorem. It does not certify the experiment's flatness,
spherical flip history or absence of other reductions.

`RulePairCollisionExample.has_pentagonal` uses the same certified rotation
at root `41 → 39` and second root `9 → 39`. Both readings identify vertex 30;
the resulting edge `30 → 32` has five-valent flanks 4 and 41. Lean checks the
complete rule matches and guards, then consumes the general collision law.
A separate exhaustive program scan finds eleven degree-five overlaps in this
graph: four satisfy the pentagonal guard and seven retain the five/six profile.
That scan is not a coverage theorem.

The independent source-fidelity replay is:

```sh
python3 tools/fourcolor/near-linear/audit_rule_pair_example.py
```

It compares all 42 Lean cyclic stars with the saved oriented faces. It also
records a limit of the earlier straddling-core candidate: vertex 38 is absent
from every positive rule reading incident with the two flat centres. Thus
those positive readings do not directly supply that particular four-vertex
core. Other geometric or negative-rule information could still do so.

Prepare the finite example once with `lake build kernelRulePairExampleData`,
then run `lake build kernelRulePairDiamond` with the rule/traversal data and
both diamond artifacts prepared. Its dependency audit requires the actual
strict-reduction and reconstruction chain. The shared diamond profile
certificate remains; original catalogue certificates, the D1774 certificate
and the complete Four Colour endpoint are absent.

This removes two explicitly described branches of joint rule profiles from the
remaining classification and specifies the surviving degrees. It removes no
coverage entry or existing assembly certificate. The exact forty-unit budget
still needs a complete account of the surviving profiles. See
[measurements](rule-pair-diamond-measurements.json).

## Continuing a rule beyond the original pair boundary

[chain-boundary-example.json](chain-boundary-example.json) retains a generated
162-vertex triangulation and its 100 legal edge flips. The adjacent centres
have degrees eight and seven; the seven is the eight's only neighbour of
degree above six. Both final charges are zero. Their radius-two balls contain
22 and 20 vertices, with 27 in their union. That union contains neither known
diamond core nor the chain degree word in either orientation.

The charge rule `rule004_2` in the reversed rotation retains three successive
neighbours of a degree-six outer vertex. Their degrees are `5,6,5`. Continuing
once reaches another degree-five vertex, beyond both original radius-two
balls, and recognizes the existing chain. All thirteen source vertices fit
within radius four of the degree-eight centre.

[RuleChainRecognition](../../../lean/fourcolor-classical/MettapediaFourColor/RuleChainRecognition.lean)
proves this implication for arbitrary triangular rotations. Its actual-map
consumer excludes the continuation in graph-backed vertex minimality, using
the same strict reduction, reconstruction and configuration-7 base certificate.
[ChainBoundaryExample](../../../lean/fourcolor-classical/MettapediaFourColor/ChainBoundaryExample.lean)
certifies the concrete cyclic geometry, rule and degree-word readings, full
occurrence, boundary crossing and radius bound. It does not certify the
example's global sphericality, flatness or absence of obstructing cycles.

Replay the separate program evidence with:

```sh
python3 tools/fourcolor/near-linear/audit_chain_boundary.py
```

The audit reconstructs the spherical triangulation from its saved flips,
checks 5,040 rooted rule matches in both orientations by two independent methods, checks both sides
of all 1,826 simple cycles of length three through five, verifies the absence
of the three known core patterns in the original view, and checks the complete
chain and all Lean cyclic stars. Results are in
[chain-boundary-audit.json](chain-boundary-audit.json).

With the preceding chain artifacts prepared, `lake build kernelChainBoundary`
replays the new theorems and their dependency audit. The
[kernel receipt](chain-boundary-measurements.json) records all four modules
and the seventeen-root audit. This supplies a concrete
reason to extend local views during the coverage search. It neither proves
universal family supply nor removes a catalogue entry. The complete assembly
still uses 633 coverage entries and 629 original configuration certificates.

## Completing the second chain profile

The degree-six word `5,6,6,5` now constructs an actual D0006 occurrence,
including all nine ordered boundary ports. The eight-port D0004 word
`5,6,5,5` has been refactored to use the same parameterized
[fan boundary law](../../../lean/fourcolor-classical/MettapediaFourColor/FanBoundaryScheme.lean).
Shared rotation readings determine a single boundary map, so the three
triangles retain their common vertices throughout completion.

[ActualExtendedChainReduction](../../../lean/fourcolor-classical/MettapediaFourColor/ActualExtendedChainReduction.lean)
connects this recognition to strict descent and reconstruction in the actual
minimal-map domain. It reuses the already certified D0006 repair from
classical configuration 7. There is no new rank certificate.
[ExtendedChainExample](../../../lean/fourcolor-classical/MettapediaFourColor/ExtendedChainExample.lean)
constructs the whole source from directed edge `(48,117)` of the retained
162-vertex graph and checks all fourteen images. Those images lie within
radius two of centre 48; flatness and global sphericality of the example
remain separate program evidence.

The [kernel receipt](extended-chain-measurements.json) records the common
geometry, exact source bridge, actual reconstruction and finite example.
This gives a second concrete consumer of the generic completion theorem.
The next coverage obligation is to derive one of the supported reductions
from the surviving joint charge profiles, or retain and characterize a
counterexample to that proposed local supply claim. Coverage remains 633
entries with 629 original certificate dependencies.

## A uniform cyclic charge budget

[CyclicCharge](../../../lean/fourcolor-classical/MettapediaFourColor/CyclicCharge.lean)
proves `T(v) >= 10(6-d) + 4k + 2m` for any receiver of degree `d >= 7`
whose neighbours all have degree five or six. The count `k` is the number
of five-valent neighbours. The count `m` is over receiver wedges with a
five-valent opposite facial tip; tips need not be distinct. The proof
constructs the first five oriented source rules from actual shared
triangles, reindexes the rotation, and retains all remaining signed terms.

[CyclicFanContinuation](../../../lean/fourcolor-classical/MettapediaFourColor/CyclicFanContinuation.lean)
uses both known outer tips of the same-root rules002_2/003_2 fan. At a flat
seven with only low neighbours, at most one neighbour is five. The actual
minimal-map consumer identifies that five with the retained shared vertex:
either an adjacent third high centre exists, distinct from the previous
two and within radius three, or all other neighbours are six. At a flat
eight with only low neighbours, the same argument bounds the fives by four.

The [finite input](cyclic-charge-examples.json) and
[independent audit](cyclic-charge-audit.json) check four receiver profiles
against all incident source rules, using two independent matchers. Two
positive examples consume the general law in Lean. The input also records
two legal flips producing the single-five residual with zero charge. Its
original centre has positive charge nine, so it is not a jointly flat or
minimal-counterexample instance. Its flatness is program evidence only.

Replay with `lake build kernelCyclicCharge` and:

```sh
python3 tools/fourcolor/near-linear/audit_cyclic_charge.py --output tools/fourcolor/near-linear/cyclic-charge-audit.json
```

The [receipt](cyclic-charge-measurements.json) keeps classification and
compression separate. The single-five residual, joint-flatness closure,
initial supply and global coverage remain open; counts stay 633 / 629.

## Joint rule-fan coverage branch

Rules `002_2` and `003_2`, matched on the same directed edge, jointly fix
`[receiver,5,5,a,b,5]` around a degree-six sender when its next neighbour
after the receiver has degree five. The three low-degree alternatives consume the mixed diamond,
D0004 and D0006. On the actual minimal-map domain, one of `a,b` must have
degree at least seven. It is a distinct vertex within radius two of the
receiver. The flat degree-at-most-eight domain thus supplies a second flat
centre of degree seven or eight.

The [Lean theorem](../../../lean/fourcolor-classical/MettapediaFourColor/ActualRuleFanSupply.lean)
uses all three reconstruction consumers; its dependency audit retains only
the shared diamond profile and the existing configuration-7 rank certificate.
The [kernel receipt](rule-fan-supply-measurements.json) distinguishes this
local supply result from initial profile classification and global coverage.
Three finite examples use the exact source rules and exercise each branch.
Replay their independent program check with:

```sh
python3 tools/fourcolor/near-linear/audit_rule_fan_supply.py --output tools/fourcolor/near-linear/rule-fan-supply-audit.json
```

`lake build kernelRuleFanSupply` checks the general laws, actual reductions,
finite consumers and audit with the earlier artifacts prepared. The next
obligation is to exploit the overlapping views at the supplied centre,
retaining shared vertices and detecting repeated centres. No universal
coverage or termination theorem is claimed, and the assembly counts stay
633 coverage entries and 629 original configuration certificates.

## Signed charge supplies an alternative to returning

The earlier joint fan can return to its original receiver when continued
through the same six-valent sender. Flatness supplies more information than
the degree word alone. [RuleFanCharge](../../../lean/fourcolor-classical/MettapediaFourColor/RuleFanCharge.lean)
proves that two consecutive fives on each side of a six-to-high edge force
three incoming contributions of at least `3,4,3`. The same facial triangles
construct the related rule occurrences, preserving their shared vertices.

At a degree-seven receiver with only degree-five/six neighbours, the two
flanking triangles add one unit each. Cyclicity makes these five senders
distinct. The complete 84-rule semantics gives zero reverse transfer and
nonnegative remaining contributions. Thus the final charge is at least
`-10 + 1 + 3 + 4 + 3 + 1 = 2`.

Consequently, if its neighbours all have degree at least five, a flat seven
receiving this fan must have a high-degree neighbour.
[ActualRuleFanCharge.third_center](../../../lean/fourcolor-classical/MettapediaFourColor/ActualRuleFanCharge.lean)
applies this to the previous source-rule profile when the first free vertex
is a flat seven and the second free vertex is five. The actual minimal-map
facial triangle theorem excludes an edge back to the original receiver.
The new high centre is adjacent to the second, distinct from both previous
centres, and within radius three of the first.

The [finite example](rule-fan-charge-example.json) uses two legal edge flips
of the retained 162-vertex triangulation. Lean verifies its cyclic geometry,
the low-neighbour hypothesis and the positive conclusion using the general
theorem. The [independent replay](rule-fan-charge-audit.json) computes exact
charge eight and agrees on all 1,176 incident rule checks. Replay with:

```sh
python3 tools/fourcolor/near-linear/audit_rule_fan_charge.py --output tools/fourcolor/near-linear/rule-fan-charge-audit.json
```

`lake build kernelRuleFanCharge` checks the general law, actual consumer,
finite example and dependency audit. The [receipt](rule-fan-charge-measurements.json)
records the scope and costs. This branch uses no original configuration
rank certificate. It neither excludes longer centre cycles nor closes the
degree-eight or second-free-degree-six branches. Coverage remains 633
entries with 629 original certificate dependencies.


## An extra source rule supplies a reduction

`ExtraChargeReduction.closing` completes the actual five-valent sender star
of rule `004_1` (index 5). With a six-valent shared neighbour and a
five-valent second successor of the sender, the outer triangle gives either
a mixed diamond or the eight-port `D0004` chain. One geometric law handles
both outer degrees. `ActualExtraChargeReduction.not_occurrence` consumes
the existing strict reductions and compatible colouring reconstructions;
no starting colouring or exterior-closure assumption is supplied by its caller.

`ActualExtraChargeReduction.flat_alternatives` strengthens the preceding
single-five classification. In its residual branch, this particular extra
rule is absent at the shared-five-to-first-free edge. Other additional
incoming rules remain possible and must still be classified.

The [input record](extra-charge-examples.json) has two finite consumers of
the general theorem, with both complete source-rule readings kernel checked.
The chain branch constructs its full boundary occurrence. The same record
replays five legal flips from the retained 162-vertex sphere: both centres
then have charge zero, the original shared fan survives, and the extra rule
exposes the existing chain. Thus joint flatness alone permits the degree
profile; the matched source rule explains a repair inside that example.

Run `lake build kernelExtraCharge` in `lean/fourcolor-classical` for the formal
result. Run
`python3 tools/fourcolor/near-linear/audit_extra_charge.py --output tools/fourcolor/near-linear/extra-charge-audit.json`
from the repository root for its independent finite evidence. The latter
compares 2,357 rule readings with an independent propagation checker.
The [measurement record](extra-charge-measurements.json) distinguishes the
Lean results from program-checked flatness and sphericality. The chain
reconstruction retains classical configuration 7 and the shared profile.
Counts remain 633 coverage entries and 629 original certificates; no new
assembly dependency or coverage entry is removed.


## Exact accounting of the residual inflows

`ExactCyclicCharge.exact_charge` strengthens the lower bound to the identity
`finalCharge(v) = 10(6-degree(v)) + 4k + 2m + E`. The domain is a finite simple
graph with triangular dart rotation, a receiver of degree at least seven,
and all its neighbours of degree five or six. Neither planarity nor a
single-cycle condition on each vertex rotation is needed for this identity.
The counts retain actual neighbours and marked wedges; two wedges may share
a five-valent outer tip. The remainder counts all matches of rules 5..12.
The other source types cannot have a sender of degree at most six.

In a single-five neighbourhood, rules 9 and 10 cannot occur: both would
retain distinct adjacent five-neighbours of the receiver. At a flat seven
with at least two marked outer five-tips, exactly two budgets remain:

| Marked tips | Additional rule-edge matches |
| --- | --- |
| 2 | 2 |
| 3 | 0 |

`ExactFanResidual.alternatives` connects this to the actual shared fan,
retaining the previous index-5 exclusion on its specified edge. These are
budgets, not two completed repair arguments. The source types still allowed
in the remainder are 5, 6, 7, 8, 11 and 12.

The [inputs](exact-charge-examples.json) and [independent audit](exact-charge-audit.json)
replay both charge budgets on spherical triangulations with both centres flat.
The two-extra example still has the marked rule excluded by the preceding
reduction. Only the three-tip example also satisfies that exclusion.
It has no extra transfer at all, so eliminating extra
rules alone cannot close the geometric obligation. Both examples have an
injective complete source-graph match of [D3009](D3009.conf), with its core
induced: a seven-valent centre, one five-valent neighbour and six six-valent
neighbours. The input manifest pins its upstream revision, source hash and
MIT licence. The general occurrence is now proved below. Colouring repair and
strict reconstruction remain open.

Run `lake build kernelExactCyclicCharge` in `lean/fourcolor-classical`.
Run `python3 tools/fourcolor/near-linear/audit_exact_charge.py --output tools/fourcolor/near-linear/exact-charge-audit.json`
from the repository root. Two base receivers consume the Lean identity to
give `2 + E` and `8 + E`. The program checks their extra counts as 2 and 1,
giving charges 4 and 9. These numerical matcher counts, the modified graphs
and the D3009 occurrences are program evidence. The
[measurement record](exact-charge-measurements.json) separates these scopes.
The actual-map continuation retains configuration 7 through the preceding
reduction. Coverage remains 633 entries /629 original certificates.

## Completing the residual wheel

`ActualWheelOccurrence.occurrence` constructs D3009 from the single-five
seven-valent profile in the actual minimal facial dual. It assumes only
that profile, not an embedded source occurrence. The construction proves
all source edges, all eight complete core stars and degrees, an induced
core, and injectivity of all 21 vertices. Every image is within radius two
of the retained centre. Extra edges between boundary vertices are not
excluded or needed by this statement.

The geometric argument is compositional. `WheelNeighborhood` first gives
an ordered wheel at arbitrary degree. Source neighbour stars then grow the
thirteen-port boundary; the actual facial seam identifies their shared
observations. An outer port cannot fold into the induced core. If two owned
outer ports coincide, the resulting four-cycle forces adjacent owners.
Facial triangles then force the common vertex to be their designated seam,
contradicting its two different owner positions. Thus the complete boundary
is a genuine simple cycle, with distinct vertices.

`ActualWheelOccurrence.residual_occurrence` consumes the exact-charge
classification without changing its centre, marked five-neighbour or rule
exclusion. Both retained budgets supply this same source shape. The occurrence
construction uses no configuration repair certificate or complete Four Colour
theorem; the residual supply still retains configuration 7 through the prior
reduction. No D3009 repair is assumed from the source catalogue.

Replay with `lake build kernelWheelNeighborhood` in `lean/fourcolor-classical`.
The [receipt](wheel-occurrence-measurements.json) records sixteen audited roots,
only standard axioms, and the full regression gates. The
[source audit](wheel-source-audit.json), reproduced by
`python3 tools/fourcolor/near-linear/audit_wheel_source.py`, verifies the source
hash and equality of its numeric rows with the Lean decoder input.

The next obligation is compatible colouring repair and actual strict
reconstruction. The exact construction and colouring interface are now proved
below. The occurrence theorem removes no coverage entry or certificate
dependency. Counts remain 633 /629.

## Shared cyclic choices for the wheel

`D3009Construction` builds the pinned source with eleven Y and eight H steps.
Its 94 darts retain all three permutations, every source edge and cyclic star,
and the thirteen ports in source order. Actual colouring witnesses and their
ordered traces transport exactly. The reference construction also supplies
the embeddability contract.

`WheelColouring.coloringEquiv` applies to any boundary graph and any
fixed-point-free rim successor. A complete colouring is equivalent to its
boundary colouring, one shared centre colour, and compatible colours around
the rim. `WheelColouringGSLT.extends_iff` identifies this with a closed GSLT
route, uniformly at every width at least two. Splitting the route keeps the
common centre colour and both interface colours. These are exact extension
laws; they do not assert that an arbitrary boundary assignment extends.

`D3009Colouring` proves the exact graph isomorphism and consumes those laws.
In particular, `two_sectors_iff` reconstructs a source colouring from compatible
three-step and four-step sectors. `constructionTrace_iff` equates the Y/H
construction's trace with this cyclic interpretation. The witness equivalence
retains multiplicities as well as support; it supplies no executable Kempe
recolouring algorithm.

`D3009ColouringExample` checks a successful pair and a precise failed closure.
For the proper boundary word `0101010101013`, each rim vertex must use colour
2 or 3. The seven-cycle cannot close with those two colours. Both sectors have
histories, even with the same centre colour and agreement at their shared
middle seam, but the other seam cannot close. Exterior recolouring remains
available; the example refutes only independent sector inhabitation.

The [finite probe](wheel-repair-probe.json) goes further experimentally:

| Centre degree | Ring length | Canonical traces | Direct extensions | Survivors after full pairing closure |
| --- | --- | --- | --- | --- |
| 5 | 9 | 820 | 257 | 0 |
| 6 | 11 | 7,381 | 1,381 | 0 |
| 7 | 13 | 66,430 | 7,496 | 0 |

These are independent program results, not Lean repair certificates. Every
terminal witness is checked on all graph edges. The closure considers all
noncrossing pairings and all unions of whole chords, up to complementary
choices and global colour permutation. In particular the thirteen-port case
allows three-chord answers. At width seven the exact pinned source is used;
its boundary labels are a checked rotation of the uniform wheel incidence.
Reproduce with `python3 tools/fourcolor/near-linear/probe_wheel_repair.py`.

Replay the proofs with `lake build kernelWheelColouring` in
`lean/fourcolor-classical`; see the [receipt](wheel-colouring-measurements.json).
The nineteen-root audit excludes configuration repair certificates and the
complete Four Colour theorem. Neither a uniform D-repair law nor the D3009
repair has yet been kernel certified. The next test is a compact repair
certificate with a measured kernel cost, followed by actual exterior repair
and strict reconstruction. Coverage and original certificate counts stay
633 /629.


## A repaired wheel seed

`generate_wheel_seed_repair.py` extracts the answer closure of the concrete
nonextending boundary `0101010101013`. The complete finite discovery still
has 66,430 canonical states, but this seed uses only nine retained states:
one repair record and eight terminal source colourings. There are 132
unsigned exterior pairings and 31 selected answers exchange three chords.
This does not establish that those three-chord moves are necessary.

`WheelSeedRepairCertificate.seed_repair` checks that finite certificate in Lean.
The theorem meets every Kempe-closed exterior containing the seed. Its
`repaired_sectors` consumer obtains compatible GSLT sector histories;
`repaired_construction` preserves the same trace in the pinned Y/H source.
No other boundary trace is covered merely by the independent rank search.

Generate the flat data with:

```sh
python3 tools/fourcolor/near-linear/generate_wheel_seed_repair.py \
  --output WheelSeedRepairData.lean --report wheel-seed-generation.json
```

`--cache` optionally retains the untrusted discovery ranks between runs.
The kernel checks every consumed fact independently of that cache. Replay
`lake build kernelWheelSeedRepair`; the
[receipt](wheel-seed-repair-measurements.json) records proof scope and costs.
The complete D3009 repair contract remains open. The following geometric
consumer supplies actual exterior closure and strict reconstruction conditional
on that full contract. No catalogue entry is removed by this seed.


## The wheel occurrence as a repair disk

`D3009Preembedding` maps all 94 source darts by their actual ordered endpoints.
The retained complete core stars preserve the face operation and arities;
whole-source vertex injection preserves dart identity. The same reading gives
an injective disk for the exact Y/H construction.

`D3009RepairGeometry` proves that the edge from the degree-seven centre to its
degree-five neighbour is a valid singleton contract. Given a full thirteen-port
repair law, the actual minimal-map consumer obtains a contract colouring from
the established strict two-vertex reduction and reconstructs the ambient
colouring. This would exclude the recognised degree profile and resolve the
wheel branch of `ActualWheelOccurrence.residual_occurrence`.

The full repair law remains an explicit hypothesis. The nine-state seed
certificate alone does not discharge it. Replay `lake build kernelWheelEmbedding`;
the [receipt](wheel-embedding-measurements.json) records ten audited roots and
standard axioms only. No coverage entry or original certificate is removed.


## One collapse transfers repair to every two-five wheel

`TwoFiveWheelData` removes the private outer fan vertex at any of the six
degree-six positions of D3009. Reinsertion is exactly a boundary-triangle
subdivision, with all graph edges, cyclic stars, degrees and ordered ports
checked. Each target has twelve boundary vertices and the same eight core
vertices, with two rim degrees five and all remaining rim degrees six.

`TwoFiveWheelRepair.transfer` applies the existing boundary split and
reconstruction theorem to all six positions. Its sole repair premise is
the full thirteen-port D3009 law; the separately running finite replay
has not yet discharged that premise. None of the three Python closure
experiments is used by the proof, and no target repair certificate is added.
`TwoFiveWheelColouring.repaired_sectors` retains the same Kempe-closed
exterior relation and obtains two GSLT sectors with shared centre and
seam colours. This establishes compatible existence, not a counted or
executable Kempe-recolouring algorithm.

Replay `lake build kernelTwoFiveWheel`; the
[receipt](two-five-wheel-measurements.json) records the fourteen-root audit.
Actual two-five occurrence is supplied by the shared geometric theorem
below; the subsequent disk theorem supplies ambient reconstruction conditional
on the same full source repair.
Coverage and original configuration certificate counts stay 633 /629.


## One geometric completion for both wheel families

`WheelBoundaryCompletion` separates finite source rows and outer-port
ownership from the geometric argument. Triangular closure equates the
readings of a shared seam. Inducedness of the wheel core excludes a port
from returning into the core. A collision between different outer ports
produces a four-cycle; its chord and a facial triangle contradict the
owned positions. This proves injectivity rather than requiring it.

`D3009BoundaryLayout` and `WheelBoundaryLayouts` supply the finite laws for
D3009 and all six twelve-port targets. `ActualWheelOccurrence.occurrence` consumes the
shared theorem for D3009. `TwoFiveWheelOccurrence.supplied` selects the
second-five position from the actual cyclic neighbour orbit and constructs
the corresponding source, preserving all edges, full core stars and both
marked neighbours. Every source vertex lies within radius two of the same
centre. Additional ambient edges between boundary vertices are permitted.

`SecondFanWheelOccurrence.alternatives` combines the charge classifier with
these occurrences without assuming a colouring repair. Its outcomes are a
new high neighbour, the original one-five wheel, or a complete two-five
wheel carrying the exact two-five/one-tip/no-extra-transfer observations.
The target repair is already a consequence of the full D3009 repair by the
preceding collapse theorem. The disk and strict reconstruction are supplied
by the following common construction argument, with that repair premise explicit.

Replay `lake build kernelWheelBoundaryCompletion`; see the
[receipt](wheel-boundary-completion-measurements.json). The general geometric
argument has actual consumers in both families. Coverage and original
certificate counts remain 633 /629.


## One strict reconstruction argument for the six two-five placements

`TwoFiveWheelConstruction` checks exact Y/H programs for every target.
Each source has ninety darts, twenty dual vertices and twelve boundary ports.
The complete edge/node/face permutations agree with the programs; the full
cyclic stars and ordered colouring traces agree with `TwoFiveWheelData`.

`TwoFiveWheelPreembedding` reads every source dart through the previously
proved actual occurrence. Its complete cyclic stars establish the same
preembedding and faithful kernel at every second-five position. The shared
kernel-to-disk theorem then gives injectivity of the repair disk.

`TwoFiveWheelRepairGeometry` checks the centre-to-marked-five contract at
all six positions. Existing graph-backed vertex minimality supplies its
initial colouring by strict two-vertex descent. The family repair transfer
then reconstructs a genuine ambient colouring, compatible with the same
exterior. The full thirteen-port D3009 repair is an explicit premise; no
additional target repair certificate is needed.

The actual consumer `second_high_neighbor` applies this to the shared fan.
Both single-five and two-five wheel outcomes are excluded, leaving a new
high neighbour within radius three of the original receiver. It retains
the same flat second centre throughout. Universal coverage is still open.

Replay `lake build kernelTwoFiveConstruction`, then
`lake build kernelTwoFiveEmbedding`; the
[receipt](two-five-embedding-measurements.json) records the finite source
checks, disk/reconstruction audit and unchanged catalogue counts.

## From the shared fan to joint seven-centre views

`RuleFanSevenCluster.pair_exists` consumes the actual shared six-valent fan,
flatness and the degree-at-most-seven bound within radius three. The existing
diamond and chain reductions force one of the two free positions to be high.
The single full D3009 repair, including its six transferred two-five repairs,
then supplies a high neighbour of that same selected position. Both vertices
are flat sevens, and neither is the original receiver.

`unique_or_third` retains this pair when selecting a second high neighbour
of its first centre. If there is none, every other neighbour has degree at
most six. Otherwise the three distinct sevens form an induced path or an
actual facial triangle, with the two possible orientations retained. The
third centre also differs from the original receiver. The complete
radius-two views fit within radius five of the original receiver.

`occurs_of_joint_laws` supplies the same supported occurrence after one of
three joint closing laws is established. These laws are still explicit
hypotheses. They correspond to the unique-neighbour and path cases of
Lemma 8.6 and the facial seven-triangle case of Lemma 8.5 in the pinned paper;
their computational classifications have not been imported as assumptions.
The radius-five degree bound is available for the full joint views.

Replay `lake build kernelRuleFanSevenCluster`. The
[receipt](rule-fan-seven-cluster-measurements.json) records the eight-root
audit. The existing shared diamond profile and classical configuration 7
remain in the initial fan reduction; the full D3009 repair remains an
explicit premise. No new repair certificate or coverage entry is removed.
