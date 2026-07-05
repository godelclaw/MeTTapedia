import Mettapedia.GraphTheory.FourColor.CAP5GraphBoundary
import Mettapedia.GraphTheory.FourColor.CyclicEdgeCut
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryOrderedEmbedding
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite

set_option linter.unusedSectionVars false

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V W α : Type*}

section BasicPredicates

variable [DecidableEq V] [Fintype V]

/-- A graph is cubic when every vertex has degree three. -/
def CubicGraph (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ v : V, G.degree v = 3

/-- A graph is bridgeless when none of its actual graph edges is a bridge. -/
def BridgelessGraph (G : SimpleGraph V) : Prop :=
  ∀ e : Sym2 V, e ∈ G.edgeSet → ¬ G.IsBridge e

/-- The Tait edge-colorability predicate in the local FourColor color algebra. -/
def TaitEdgeColorable (G : SimpleGraph V) : Prop :=
  ∃ C : G.EdgeColoring Color, IsTaitEdgeColoring G C

/-- A Tait counterexample is a graph with no nonzero proper edge-coloring by the three
nonzero `F_2^2` colors. -/
def TaitEdgeUncolorable (G : SimpleGraph V) : Prop :=
  ¬ TaitEdgeColorable G

/-- Minimum-degree lower bound for finite simple graphs. -/
def MinimumDegreeAtLeast (G : SimpleGraph V) [DecidableRel G.Adj] (n : Nat) : Prop :=
  ∀ v : V, n ≤ G.degree v

/-- The vertex-minimal Tait counterexample predicate used by the normal-form layer.  This
definition intentionally does not include any of the normal-form conclusions as fields. -/
structure MinimalTaitCounterexample (G : SimpleGraph V) [DecidableRel G.Adj] : Prop where
  cubic : CubicGraph G
  bridgeless : BridgelessGraph G
  planar : AdmitsPlanarBoundaryClosedWalkEmbeddingData G
  uncolorable : TaitEdgeUncolorable G
  vertex_minimal :
    ∀ {U : Type*} [DecidableEq U] [Fintype U] {H : SimpleGraph U} [DecidableRel H.Adj],
      Fintype.card U < Fintype.card V →
        CubicGraph H → BridgelessGraph H →
          AdmitsPlanarBoundaryClosedWalkEmbeddingData H →
            TaitEdgeUncolorable H → False

universe uMin uSurgery

namespace MinimalTaitCounterexample

/-- A minimal Tait counterexample is, by definition, not Tait edge-colorable. -/
theorem not_taitEdgeColorable
    {V0 : Type uMin} [DecidableEq V0] [Fintype V0]
    {G : SimpleGraph V0} [DecidableRel G.Adj]
    (minimal : MinimalTaitCounterexample.{uMin, uSurgery} G) :
    ¬ TaitEdgeColorable G :=
  minimal.uncolorable

/-- Any smaller cubic bridgeless planar graph is Tait edge-colorable; otherwise it would be a
smaller counterexample. -/
theorem smaller_taitEdgeColorable
    {V0 : Type uMin} [DecidableEq V0] [Fintype V0]
    {G : SimpleGraph V0} [DecidableRel G.Adj]
    (minimal : MinimalTaitCounterexample.{uMin, uSurgery} G)
    {U : Type uSurgery} [DecidableEq U] [Fintype U]
    {H : SimpleGraph U} [DecidableRel H.Adj]
    (hcard : Fintype.card U < Fintype.card V0)
    (hcubic : CubicGraph H) (hbridgeless : BridgelessGraph H)
    (hplanar : AdmitsPlanarBoundaryClosedWalkEmbeddingData H) :
    TaitEdgeColorable H := by
  classical
  by_contra huncolorable
  exact MinimalTaitCounterexample.vertex_minimal (G := G) (U := U) (H := H)
    minimal hcard hcubic hbridgeless hplanar huncolorable

/-- Generic Birkhoff-surgery contradiction.  If a surgery produces a smaller cubic bridgeless
planar graph whose Tait coloring would lift back to the original graph, then the original graph
was not a minimal Tait counterexample. -/
theorem false_of_smaller_color_lift
    {V0 : Type uMin} [DecidableEq V0] [Fintype V0]
    {G : SimpleGraph V0} [DecidableRel G.Adj]
    (minimal : MinimalTaitCounterexample.{uMin, uSurgery} G)
    {U : Type uSurgery} [DecidableEq U] [Fintype U]
    {H : SimpleGraph U} [DecidableRel H.Adj]
    (hcard : Fintype.card U < Fintype.card V0)
    (hcubic : CubicGraph H) (hbridgeless : BridgelessGraph H)
    (hplanar : AdmitsPlanarBoundaryClosedWalkEmbeddingData H)
    (hlift : TaitEdgeColorable H → TaitEdgeColorable G) :
    False :=
  minimal.uncolorable
    (hlift (minimal.smaller_taitEdgeColorable hcard hcubic hbridgeless hplanar))

end MinimalTaitCounterexample

/-- Bundled smaller-surgery target for the Birkhoff moves: a smaller cubic bridgeless planar
graph together with a lift from any Tait coloring of that target back to the original graph. -/
structure SmallerTaitSurgeryReduction
    {V0 : Type uMin} [DecidableEq V0] [Fintype V0]
    {G : SimpleGraph V0} [DecidableRel G.Adj]
    (minimal : MinimalTaitCounterexample.{uMin, uSurgery} G)
    {U : Type uSurgery} [DecidableEq U] [Fintype U]
    (H : SimpleGraph U) [DecidableRel H.Adj] : Prop where
  smaller : Fintype.card U < Fintype.card V0
  cubic : CubicGraph H
  bridgeless : BridgelessGraph H
  planar : AdmitsPlanarBoundaryClosedWalkEmbeddingData H
  color_lift : TaitEdgeColorable H → TaitEdgeColorable G

namespace SmallerTaitSurgeryReduction

variable {V0 : Type uMin} [DecidableEq V0] [Fintype V0]
variable {G : SimpleGraph V0} [DecidableRel G.Adj]
variable {minimal : MinimalTaitCounterexample.{uMin, uSurgery} G}
variable {U : Type uSurgery} [DecidableEq U] [Fintype U]
variable {H : SimpleGraph U} [DecidableRel H.Adj]

/-- Minimality colors the smaller surgery target. -/
theorem target_taitEdgeColorable
    (reduction : SmallerTaitSurgeryReduction minimal H) :
    TaitEdgeColorable H :=
  minimal.smaller_taitEdgeColorable reduction.smaller reduction.cubic reduction.bridgeless
    reduction.planar

/-- Any bundled smaller-surgery reduction contradicts minimality. -/
theorem false (reduction : SmallerTaitSurgeryReduction minimal H) : False :=
  minimal.false_of_smaller_color_lift reduction.smaller reduction.cubic reduction.bridgeless
    reduction.planar reduction.color_lift

end SmallerTaitSurgeryReduction

/-- A universe- and instance-carrying witness that some smaller Birkhoff surgery target exists.
This is the ergonomic form used by configuration-specific surgery lemmas: construct one witness,
then the generic minimality theorem refutes the bad configuration. -/
structure SmallerTaitSurgeryWitness
    {V0 : Type uMin} [DecidableEq V0] [Fintype V0]
    {G : SimpleGraph V0} [DecidableRel G.Adj]
    (minimal : MinimalTaitCounterexample.{uMin, uSurgery} G) : Type (max uMin (uSurgery + 1)) where
  U : Type uSurgery
  [decidableEq : DecidableEq U]
  [fintype : Fintype U]
  H : SimpleGraph U
  [decidableRel : DecidableRel H.Adj]
  reduction : SmallerTaitSurgeryReduction minimal H

namespace SmallerTaitSurgeryWitness

variable {V0 : Type uMin} [DecidableEq V0] [Fintype V0]
variable {G : SimpleGraph V0} [DecidableRel G.Adj]
variable {minimal : MinimalTaitCounterexample.{uMin, uSurgery} G}

/-- The bundled smaller surgery target is Tait edge-colorable by minimality. -/
theorem target_taitEdgeColorable (witness : SmallerTaitSurgeryWitness minimal) :
    TaitEdgeColorable witness.H := by
  letI := witness.decidableEq
  letI := witness.fintype
  letI := witness.decidableRel
  exact witness.reduction.target_taitEdgeColorable

/-- Any smaller surgery witness contradicts minimality. -/
theorem false (witness : SmallerTaitSurgeryWitness minimal) : False := by
  letI := witness.decidableEq
  letI := witness.fintype
  letI := witness.decidableRel
  exact witness.reduction.false

end SmallerTaitSurgeryWitness

end BasicPredicates

section PlaneDuality

variable [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W]
variable {G : SimpleGraph V} {T : SimpleGraph W}

/-- Plane triangulation data in the current embedding API: an embedding together with a closed
walk for every face, each of length three.  This is the reusable target needed before one can
talk about the cubic graph's planar dual as an honest triangulation. -/
structure PlaneTriangulationData (T : SimpleGraph W) where
  embedding : PlaneEmbeddingWithBoundary T
  faceWalks : PlanarBoundaryClosedWalkEmbeddingData embedding
  face_length_three :
    ∀ f : {f // f ∈ embedding.faces},
      (faceWalks.faceBoundaryClosedWalk f).walk.length = 3

/-- Shared planar-duality data between a primal cubic graph and its triangulation-side dual.
The edge equivalence is the formal handle used to translate a separating dual cycle into a
primal edge cut. -/
structure PlaneCubicDualData (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : SimpleGraph W) [DecidableRel T.Adj] where
  primalEmbedding : PlaneEmbeddingWithBoundary G
  primalBoundaryWalks : PlanarBoundaryClosedWalkEmbeddingData primalEmbedding
  dualTriangulation : PlaneTriangulationData T
  dualEdgeEquiv : G.edgeSet ≃ T.edgeSet
  primal_cubic : CubicGraph G

namespace PlaneCubicDualData

variable [DecidableRel G.Adj] [DecidableRel T.Adj]

/-- The inverse edge map from dual edges back to primal edges. -/
def primalEdgeOfDualEdge (dual : PlaneCubicDualData G T) : T.edgeSet ≃ G.edgeSet :=
  dual.dualEdgeEquiv.symm

/-- Translate a finite dual-edge support into its primal edge-cut support. -/
def primalCutOfDualSupport (dual : PlaneCubicDualData G T)
    (support : Finset T.edgeSet) : Finset G.edgeSet :=
  support.map dual.primalEdgeOfDualEdge.toEmbedding

@[simp]
theorem primalCutOfDualSupport_card (dual : PlaneCubicDualData G T)
    (support : Finset T.edgeSet) :
    (dual.primalCutOfDualSupport support).card = support.card := by
  simp [primalCutOfDualSupport]

end PlaneCubicDualData

/-- Prop-level normal-form ingredient: the cubic graph has a planar dual whose dual side is a
triangulation in the available embedding API. -/
def CubicDualIsTriangulation (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : SimpleGraph W) [DecidableRel T.Adj] : Prop :=
  Nonempty (PlaneCubicDualData G T)

/-- A separating cycle on the dual side, represented by the primal cyclic cut it induces.  The
Jordan burden is exactly the `CyclicEdgeCutRealization`: it supplies the two sides and proves the
listed primal edges are precisely the side-crossing edges. -/
structure SeparatingDualCycleData [DecidableRel G.Adj] [DecidableRel T.Adj]
    (dual : PlaneCubicDualData G T) (k : Nat) where
  dualEdgeSupport : Finset T.edgeSet
  primalCut : Finset G.edgeSet
  dual_card : dualEdgeSupport.card = k
  primal_card : primalCut.card = k
  primalCut_eq_dualEdgeSupport :
    primalCut = dual.primalCutOfDualSupport dualEdgeSupport
  realization : CyclicEdgeCutRealization G primalCut

namespace SeparatingDualCycleData

variable [DecidableRel G.Adj] [DecidableRel T.Adj]
variable {dual : PlaneCubicDualData G T} {k : Nat}

@[simp]
theorem primalCut_card (cycle : SeparatingDualCycleData dual k) :
    cycle.primalCut.card = k :=
  cycle.primal_card

@[simp]
theorem dualEdgeSupport_card (cycle : SeparatingDualCycleData dual k) :
    cycle.dualEdgeSupport.card = k :=
  cycle.dual_card

/-- Membership in the primal support of a separating dual cycle is exactly crossing the induced
Jordan side. -/
theorem primalCut_mem_iff_crosses
    (cycle : SeparatingDualCycleData dual k) (e : G.edgeSet) :
    e ∈ cycle.primalCut ↔ EdgeCrossesVertexSide G cycle.realization.side e :=
  cycle.realization.hcut_eq e

/-- A separating dual cycle of length at most four induces a bundled graph-side small cyclic
edge cut. -/
def toSmallCyclicEdgeCutOfLengthLeFour
    (cycle : SeparatingDualCycleData dual k) (hk : k ≤ 4) :
    SmallCyclicEdgeCut G :=
  cycle.realization.toSmallCyclicEdgeCut (by
    rw [cycle.primal_card]
    exact hk)

/-- Existence form of the same conversion, matching the repository's cyclic-cut obstruction API. -/
theorem hasCyclicEdgeCutOfSizeAtMostFour_of_length_le_four
    (cycle : SeparatingDualCycleData dual k) (hk : k ≤ 4) :
    HasCyclicEdgeCutOfSizeAtMostFour G :=
  cycle.realization.hasCyclicEdgeCutOfSizeAtMostFour (by
    rw [cycle.primal_card]
    exact hk)

/-- A walk crossing the two Jordan sides of a separating dual cycle hits its primal cut support. -/
theorem exists_mem_primalCut_of_walk_endpoint_sides
    (cycle : SeparatingDualCycleData dual k)
    {u v : V} (p : G.Walk u v)
    (hu : cycle.realization.side u) (hv : ¬ cycle.realization.side v) :
    ∃ e : G.edgeSet, e ∈ cycle.primalCut ∧ (e : Sym2 V) ∈ p.edges :=
  cycle.realization.exists_mem_edgeCut_of_walk_endpoint_sides p hu hv

/-- A walk avoiding the primal cut of a separating dual cycle cannot change Jordan sides. -/
theorem side_iff_of_forall_not_mem_primalCut_of_walk
    (cycle : SeparatingDualCycleData dual k)
    {u v : V} (p : G.Walk u v)
    (havoid : ∀ e : G.edgeSet, e ∈ cycle.primalCut → (e : Sym2 V) ∉ p.edges) :
    cycle.realization.side u ↔ cycle.realization.side v :=
  cycle.realization.side_iff_of_forall_not_mem_edgeCut_of_walk p havoid

end SeparatingDualCycleData

/-- There is no separating dual cycle of a fixed length. -/
def NoSeparatingDualCycleOfLength [DecidableRel G.Adj] [DecidableRel T.Adj]
    (dual : PlaneCubicDualData G T) (k : Nat) : Prop :=
  ¬ Nonempty (SeparatingDualCycleData dual k)

/-- There is no separating dual cycle of any length at most four. -/
def NoSeparatingDualCycleOfLengthAtMostFour [DecidableRel G.Adj] [DecidableRel T.Adj]
    (dual : PlaneCubicDualData G T) : Prop :=
  ∀ k : Nat, k ≤ 4 → NoSeparatingDualCycleOfLength dual k

/-- The Lemma 5.2 small-separator exclusion on the dual side. -/
def NoSeparatingDualCyclesOfLengthThreeAndFour [DecidableRel G.Adj] [DecidableRel T.Adj]
    (dual : PlaneCubicDualData G T) : Prop :=
  NoSeparatingDualCycleOfLength dual 3 ∧ NoSeparatingDualCycleOfLength dual 4

variable [DecidableRel G.Adj] [DecidableRel T.Adj]

/-- The graph-side no-small-cyclic-cut predicate rules out any separating dual cycle whose
translated primal cut has size at most four. -/
theorem noSeparatingDualCycleOfLength_of_noCyclicEdgeCutOfSizeAtMostFour
    (dual : PlaneCubicDualData G T) (hno : NoCyclicEdgeCutOfSizeAtMostFour G)
    {k : Nat} (hk : k ≤ 4) :
    NoSeparatingDualCycleOfLength dual k := by
  rintro ⟨cycle⟩
  exact hno (cycle.hasCyclicEdgeCutOfSizeAtMostFour_of_length_le_four hk)

/-- The graph-side no-small-cyclic-cut predicate rules out separating dual cycles of every
length at most four. -/
theorem noSeparatingDualCycleOfLengthAtMostFour_of_noCyclicEdgeCutOfSizeAtMostFour
    (dual : PlaneCubicDualData G T) (hno : NoCyclicEdgeCutOfSizeAtMostFour G) :
    NoSeparatingDualCycleOfLengthAtMostFour dual :=
  fun _ hk => noSeparatingDualCycleOfLength_of_noCyclicEdgeCutOfSizeAtMostFour dual hno hk

/-- The graph-side no-small-cyclic-cut predicate gives the dual-side exclusion of separating
triangles and separating 4-cycles. -/
theorem noSeparatingDualCyclesOfLengthThreeAndFour_of_noCyclicEdgeCutOfSizeAtMostFour
    (dual : PlaneCubicDualData G T) (hno : NoCyclicEdgeCutOfSizeAtMostFour G) :
    NoSeparatingDualCyclesOfLengthThreeAndFour dual := by
  have hle4 := noSeparatingDualCycleOfLengthAtMostFour_of_noCyclicEdgeCutOfSizeAtMostFour
    dual hno
  constructor
  · exact hle4 3 (by decide)
  · exact hle4 4 (by decide)

/-- A graph-side normal-form package for the minimal-counterexample regime. -/
structure MinimalCounterexampleNormalForm (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : SimpleGraph W) [DecidableRel T.Adj] where
  duality : PlaneCubicDualData G T
  dual_min_degree : MinimumDegreeAtLeast T 5
  no_small_cyclic_edge_cut : NoCyclicEdgeCutOfSizeAtMostFour G
  no_small_separating_dual_cycles :
    NoSeparatingDualCyclesOfLengthThreeAndFour duality

namespace MinimalCounterexampleNormalForm

/-- The dual graph in normal form has no separating triangle. -/
theorem noSeparatingTriangle
    (normal : MinimalCounterexampleNormalForm G T) :
    NoSeparatingDualCycleOfLength normal.duality 3 :=
  normal.no_small_separating_dual_cycles.1

/-- The dual graph in normal form has no separating 4-cycle. -/
theorem noSeparatingFourCycle
    (normal : MinimalCounterexampleNormalForm G T) :
    NoSeparatingDualCycleOfLength normal.duality 4 :=
  normal.no_small_separating_dual_cycles.2

/-- The cubic side in normal form is cyclically five-edge-connected in the existing API. -/
theorem cyclicallyFiveEdgeConnected
    (normal : MinimalCounterexampleNormalForm G T) :
    CyclicallyFiveEdgeConnected G :=
  normal.no_small_cyclic_edge_cut.cyclicallyFiveEdgeConnected

/-- Normal form excludes every separating dual cycle whose translated cyclic cut has size at
most four. -/
theorem noSeparatingDualCycleOfLengthAtMostFour
    (normal : MinimalCounterexampleNormalForm G T) :
    NoSeparatingDualCycleOfLengthAtMostFour normal.duality :=
  noSeparatingDualCycleOfLengthAtMostFour_of_noCyclicEdgeCutOfSizeAtMostFour
    normal.duality normal.no_small_cyclic_edge_cut

end MinimalCounterexampleNormalForm

/-- Assemble the normal-form package once the dual triangulation data, the minimum-degree
bound, and the graph-side small-cut exclusion are available. -/
def minimalCounterexampleNormalForm
    (dual : PlaneCubicDualData G T)
    (hdegree : MinimumDegreeAtLeast T 5)
    (hcut : NoCyclicEdgeCutOfSizeAtMostFour G) :
    MinimalCounterexampleNormalForm G T where
  duality := dual
  dual_min_degree := hdegree
  no_small_cyclic_edge_cut := hcut
  no_small_separating_dual_cycles :=
    noSeparatingDualCyclesOfLengthThreeAndFour_of_noCyclicEdgeCutOfSizeAtMostFour dual hcut

/-- Lemma 5.2 stated as an obligation against the current infrastructure boundary: a minimal
Tait counterexample equipped with cubic-dual triangulation data must lie in normal form. -/
def Lemma52MinimalCounterexampleNormalFormObligation
    (_minimal : MinimalTaitCounterexample G) (dual : PlaneCubicDualData G T) : Prop :=
  ∃ normal : MinimalCounterexampleNormalForm G T, normal.duality = dual

/-- The single named Birkhoff-surgery obligation left by Lemma 5.2 at this layer: from true
minimality plus the plane duality data, prove minimum dual degree at least five and no cyclic
edge cut of size at most four. -/
structure Lemma52BirkhoffSurgeryObligation
    (minimal : MinimalTaitCounterexample G) (dual : PlaneCubicDualData G T) : Prop where
  minimum_degree : MinimumDegreeAtLeast T 5
  no_small_cyclic_edge_cut : NoCyclicEdgeCutOfSizeAtMostFour G

/-- Vertex-deletion surgery surface for Lemma 5.2: a low-degree dual vertex would be deleted,
the smaller graph colored by minimality, and the color extended back.  The formal conclusion of
that surgery is the minimum-degree lower bound. -/
structure VertexDeletionSurgery
    (minimal : MinimalTaitCounterexample G) (dual : PlaneCubicDualData G T) : Prop where
  minimum_degree : MinimumDegreeAtLeast T 5

/-- Triangle cut-and-paste surgery surface for Lemma 5.2: color the two disks cut off by a
separating triangle and relabel one coloring so the boundary triangle agrees. -/
structure SeparatingTriangleCutPasteSurgery
    (minimal : MinimalTaitCounterexample G) (dual : PlaneCubicDualData G T) : Prop where
  no_separating_triangle : NoSeparatingDualCycleOfLength dual 3

/-- Four-cycle identification surgery surface for Lemma 5.2: use an absent diagonal of the
separating 4-cycle, identify opposite vertices, color the smaller graph, and lift the coloring. -/
structure SeparatingFourCycleIdentificationSurgery
    (minimal : MinimalTaitCounterexample G) (dual : PlaneCubicDualData G T) : Prop where
  no_separating_four_cycle : NoSeparatingDualCycleOfLength dual 4

/-- Graph-side small-cut surgery surface for Lemma 5.2.  This is the reusable conclusion needed
by the CAP5 and annulus layers already present in the repository. -/
structure SmallCyclicCutBirkhoffSurgery
    (minimal : MinimalTaitCounterexample G) : Prop where
  no_small_cyclic_edge_cut : NoCyclicEdgeCutOfSizeAtMostFour G

/-- Generic vertex-deletion normal-form step: if every low-degree dual vertex supplies a smaller
Birkhoff surgery witness, then no low-degree dual vertex exists. -/
theorem minimumDegreeAtLeast_of_forall_lowDegree_smallerTaitSurgeryWitness
    {minimal : MinimalTaitCounterexample G}
    (hreduce :
      ∀ v : W, T.degree v < 5 → Nonempty (SmallerTaitSurgeryWitness minimal)) :
    MinimumDegreeAtLeast T 5 := by
  intro v
  by_contra hnot
  have hlt : T.degree v < 5 := Nat.lt_of_not_ge hnot
  rcases hreduce v hlt with ⟨witness⟩
  exact witness.false

/-- Vertex-deletion surgery from its concrete smaller-surgery reduction target. -/
def vertexDeletionSurgery_of_forall_lowDegree_smallerTaitSurgeryWitness
    {minimal : MinimalTaitCounterexample G} {dual : PlaneCubicDualData G T}
    (hreduce :
      ∀ v : W, T.degree v < 5 → Nonempty (SmallerTaitSurgeryWitness minimal)) :
    VertexDeletionSurgery minimal dual where
  minimum_degree :=
    minimumDegreeAtLeast_of_forall_lowDegree_smallerTaitSurgeryWitness hreduce

/-- Generic cut-and-paste normal-form step: if every separating dual cycle of length `k` supplies
a smaller Birkhoff surgery witness, then no such separator exists. -/
theorem noSeparatingDualCycleOfLength_of_forall_cycle_smallerTaitSurgeryWitness
    {minimal : MinimalTaitCounterexample G} {dual : PlaneCubicDualData G T} {k : Nat}
    (hreduce :
      ∀ _cycle : SeparatingDualCycleData dual k,
        Nonempty (SmallerTaitSurgeryWitness minimal)) :
    NoSeparatingDualCycleOfLength dual k := by
  rintro ⟨cycle⟩
  rcases hreduce cycle with ⟨witness⟩
  exact witness.false

/-- Triangle cut-and-paste surgery from concrete smaller-surgery reductions for every separating
dual triangle. -/
def separatingTriangleCutPasteSurgery_of_forall_triangle_smallerTaitSurgeryWitness
    {minimal : MinimalTaitCounterexample G} {dual : PlaneCubicDualData G T}
    (hreduce :
      ∀ _cycle : SeparatingDualCycleData dual 3,
        Nonempty (SmallerTaitSurgeryWitness minimal)) :
    SeparatingTriangleCutPasteSurgery minimal dual where
  no_separating_triangle :=
    noSeparatingDualCycleOfLength_of_forall_cycle_smallerTaitSurgeryWitness hreduce

/-- Four-cycle identification surgery from concrete smaller-surgery reductions for every
separating dual 4-cycle. -/
def separatingFourCycleIdentificationSurgery_of_forall_fourCycle_smallerTaitSurgeryWitness
    {minimal : MinimalTaitCounterexample G} {dual : PlaneCubicDualData G T}
    (hreduce :
      ∀ _cycle : SeparatingDualCycleData dual 4,
        Nonempty (SmallerTaitSurgeryWitness minimal)) :
    SeparatingFourCycleIdentificationSurgery minimal dual where
  no_separating_four_cycle :=
    noSeparatingDualCycleOfLength_of_forall_cycle_smallerTaitSurgeryWitness hreduce

/-- Generic small-cut normal-form step: if every small cyclic cut supplies a smaller Birkhoff
surgery witness, then the graph has no cyclic edge cut of size at most four. -/
theorem noCyclicEdgeCutOfSizeAtMostFour_of_forall_smallCut_smallerTaitSurgeryWitness
    {minimal : MinimalTaitCounterexample G}
    (hreduce :
      ∀ cut : SmallCyclicEdgeCut G, cut.edgeCut.card ≤ 4 →
        Nonempty (SmallerTaitSurgeryWitness minimal)) :
    NoCyclicEdgeCutOfSizeAtMostFour G := by
  rintro ⟨cut, hcard⟩
  rcases hreduce cut hcard with ⟨witness⟩
  exact witness.false

/-- Small cyclic-cut surgery from concrete smaller-surgery reductions for every size-at-most-four
cyclic cut. -/
def smallCyclicCutBirkhoffSurgery_of_forall_smallCut_smallerTaitSurgeryWitness
    {minimal : MinimalTaitCounterexample G}
    (hreduce :
      ∀ cut : SmallCyclicEdgeCut G, cut.edgeCut.card ≤ 4 →
        Nonempty (SmallerTaitSurgeryWitness minimal)) :
    SmallCyclicCutBirkhoffSurgery minimal where
  no_small_cyclic_edge_cut :=
    noCyclicEdgeCutOfSizeAtMostFour_of_forall_smallCut_smallerTaitSurgeryWitness hreduce

/-- The Birkhoff surgery suite organized by the three manuscript moves.  The triangle and
4-cycle fields expose the dual separator conclusions directly; the small-cut field is the
graph-side form consumed by the existing `CyclicEdgeCut` API. -/
structure Lemma52BirkhoffSurgerySuite
    (minimal : MinimalTaitCounterexample G) (dual : PlaneCubicDualData G T) : Prop where
  vertex_deletion : VertexDeletionSurgery minimal dual
  triangle_cut_paste : SeparatingTriangleCutPasteSurgery minimal dual
  four_cycle_identification : SeparatingFourCycleIdentificationSurgery minimal dual
  small_cyclic_cut : SmallCyclicCutBirkhoffSurgery minimal

/-- The structured Birkhoff surgery suite supplies the compact Lemma 5.2 obligation used by
the normal-form constructor. -/
def Lemma52BirkhoffSurgerySuite.toObligation
    {minimal : MinimalTaitCounterexample G} {dual : PlaneCubicDualData G T}
    (suite : Lemma52BirkhoffSurgerySuite minimal dual) :
    Lemma52BirkhoffSurgeryObligation minimal dual where
  minimum_degree := suite.vertex_deletion.minimum_degree
  no_small_cyclic_edge_cut := suite.small_cyclic_cut.no_small_cyclic_edge_cut

/-- The triangle surgery conclusion is preserved as a direct projection from the suite. -/
theorem Lemma52BirkhoffSurgerySuite.noSeparatingTriangle
    {minimal : MinimalTaitCounterexample G} {dual : PlaneCubicDualData G T}
    (suite : Lemma52BirkhoffSurgerySuite minimal dual) :
    NoSeparatingDualCycleOfLength dual 3 :=
  suite.triangle_cut_paste.no_separating_triangle

/-- The 4-cycle surgery conclusion is preserved as a direct projection from the suite. -/
theorem Lemma52BirkhoffSurgerySuite.noSeparatingFourCycle
    {minimal : MinimalTaitCounterexample G} {dual : PlaneCubicDualData G T}
    (suite : Lemma52BirkhoffSurgerySuite minimal dual) :
    NoSeparatingDualCycleOfLength dual 4 :=
  suite.four_cycle_identification.no_separating_four_cycle

/-- Conditional Lemma 5.2 data endpoint: once the Birkhoff surgeries have supplied their two
exact normal-form consequences, the shared normal-form package follows, including the dual
separator exclusion via the existing cyclic-cut API. -/
def lemma52_minimalCounterexampleNormalFormData
    {minimal : MinimalTaitCounterexample G} {dual : PlaneCubicDualData G T}
    (h : Lemma52BirkhoffSurgeryObligation minimal dual) :
    MinimalCounterexampleNormalForm G T :=
  minimalCounterexampleNormalForm dual h.minimum_degree h.no_small_cyclic_edge_cut

/-- Proposition-valued Lemma 5.2 endpoint for downstream theorem statements. -/
theorem lemma52_minimalCounterexampleNormalForm
    {minimal : MinimalTaitCounterexample G} {dual : PlaneCubicDualData G T}
    (h : Lemma52BirkhoffSurgeryObligation minimal dual) :
    Nonempty (MinimalCounterexampleNormalForm G T) :=
  ⟨lemma52_minimalCounterexampleNormalFormData h⟩

/-- Lemma 5.2 endpoint from the named Birkhoff surgery suite. -/
theorem lemma52_minimalCounterexampleNormalForm_of_birkhoffSurgerySuite
    {minimal : MinimalTaitCounterexample G} {dual : PlaneCubicDualData G T}
    (suite : Lemma52BirkhoffSurgerySuite minimal dual) :
    Nonempty (MinimalCounterexampleNormalForm G T) :=
  lemma52_minimalCounterexampleNormalForm suite.toObligation

/-- Assemble the full Lemma 5.2 surgery suite from the concrete smaller-surgery reduction
targets for each forbidden configuration family. -/
def lemma52BirkhoffSurgerySuite_of_smallerTaitSurgeryWitnesses
    {minimal : MinimalTaitCounterexample G} {dual : PlaneCubicDualData G T}
    (hlowDegree :
      ∀ v : W, T.degree v < 5 → Nonempty (SmallerTaitSurgeryWitness minimal))
    (htriangle :
      ∀ _cycle : SeparatingDualCycleData dual 3,
        Nonempty (SmallerTaitSurgeryWitness minimal))
    (hfourCycle :
      ∀ _cycle : SeparatingDualCycleData dual 4,
        Nonempty (SmallerTaitSurgeryWitness minimal))
    (hsmallCut :
      ∀ cut : SmallCyclicEdgeCut G, cut.edgeCut.card ≤ 4 →
        Nonempty (SmallerTaitSurgeryWitness minimal)) :
    Lemma52BirkhoffSurgerySuite minimal dual where
  vertex_deletion :=
    vertexDeletionSurgery_of_forall_lowDegree_smallerTaitSurgeryWitness hlowDegree
  triangle_cut_paste :=
    separatingTriangleCutPasteSurgery_of_forall_triangle_smallerTaitSurgeryWitness htriangle
  four_cycle_identification :=
    separatingFourCycleIdentificationSurgery_of_forall_fourCycle_smallerTaitSurgeryWitness
      hfourCycle
  small_cyclic_cut :=
    smallCyclicCutBirkhoffSurgery_of_forall_smallCut_smallerTaitSurgeryWitness hsmallCut

/-- Lemma 5.2 normal-form endpoint directly from concrete smaller-surgery reductions for all
forbidden configuration families. -/
theorem lemma52_minimalCounterexampleNormalForm_of_smallerTaitSurgeryWitnesses
    {minimal : MinimalTaitCounterexample G} {dual : PlaneCubicDualData G T}
    (hlowDegree :
      ∀ v : W, T.degree v < 5 → Nonempty (SmallerTaitSurgeryWitness minimal))
    (htriangle :
      ∀ _cycle : SeparatingDualCycleData dual 3,
        Nonempty (SmallerTaitSurgeryWitness minimal))
    (hfourCycle :
      ∀ _cycle : SeparatingDualCycleData dual 4,
        Nonempty (SmallerTaitSurgeryWitness minimal))
    (hsmallCut :
      ∀ cut : SmallCyclicEdgeCut G, cut.edgeCut.card ≤ 4 →
        Nonempty (SmallerTaitSurgeryWitness minimal)) :
    Nonempty (MinimalCounterexampleNormalForm G T) :=
  lemma52_minimalCounterexampleNormalForm_of_birkhoffSurgerySuite
    (lemma52BirkhoffSurgerySuite_of_smallerTaitSurgeryWitnesses
      hlowDegree htriangle hfourCycle hsmallCut)

end PlaneDuality

section CAP5Tightness

variable [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W]
variable {G : SimpleGraph V} {T : SimpleGraph W}
variable [DecidableRel G.Adj] [DecidableRel T.Adj]

/-- A literal 5-cycle carried by one side of a cut.  The exact side/component statement is kept
separate from the existence of a side-contained cycle so later planar disk-counting code can
strengthen it without changing CAP5 users. -/
structure LiteralFiveCycleOnSide (G : SimpleGraph V) (side : V → Prop) where
  base : V
  cycle : G.Walk base base
  base_side : side base
  isCycle : cycle.IsCycle
  length_five : cycle.length = 5
  support_side : ∀ v : V, v ∈ cycle.support → side v

/-- A literal side 5-cycle is, in particular, a cycle on that side. -/
theorem LiteralFiveCycleOnSide.hasCycleOnSide
    {side : V → Prop} (cap : LiteralFiveCycleOnSide G side) :
    HasCycleOnSide G side :=
  ⟨cap.base, cap.base_side, cap.cycle, cap.isCycle, cap.support_side⟩

/-- Graph-facing CAP5 pinch data: a cyclic 5-edge cut whose selected side carries a literal
5-cycle and whose five boundary edges are explicitly enumerated. -/
structure CAP5Pinch (G : SimpleGraph V) where
  edgeCut : Finset G.edgeSet
  realization : CyclicEdgeCutRealization G edgeCut
  hcard : edgeCut.card = 5
  boundary : CAP5BoundaryEdgeEnumeration edgeCut
  capCycle : LiteralFiveCycleOnSide G realization.side

namespace CAP5Pinch

/-- Construct CAP5 pinch data from a realized cyclic cut, a five-edge boundary enumeration, and
a literal side 5-cycle. -/
def ofBoundary
    {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut)
    (boundary : CAP5BoundaryEdgeEnumeration edgeCut)
    (capCycle : LiteralFiveCycleOnSide G realization.side) :
    CAP5Pinch G where
  edgeCut := edgeCut
  realization := realization
  hcard := boundary.card_support
  boundary := boundary
  capCycle := capCycle

@[simp]
theorem edgeCut_card (pinch : CAP5Pinch G) :
    pinch.edgeCut.card = 5 :=
  pinch.hcard

@[simp]
theorem boundary_card (pinch : CAP5Pinch G) :
    pinch.edgeCut.card = 5 :=
  pinch.boundary.card_support

/-- The selected side of a CAP5 pinch contains the literal boundary 5-cycle. -/
theorem capCycle_length_five (pinch : CAP5Pinch G) :
    pinch.capCycle.cycle.length = 5 :=
  pinch.capCycle.length_five

/-- The selected side of a CAP5 pinch contains a cycle. -/
theorem hasCycleOnCapSide (pinch : CAP5Pinch G) :
    HasCycleOnSide G pinch.realization.side :=
  pinch.capCycle.hasCycleOnSide

/-- The complementary side of a CAP5 pinch also contains a cycle, because the pinch is a cyclic
edge-cut realization. -/
theorem hasCycleOnOutside (pinch : CAP5Pinch G) :
    HasCycleOnSide G (fun v => ¬ pinch.realization.side v) :=
  pinch.realization.houtside_cycle

/-- Every enumerated CAP5 boundary edge belongs to the pinch edge support. -/
theorem boundaryEdge_mem (pinch : CAP5Pinch G) (i : Fin 5) :
    pinch.boundary.boundaryEdge i ∈ pinch.edgeCut :=
  pinch.boundary.boundaryEdge_mem_support i

/-- Every enumerated CAP5 boundary edge crosses the chosen Jordan side. -/
theorem boundaryEdge_crosses (pinch : CAP5Pinch G) (i : Fin 5) :
    EdgeCrossesVertexSide G pinch.realization.side (pinch.boundary.boundaryEdge i) :=
  (pinch.realization.hcut_eq (pinch.boundary.boundaryEdge i)).1
    (pinch.boundaryEdge_mem i)

end CAP5Pinch

/-- CAP5-free graph-side normal form: no cyclic five-edge cut whose small side is a literal
5-cycle has been realized. -/
def CAP5Free (G : SimpleGraph V) : Prop :=
  ¬ Nonempty (CAP5Pinch G)

/-- Normal form after CAP5 elimination: the Lemma 5.2 normal-form package plus absence of CAP5
pinches. -/
structure MinimalCounterexampleCAP5FreeNormalForm (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : SimpleGraph W) [DecidableRel T.Adj] where
  normal : MinimalCounterexampleNormalForm G T
  cap5_free : CAP5Free G

/-- Tightness data for a separating dual 5-cycle: its translated primal cut is a CAP5 pinch. -/
structure TightSeparatingDualFiveCycle
    {dual : PlaneCubicDualData G T} (cycle : SeparatingDualCycleData dual 5) where
  pinch : CAP5Pinch G
  same_cut : pinch.edgeCut = cycle.primalCut

namespace TightSeparatingDualFiveCycle

variable {dual : PlaneCubicDualData G T}
variable {cycle : SeparatingDualCycleData dual 5}

@[simp]
theorem pinch_edgeCut_eq_primalCut (tight : TightSeparatingDualFiveCycle cycle) :
    tight.pinch.edgeCut = cycle.primalCut :=
  tight.same_cut

@[simp]
theorem primalCut_card (_tight : TightSeparatingDualFiveCycle cycle) :
    cycle.primalCut.card = 5 :=
  cycle.primal_card

theorem pinch_card (tight : TightSeparatingDualFiveCycle cycle) :
    tight.pinch.edgeCut.card = 5 :=
  tight.pinch.hcard

/-- Tightness transports the CAP5 boundary enumeration onto the separating cycle's primal cut. -/
theorem primalCut_has_boundary_enumeration (tight : TightSeparatingDualFiveCycle cycle) :
    Nonempty (CAP5BoundaryEdgeEnumeration cycle.primalCut) := by
  rw [← tight.same_cut]
  exact ⟨tight.pinch.boundary⟩

/-- Tightness transports the CAP5 side-cycle witness onto the induced primal realization. -/
theorem hasCycleOnTightSide (tight : TightSeparatingDualFiveCycle cycle) :
    HasCycleOnSide G tight.pinch.realization.side :=
  tight.pinch.hasCycleOnCapSide

end TightSeparatingDualFiveCycle

/-- The five boundary positions of a disk bounded by a separating dual 5-cycle. -/
inductive FiveBoundaryIndex where
  | b0
  | b1
  | b2
  | b3
  | b4
  deriving DecidableEq

namespace FiveBoundaryIndex

/-- Cyclic successor around the five boundary positions. -/
def next : FiveBoundaryIndex → FiveBoundaryIndex
  | .b0 => .b1
  | .b1 => .b2
  | .b2 => .b3
  | .b3 => .b4
  | .b4 => .b0

/-- Two boundary positions are cyclically adjacent when one is the successor of the other. -/
def CyclicAdjacent (i j : FiveBoundaryIndex) : Prop :=
  next i = j ∨ next j = i

/-- Every boundary position is cyclically adjacent to its successor. -/
theorem cyclicAdjacent_next (i : FiveBoundaryIndex) :
    CyclicAdjacent i (next i) :=
  Or.inl rfl

end FiveBoundaryIndex

/-- Boundary-charge arithmetic profile for the five vertices on a separating 5-cycle.  The
geometric disk-counting part of Lemma 5.3 supplies the hypotheses: each boundary charge is at
most one, and the total boundary charge is at least four. -/
structure FiveBoundaryChargeProfile where
  ch0 : Int
  ch1 : Int
  ch2 : Int
  ch3 : Int
  ch4 : Int
  ch0_le_one : ch0 ≤ 1
  ch1_le_one : ch1 ≤ 1
  ch2_le_one : ch2 ≤ 1
  ch3_le_one : ch3 ≤ 1
  ch4_le_one : ch4 ≤ 1
  boundary_sum_ge_four : 4 ≤ ch0 + ch1 + ch2 + ch3 + ch4

namespace FiveBoundaryChargeProfile

/-- Read a boundary charge by boundary position. -/
def charge (profile : FiveBoundaryChargeProfile) : FiveBoundaryIndex → Int
  | .b0 => profile.ch0
  | .b1 => profile.ch1
  | .b2 => profile.ch2
  | .b3 => profile.ch3
  | .b4 => profile.ch4

/-- Every charge in the five-boundary profile is at most one. -/
theorem charge_le_one (profile : FiveBoundaryChargeProfile) (i : FiveBoundaryIndex) :
    profile.charge i ≤ 1 := by
  cases i <;> simp [charge, profile.ch0_le_one, profile.ch1_le_one,
    profile.ch2_le_one, profile.ch3_le_one, profile.ch4_le_one]

/-- In a five-entry integer profile with each entry at most one and total at least four, at most
one boundary charge can differ from one.  This is the finite arithmetic core of the Lemma 5.3
disk-charge count. -/
theorem not_two_boundaryCharges_ne_one
    (profile : FiveBoundaryChargeProfile) {i j : FiveBoundaryIndex} (hij : i ≠ j)
    (hi : profile.charge i ≠ 1) (hj : profile.charge j ≠ 1) :
    False := by
  have hlei := profile.charge_le_one i
  have hlej := profile.charge_le_one j
  have hi0 : profile.charge i ≤ 0 := by omega
  have hj0 : profile.charge j ≤ 0 := by omega
  have h0 := profile.ch0_le_one
  have h1 := profile.ch1_le_one
  have h2 := profile.ch2_le_one
  have h3 := profile.ch3_le_one
  have h4 := profile.ch4_le_one
  have hsum := profile.boundary_sum_ge_four
  cases i <;> cases j <;> simp [charge] at hij hi hj hi0 hj0
  all_goals omega

/-- If one boundary position is chosen as the non-unit exception, every other boundary charge
is forced to be one. -/
theorem charge_eq_one_of_ne_of_charge_ne_one
    (profile : FiveBoundaryChargeProfile) {exception i : FiveBoundaryIndex}
    (hne : i ≠ exception) (hexception : profile.charge exception ≠ 1) :
    profile.charge i = 1 := by
  by_contra hi
  exact profile.not_two_boundaryCharges_ne_one hne hi hexception

/-- There is a boundary position away from which all five-cycle boundary charges are one.  This
is the form consumed by the disk-triangulation part of Lemma 5.3: the charge count leaves at most
one possible exceptional boundary vertex. -/
theorem exists_exception_charge_eq_one_of_ne
    (profile : FiveBoundaryChargeProfile) :
    ∃ exception : FiveBoundaryIndex, ∀ i : FiveBoundaryIndex, i ≠ exception →
      profile.charge i = 1 := by
  classical
  by_cases hall : ∀ i : FiveBoundaryIndex, profile.charge i = 1
  · exact ⟨.b0, fun i _ => hall i⟩
  · push Not at hall
    rcases hall with ⟨exception, hexception⟩
    exact ⟨exception, fun i hne =>
      profile.charge_eq_one_of_ne_of_charge_ne_one hne hexception⟩

/-- The five-cycle charge count supplies three consecutive unit boundary charges.  This is the
finite combinatorial shape used by the next Lemma 5.3 step, where consecutive degree-three
boundary vertices force a common interior apex. -/
theorem exists_three_consecutive_charges_eq_one
    (profile : FiveBoundaryChargeProfile) :
    ∃ i : FiveBoundaryIndex,
      profile.charge i = 1 ∧
        profile.charge (FiveBoundaryIndex.next i) = 1 ∧
          profile.charge (FiveBoundaryIndex.next (FiveBoundaryIndex.next i)) = 1 := by
  rcases profile.exists_exception_charge_eq_one_of_ne with ⟨exception, hunit⟩
  cases exception
  · exact ⟨.b1,
      hunit .b1 (by decide),
      by simpa [FiveBoundaryIndex.next] using hunit .b2 (by decide),
      by simpa [FiveBoundaryIndex.next] using hunit .b3 (by decide)⟩
  · exact ⟨.b2,
      hunit .b2 (by decide),
      by simpa [FiveBoundaryIndex.next] using hunit .b3 (by decide),
      by simpa [FiveBoundaryIndex.next] using hunit .b4 (by decide)⟩
  · exact ⟨.b3,
      hunit .b3 (by decide),
      by simpa [FiveBoundaryIndex.next] using hunit .b4 (by decide),
      by simpa [FiveBoundaryIndex.next] using hunit .b0 (by decide)⟩
  · exact ⟨.b4,
      hunit .b4 (by decide),
      by simpa [FiveBoundaryIndex.next] using hunit .b0 (by decide),
      by simpa [FiveBoundaryIndex.next] using hunit .b1 (by decide)⟩
  · exact ⟨.b0,
      hunit .b0 (by decide),
      by simpa [FiveBoundaryIndex.next] using hunit .b1 (by decide),
      by simpa [FiveBoundaryIndex.next] using hunit .b2 (by decide)⟩

/-- In particular, the five-cycle charge count supplies an adjacent pair of unit boundary
charges. -/
theorem exists_adjacent_charges_eq_one
    (profile : FiveBoundaryChargeProfile) :
    ∃ i j : FiveBoundaryIndex,
      FiveBoundaryIndex.CyclicAdjacent i j ∧
        profile.charge i = 1 ∧ profile.charge j = 1 := by
  rcases profile.exists_three_consecutive_charges_eq_one with ⟨i, hi, hnext, _⟩
  exact ⟨i, FiveBoundaryIndex.next i, FiveBoundaryIndex.cyclicAdjacent_next i, hi, hnext⟩

end FiveBoundaryChargeProfile

/-- Arithmetic interface for the Euler charge count on a disk triangulation bounded by a
5-cycle.  The geometric disk layer must supply the identity and the interior-charge upper bound;
this structure then produces the boundary-charge profile used by the finite CAP5 argument. -/
structure FiveCycleDiskEulerChargeData where
  ch0 : Int
  ch1 : Int
  ch2 : Int
  ch3 : Int
  ch4 : Int
  interior_charge_sum : Int
  ch0_le_one : ch0 ≤ 1
  ch1_le_one : ch1 ≤ 1
  ch2_le_one : ch2 ≤ 1
  ch3_le_one : ch3 ≤ 1
  ch4_le_one : ch4 ≤ 1
  euler_charge_identity : interior_charge_sum + (ch0 + ch1 + ch2 + ch3 + ch4) = 6
  interior_charge_sum_le_two : interior_charge_sum ≤ 2

namespace FiveCycleDiskEulerChargeData

/-- The Euler identity plus the interior-charge bound force total boundary charge at least four. -/
theorem boundary_charge_sum_ge_four (data : FiveCycleDiskEulerChargeData) :
    4 ≤ data.ch0 + data.ch1 + data.ch2 + data.ch3 + data.ch4 := by
  have hidentity := data.euler_charge_identity
  have hinterior := data.interior_charge_sum_le_two
  omega

/-- Convert the disk Euler-charge data into the five-boundary charge profile used by the finite
Lemma 5.3 arithmetic. -/
def toFiveBoundaryChargeProfile (data : FiveCycleDiskEulerChargeData) :
    FiveBoundaryChargeProfile where
  ch0 := data.ch0
  ch1 := data.ch1
  ch2 := data.ch2
  ch3 := data.ch3
  ch4 := data.ch4
  ch0_le_one := data.ch0_le_one
  ch1_le_one := data.ch1_le_one
  ch2_le_one := data.ch2_le_one
  ch3_le_one := data.ch3_le_one
  ch4_le_one := data.ch4_le_one
  boundary_sum_ge_four := data.boundary_charge_sum_ge_four

/-- Disk Euler-charge data supplies three consecutive unit boundary charges. -/
theorem exists_three_consecutive_charges_eq_one
    (data : FiveCycleDiskEulerChargeData) :
    ∃ i : FiveBoundaryIndex,
      data.toFiveBoundaryChargeProfile.charge i = 1 ∧
        data.toFiveBoundaryChargeProfile.charge (FiveBoundaryIndex.next i) = 1 ∧
          data.toFiveBoundaryChargeProfile.charge
            (FiveBoundaryIndex.next (FiveBoundaryIndex.next i)) = 1 :=
  data.toFiveBoundaryChargeProfile.exists_three_consecutive_charges_eq_one

end FiveCycleDiskEulerChargeData

/-- Local disk-triangulation facts around a chordless separating dual 5-cycle, after the charge
count has identified unit-charge boundary vertices.  Each boundary edge has an interior triangular
face apex; a unit-charge boundary vertex has at most one interior neighbor in the disk. -/
structure FiveCycleDiskTriangulationLocalData
    (T : SimpleGraph W) (profile : FiveBoundaryChargeProfile) where
  boundary : FiveBoundaryIndex → W
  interior : W → Prop
  edgeApex : FiveBoundaryIndex → W
  edgeApex_interior : ∀ i : FiveBoundaryIndex, interior (edgeApex i)
  edgeApex_adj_left : ∀ i : FiveBoundaryIndex, T.Adj (boundary i) (edgeApex i)
  edgeApex_adj_right :
    ∀ i : FiveBoundaryIndex, T.Adj (boundary (FiveBoundaryIndex.next i)) (edgeApex i)
  unit_unique_interior_neighbor :
    ∀ i : FiveBoundaryIndex, profile.charge i = 1 →
      ∀ x y : W, interior x → interior y →
        T.Adj (boundary i) x → T.Adj (boundary i) y → x = y

namespace FiveCycleDiskTriangulationLocalData

variable {profile : FiveBoundaryChargeProfile}
variable {T : SimpleGraph W}

/-- Adjacent boundary-edge apices agree across a unit-charge boundary vertex. -/
theorem edgeApex_eq_next_of_unit
    (disk : FiveCycleDiskTriangulationLocalData T profile)
    {i : FiveBoundaryIndex} (hunit : profile.charge (FiveBoundaryIndex.next i) = 1) :
    disk.edgeApex i = disk.edgeApex (FiveBoundaryIndex.next i) :=
  disk.unit_unique_interior_neighbor (FiveBoundaryIndex.next i) hunit
    (disk.edgeApex i) (disk.edgeApex (FiveBoundaryIndex.next i))
    (disk.edgeApex_interior i) (disk.edgeApex_interior (FiveBoundaryIndex.next i))
    (disk.edgeApex_adj_right i) (disk.edgeApex_adj_left (FiveBoundaryIndex.next i))

/-- The local disk facts plus the five-cycle charge count force all five boundary-edge apices
to be the same vertex. -/
theorem edgeApex_eq_edgeApex_b0
    (disk : FiveCycleDiskTriangulationLocalData T profile) :
    ∀ i : FiveBoundaryIndex, disk.edgeApex i = disk.edgeApex .b0 := by
  rcases profile.exists_exception_charge_eq_one_of_ne with ⟨exception, hunit⟩
  cases exception
  · have h01 : disk.edgeApex .b0 = disk.edgeApex .b1 :=
      disk.edgeApex_eq_next_of_unit
        (by simpa [FiveBoundaryIndex.next] using hunit .b1 (by decide))
    have h12 : disk.edgeApex .b1 = disk.edgeApex .b2 :=
      disk.edgeApex_eq_next_of_unit
        (by simpa [FiveBoundaryIndex.next] using hunit .b2 (by decide))
    have h23 : disk.edgeApex .b2 = disk.edgeApex .b3 :=
      disk.edgeApex_eq_next_of_unit
        (by simpa [FiveBoundaryIndex.next] using hunit .b3 (by decide))
    have h34 : disk.edgeApex .b3 = disk.edgeApex .b4 :=
      disk.edgeApex_eq_next_of_unit
        (by simpa [FiveBoundaryIndex.next] using hunit .b4 (by decide))
    intro i
    cases i
    · rfl
    · exact h01.symm
    · exact (h01.trans h12).symm
    · exact ((h01.trans h12).trans h23).symm
    · exact (((h01.trans h12).trans h23).trans h34).symm
  · have h12 : disk.edgeApex .b1 = disk.edgeApex .b2 :=
      disk.edgeApex_eq_next_of_unit
        (by simpa [FiveBoundaryIndex.next] using hunit .b2 (by decide))
    have h23 : disk.edgeApex .b2 = disk.edgeApex .b3 :=
      disk.edgeApex_eq_next_of_unit
        (by simpa [FiveBoundaryIndex.next] using hunit .b3 (by decide))
    have h34 : disk.edgeApex .b3 = disk.edgeApex .b4 :=
      disk.edgeApex_eq_next_of_unit
        (by simpa [FiveBoundaryIndex.next] using hunit .b4 (by decide))
    have h40 : disk.edgeApex .b4 = disk.edgeApex .b0 :=
      disk.edgeApex_eq_next_of_unit
        (by simpa [FiveBoundaryIndex.next] using hunit .b0 (by decide))
    intro i
    cases i
    · rfl
    · exact (((h12.trans h23).trans h34).trans h40)
    · exact ((h23.trans h34).trans h40)
    · exact (h34.trans h40)
    · exact h40
  · have h01 : disk.edgeApex .b0 = disk.edgeApex .b1 :=
      disk.edgeApex_eq_next_of_unit
        (by simpa [FiveBoundaryIndex.next] using hunit .b1 (by decide))
    have h23 : disk.edgeApex .b2 = disk.edgeApex .b3 :=
      disk.edgeApex_eq_next_of_unit
        (by simpa [FiveBoundaryIndex.next] using hunit .b3 (by decide))
    have h34 : disk.edgeApex .b3 = disk.edgeApex .b4 :=
      disk.edgeApex_eq_next_of_unit
        (by simpa [FiveBoundaryIndex.next] using hunit .b4 (by decide))
    have h40 : disk.edgeApex .b4 = disk.edgeApex .b0 :=
      disk.edgeApex_eq_next_of_unit
        (by simpa [FiveBoundaryIndex.next] using hunit .b0 (by decide))
    intro i
    cases i
    · rfl
    · exact h01.symm
    · exact ((h23.trans h34).trans h40)
    · exact (h34.trans h40)
    · exact h40
  · have h01 : disk.edgeApex .b0 = disk.edgeApex .b1 :=
      disk.edgeApex_eq_next_of_unit
        (by simpa [FiveBoundaryIndex.next] using hunit .b1 (by decide))
    have h12 : disk.edgeApex .b1 = disk.edgeApex .b2 :=
      disk.edgeApex_eq_next_of_unit
        (by simpa [FiveBoundaryIndex.next] using hunit .b2 (by decide))
    have h34 : disk.edgeApex .b3 = disk.edgeApex .b4 :=
      disk.edgeApex_eq_next_of_unit
        (by simpa [FiveBoundaryIndex.next] using hunit .b4 (by decide))
    have h40 : disk.edgeApex .b4 = disk.edgeApex .b0 :=
      disk.edgeApex_eq_next_of_unit
        (by simpa [FiveBoundaryIndex.next] using hunit .b0 (by decide))
    intro i
    cases i
    · rfl
    · exact h01.symm
    · exact (h01.trans h12).symm
    · exact (h34.trans h40)
    · exact h40
  · have h01 : disk.edgeApex .b0 = disk.edgeApex .b1 :=
      disk.edgeApex_eq_next_of_unit
        (by simpa [FiveBoundaryIndex.next] using hunit .b1 (by decide))
    have h12 : disk.edgeApex .b1 = disk.edgeApex .b2 :=
      disk.edgeApex_eq_next_of_unit
        (by simpa [FiveBoundaryIndex.next] using hunit .b2 (by decide))
    have h23 : disk.edgeApex .b2 = disk.edgeApex .b3 :=
      disk.edgeApex_eq_next_of_unit
        (by simpa [FiveBoundaryIndex.next] using hunit .b3 (by decide))
    have h40 : disk.edgeApex .b4 = disk.edgeApex .b0 :=
      disk.edgeApex_eq_next_of_unit
        (by simpa [FiveBoundaryIndex.next] using hunit .b0 (by decide))
    intro i
    cases i
    · rfl
    · exact h01.symm
    · exact (h01.trans h12).symm
    · exact ((h01.trans h12).trans h23).symm
    · exact h40

/-- The local disk facts plus the charge count force one interior apex adjacent to all five
boundary vertices. -/
theorem exists_common_boundary_apex
    (disk : FiveCycleDiskTriangulationLocalData T profile) :
    ∃ x : W, disk.interior x ∧
      ∀ i : FiveBoundaryIndex, T.Adj (disk.boundary i) x := by
  refine ⟨disk.edgeApex .b0, disk.edgeApex_interior .b0, ?_⟩
  intro i
  have hEq := disk.edgeApex_eq_edgeApex_b0 i
  simpa [hEq] using disk.edgeApex_adj_left i

end FiveCycleDiskTriangulationLocalData

/-- Bundled local Lemma 5.3 disk data: Euler charge data plus the local triangulation facts
interpreted against the boundary-charge profile produced by that Euler count. -/
structure FiveCycleDiskChargeLocalData (T : SimpleGraph W) where
  chargeData : FiveCycleDiskEulerChargeData
  localData : FiveCycleDiskTriangulationLocalData T chargeData.toFiveBoundaryChargeProfile

namespace FiveCycleDiskChargeLocalData

variable {T : SimpleGraph W}

/-- The bundled disk data exposes the three consecutive unit boundary charges from the Euler
count. -/
theorem exists_three_consecutive_charges_eq_one
    (data : FiveCycleDiskChargeLocalData T) :
    ∃ i : FiveBoundaryIndex,
      data.chargeData.toFiveBoundaryChargeProfile.charge i = 1 ∧
        data.chargeData.toFiveBoundaryChargeProfile.charge (FiveBoundaryIndex.next i) = 1 ∧
          data.chargeData.toFiveBoundaryChargeProfile.charge
            (FiveBoundaryIndex.next (FiveBoundaryIndex.next i)) = 1 :=
  data.chargeData.exists_three_consecutive_charges_eq_one

/-- The bundled disk data forces all boundary-edge triangle apices to coincide. -/
theorem edgeApex_eq_edgeApex_b0
    (data : FiveCycleDiskChargeLocalData T) :
    ∀ i : FiveBoundaryIndex, data.localData.edgeApex i = data.localData.edgeApex .b0 :=
  data.localData.edgeApex_eq_edgeApex_b0

/-- The bundled disk data forces one interior apex adjacent to all five boundary vertices. -/
theorem exists_common_boundary_apex
    (data : FiveCycleDiskChargeLocalData T) :
    ∃ x : W, data.localData.interior x ∧
      ∀ i : FiveBoundaryIndex, T.Adj (data.localData.boundary i) x :=
  data.localData.exists_common_boundary_apex

end FiveCycleDiskChargeLocalData

/-- The remaining translation surface in Lemma 5.3: from the charged one-apex disk on the dual
side, construct the primal CAP5 pinch whose cut is the separating cycle's translated primal cut. -/
structure FiveCycleDiskPrimalCAP5TranslationData
    {dual : PlaneCubicDualData G T} (cycle : SeparatingDualCycleData dual 5) where
  diskData : FiveCycleDiskChargeLocalData T
  pinch : CAP5Pinch G
  same_cut : pinch.edgeCut = cycle.primalCut

namespace FiveCycleDiskPrimalCAP5TranslationData

variable {dual : PlaneCubicDualData G T}
variable {cycle : SeparatingDualCycleData dual 5}

/-- The translation package retains the one-apex conclusion on the dual disk side. -/
theorem exists_common_boundary_apex
    (translation : FiveCycleDiskPrimalCAP5TranslationData cycle) :
    ∃ x : W, translation.diskData.localData.interior x ∧
      ∀ i : FiveBoundaryIndex, T.Adj (translation.diskData.localData.boundary i) x :=
  translation.diskData.exists_common_boundary_apex

/-- A completed disk-to-primal translation is exactly tightness for the separating dual 5-cycle. -/
def toTightSeparatingDualFiveCycle
    (translation : FiveCycleDiskPrimalCAP5TranslationData cycle) :
    TightSeparatingDualFiveCycle cycle where
  pinch := translation.pinch
  same_cut := translation.same_cut

end FiveCycleDiskPrimalCAP5TranslationData

/-- Lemma 5.3 as the exact remaining disk-triangulation obligation: in normal form, every
separating dual 5-cycle is tight, i.e. yields CAP5 pinch data on the primal side. -/
def Lemma53DiskTriangulationTightnessObligation
    (normal : MinimalCounterexampleNormalForm G T) : Prop :=
  ∀ cycle : SeparatingDualCycleData normal.duality 5,
    Nonempty (TightSeparatingDualFiveCycle cycle)

/-- Named Lemma 5.3 infrastructure obligation: construct the charged disk data and its primal
CAP5 translation for every separating dual 5-cycle. -/
def Lemma53DiskToPrimalCAP5TranslationObligation
    (normal : MinimalCounterexampleNormalForm G T) : Prop :=
  ∀ cycle : SeparatingDualCycleData normal.duality 5,
    Nonempty (FiveCycleDiskPrimalCAP5TranslationData cycle)

/-- Disk-to-primal translation data discharge the tightness formulation of Lemma 5.3. -/
theorem lemma53_tightnessObligation_of_diskToPrimalCAP5Translations
    {normal : MinimalCounterexampleNormalForm G T}
    (h : Lemma53DiskToPrimalCAP5TranslationObligation normal) :
    Lemma53DiskTriangulationTightnessObligation normal := by
  intro cycle
  rcases h cycle with ⟨translation⟩
  exact ⟨translation.toTightSeparatingDualFiveCycle⟩

/-- Lemma 5.3 stated in the graph-facing form consumed downstream: every separating dual
5-cycle in normal form yields a CAP5 pinch on the primal side with the same primal cut. -/
def Lemma53SeparatingDualFiveCycleCAP5PinchObligation
    (normal : MinimalCounterexampleNormalForm G T) : Prop :=
  ∀ cycle : SeparatingDualCycleData normal.duality 5,
    ∃ pinch : CAP5Pinch G, pinch.edgeCut = cycle.primalCut

/-- A charge-count certificate for the disk bounded by a separating dual 5-cycle.  The arithmetic
and Jordan side of Lemma 5.3 should construct this certificate; its payload is the tight CAP5
pinch conclusion needed by graph-side consumers. -/
structure DiskTriangulationFiveCycleChargeCertificate
    {normal : MinimalCounterexampleNormalForm G T}
    (cycle : SeparatingDualCycleData normal.duality 5) : Prop where
  tight : Nonempty (TightSeparatingDualFiveCycle cycle)

/-- Charge certificates for every separating dual 5-cycle imply the Lemma 5.3 tightness
obligation. -/
theorem lemma53_tightnessObligation_of_chargeCertificates
    {normal : MinimalCounterexampleNormalForm G T}
    (h :
      ∀ cycle : SeparatingDualCycleData normal.duality 5,
        DiskTriangulationFiveCycleChargeCertificate cycle) :
    Lemma53DiskTriangulationTightnessObligation normal := by
  intro cycle
  exact (h cycle).tight

/-- Conditional Lemma 5.3 endpoint: tightness data exposes the graph-facing CAP5 pinch. -/
theorem lemma53_cap5Pinch_of_tightnessObligation
    {normal : MinimalCounterexampleNormalForm G T}
    (h : Lemma53DiskTriangulationTightnessObligation normal)
    (cycle : SeparatingDualCycleData normal.duality 5) :
    ∃ pinch : CAP5Pinch G, pinch.edgeCut = cycle.primalCut := by
  rcases h cycle with ⟨tight⟩
  exact ⟨tight.pinch, tight.same_cut⟩

/-- The tight-cycle formulation of Lemma 5.3 implies the graph-facing CAP5-pinch obligation. -/
theorem lemma53_CAP5PinchObligation_of_tightnessObligation
    {normal : MinimalCounterexampleNormalForm G T}
    (h : Lemma53DiskTriangulationTightnessObligation normal) :
    Lemma53SeparatingDualFiveCycleCAP5PinchObligation normal := by
  intro cycle
  exact lemma53_cap5Pinch_of_tightnessObligation h cycle

end CAP5Tightness

section EdgeColoringGlue

variable [DecidableEq V]
variable {β : Type*} {G : SimpleGraph V}

/-- Recolor an edge-coloring through an injective color map.  Injectivity preserves properness on
the line graph. -/
def edgeColoringMapOfInjective
    (C : G.EdgeColoring α) (σ : α → β) (hσ : Function.Injective σ) :
    G.EdgeColoring β :=
  SimpleGraph.Coloring.mk (fun e => σ (C e)) (by
    intro e₁ e₂ hAdj hsame
    exact C.valid hAdj (hσ hsame))

@[simp]
theorem edgeColoringMapOfInjective_apply
    (C : G.EdgeColoring α) (σ : α → β) (hσ : Function.Injective σ)
    (e : G.edgeSet) :
    edgeColoringMapOfInjective C σ hσ e = σ (C e) :=
  rfl

/-- A color equivalence fixing zero preserves nonzero colors. -/
theorem colorEquiv_apply_ne_zero_of_map_zero
    (σ : Color ≃ Color) (hzero : σ 0 = 0) {c : Color} (hc : c ≠ 0) :
    σ c ≠ 0 := by
  intro hσc
  apply hc
  exact σ.injective (by simpa [hzero] using hσc)

/-- Relabeling a Tait edge-coloring by an injective nonzero-preserving map gives another Tait
edge-coloring. -/
theorem isTaitEdgeColoring_edgeColoringMapOfInjective
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (σ : Color → Color) (hσ : Function.Injective σ)
    (hσ_nonzero : ∀ {c : Color}, c ≠ 0 → σ c ≠ 0) :
    IsTaitEdgeColoring G (edgeColoringMapOfInjective C σ hσ) := by
  intro e
  exact hσ_nonzero (hC e)

/-- Relabeling a Tait edge-coloring by a color equivalence fixing zero gives another Tait
edge-coloring. -/
theorem isTaitEdgeColoring_edgeColoringMapEquiv_of_map_zero
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (σ : Color ≃ Color) (hzero : σ 0 = 0) :
    IsTaitEdgeColoring G (edgeColoringMapOfInjective C σ σ.injective) :=
  isTaitEdgeColoring_edgeColoringMapOfInjective C hC σ σ.injective
    (fun hc => colorEquiv_apply_ne_zero_of_map_zero σ hzero hc)

/-- Glue two edge colorings by taking the inside coloring on one edge-side predicate and the
outside coloring on the complement.  This is the edge-coloring analogue of the vertex-coloring
glue helper below. -/
noncomputable def sideGlueEdgeColor
    (edgeSide : G.edgeSet → Prop) (inside outside : G.EdgeColoring α) :
    G.edgeSet → α := by
  classical
  exact fun e => if edgeSide e then inside e else outside e

@[simp]
theorem sideGlueEdgeColor_of_side
    (edgeSide : G.edgeSet → Prop) (inside outside : G.EdgeColoring α)
    {e : G.edgeSet} (he : edgeSide e) :
    sideGlueEdgeColor edgeSide inside outside e = inside e := by
  simp [sideGlueEdgeColor, he]

@[simp]
theorem sideGlueEdgeColor_of_not_side
    (edgeSide : G.edgeSet → Prop) (inside outside : G.EdgeColoring α)
    {e : G.edgeSet} (he : ¬ edgeSide e) :
    sideGlueEdgeColor edgeSide inside outside e = outside e := by
  simp [sideGlueEdgeColor, he]

/-- Compatibility condition saying the edge-side glued color function is proper on the line
graph. -/
def SideGlueEdgeCompatible
    (G : SimpleGraph V) (edgeSide : G.edgeSet → Prop)
    (inside outside : G.EdgeColoring α) : Prop :=
  ∀ {e f : G.edgeSet}, G.lineGraph.Adj e f →
    sideGlueEdgeColor edgeSide inside outside e ≠
      sideGlueEdgeColor edgeSide inside outside f

/-- Build an edge coloring from edge-side glue compatibility. -/
noncomputable def sideGlueEdgeColoring
    (edgeSide : G.edgeSet → Prop) (inside outside : G.EdgeColoring α)
    (hcompat : SideGlueEdgeCompatible G edgeSide inside outside) :
    G.EdgeColoring α :=
  SimpleGraph.Coloring.mk (sideGlueEdgeColor edgeSide inside outside) hcompat

/-- If every line-graph adjacency preserves the selected edge side, two edge colorings glue
without mixed boundary checks. -/
theorem sideGlueEdgeCompatible_of_side_preserving_adjacencies
    (edgeSide : G.edgeSet → Prop) (inside outside : G.EdgeColoring α)
    (hpreserve : ∀ {e f : G.edgeSet}, G.lineGraph.Adj e f → (edgeSide e ↔ edgeSide f)) :
    SideGlueEdgeCompatible G edgeSide inside outside := by
  classical
  intro e f hef
  by_cases he : edgeSide e
  · have hf : edgeSide f := (hpreserve hef).1 he
    simpa [sideGlueEdgeColor, he, hf] using inside.valid hef
  · have hf : ¬ edgeSide f := by
      intro hf
      exact he ((hpreserve hef).2 hf)
    simpa [sideGlueEdgeColor, he, hf] using outside.valid hef

/-- Cross-adjacency compatibility for edge-coloring glue.  Properness inside each side is already
provided by the two edge colorings; only adjacent edge pairs on opposite sides need mixed checks. -/
def SideGlueEdgeCrossCompatible
    (G : SimpleGraph V) (edgeSide : G.edgeSet → Prop)
    (inside outside : G.EdgeColoring α) : Prop :=
  ∀ {e f : G.edgeSet}, G.lineGraph.Adj e f →
    (edgeSide e → ¬ edgeSide f → inside e ≠ outside f) ∧
      (¬ edgeSide e → edgeSide f → outside e ≠ inside f)

/-- Mixed checks on crossing line-graph adjacencies are sufficient for edge-coloring glue. -/
theorem sideGlueEdgeCompatible_of_cross_compatible
    (edgeSide : G.edgeSet → Prop) (inside outside : G.EdgeColoring α)
    (hcross : SideGlueEdgeCrossCompatible G edgeSide inside outside) :
    SideGlueEdgeCompatible G edgeSide inside outside := by
  classical
  intro e f hef
  by_cases he : edgeSide e <;> by_cases hf : edgeSide f
  · simpa [sideGlueEdgeColor, he, hf] using inside.valid hef
  · simpa [sideGlueEdgeColor, he, hf] using (hcross hef).1 he hf
  · simpa [sideGlueEdgeColor, he, hf] using (hcross hef).2 he hf
  · simpa [sideGlueEdgeColor, he, hf] using outside.valid hef

/-- Gluing two Tait edge colorings along a compatible edge-side split remains Tait. -/
theorem isTaitEdgeColoring_sideGlueEdgeColoring
    (edgeSide : G.edgeSet → Prop) (inside outside : G.EdgeColoring Color)
    (hinside : IsTaitEdgeColoring G inside) (houtside : IsTaitEdgeColoring G outside)
    (hcompat : SideGlueEdgeCompatible G edgeSide inside outside) :
    IsTaitEdgeColoring G (sideGlueEdgeColoring edgeSide inside outside hcompat) := by
  intro e
  change sideGlueEdgeColor edgeSide inside outside e ≠ 0
  by_cases he : edgeSide e
  · simpa [sideGlueEdgeColor, he] using hinside e
  · simpa [sideGlueEdgeColor, he] using houtside e

/-- Relabel one side of a separator and glue the two Tait edge colorings.  This is the reusable
coloring endpoint needed by Birkhoff cut-and-paste surgeries. -/
theorem taitEdgeColorable_of_relabel_sideGlueEdgeCompatible
    [Fintype V]
    (edgeSide : G.edgeSet → Prop)
    (inside outside : G.EdgeColoring Color)
    (hinside : IsTaitEdgeColoring G inside) (houtside : IsTaitEdgeColoring G outside)
    (σ : Color → Color) (hσ : Function.Injective σ)
    (hσ_nonzero : ∀ {c : Color}, c ≠ 0 → σ c ≠ 0)
    (hcompat :
      SideGlueEdgeCompatible G edgeSide inside (edgeColoringMapOfInjective outside σ hσ)) :
    TaitEdgeColorable G := by
  refine ⟨sideGlueEdgeColoring edgeSide inside (edgeColoringMapOfInjective outside σ hσ)
    hcompat, ?_⟩
  exact isTaitEdgeColoring_sideGlueEdgeColoring edgeSide inside
    (edgeColoringMapOfInjective outside σ hσ) hinside
    (isTaitEdgeColoring_edgeColoringMapOfInjective outside houtside σ hσ hσ_nonzero)
    hcompat

end EdgeColoringGlue

section ColoringGlue

variable [DecidableEq V]
variable {G : SimpleGraph V}

/-- Glue two vertex colorings by taking the inside coloring on one side predicate and the
outside coloring on the complement. -/
noncomputable def sideGlueVertexColor
    (side : V → Prop) (inside outside : G.Coloring α) : V → α :=
  by
    classical
    exact fun v => if side v then inside v else outside v

@[simp]
theorem sideGlueVertexColor_of_side
    (side : V → Prop) (inside outside : G.Coloring α)
    {v : V} (hv : side v) :
    sideGlueVertexColor side inside outside v = inside v := by
  simp [sideGlueVertexColor, hv]

@[simp]
theorem sideGlueVertexColor_of_not_side
    (side : V → Prop) (inside outside : G.Coloring α)
    {v : V} (hv : ¬ side v) :
    sideGlueVertexColor side inside outside v = outside v := by
  simp [sideGlueVertexColor, hv]

/-- The direct compatibility condition saying that the side-glued function is a proper coloring. -/
def SideGlueCompatible
    (G : SimpleGraph V) (side : V → Prop) (inside outside : G.Coloring α) : Prop :=
  ∀ {u v : V}, G.Adj u v →
    sideGlueVertexColor side inside outside u ≠ sideGlueVertexColor side inside outside v

/-- Build a graph coloring from the side-glue compatibility condition. -/
noncomputable def sideGlueVertexColoring
    (side : V → Prop) (inside outside : G.Coloring α)
    (hcompat : SideGlueCompatible G side inside outside) :
    G.Coloring α :=
  SimpleGraph.Coloring.mk (sideGlueVertexColor side inside outside) hcompat

/-- If every graph edge preserves the side predicate, two full graph colorings can be glued
without any extra separator compatibility condition. -/
theorem sideGlueCompatible_of_side_preserving_edges
    (side : V → Prop) (inside outside : G.Coloring α)
    (hpreserve : ∀ {u v : V}, G.Adj u v → (side u ↔ side v)) :
    SideGlueCompatible G side inside outside := by
  classical
  intro u v huv
  by_cases hu : side u
  · have hv : side v := (hpreserve huv).1 hu
    simpa [sideGlueVertexColor, hu, hv] using inside.valid huv
  · have hv : ¬ side v := by
      intro hv
      exact hu ((hpreserve huv).2 hv)
    simpa [sideGlueVertexColor, hu, hv] using outside.valid huv

/-- Cross-edge compatibility for side gluing.  Internal edges are handled by the two supplied
colorings; only edges whose endpoints lie on opposite sides need mixed-color checks. -/
def SideGlueCrossCompatible
    (G : SimpleGraph V) (side : V → Prop) (inside outside : G.Coloring α) : Prop :=
  ∀ {u v : V}, G.Adj u v →
    (side u → ¬ side v → inside u ≠ outside v) ∧
      (¬ side u → side v → outside u ≠ inside v)

/-- Mixed checks on crossing edges are sufficient for the side-glued coloring to be proper. -/
theorem sideGlueCompatible_of_cross_compatible
    (side : V → Prop) (inside outside : G.Coloring α)
    (hcross : SideGlueCrossCompatible G side inside outside) :
    SideGlueCompatible G side inside outside := by
  classical
  intro u v huv
  by_cases hu : side u <;> by_cases hv : side v
  · simpa [sideGlueVertexColor, hu, hv] using inside.valid huv
  · simpa [sideGlueVertexColor, hu, hv] using (hcross huv).1 hu hv
  · simpa [sideGlueVertexColor, hu, hv] using (hcross huv).2 hu hv
  · simpa [sideGlueVertexColor, hu, hv] using outside.valid huv

end ColoringGlue

end Mettapedia.GraphTheory.FourColor
