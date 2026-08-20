import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutComponentProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutLayerSeparation
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationCutDartDecomposition
import Mettapedia.GraphTheory.FourColor.GoertzelV24SpliceUnification

/-!
# Closed splice specialization from paired annular crosscuts

The source splice first operates on open tangles.  This file records a useful
closed-graph specialization: if paired source interfaces can be closed without
identifying a seam edge's endpoints, the retained-side rotation-system splice
is available.  The retained side, every outward boundary dart, its full
coverage, and the two-cut partition are constructed from the paired dual loop;
none is an ambient assumption.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteEdgeDeletion
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SpliceUnification
open GoertzelV24SpliceUnification.OrderedCutSidesData
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- The ordered image of a simple dual crosscut is exactly its finite primal
crossing support.  This keeps the source's transversal order while exposing
the ordinary `Finset` needed by the splice implementation. -/
theorem orderedCut_crossingEdge_eq_crossingEdges
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (crosscut : SimpleDualCrosscut (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))) :
    orderedCut (crosscut.crossingEdge hunique) = crosscut.crossingEdges hunique := by
  ext edge
  constructor
  · intro hmem
    change edge ∈ Finset.univ.image (crosscut.crossingEdge hunique) at hmem
    rcases Finset.mem_image.1 hmem with ⟨step, _, hstep⟩
    exact (crosscut.mem_crossingEdges_iff hunique edge).2 ⟨step, hstep⟩
  · intro hmem
    rcases (crosscut.mem_crossingEdges_iff hunique edge).1 hmem with
      ⟨step, hstep⟩
    change edge ∈ Finset.univ.image (crosscut.crossingEdge hunique)
    exact Finset.mem_image.2 ⟨step, Finset.mem_univ _, hstep⟩

/-- An exposed retained dart is an actual crossing edge of its finite vertex
side.  This is the small rotation-system bridge needed to prove that the two
source crosscuts cover every boundary port of the selected component. -/
theorem boundaryDart_edge_mem_vertexSetCrossingEdges
    (RS : RotationSystem V G.edgeSet) (side : Finset V)
    (boundary : BoundaryDart RS (fun vertex => vertex ∈ side)) :
    RS.edgeOf boundary.1.1 ∈ vertexSetCrossingEdges RS side := by
  rw [mem_vertexSetCrossingEdges_iff]
  refine ⟨RS.vertOf boundary.1.1, ?_, boundary.1.2,
    RS.vertOf (RS.alpha boundary.1.1), ?_, boundary.2⟩
  · rw [RS.mem_endpoints_iff]
    exact ⟨boundary.1.1, by simp, rfl⟩
  · rw [RS.mem_endpoints_iff]
    refine ⟨RS.alpha boundary.1.1, ?_, rfl⟩
    rw [RS.mem_dartsOn]
    exact RS.edge_alpha boundary.1.1

/-- A vertex distinct from some other vertex in a connected graph carries a
literal graph dart.  This is the local root datum needed to open one side of a
source splice; global cubicity is much stronger than this conclusion. -/
theorem exists_dartAt_of_connected_of_ne
    (data : Data G) (hconnected : G.Connected) {vertex other : V}
    (hne : vertex ≠ other) :
    ∃ dart : data.toRotationSystem.D,
      data.toRotationSystem.vertOf dart = vertex := by
  rcases (hconnected vertex other).nonempty_neighborSet_left hne with
    ⟨neighbor, hadjacent⟩
  exact ⟨⟨(vertex, neighbor), hadjacent⟩, rfl⟩

/-- The complete, source-derived boundary data of the paired annular
transversals.  It intentionally records only geometry: the later semantic
profile layer must still prove its own preservation claims against this real
boundary rather than acquire them from this package. -/
structure SourceCrosscutBoundaryData
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique) where
  component : (G.deleteEdges
    (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent
  component_boundary : componentCrossingEdges (pair.primalCutEdges data)
    component = pair.primalCutEdges data
  outer_kept : data.toRotationSystem.vertOf data.toRotationSystem.outer ∈
    pair.componentSide component
  removed : V
  removed_not_kept : removed ∉ pair.componentSide component
  removedDart : data.toRotationSystem.D
  removedDart_vertOf : data.toRotationSystem.vertOf removedDart = removed
  leftCrosses : ∀ step, ∃ dart : data.toRotationSystem.D,
    data.toRotationSystem.edgeOf dart = pair.left.crossingEdge hunique step ∧
    data.toRotationSystem.vertOf dart ∈ pair.componentSide component ∧
    data.toRotationSystem.vertOf (data.toRotationSystem.alpha dart) ∉
      pair.componentSide component
  rightCrosses : ∀ step, ∃ dart : data.toRotationSystem.D,
    data.toRotationSystem.edgeOf dart = pair.right.crossingEdge hunique step ∧
    data.toRotationSystem.vertOf dart ∈ pair.componentSide component ∧
    data.toRotationSystem.vertOf (data.toRotationSystem.alpha dart) ∉
      pair.componentSide component
  leftInjective : Function.Injective (pair.left.crossingEdge hunique)
  rightInjective : Function.Injective (pair.right.crossingEdge hunique)
  cover : ∀ boundary : BoundaryDart data.toRotationSystem
      (fun vertex => vertex ∈ pair.componentSide component),
    data.toRotationSystem.edgeOf boundary.1.1 ∈
        orderedCut (pair.left.crossingEdge hunique) ∨
      data.toRotationSystem.edgeOf boundary.1.1 ∈
        orderedCut (pair.right.crossingEdge hunique)
  disjoint : Disjoint (orderedCut (pair.left.crossingEdge hunique))
    (orderedCut (pair.right.crossingEdge hunique))

/-- The paired simple source transversals construct all geometric boundary
fields required by the splice.  The proof selects the outer deletion
component, obtains every port orientation from its exact boundary, and then
uses the dual-loop decomposition to establish coverage and disjointness. -/
theorem exists_sourceCrosscutBoundaryData
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique) :
    Nonempty (SourceCrosscutBoundaryData data pair) := by
  rcases pair.exists_outer_primalCutComponent_exactBoundary_and_removed data
      htwoSided hdual hconnected hsphere with
    ⟨component, removed, houter, hremoved, hboundary⟩
  have hremovedNeOuter :
      removed ≠ data.toRotationSystem.vertOf data.toRotationSystem.outer := by
    intro heq
    apply hremoved
    simpa [heq] using houter
  let removedDart := Classical.choose
    (exists_dartAt_of_connected_of_ne data hconnected hremovedNeOuter)
  have hremovedDart : data.toRotationSystem.vertOf removedDart = removed :=
    Classical.choose_spec
      (exists_dartAt_of_connected_of_ne data hconnected hremovedNeOuter)
  exact ⟨{
    component := component
    component_boundary := hboundary
    outer_kept := (pair.mem_componentSide_iff component
      (data.toRotationSystem.vertOf data.toRotationSystem.outer)).2 houter
    removed := removed
    removed_not_kept := by
      intro hkept
      exact hremoved ((pair.mem_componentSide_iff component removed).1 hkept)
    removedDart := removedDart
    removedDart_vertOf := hremovedDart
    leftCrosses := by
      intro step
      apply pair.exists_oriented_componentSide_crossingDart data component hboundary
      rw [pair.primalCutEdges_eq_sourceCrossingSupport data]
      exact Finset.mem_union_left _
        ((pair.left.mem_crossingEdges_iff hunique _).2 ⟨step, rfl⟩)
    rightCrosses := by
      intro step
      apply pair.exists_oriented_componentSide_crossingDart data component hboundary
      rw [pair.primalCutEdges_eq_sourceCrossingSupport data]
      exact Finset.mem_union_right _
        ((pair.right.mem_crossingEdges_iff hunique _).2 ⟨step, rfl⟩)
    leftInjective := pair.left.crossingEdge_injective
      (orbitFace_incidence_le_two data.toRotationSystem) hunique
    rightInjective := pair.right.crossingEdge_injective
      (orbitFace_incidence_le_two data.toRotationSystem) hunique
    cover := by
      intro exposed
      have hcut : data.toRotationSystem.edgeOf exposed.1.1 ∈
          pair.primalCutEdges data := by
        rw [← pair.vertexSetCrossingEdges_componentSide_eq_primalCutEdges
          data component hboundary]
        exact boundaryDart_edge_mem_vertexSetCrossingEdges
          data.toRotationSystem (pair.componentSide component) exposed
      rw [pair.primalCutEdges_eq_sourceCrossingSupport data] at hcut
      rcases Finset.mem_union.1 hcut with hleft | hright
      · left
        rw [orderedCut_crossingEdge_eq_crossingEdges pair.left hunique]
        exact hleft
      · right
        rw [orderedCut_crossingEdge_eq_crossingEdges pair.right hunique]
        exact hright
    disjoint := by
      rw [orderedCut_crossingEdge_eq_crossingEdges pair.left hunique,
        orderedCut_crossingEdge_eq_crossingEdges pair.right hunique]
      exact pair.crossing_disjoint
    }⟩

/-- Construct the source splice boundary on a framed Euler carrier.  This
specialization removes the false global-cubic requirement from the old
closed-map wrapper, but deliberately retains two-sidedness and the paired
crosscuts as explicit inputs: those are the still-open L1/source-formation
geometry, not consequences of Euler counting. -/
theorem exists_sourceCrosscutBoundaryData_of_euler
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (heuler : (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace data.toRotationSystem) = 2)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique) :
    Nonempty (SourceCrosscutBoundaryData data pair) := by
  rcases pair.exists_outer_primalCutComponent_exactBoundary_and_removed_of_euler
      data htwoSided hdual hconnected heuler with
    ⟨component, removed, houter, hremoved, hboundary⟩
  have hremovedNeOuter :
      removed ≠ data.toRotationSystem.vertOf data.toRotationSystem.outer := by
    intro heq
    apply hremoved
    simpa [heq] using houter
  let removedDart := Classical.choose
    (exists_dartAt_of_connected_of_ne data hconnected hremovedNeOuter)
  have hremovedDart : data.toRotationSystem.vertOf removedDart = removed :=
    Classical.choose_spec
      (exists_dartAt_of_connected_of_ne data hconnected hremovedNeOuter)
  exact ⟨{
    component := component
    component_boundary := hboundary
    outer_kept := (pair.mem_componentSide_iff component
      (data.toRotationSystem.vertOf data.toRotationSystem.outer)).2 houter
    removed := removed
    removed_not_kept := by
      intro hkept
      exact hremoved ((pair.mem_componentSide_iff component removed).1 hkept)
    removedDart := removedDart
    removedDart_vertOf := hremovedDart
    leftCrosses := by
      intro step
      apply pair.exists_oriented_componentSide_crossingDart data component hboundary
      rw [pair.primalCutEdges_eq_sourceCrossingSupport data]
      exact Finset.mem_union_left _
        ((pair.left.mem_crossingEdges_iff hunique _).2 ⟨step, rfl⟩)
    rightCrosses := by
      intro step
      apply pair.exists_oriented_componentSide_crossingDart data component hboundary
      rw [pair.primalCutEdges_eq_sourceCrossingSupport data]
      exact Finset.mem_union_right _
        ((pair.right.mem_crossingEdges_iff hunique _).2 ⟨step, rfl⟩)
    leftInjective := pair.left.crossingEdge_injective
      (orbitFace_incidence_le_two data.toRotationSystem) hunique
    rightInjective := pair.right.crossingEdge_injective
      (orbitFace_incidence_le_two data.toRotationSystem) hunique
    cover := by
      intro exposed
      have hcut : data.toRotationSystem.edgeOf exposed.1.1 ∈
          pair.primalCutEdges data := by
        rw [← pair.vertexSetCrossingEdges_componentSide_eq_primalCutEdges
          data component hboundary]
        exact boundaryDart_edge_mem_vertexSetCrossingEdges
          data.toRotationSystem (pair.componentSide component) exposed
      rw [pair.primalCutEdges_eq_sourceCrossingSupport data] at hcut
      rcases Finset.mem_union.1 hcut with hleft | hright
      · left
        rw [orderedCut_crossingEdge_eq_crossingEdges pair.left hunique]
        exact hleft
      · right
        rw [orderedCut_crossingEdge_eq_crossingEdges pair.right hunique]
        exact hright
    disjoint := by
      rw [orderedCut_crossingEdge_eq_crossingEdges pair.left hunique,
        orderedCut_crossingEdge_eq_crossingEdges pair.right hunique]
      exact pair.crossing_disjoint
    }⟩

/-! ## Source order on the actual paired boundary -/

/-- The elementary finite equivalence that places the left interface before
the right interface.  It is kept local because the order is part of this
source-level boundary construction, not a global convention for arbitrary
finite types. -/
private def sourceCrosscutSumEquiv (leftLength rightLength : Nat) :
    Fin leftLength ⊕ Fin rightLength ≃ Fin (leftLength + rightLength) where
  toFun := Sum.elim (Fin.castAdd rightLength) (Fin.natAdd leftLength)
  invFun := fun index => Fin.addCases Sum.inl Sum.inr index
  left_inv := by
    rintro (left | right) <;> simp
  right_inv := by
    intro index
    refine Fin.addCases (fun left => ?_) (fun right => ?_) index <;> simp

/-- Read the two source transversals as one exact boundary-port carrier: the
left path occupies the first block of coordinates and the right path the
second.  Membership is proved against the computed deletion boundary, so this
does not choose a synthetic side or a canonical finite enumeration. -/
noncomputable def sourceCrosscutPort
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) :
    Fin pair.left.walk.length ⊕ Fin pair.right.walk.length →
      VertexSetCrossingEdge data.toRotationSystem
        (pair.componentSide boundary.component)
  | .inl step =>
      ⟨pair.left.crossingEdge hunique step, by
        rw [pair.vertexSetCrossingEdges_componentSide_eq_primalCutEdges
          data boundary.component boundary.component_boundary,
          pair.primalCutEdges_eq_sourceCrossingSupport data]
        exact Finset.mem_union_left _
          ((pair.left.mem_crossingEdges_iff hunique _).2 ⟨step, rfl⟩)⟩
  | .inr step =>
      ⟨pair.right.crossingEdge hunique step, by
        rw [pair.vertexSetCrossingEdges_componentSide_eq_primalCutEdges
          data boundary.component boundary.component_boundary,
          pair.primalCutEdges_eq_sourceCrossingSupport data]
        exact Finset.mem_union_right _
          ((pair.right.mem_crossingEdges_iff hunique _).2 ⟨step, rfl⟩)⟩

@[simp]
theorem sourceCrosscutPort_left
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (step : Fin pair.left.walk.length) :
    (pair.sourceCrosscutPort data boundary (Sum.inl step)).1 =
      pair.left.crossingEdge hunique step :=
  rfl

@[simp]
theorem sourceCrosscutPort_right
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (step : Fin pair.right.walk.length) :
    (pair.sourceCrosscutPort data boundary (Sum.inr step)).1 =
      pair.right.crossingEdge hunique step :=
  rfl

theorem sourceCrosscutPort_injective
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) :
    Function.Injective (pair.sourceCrosscutPort data boundary) := by
  intro first second heq
  cases first with
  | inl left =>
      cases second with
      | inl right =>
          have hedges : pair.left.crossingEdge hunique left =
              pair.left.crossingEdge hunique right :=
            congrArg Subtype.val heq
          have hsteps : left = right :=
            pair.left.crossingEdge_injective
              (orbitFace_incidence_le_two data.toRotationSystem) hunique hedges
          simp [hsteps]
      | inr right =>
          exfalso
          have hedges : pair.left.crossingEdge hunique left =
              pair.right.crossingEdge hunique right :=
            congrArg Subtype.val heq
          have hleft : pair.left.crossingEdge hunique left ∈
              pair.left.crossingEdges hunique :=
            (pair.left.mem_crossingEdges_iff hunique _).2 ⟨left, rfl⟩
          have hright : pair.left.crossingEdge hunique left ∈
              pair.right.crossingEdges hunique := by
            rw [hedges]
            exact (pair.right.mem_crossingEdges_iff hunique _).2 ⟨right, rfl⟩
          exact (Finset.disjoint_left.1 pair.crossing_disjoint hleft hright).elim
  | inr left =>
      cases second with
      | inl right =>
          exfalso
          have hedges : pair.right.crossingEdge hunique left =
              pair.left.crossingEdge hunique right :=
            congrArg Subtype.val heq
          have hright : pair.right.crossingEdge hunique left ∈
              pair.right.crossingEdges hunique :=
            (pair.right.mem_crossingEdges_iff hunique _).2 ⟨left, rfl⟩
          have hleft : pair.right.crossingEdge hunique left ∈
              pair.left.crossingEdges hunique := by
            rw [hedges]
            exact (pair.left.mem_crossingEdges_iff hunique _).2 ⟨right, rfl⟩
          exact (Finset.disjoint_left.1 pair.crossing_disjoint hleft hright).elim
      | inr right =>
          have hedges : pair.right.crossingEdge hunique left =
              pair.right.crossingEdge hunique right :=
            congrArg Subtype.val heq
          have hsteps : left = right :=
            pair.right.crossingEdge_injective
              (orbitFace_incidence_le_two data.toRotationSystem) hunique hedges
          simp [hsteps]

theorem sourceCrosscutPort_surjective
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) :
    Function.Surjective (pair.sourceCrosscutPort data boundary) := by
  intro crossing
  have hcut : crossing.1 ∈ pair.primalCutEdges data := by
    rw [← pair.vertexSetCrossingEdges_componentSide_eq_primalCutEdges
      data boundary.component boundary.component_boundary]
    exact crossing.2
  rw [pair.primalCutEdges_eq_sourceCrossingSupport data] at hcut
  rcases Finset.mem_union.1 hcut with hleft | hright
  · rcases (pair.left.mem_crossingEdges_iff hunique crossing.1).1 hleft with
      ⟨step, hstep⟩
    refine ⟨Sum.inl step, ?_⟩
    exact Subtype.ext hstep
  · rcases (pair.right.mem_crossingEdges_iff hunique crossing.1).1 hright with
      ⟨step, hstep⟩
    refine ⟨Sum.inr step, ?_⟩
    exact Subtype.ext hstep

/-- The source order is a genuine finite equivalence, rather than an opaque
enumeration: each port has one source transversal and one source step. -/
noncomputable def sourceCrosscutPortEquiv
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) :
    Fin pair.left.walk.length ⊕ Fin pair.right.walk.length ≃
      VertexSetCrossingEdge data.toRotationSystem
        (pair.componentSide boundary.component) :=
  Equiv.ofBijective (pair.sourceCrosscutPort data boundary)
    ⟨pair.sourceCrosscutPort_injective data boundary,
      pair.sourceCrosscutPort_surjective data boundary⟩

/-- The profile engine's coordinate carrier can therefore be chosen to follow
the actual two simple source transversals.  This is the needed bridge from a
paired layer boundary to finite profile data; it retains both interface orders
instead of falling back to a canonical `Fintype` enumeration. -/
noncomputable def sourceCrosscutBoundaryIndexing
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) :
    VertexSetCrossingIndexing data.toRotationSystem
      (pair.componentSide boundary.component) :=
  let hcard := pair.componentSide_crossingCard_eq_interfaceWidths data
    boundary.component boundary.component_boundary
  (finCongr hcard).trans
    ((sourceCrosscutSumEquiv pair.left.walk.length pair.right.walk.length).symm.trans
      (pair.sourceCrosscutPortEquiv data boundary))

/-- The first coordinate block of the source-ordered boundary profile is
definitionally the first simple transversal. -/
@[simp]
theorem sourceCrosscutBoundaryIndexing_left
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (step : Fin pair.left.walk.length) :
    vertexSetCrossingEdgeAtWithIndexing data.toRotationSystem
      (pair.componentSide boundary.component)
      (pair.sourceCrosscutBoundaryIndexing data boundary)
      (Fin.cast
        (pair.componentSide_crossingCard_eq_interfaceWidths data
          boundary.component boundary.component_boundary).symm
        (Fin.castAdd pair.right.walk.length step)) =
      pair.left.crossingEdge hunique step := by
  simp [sourceCrosscutBoundaryIndexing, sourceCrosscutSumEquiv,
    sourceCrosscutPortEquiv, sourceCrosscutPort,
    vertexSetCrossingEdgeAtWithIndexing]

/-- The second coordinate block of the source-ordered boundary profile is
definitionally the second simple transversal. -/
@[simp]
theorem sourceCrosscutBoundaryIndexing_right
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (step : Fin pair.right.walk.length) :
    vertexSetCrossingEdgeAtWithIndexing data.toRotationSystem
      (pair.componentSide boundary.component)
      (pair.sourceCrosscutBoundaryIndexing data boundary)
      (Fin.cast
        (pair.componentSide_crossingCard_eq_interfaceWidths data
          boundary.component boundary.component_boundary).symm
        (Fin.natAdd pair.left.walk.length step)) =
      pair.right.crossingEdge hunique step := by
  simp [sourceCrosscutBoundaryIndexing, sourceCrosscutSumEquiv,
    sourceCrosscutPortEquiv, sourceCrosscutPort,
    vertexSetCrossingEdgeAtWithIndexing]

/-- The complete finite profile carrier attached to the actual paired layer
boundary, in the source's left-then-right port order.  This is not a profile
for a chord or an arbitrary vertex predicate: it is computed from the
component separated by the two simple transversals. -/
noncomputable def sourceCrosscutBoundaryProfileData
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) :=
  vertexSetBoundaryGraphCutDataWithIndexing data.toRotationSystem
    (pair.componentSide boundary.component)
    (pair.sourceCrosscutBoundaryIndexing data boundary)

theorem sourceCrosscutBoundaryProfileData_portsInRegion
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) :
    (pair.sourceCrosscutBoundaryProfileData data boundary).PortsInRegion :=
  vertexSetBoundaryGraphCutDataWithIndexing_portsInRegion
    data.toRotationSystem (pair.componentSide boundary.component)
    (pair.sourceCrosscutBoundaryIndexing data boundary)

theorem sourceCrosscutBoundaryProfileData_fragmentsOnFaceInRegion
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) :
    (pair.sourceCrosscutBoundaryProfileData data boundary).FragmentsOnFaceInRegion :=
  vertexSetBoundaryGraphCutDataWithIndexing_fragmentsOnFaceInRegion
    data.toRotationSystem (pair.componentSide boundary.component)
    (pair.sourceCrosscutBoundaryIndexing data boundary)

/-- The profile's first block reads the literal colors of the left source
transversal. -/
theorem sourceCrosscutBoundaryProfile_left_edgeColor
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (hcoloring : data.toRotationSystem.IsTaitEdgeColoring coloring)
    (step : Fin pair.left.walk.length) :
    (((pair.sourceCrosscutBoundaryProfileData data boundary).profile
      coloring hcoloring).edgeColor
      (Fin.cast
        (pair.componentSide_crossingCard_eq_interfaceWidths data
          boundary.component boundary.component_boundary).symm
        (Fin.castAdd pair.right.walk.length step))).toColor =
      coloring (pair.left.crossingEdge hunique step) := by
  rw [GraphCorridorCutData.profile_edgeColor_toColor]
  change coloring
      (vertexSetCrossingEdgeAtWithIndexing data.toRotationSystem
        (pair.componentSide boundary.component)
        (pair.sourceCrosscutBoundaryIndexing data boundary)
        (Fin.cast
          (pair.componentSide_crossingCard_eq_interfaceWidths data
            boundary.component boundary.component_boundary).symm
          (Fin.castAdd pair.right.walk.length step))) =
      coloring (pair.left.crossingEdge hunique step)
  exact congrArg coloring
    (pair.sourceCrosscutBoundaryIndexing_left data boundary step)

/-- The profile's second block reads the literal colors of the right source
transversal in its aligned rung order. -/
theorem sourceCrosscutBoundaryProfile_right_edgeColor
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (hcoloring : data.toRotationSystem.IsTaitEdgeColoring coloring)
    (step : Fin pair.right.walk.length) :
    (((pair.sourceCrosscutBoundaryProfileData data boundary).profile
      coloring hcoloring).edgeColor
      (Fin.cast
        (pair.componentSide_crossingCard_eq_interfaceWidths data
          boundary.component boundary.component_boundary).symm
        (Fin.natAdd pair.left.walk.length step))).toColor =
      coloring (pair.right.crossingEdge hunique step) := by
  rw [GraphCorridorCutData.profile_edgeColor_toColor]
  change coloring
      (vertexSetCrossingEdgeAtWithIndexing data.toRotationSystem
        (pair.componentSide boundary.component)
        (pair.sourceCrosscutBoundaryIndexing data boundary)
        (Fin.cast
          (pair.componentSide_crossingCard_eq_interfaceWidths data
            boundary.component boundary.component_boundary).symm
          (Fin.natAdd pair.left.walk.length step))) =
      coloring (pair.right.crossingEdge hunique step)
  exact congrArg coloring
    (pair.sourceCrosscutBoundaryIndexing_right data boundary step)

/-! ## The source boundary as concrete splice input -/

/-- The number of open face fragments seen by the actual component-side
boundary.  Both source interfaces use this one computed carrier; only their
crossing-port order differs. -/
abbrev sourceCrosscutFaceFragmentCount
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) : Nat :=
  Fintype.card (BoundaryRegionalFragment data.toRotationSystem
    (vertexSetCrossingEdges data.toRotationSystem
      (pair.componentSide boundary.component))
    (vertexSetRegionEdges data.toRotationSystem
      (pair.componentSide boundary.component)))

/-- Raw graph-derived profile coordinates for an actual source interface.
This is deliberately a construction rather than a record of promised fields:
the region and every face fragment are the component-side objects computed
from the paired simple transversals. -/
noncomputable def sourceCrosscutCutData
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    {width : Nat} (crossingEdge : Fin width → G.edgeSet) :
    GraphCorridorCutData data.toRotationSystem width 0
      (pair.sourceCrosscutFaceFragmentCount data boundary) where
  regionEdges := vertexSetRegionEdges data.toRotationSystem
    (pair.componentSide boundary.component)
  crossingEdge := crossingEdge
  terminalEdge := fun terminal => Fin.elim0 terminal
  fragmentFace := fun fragment =>
    (boundaryRegionalFragmentAt data.toRotationSystem
      (vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component))
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)) fragment).1.1
  fragmentEdges := fun fragment =>
    boundaryRegionalFragmentEdges data.toRotationSystem
      (vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component))
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component))
      (boundaryRegionalFragmentAt data.toRotationSystem
        (vertexSetCrossingEdges data.toRotationSystem
          (pair.componentSide boundary.component))
        (vertexSetRegionEdges data.toRotationSystem
          (pair.componentSide boundary.component)) fragment)

/-- The left transverse interface in its source order. -/
noncomputable def sourceCrosscutLeftCutData
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) :
    GraphCorridorCutData data.toRotationSystem pair.left.walk.length 0
      (pair.sourceCrosscutFaceFragmentCount data boundary) :=
  pair.sourceCrosscutCutData data boundary (pair.left.crossingEdge hunique)

/-- The right transverse interface, reindexed by the aligned left-hand
coordinate.  The cast is the source's rung-position correspondence, not an
arbitrary finite permutation. -/
noncomputable def sourceCrosscutRightCutData
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) :
    GraphCorridorCutData data.toRotationSystem pair.left.walk.length 0
      (pair.sourceCrosscutFaceFragmentCount data boundary) :=
  pair.sourceCrosscutCutData data boundary
    (fun step => pair.right.crossingEdge hunique (Fin.cast pair.length_eq step))

/-- The reindexed right list has the same underlying cut support as the
source right transversal.  This is the finite change-of-coordinate used when
the two equal-width interfaces are placed in one splice coordinate. -/
theorem orderedCut_sourceCrosscutRight_eq
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique) :
    orderedCut (fun step : Fin pair.left.walk.length =>
      pair.right.crossingEdge hunique (Fin.cast pair.length_eq step)) =
      orderedCut (pair.right.crossingEdge hunique) := by
  ext edge
  simp only [orderedCut, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨step, hstep⟩
    exact ⟨Fin.cast pair.length_eq step, hstep⟩
  · rintro ⟨step, hstep⟩
    refine ⟨Fin.cast pair.length_eq.symm step, ?_⟩
    simpa using hstep

/-- Every port of either source interface is genuinely in the computed
component-side region.  The proof is by the exact deletion-boundary equality,
not by a free `PortsInRegion` assumption. -/
theorem sourceCrosscutLeftCutData_portsInRegion
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) :
    (pair.sourceCrosscutLeftCutData data boundary).PortsInRegion := by
  intro port
  rcases port with crossing | terminal
  · apply vertexSetCrossingEdges_subset_regionEdges data.toRotationSystem
    rw [pair.vertexSetCrossingEdges_componentSide_eq_primalCutEdges data
      boundary.component boundary.component_boundary,
      pair.primalCutEdges_eq_sourceCrossingSupport data]
    exact Finset.mem_union_left _
      ((pair.left.mem_crossingEdges_iff hunique _).2 ⟨crossing, rfl⟩)
  · exact Fin.elim0 terminal

theorem sourceCrosscutRightCutData_portsInRegion
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) :
    (pair.sourceCrosscutRightCutData data boundary).PortsInRegion := by
  intro port
  rcases port with crossing | terminal
  · apply vertexSetCrossingEdges_subset_regionEdges data.toRotationSystem
    rw [pair.vertexSetCrossingEdges_componentSide_eq_primalCutEdges data
      boundary.component boundary.component_boundary,
      pair.primalCutEdges_eq_sourceCrossingSupport data]
    exact Finset.mem_union_right _
      ((pair.right.mem_crossingEdges_iff hunique _).2
        ⟨Fin.cast pair.length_eq crossing, rfl⟩)
  · exact Fin.elim0 terminal

/-- The face fragments of either source-interface data are exactly the
computed open fragments of the component-side region. -/
theorem sourceCrosscutCutData_fragmentsOnFaceInRegion
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    {width : Nat} (crossingEdge : Fin width → G.edgeSet) :
    (pair.sourceCrosscutCutData data boundary crossingEdge).FragmentsOnFaceInRegion := by
  intro fragment
  exact boundaryRegionalFragmentEdges_subset_boundary_inter_region
    data.toRotationSystem
    (vertexSetCrossingEdges data.toRotationSystem
      (pair.componentSide boundary.component))
    (vertexSetRegionEdges data.toRotationSystem
      (pair.componentSide boundary.component))
    (boundaryRegionalFragmentAt data.toRotationSystem
      (vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component))
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)) fragment)

/-- The paired simple transversals now populate the concrete splice input
directly.  This is the missing source-to-Lean construction: it uses the two
actual interfaces, their aligned source order, and the deletion component
they bound.  It does not identify a chord wall with a transversal. -/
noncomputable def sourceCrosscutOrderedCutSidesData
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) :
    OrderedCutSidesData data.toRotationSystem pair.left.walk.length 0
      (pair.sourceCrosscutFaceFragmentCount data boundary) where
  keep := fun vertex => vertex ∈ pair.componentSide boundary.component
  left := pair.sourceCrosscutLeftCutData data boundary
  right := pair.sourceCrosscutRightCutData data boundary
  leftCrosses := boundary.leftCrosses
  rightCrosses := fun step => boundary.rightCrosses (Fin.cast pair.length_eq step)
  leftInjective := boundary.leftInjective
  rightInjective := by
    intro first second heq
    change pair.right.crossingEdge hunique (Fin.cast pair.length_eq first) =
      pair.right.crossingEdge hunique (Fin.cast pair.length_eq second) at heq
    have hcast : Fin.cast pair.length_eq first = Fin.cast pair.length_eq second :=
      boundary.rightInjective heq
    exact Fin.cast_injective pair.length_eq hcast
  cover := by
    intro dart
    change data.toRotationSystem.edgeOf dart.1.1 ∈
        orderedCut (pair.left.crossingEdge hunique) ∨
      data.toRotationSystem.edgeOf dart.1.1 ∈
        orderedCut (fun step : Fin pair.left.walk.length =>
          pair.right.crossingEdge hunique (Fin.cast pair.length_eq step))
    rcases boundary.cover dart with hleft | hright
    · exact Or.inl hleft
    · rw [pair.orderedCut_sourceCrosscutRight_eq data]
      exact Or.inr hright
  disjoint := by
    change Disjoint (orderedCut (pair.left.crossingEdge hunique))
      (orderedCut (fun step : Fin pair.left.walk.length =>
        pair.right.crossingEdge hunique (Fin.cast pair.length_eq step)))
    rw [pair.orderedCut_sourceCrosscutRight_eq data]
    exact boundary.disjoint
  outer_kept := boundary.outer_kept
  removed := boundary.removed
  removed_not_kept := boundary.removed_not_kept

/-- The left port coordinate in the concrete splice is the literal left
source-crosscut coordinate. -/
@[simp]
theorem sourceCrosscutOrderedCutSidesData_left
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (step : Fin pair.left.walk.length) :
    (pair.sourceCrosscutOrderedCutSidesData data boundary).left.crossingEdge step =
      pair.left.crossingEdge hunique step :=
  rfl

/-- The right port coordinate in the concrete splice is the aligned right
source-crosscut coordinate. -/
@[simp]
theorem sourceCrosscutOrderedCutSidesData_right
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (step : Fin pair.left.walk.length) :
    (pair.sourceCrosscutOrderedCutSidesData data boundary).right.crossingEdge step =
      pair.right.crossingEdge hunique (Fin.cast pair.length_eq step) :=
  rfl

/-- The local extra condition for the closed-graph specialization of two
simple layer boundaries.  It talks directly about the two actual primal edge
endpoint sets, before any boundary dart is chosen.  The primary open-tangle
operation does not require it; it is needed only when the open seam is
suppressed back to a loopless ordinary rotation system. -/
def MatchedCrossingsVertexDisjoint
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique) : Prop :=
  ∀ step : Fin pair.left.walk.length, ∀ left right : V,
    left ∈ data.toRotationSystem.endpoints
        (pair.left.crossingEdge hunique step) →
      right ∈ data.toRotationSystem.endpoints
        (pair.right.crossingEdge hunique (Fin.cast pair.length_eq step)) →
        left ≠ right

/-- Paired simple transverse layer boundaries rule out every matched primal
endpoint collision except a collision visible on one of the two named hole
faces.  The latter is the finite boundary-port check recorded by
`MatchedCrossingsAvoidEndpointFaces`; no arbitrary closed-seam hypothesis
remains after this reduction. -/
theorem matchedCrossingsVertexDisjoint_of_avoidEndpointFaces
    (data : Data G)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (hboundary : pair.MatchedCrossingsAvoidEndpointFaces data) :
    pair.MatchedCrossingsVertexDisjoint data :=
  pair.matchedCrossingsEndpointSeparation_of_avoidEndpointFaces
    data hcubic hrotation hboundary

/-- Endpoint-set separation supplies the no-loop premise of the concrete
splice automatically.  Unlike an opaque seam condition, this is a direct
fact about the actual two layer-boundary crossings and can be established by
the corridor/layer formation proof. -/
theorem sourceCrosscutSeamEndpoints_of_matchedCrossingsVertexDisjoint
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (hseparated : pair.MatchedCrossingsVertexDisjoint data)
    (step : Fin pair.left.walk.length) :
    data.toRotationSystem.vertOf
        (orderedBoundaryDart data.toRotationSystem
          (fun vertex => vertex ∈ pair.componentSide boundary.component)
          (pair.left.crossingEdge hunique) boundary.leftCrosses step).1.1.1 ≠
      data.toRotationSystem.vertOf
        (orderedBoundaryDart data.toRotationSystem
          (fun vertex => vertex ∈ pair.componentSide boundary.component)
          (fun index => pair.right.crossingEdge hunique
            (Fin.cast pair.length_eq index))
          (fun index => boundary.rightCrosses
            (Fin.cast pair.length_eq index)) step).1.1.1 := by
  let leftDart := orderedBoundaryDart data.toRotationSystem
    (fun vertex => vertex ∈ pair.componentSide boundary.component)
    (pair.left.crossingEdge hunique) boundary.leftCrosses step
  let rightDart := orderedBoundaryDart data.toRotationSystem
    (fun vertex => vertex ∈ pair.componentSide boundary.component)
    (fun index => pair.right.crossingEdge hunique
      (Fin.cast pair.length_eq index))
    (fun index => boundary.rightCrosses
      (Fin.cast pair.length_eq index)) step
  apply hseparated step
    (data.toRotationSystem.vertOf leftDart.1.1.1)
    (data.toRotationSystem.vertOf rightDart.1.1.1)
  · rw [data.toRotationSystem.mem_endpoints_iff]
    exact ⟨leftDart.1.1.1,
      data.toRotationSystem.mem_dartsOn.2
        (orderedBoundaryDart_edgeOf data.toRotationSystem
          (fun vertex => vertex ∈ pair.componentSide boundary.component)
          (pair.left.crossingEdge hunique) boundary.leftCrosses step),
      rfl⟩
  · rw [data.toRotationSystem.mem_endpoints_iff]
    exact ⟨rightDart.1.1.1,
      data.toRotationSystem.mem_dartsOn.2
        (orderedBoundaryDart_edgeOf data.toRotationSystem
          (fun vertex => vertex ∈ pair.componentSide boundary.component)
          (fun index => pair.right.crossingEdge hunique
            (Fin.cast pair.length_eq index))
          (fun index => boundary.rightCrosses
            (Fin.cast pair.length_eq index)) step),
      rfl⟩

/-- Perform the concrete retained-vertex shortening on the two actual source
interfaces.  The sole remaining geometric input is the local noncollision of
the two matched seam endpoints; all cut, side, coverage, orientation, and
strict-removal data were constructed above from the paired layer boundary. -/
noncomputable def sourceCrosscutSpliceData
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (seamEndpoints : ∀ step,
      data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (pair.left.crossingEdge hunique) boundary.leftCrosses step).1.1.1 ≠
        data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (fun index => pair.right.crossingEdge hunique
              (Fin.cast pair.length_eq index))
            (fun index => boundary.rightCrosses
              (Fin.cast pair.length_eq index)) step).1.1.1) :
    OrderedCutSpliceData data.toRotationSystem pair.left.walk.length 0
      (pair.sourceCrosscutFaceFragmentCount data boundary) :=
  (pair.sourceCrosscutOrderedCutSidesData data boundary).splice seamEndpoints

/-- The source-facing splice needs no opaque seam premise: a simple layer
boundary supplies it by saying that the two *actual matched crossing edges*
have disjoint endpoint sets.  This is the concrete local condition which the
corridor/layer construction must establish, and it is deliberately phrased
before any auxiliary boundary dart is selected. -/
noncomputable def sourceCrosscutLayerSpliceData
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (hseparated : pair.MatchedCrossingsVertexDisjoint data) :
    OrderedCutSpliceData data.toRotationSystem pair.left.walk.length 0
      (pair.sourceCrosscutFaceFragmentCount data boundary) :=
  pair.sourceCrosscutSpliceData data boundary
    (fun step => pair.sourceCrosscutSeamEndpoints_of_matchedCrossingsVertexDisjoint
      data boundary hseparated step)

/-- A repeated source profile is exactly the equal-profile certificate
consumed by the concrete shortening.  No boundary-color equality is supplied
separately: it is extracted from the full finite profile by the splice
library. -/
noncomputable def sourceCrosscutSpliceEqualProfile
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (seamEndpoints : ∀ step,
      data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (pair.left.crossingEdge hunique) boundary.leftCrosses step).1.1.1 ≠
        data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (fun index => pair.right.crossingEdge hunique
              (Fin.cast pair.length_eq index))
            (fun index => boundary.rightCrosses
              (Fin.cast pair.length_eq index)) step).1.1.1)
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (hcoloring : data.toRotationSystem.IsTaitEdgeColoring coloring)
    (hprofile :
      (pair.sourceCrosscutOrderedCutSidesData data boundary).left.profile
          coloring hcoloring =
        (pair.sourceCrosscutOrderedCutSidesData data boundary).right.profile
          coloring hcoloring) :
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints).EqualProfile where
  coloring := coloring
  coloring_isTait := hcoloring
  profile_eq := hprofile

/-- Equal profiles on the two genuine layer interfaces transport a Tait
coloring to the concrete shorter rotation system.  This is the source
splice's properness and color-matching calculation, now attached to the
actual crosscuts rather than an abstract cut-side placeholder. -/
theorem sourceCrosscutSplice_output_taitColorable
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (seamEndpoints : ∀ step,
      data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (pair.left.crossingEdge hunique) boundary.leftCrosses step).1.1.1 ≠
        data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (fun index => pair.right.crossingEdge hunique
              (Fin.cast pair.length_eq index))
            (fun index => boundary.rightCrosses
              (Fin.cast pair.length_eq index)) step).1.1.1)
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (hcoloring : data.toRotationSystem.IsTaitEdgeColoring coloring)
    (hprofile :
      (pair.sourceCrosscutOrderedCutSidesData data boundary).left.profile
          coloring hcoloring =
        (pair.sourceCrosscutOrderedCutSidesData data boundary).right.profile
          coloring hcoloring) :
    TaitColorable
      (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output :=
  (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output_taitColorable_of_equalProfile
    (pair.sourceCrosscutSpliceEqualProfile data boundary seamEndpoints
      coloring hcoloring hprofile)

/-- Equal source profiles transport a Tait coloring across the concrete layer
splice.  This version exposes only the literal matched-crossing separation
that source layer formation has to prove, never an arbitrary dart-level seam
condition. -/
theorem sourceCrosscutLayerSplice_output_taitColorable
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (hseparated : pair.MatchedCrossingsVertexDisjoint data)
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (hcoloring : data.toRotationSystem.IsTaitEdgeColoring coloring)
    (hprofile :
      (pair.sourceCrosscutOrderedCutSidesData data boundary).left.profile
          coloring hcoloring =
        (pair.sourceCrosscutOrderedCutSidesData data boundary).right.profile
          coloring hcoloring) :
    TaitColorable
      (pair.sourceCrosscutLayerSpliceData data boundary hseparated).output := by
  exact pair.sourceCrosscutSplice_output_taitColorable data boundary
    (fun step => pair.sourceCrosscutSeamEndpoints_of_matchedCrossingsVertexDisjoint
      data boundary hseparated step)
    coloring hcoloring hprofile

/-- The source-derived splice has strict size descent: the paired separator
already constructed a component with an actual removed vertex. -/
theorem sourceCrosscutSplice_outputSize_lt
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (seamEndpoints : ∀ step,
      data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (pair.left.crossingEdge hunique) boundary.leftCrosses step).1.1.1 ≠
        data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (fun index => pair.right.crossingEdge hunique
              (Fin.cast pair.length_eq index))
            (fun index => boundary.rightCrosses
              (Fin.cast pair.length_eq index)) step).1.1.1) :
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints).outputSize <
      Fintype.card V :=
  (pair.sourceCrosscutSpliceData data boundary seamEndpoints).outputSize_lt

/-- The actual simple-layer splice strictly shortens the retained vertex set.
The strict inequality is kernel-checked from the selected deletion component's
explicit removed vertex. -/
theorem sourceCrosscutLayerSplice_outputSize_lt
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (hseparated : pair.MatchedCrossingsVertexDisjoint data) :
    (pair.sourceCrosscutLayerSpliceData data boundary hseparated).outputSize <
      Fintype.card V := by
  exact pair.sourceCrosscutSplice_outputSize_lt data boundary
    (fun step => pair.sourceCrosscutSeamEndpoints_of_matchedCrossingsVertexDisjoint
      data boundary hseparated step)

/-- The retained-vertex specialization for simple layer boundaries.  Its only
extra geometric premise beyond the open-interface construction is the finite
endpoint-hole test; interior noncollision is derived from paired
dual-transversal disjointness. -/
noncomputable def sourceCrosscutLayerSpliceDataOfEndpointFaces
    (data : Data G)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (hboundary : pair.MatchedCrossingsAvoidEndpointFaces data) :
    OrderedCutSpliceData data.toRotationSystem pair.left.walk.length 0
      (pair.sourceCrosscutFaceFragmentCount data boundary) :=
  pair.sourceCrosscutLayerSpliceData data boundary
    (pair.matchedCrossingsVertexDisjoint_of_avoidEndpointFaces
      data hcubic hrotation hboundary)

/-- Equal source profiles preserve Tait colorability through the concrete
simple-layer splice whose seam separation has been derived from the two
transversals and the finite hole-face test. -/
theorem sourceCrosscutLayerSpliceDataOfEndpointFaces_output_taitColorable
    (data : Data G)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (hboundary : pair.MatchedCrossingsAvoidEndpointFaces data)
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (hcoloring : data.toRotationSystem.IsTaitEdgeColoring coloring)
    (hprofile :
      (pair.sourceCrosscutOrderedCutSidesData data boundary).left.profile
          coloring hcoloring =
        (pair.sourceCrosscutOrderedCutSidesData data boundary).right.profile
          coloring hcoloring) :
    TaitColorable
      (pair.sourceCrosscutLayerSpliceDataOfEndpointFaces
        data hcubic hrotation boundary hboundary).output := by
  exact pair.sourceCrosscutLayerSplice_output_taitColorable data boundary
    (pair.matchedCrossingsVertexDisjoint_of_avoidEndpointFaces
      data hcubic hrotation hboundary)
    coloring hcoloring hprofile

/-- The same source-facing construction strictly decreases the retained
vertex count; the descent remains independent of the endpoint-hole proof. -/
theorem sourceCrosscutLayerSpliceDataOfEndpointFaces_outputSize_lt
    (data : Data G)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (hboundary : pair.MatchedCrossingsAvoidEndpointFaces data) :
    (pair.sourceCrosscutLayerSpliceDataOfEndpointFaces
      data hcubic hrotation boundary hboundary).outputSize < Fintype.card V := by
  exact pair.sourceCrosscutLayerSplice_outputSize_lt data boundary
    (pair.matchedCrossingsVertexDisjoint_of_avoidEndpointFaces
      data hcubic hrotation hboundary)

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
