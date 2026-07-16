import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutCap
import Mettapedia.GraphTheory.FourColor.GoertzelV24PlanarBondSpliceEuler
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedSplicePrimalGraph
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceTwoSided

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TwoEdgeCutCapGeometry

open GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceDualConnectedness
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24PlanarBondSpliceEuler
open GoertzelV24RetainedSplicePrimalGraph
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor
open GoertzelV24RotationVertexCutProfile
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The endpoint-existence and endpoint-cardinality definitions of a
rotation-system vertex cut compute the same edge set. -/
theorem vertexSetCrossingEdges_eq_vertexSideEdgeBoundary
    (RS : RotationSystem V E) (side : Finset V) :
    vertexSetCrossingEdges RS side = RS.vertexSideEdgeBoundary side := by
  classical
  ext edge
  rw [mem_vertexSetCrossingEdges_iff,
    RS.mem_vertexSideEdgeBoundary_iff]
  constructor
  · rintro ⟨inner, hinnerEndpoint, hinnerSide,
      outer, houterEndpoint, houterSide⟩
    have hnonempty : (RS.endpoints edge ∩ side).Nonempty :=
      ⟨inner, Finset.mem_inter.mpr ⟨hinnerEndpoint, hinnerSide⟩⟩
    have hproper : RS.endpoints edge ∩ side ⊂ RS.endpoints edge := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.inter_subset_left, ?_⟩
      intro heq
      have houterInter : outer ∈ RS.endpoints edge ∩ side := by
        rw [heq]
        exact houterEndpoint
      exact houterSide (Finset.mem_inter.mp houterInter).2
    have hpositive : 0 < (RS.endpoints edge ∩ side).card :=
      Finset.card_pos.mpr hnonempty
    have hstrict := Finset.card_lt_card hproper
    rw [RS.endpoints_card_two] at hstrict
    omega
  · intro hcard
    rcases Finset.card_eq_one.mp hcard with ⟨inner, hinter⟩
    have hinnerInter : inner ∈ RS.endpoints edge ∩ side := by
      rw [hinter]
      simp
    have houter : ∃ outer ∈ RS.endpoints edge, outer ∉ side := by
      by_contra hnone
      push Not at hnone
      have hsubset : RS.endpoints edge ⊆ side := by
        intro vertex hvertex
        exact hnone vertex hvertex
      have heq : RS.endpoints edge ∩ side = RS.endpoints edge :=
        Finset.inter_eq_left.mpr hsubset
      rw [heq, RS.endpoints_card_two] at hcard
      omega
    rcases houter with ⟨outer, houterEndpoint, houterSide⟩
    have hinnerEndpoint : inner ∈ RS.endpoints edge :=
      (Finset.mem_inter.mp hinnerInter).1
    have hinnerSide : inner ∈ side :=
      (Finset.mem_inter.mp hinnerInter).2
    exact ⟨inner, hinnerEndpoint, hinnerSide,
      outer, houterEndpoint, houterSide⟩

@[simp]
theorem rotationPrimalGraph_withOuter
    (RS : RotationSystem V E) (root : RS.D) :
    rotationPrimalGraph (RS.withOuter root) = rotationPrimalGraph RS :=
  rfl

@[simp]
theorem orbitSphericalCubicMapData_withOuter_iff
    (RS : RotationSystem V E) (root : RS.D) :
    OrbitSphericalCubicMapData (RS.withOuter root) ↔
      OrbitSphericalCubicMapData RS :=
  by
    constructor
    · intro h
      exact ⟨h.cubic, h.euler⟩
    · intro h
      exact ⟨h.cubic, h.euler⟩

@[simp]
theorem orbitFacesTwoSided_withOuter_iff
    (RS : RotationSystem V E) (root : RS.D) :
    OrbitFacesTwoSided (RS.withOuter root) ↔ OrbitFacesTwoSided RS :=
  Iff.rfl

@[simp]
theorem vertexRotationCyclic_withOuter_iff
    (RS : RotationSystem V E) (root : RS.D) :
    VertexRotationCyclic (RS.withOuter root) ↔ VertexRotationCyclic RS :=
  Iff.rfl

/-- The spherical-map conclusion of an ordered retained splice is unchanged
when its retained-vertex predicate is replaced by an equal predicate. The
explicit proof arguments on both sides make this a reusable dependent
congruence lemma for concrete splice packages. -/
theorem orbitSphericalCubicMapData_orderedCutRetainedVertexRotationSystem_congr_keep
    (RS : RotationSystem V E)
    {keep₁ keep₂ : V → Prop} (hkeep : keep₁ = keep₂)
    (leftCrossing rightCrossing : Fin n → E)
    (hleftCrosses₁ : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = leftCrossing step ∧
      keep₁ (RS.vertOf dart) ∧
      ¬ keep₁ (RS.vertOf (RS.alpha dart)))
    (hrightCrosses₁ : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = rightCrossing step ∧
      keep₁ (RS.vertOf dart) ∧
      ¬ keep₁ (RS.vertOf (RS.alpha dart)))
    (hleftCrosses₂ : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = leftCrossing step ∧
      keep₂ (RS.vertOf dart) ∧
      ¬ keep₂ (RS.vertOf (RS.alpha dart)))
    (hrightCrosses₂ : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = rightCrossing step ∧
      keep₂ (RS.vertOf dart) ∧
      ¬ keep₂ (RS.vertOf (RS.alpha dart)))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover₁ : ∀ dart : BoundaryDart RS keep₁,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing ∨
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hcover₂ : ∀ dart : BoundaryDart RS keep₂,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing ∨
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (houter₁ : keep₁ (RS.vertOf RS.outer))
    (houter₂ : keep₂ (RS.vertOf RS.outer))
    (hseamEndpoints₁ : ∀ step,
      RS.vertOf
          (orderedBoundaryDart RS keep₁ leftCrossing
            hleftCrosses₁ step).1.1.1 ≠
        RS.vertOf
          (orderedBoundaryDart RS keep₁ rightCrossing
            hrightCrosses₁ step).1.1.1)
    (hseamEndpoints₂ : ∀ step,
      RS.vertOf
          (orderedBoundaryDart RS keep₂ leftCrossing
            hleftCrosses₂ step).1.1.1 ≠
        RS.vertOf
          (orderedBoundaryDart RS keep₂ rightCrossing
            hrightCrosses₂ step).1.1.1)
    (hsphere : OrbitSphericalCubicMapData
      (orderedCutRetainedVertexRotationSystem RS keep₁
        leftCrossing rightCrossing hleftCrosses₁ hrightCrosses₁
        hleftInjective hrightInjective hcover₁ hdisjoint houter₁
        hseamEndpoints₁)) :
    OrbitSphericalCubicMapData
      (orderedCutRetainedVertexRotationSystem RS keep₂
        leftCrossing rightCrossing hleftCrosses₂ hrightCrosses₂
        hleftInjective hrightInjective hcover₂ hdisjoint houter₂
        hseamEndpoints₂) := by
  subst keep₂
  exact hsphere

variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Reroot graph-backed rotation data without changing its embedded graph or
cyclic orders. -/
def graphDataWithOuter (data : Data G) (root : G.Dart) : Data G :=
  { data with outer := root }

@[simp]
theorem graphDataWithOuter_toRotationSystem
    (data : Data G) (root : G.Dart) :
    (graphDataWithOuter data root).toRotationSystem =
      data.toRotationSystem.withOuter root :=
  rfl

/-- On a two-element carrier, a fixed-point-free permutation is unique. -/
theorem perm_eq_of_card_two_of_fixedPointFree
    {A : Type*} [Fintype A] (hcard : Fintype.card A = 2)
    (left right : Equiv.Perm A)
    (hleft : ∀ point, left point ≠ point)
    (hright : ∀ point, right point ≠ point) :
    left = right := by
  apply Equiv.ext
  intro point
  have hnatCard : Nat.card A = 2 := by
    simpa using hcard
  rcases (Nat.card_eq_two_iff' point).mp hnatCard with
    ⟨other, _hother, hunique⟩
  exact (hunique (left point) (hleft point)).trans
    (hunique (right point) (hright point)).symm

/-- The opposite boundary cycle on one position per interface swaps the two
positions and hence has no fixed point. -/
theorem oppositeBoundaryCycle_one_ne
    (position : OrderedSeamPosition 1) :
    oppositeBoundaryCycle 1 position ≠ position := by
  rcases position with position | position <;>
    fin_cases position <;> decide

/-- Two-sided ambient faces prevent the deleted-side boundary return from
fixing an exposed half-edge. -/
theorem deletedRegionBoundarySuccessor_ne_of_twoSided
    (RS : RotationSystem V E) (deleted : Finset V)
    (htwoSided : OrbitFacesTwoSided RS)
    (root : BoundaryDart RS (deletedRegionKeep deleted)) :
    deletedRegionBoundarySuccessor RS deleted root ≠ root := by
  intro hfixed
  apply htwoSided root.1.1
  apply Quotient.sound
  have hface := deletedRegionBoundarySuccessor_sameAmbientFace_alpha
    RS deleted root
  rw [hfixed] at hface
  exact hface

/-- With one edge on each interface, two-sidedness discharges the complete
opposite-boundary-order premise required by the planar-bond Euler theorem. -/
theorem cutsFollowOppositeDeletedBoundaryOrder_fin_one
    (RS : RotationSystem V E) (deleted : Finset V)
    (leftCrossing rightCrossing : Fin 1 → E)
    (hboundary : orderedCut leftCrossing ∪ orderedCut rightCrossing =
      vertexSetCrossingEdges RS deleted)
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (htwoSided : OrbitFacesTwoSided RS) :
    CutsFollowOppositeDeletedBoundaryOrder RS deleted
      leftCrossing rightCrossing hboundary hleftInjective
      hrightInjective hdisjoint := by
  let boundaryEquiv := orderedBoundaryPositionEquiv RS deleted
    leftCrossing rightCrossing hboundary hleftInjective
    hrightInjective hdisjoint
  apply perm_eq_of_card_two_of_fixedPointFree
  · calc
      Fintype.card (BoundaryDart RS (deletedRegionKeep deleted)) =
          Fintype.card (OrderedSeamPosition 1) :=
        (Fintype.card_congr boundaryEquiv).symm
      _ = 2 := by simp [OrderedSeamPosition]
  · exact deletedRegionBoundarySuccessor_ne_of_twoSided
      RS deleted htwoSided
  · intro root hfixed
    let position := boundaryEquiv.symm root
    apply oppositeBoundaryCycle_one_ne position
    have htransport := congrArg boundaryEquiv.symm hfixed
    simpa [boundaryEquiv, position, Equiv.permCongr_apply] using htransport

namespace RotationSystem.TwoEdgeCutSideData

variable {RS : RotationSystem V E} (data : RS.TwoEdgeCutSideData)

/-- The two singleton interfaces are exactly the crossing-edge boundary of
the region removed when constructing this cap. -/
theorem capBoundary :
    orderedCut data.leftCrossing ∪ orderedCut data.rightCrossing =
      vertexSetCrossingEdges RS data.sideᶜ := by
  rw [data.orderedCut_leftCrossing, data.orderedCut_rightCrossing,
    vertexSetCrossingEdges_eq_vertexSideEdgeBoundary,
    RS.vertexSideEdgeBoundary_compl, data.boundary_eq]
  ext edge
  simp

/-- For an exact two-edge cap in a two-sided map, the boundary-order premise
of the planar-bond Euler theorem is automatic. -/
theorem capCutsFollowOppositeDeletedBoundaryOrder
    (htwoSided : OrbitFacesTwoSided RS) :
    CutsFollowOppositeDeletedBoundaryOrder RS data.sideᶜ
      data.leftCrossing data.rightCrossing (capBoundary data)
      data.leftCrossing_injective data.rightCrossing_injective
      data.cutsDisjoint := by
  exact cutsFollowOppositeDeletedBoundaryOrder_fin_one RS data.sideᶜ
    data.leftCrossing data.rightCrossing (capBoundary data)
    data.leftCrossing_injective data.rightCrossing_injective
    data.cutsDisjoint htwoSided

/-- A graph-backed exact two-edge cap preserves the spherical cubic-map
equation when both sides of the bond are connected. -/
theorem cap_orbitSphericalCubicMapData
    (graphData : Data G)
    (data : graphData.toRotationSystem.TwoEdgeCutSideData)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (hsideConnected :
      (G.induce {vertex | vertex ∈ data.side}).Connected)
    (hcomplementConnected :
      (G.induce {vertex | vertex ∈ data.sideᶜ}).Connected) :
    OrbitSphericalCubicMapData data.capRotationSystem := by
  have hkeepEq :
      deletedRegionKeep data.sideᶜ = data.keep := by
    funext vertex
    apply propext
    simp [deletedRegionKeep, RotationSystem.TwoEdgeCutSideData.keep]
  have hdeletedEq :
      (fun vertex => ¬ deletedRegionKeep data.sideᶜ vertex) =
        (fun vertex => vertex ∈ data.sideᶜ) := by
    funext vertex
    apply propext
    simp [deletedRegionKeep]
  have houterDeleted :
      deletedRegionKeep data.sideᶜ
        (graphData.toRotationSystem.vertOf
          graphData.toRotationSystem.outer) := by
    rw [hkeepEq]
    exact data.outer_mem
  have hseamDeleted : ∀ step,
      graphData.toRotationSystem.vertOf
          (orderedBoundaryDart graphData.toRotationSystem
            (deletedRegionKeep data.sideᶜ) data.leftCrossing
            (leftCrossing_outward graphData.toRotationSystem data.sideᶜ
              data.leftCrossing data.rightCrossing (capBoundary data))
            step).1.1.1 ≠
        graphData.toRotationSystem.vertOf
          (orderedBoundaryDart graphData.toRotationSystem
            (deletedRegionKeep data.sideᶜ) data.rightCrossing
            (rightCrossing_outward graphData.toRotationSystem data.sideᶜ
              data.leftCrossing data.rightCrossing (capBoundary data))
            step).1.1.1 := by
    intro step
    let leftDeleted := orderedBoundaryDart
      graphData.toRotationSystem (deletedRegionKeep data.sideᶜ)
      data.leftCrossing
      (leftCrossing_outward graphData.toRotationSystem data.sideᶜ
        data.leftCrossing data.rightCrossing (capBoundary data)) step
    let rightDeleted := orderedBoundaryDart
      graphData.toRotationSystem (deletedRegionKeep data.sideᶜ)
      data.rightCrossing
      (rightCrossing_outward graphData.toRotationSystem data.sideᶜ
        data.leftCrossing data.rightCrossing (capBoundary data)) step
    let left : BoundaryDart graphData.toRotationSystem data.keep :=
      ⟨⟨leftDeleted.1.1.1, by
          show data.keep
            (graphData.toRotationSystem.vertOf leftDeleted.1.1.1)
          rw [← hkeepEq]
          exact leftDeleted.1.1.2⟩, by
        show ¬ data.keep
          (graphData.toRotationSystem.vertOf
            (graphData.toRotationSystem.alpha leftDeleted.1.1.1))
        rw [← hkeepEq]
        exact leftDeleted.1.2⟩
    let right : BoundaryDart graphData.toRotationSystem data.keep :=
      ⟨⟨rightDeleted.1.1.1, by
          show data.keep
            (graphData.toRotationSystem.vertOf rightDeleted.1.1.1)
          rw [← hkeepEq]
          exact rightDeleted.1.1.2⟩, by
        show ¬ data.keep
          (graphData.toRotationSystem.vertOf
            (graphData.toRotationSystem.alpha rightDeleted.1.1.1))
        rw [← hkeepEq]
        exact rightDeleted.1.2⟩
    have hleftEdge :
        graphData.toRotationSystem.edgeOf left.1.1 =
          data.leftEdge := by
      change graphData.toRotationSystem.edgeOf leftDeleted.1.1.1 =
        data.leftEdge
      simpa [RotationSystem.TwoEdgeCutSideData.leftCrossing] using
        orderedBoundaryDart_edgeOf graphData.toRotationSystem
          (deletedRegionKeep data.sideᶜ) data.leftCrossing
          (leftCrossing_outward graphData.toRotationSystem data.sideᶜ
            data.leftCrossing data.rightCrossing (capBoundary data)) step
    have hrightEdge :
        graphData.toRotationSystem.edgeOf right.1.1 =
          data.rightEdge := by
      change graphData.toRotationSystem.edgeOf rightDeleted.1.1.1 =
        data.rightEdge
      simpa [RotationSystem.TwoEdgeCutSideData.rightCrossing] using
        orderedBoundaryDart_edgeOf graphData.toRotationSystem
          (deletedRegionKeep data.sideᶜ) data.rightCrossing
          (rightCrossing_outward graphData.toRotationSystem data.sideᶜ
            data.leftCrossing data.rightCrossing (capBoundary data)) step
    exact data.retainedEndpointsDistinct left right hleftEdge hrightEdge
  have hshortened :=
    orbitSphericalCubicMapData_orderedCutSplice_of_planar_bond
      graphData data.sideᶜ data.leftCrossing data.rightCrossing
      (capBoundary data) data.leftCrossing_injective
      data.rightCrossing_injective data.cutsDisjoint (by omega)
      (capCutsFollowOppositeDeletedBoundaryOrder data htwoSided)
      hsphere htwoSided hconnected hrotation
      (by
        rw [hkeepEq]
        simpa [RotationSystem.TwoEdgeCutSideData.keep] using
          hsideConnected)
      (by
        rw [hdeletedEq]
        exact hcomplementConnected)
      houterDeleted hseamDeleted
  have htransported :=
    orbitSphericalCubicMapData_orderedCutRetainedVertexRotationSystem_congr_keep
      graphData.toRotationSystem hkeepEq data.leftCrossing
      data.rightCrossing
      (leftCrossing_outward graphData.toRotationSystem data.sideᶜ
        data.leftCrossing data.rightCrossing (capBoundary data))
      (rightCrossing_outward graphData.toRotationSystem data.sideᶜ
        data.leftCrossing data.rightCrossing (capBoundary data))
      data.leftCrosses data.rightCrosses data.leftCrossing_injective
      data.rightCrossing_injective
      (deletedRegionBoundaryCover graphData.toRotationSystem data.sideᶜ
        data.leftCrossing data.rightCrossing (capBoundary data))
      data.boundaryCover data.cutsDisjoint houterDeleted data.outer_mem
      hseamDeleted data.seamEndpoints hshortened
  exact htransported

end RotationSystem.TwoEdgeCutSideData

namespace RotationSystem.TwoEdgeCutPairData

variable {RS : RotationSystem V E} (data : RS.TwoEdgeCutPairData)

/-- A connected chosen side remains connected after its two exposed
half-edges are joined into the cap edge. -/
theorem sideCap_primal_connected
    (hsideConnected :
      ((rotationPrimalGraph RS).induce
        {vertex | vertex ∈ data.side}).Connected) :
    (rotationPrimalGraph data.sideData.capRotationSystem).Connected := by
  apply
    rotationPrimalGraph_orderedCutRetainedVertexRotationSystem_connected_of_retained
  change
    ((rotationPrimalGraph RS).induce
      {vertex | vertex ∈ data.side}).Connected
  exact hsideConnected

/-- A connected complementary side remains connected after its two exposed
half-edges are joined into the cap edge. -/
theorem complementCap_primal_connected
    (hcomplementConnected :
      ((rotationPrimalGraph RS).induce
        {vertex | vertex ∈ data.sideᶜ}).Connected) :
    (rotationPrimalGraph data.complementData.capRotationSystem).Connected := by
  apply
    rotationPrimalGraph_orderedCutRetainedVertexRotationSystem_connected_of_retained
  change
    ((rotationPrimalGraph RS).induce
      {vertex | vertex ∈ data.sideᶜ}).Connected
  exact hcomplementConnected

/-- The chosen capped half of a graph-backed exact two-edge cut retains the
spherical cubic-map equation. -/
theorem sideCap_orbitSphericalCubicMapData
    (graphData : Data G)
    (pair : graphData.toRotationSystem.TwoEdgeCutPairData)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (hsideConnected :
      (G.induce {vertex | vertex ∈ pair.side}).Connected)
    (hcomplementConnected :
      (G.induce {vertex | vertex ∈ pair.sideᶜ}).Connected) :
    OrbitSphericalCubicMapData pair.sideData.capRotationSystem := by
  apply TwoEdgeCutSideData.cap_orbitSphericalCubicMapData
    (graphDataWithOuter graphData pair.sideRoot) pair.sideData
  · exact (orbitSphericalCubicMapData_withOuter_iff
      graphData.toRotationSystem pair.sideRoot).2 hsphere
  · exact (orbitFacesTwoSided_withOuter_iff
      graphData.toRotationSystem pair.sideRoot).2 htwoSided
  · exact hconnected
  · exact (vertexRotationCyclic_withOuter_iff
      graphData.toRotationSystem pair.sideRoot).2 hrotation
  · exact hsideConnected
  · exact hcomplementConnected

/-- The complementary capped half of a graph-backed exact two-edge cut also
retains the spherical cubic-map equation. -/
theorem complementCap_orbitSphericalCubicMapData
    (graphData : Data G)
    (pair : graphData.toRotationSystem.TwoEdgeCutPairData)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (hsideConnected :
      (G.induce {vertex | vertex ∈ pair.side}).Connected)
    (hcomplementConnected :
      (G.induce {vertex | vertex ∈ pair.sideᶜ}).Connected) :
    OrbitSphericalCubicMapData pair.complementData.capRotationSystem := by
  apply TwoEdgeCutSideData.cap_orbitSphericalCubicMapData
    (graphDataWithOuter graphData pair.complementRoot)
    pair.complementData
  · exact (orbitSphericalCubicMapData_withOuter_iff
      graphData.toRotationSystem pair.complementRoot).2 hsphere
  · exact (orbitFacesTwoSided_withOuter_iff
      graphData.toRotationSystem pair.complementRoot).2 htwoSided
  · exact hconnected
  · exact (vertexRotationCyclic_withOuter_iff
      graphData.toRotationSystem pair.complementRoot).2 hrotation
  · exact hcomplementConnected
  · change (G.induce {vertex | vertex ∈ pair.sideᶜᶜ}).Connected
    rw [compl_compl]
    exact hsideConnected

end RotationSystem.TwoEdgeCutPairData

end

end GoertzelV24TwoEdgeCutCapGeometry

end Mettapedia.GraphTheory.FourColor
