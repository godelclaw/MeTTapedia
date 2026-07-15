import Mettapedia.GraphTheory.FourColor.GoertzelV24PlanarBondBoundaryOrder

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24PlanarBondSpliceEuler

open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24CurvatureScope
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceOrbitPartitionBridge
open GoertzelV24FaceDualConnectedness
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PlanarBondBoundaryOrder
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RetainedSpliceAmbientFaceCount
open GoertzelV24RetainedSpliceEdgeCount
open GoertzelV24RetainedSpliceEuler
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RetainedSpliceFaceCount
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SimpleGraphFaceDualConnectedness
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

noncomputable section

/-- Capping a boundary permutation by an involution has the same cycle count
when the boundary orientation is reversed. -/
theorem card_inv_mul_involution_partition_eq
    {A : Type*} [Fintype A] [DecidableEq A]
    (boundary cap : Equiv.Perm A) (hcap : cap * cap = 1) :
    (boundary⁻¹ * cap).partition.parts.card =
      (boundary * cap).partition.parts.card := by
  have hcapInv : cap⁻¹ = cap := inv_eq_of_mul_eq_one_left hcap
  let reversedCap := boundary⁻¹ * cap
  have hinverseParts :
      reversedCap⁻¹.partition.parts = reversedCap.partition.parts := by
    rw [Equiv.Perm.parts_partition, Equiv.Perm.parts_partition,
      Equiv.Perm.cycleType_inv, Equiv.Perm.support_inv]
  have hinverseForm : reversedCap⁻¹ = cap * boundary := by
    simp [reversedCap, hcapInv]
  have hconjugate : IsConj (cap * boundary) (boundary * cap) := by
    rw [isConj_iff]
    refine ⟨boundary, ?_⟩
    group
  have hconjugatePartition :
      (cap * boundary).partition = (boundary * cap).partition :=
    (Equiv.Perm.partition_eq_of_isConj).1 hconjugate
  calc
    reversedCap.partition.parts.card =
        reversedCap⁻¹.partition.parts.card := by rw [hinverseParts]
    _ = (cap * boundary).partition.parts.card := by rw [hinverseForm]
    _ = (boundary * cap).partition.parts.card := by
      rw [hconjugatePartition]

/-- The ordered retained-boundary enumeration specializes definitionally to
the deleted-region boundary enumeration. -/
theorem orderedRetainedBoundaryPositionEquiv_eq_deleted
    (RS : RotationSystem V E) (deleted : Finset V)
    (leftCrossing rightCrossing : Fin n → E)
    (hboundary : orderedCut leftCrossing ∪ orderedCut rightCrossing =
      vertexSetCrossingEdges RS deleted)
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing)) :
    orderedRetainedBoundaryPositionEquiv RS (deletedRegionKeep deleted)
        leftCrossing rightCrossing
        (leftCrossing_outward RS deleted leftCrossing rightCrossing hboundary)
        (rightCrossing_outward RS deleted leftCrossing rightCrossing hboundary)
        hleftInjective hrightInjective
        (deletedRegionBoundaryCover RS deleted leftCrossing rightCrossing
          hboundary) hdisjoint =
      orderedBoundaryPositionEquiv RS deleted leftCrossing rightCrossing
        hboundary hleftInjective hrightInjective hdisjoint := by
  rfl

/-- In ordered coordinates, the actual retained-side seam swap is the
equal-index swap on the two interfaces. -/
theorem orderedRetainedBoundaryPosition_seamSwap_congr
    (RS : RotationSystem V E) (deleted : Finset V)
    (leftCrossing rightCrossing : Fin n → E)
    (hboundary : orderedCut leftCrossing ∪ orderedCut rightCrossing =
      vertexSetCrossingEdges RS deleted)
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing)) :
    let hleftCrosses := leftCrossing_outward RS deleted
      leftCrossing rightCrossing hboundary
    let hrightCrosses := rightCrossing_outward RS deleted
      leftCrossing rightCrossing hboundary
    let hcover := deletedRegionBoundaryCover RS deleted
      leftCrossing rightCrossing hboundary
    let positionEquiv := orderedRetainedBoundaryPositionEquiv RS
      (deletedRegionKeep deleted) leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint
    positionEquiv.symm.permCongr
        (orderedBoundarySeamSwap RS (deletedRegionKeep deleted)
          leftCrossing rightCrossing hleftCrosses hrightCrosses
          hleftInjective hrightInjective hcover hdisjoint) =
      orderedPositionSeamSwap n := by
  dsimp only
  rw [orderedRetainedBoundaryPositionEquiv_eq_deleted RS deleted
    leftCrossing rightCrossing hboundary hleftInjective hrightInjective
    hdisjoint]
  apply Equiv.ext
  intro position
  rcases position with step | step
  · simp only [Equiv.permCongr_apply, Equiv.symm_symm]
    rw [orderedBoundaryPositionEquiv_apply_left,
      orderedBoundarySeamSwap_apply_left]
    simpa [orderedPositionSeamSwap] using
      (Equiv.symm_apply_apply
        (orderedBoundaryPositionEquiv RS deleted leftCrossing rightCrossing
          hboundary hleftInjective hrightInjective hdisjoint)
        (Sum.inr step))
  · simp only [Equiv.permCongr_apply, Equiv.symm_symm]
    rw [orderedBoundaryPositionEquiv_apply_right,
      orderedBoundarySeamSwap_apply_right]
    simpa [orderedPositionSeamSwap] using
      (Equiv.symm_apply_apply
        (orderedBoundaryPositionEquiv RS deleted leftCrossing rightCrossing
          hboundary hleftInjective hrightInjective hdisjoint)
        (Sum.inl step))

/-- Ambient face cycles avoiding the deleted side are exactly the quotient
faces whose every dart is based on the retained side. -/
def ambientRetainedFaceOrbitEquivAllOnSide
    (RS : RotationSystem V E) (keep : V → Prop) :
    AmbientRetainedFaceOrbit RS keep ≃
      ↑(orbitFacesAllOnSide RS keep) where
  toFun orbit := ⟨orbit.1, (mem_orbitFacesAllOnSide_iff RS keep orbit.1).2
    (by
      intro dart hdart
      have hquotient :
          Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) dart =
            Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) orbit.1.out :=
        ((mem_orbitFaceDarts_iff RS orbit.1 dart).1 hdart).trans
          (Quotient.out_eq orbit.1).symm
      have hsame : RS.phi.SameCycle orbit.1.out dart :=
        (Quotient.exact hquotient).symm
      by_contra hdeleted
      exact nonHitOrbit_not_hit_of_sameCycle RS.phi
        (fun point ↦ Not (keep (RS.vertOf point))) orbit dart hsame hdeleted)⟩
  invFun face := ⟨face.1, by
    rintro ⟨dart, hdeleted, hdartFace⟩
    exact hdeleted
      ((mem_orbitFacesAllOnSide_iff RS keep face.1).1 face.2 dart
        ((mem_orbitFaceDarts_iff RS face.1 dart).2 hdartFace))⟩
  left_inv orbit := by
    apply Subtype.ext
    rfl
  right_inv face := by
    apply Subtype.ext
    rfl

theorem card_ambientRetainedFaceOrbit_eq_allOnSide
    (RS : RotationSystem V E) (keep : V → Prop) :
    Fintype.card (AmbientRetainedFaceOrbit RS keep) =
      (orbitFacesAllOnSide RS keep).card := by
  calc
    Fintype.card (AmbientRetainedFaceOrbit RS keep) =
        Fintype.card ↑(orbitFacesAllOnSide RS keep) :=
      Fintype.card_congr (ambientRetainedFaceOrbitEquivAllOnSide RS keep)
    _ = (orbitFacesAllOnSide RS keep).card := Fintype.card_coe _

/-- For a graph-backed rotation, the abstract surviving-edge carrier is
exactly the ambient graph edges whose two endpoints lie on the selected
side. -/
def retainedInternalEdgeEquivAllOnSide
    (data : Data G) (side : V → Prop) :
    RetainedInternalEdge data.toRotationSystem side ≃
      ↑(graphEdgesAllOnSide G side) where
  toFun edge := ⟨edge.1.1,
    (mem_graphEdgesAllOnSide_iff G side edge.1.1).2 ⟨edge.1.2, by
      intro vertex hvertex
      rcases edge.2 with ⟨dart, hdartEdge⟩
      have hedgeValue : dart.1.1.edge = edge.1.1 :=
        congrArg Subtype.val hdartEdge
      rcases dart.1.1 with ⟨⟨left, right⟩, hadj⟩
      simp only [SimpleGraph.Dart.edge] at hedgeValue
      rw [← hedgeValue] at hvertex
      rcases (Sym2.mem_iff.1 hvertex) with hleft | hright
      · simpa [hleft] using dart.1.2
      · simpa [hright] using dart.2⟩⟩
  invFun edge := by
    rcases edge with ⟨ambientEdge, hall⟩
    have hallData :=
      (mem_graphEdgesAllOnSide_iff G side ambientEdge).1 hall
    let graphEdge : G.edgeSet := ⟨ambientEdge, hallData.1⟩
    have hnonempty := data.toRotationSystem.dartsOn_nonempty graphEdge
    let dart := Classical.choose hnonempty
    have hdartOn : dart ∈ data.toRotationSystem.dartsOn graphEdge :=
      Classical.choose_spec hnonempty
    have hdartEdge : data.toRotationSystem.edgeOf dart = graphEdge :=
      (data.toRotationSystem.mem_dartsOn).1 hdartOn
    have hedgeValue : dart.edge = ambientEdge :=
      congrArg Subtype.val hdartEdge
    let internal : InternalDart data.toRotationSystem side :=
      ⟨⟨dart, hallData.2 dart.fst (by
          rw [← hedgeValue]
          simp [SimpleGraph.Dart.edge])⟩,
        hallData.2 dart.snd (by
          rw [← hedgeValue]
          simp [SimpleGraph.Dart.edge])⟩
    exact ⟨graphEdge, ⟨internal, hdartEdge⟩⟩
  left_inv edge := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv edge := by
    apply Subtype.ext
    rfl

theorem card_retainedInternalEdge_eq_allOnSide
    (data : Data G) (side : V → Prop) :
    Fintype.card (RetainedInternalEdge data.toRotationSystem side) =
      (graphEdgesAllOnSide G side).card := by
  calc
    Fintype.card (RetainedInternalEdge data.toRotationSystem side) =
        Fintype.card ↑(graphEdgesAllOnSide G side) :=
      Fintype.card_congr (retainedInternalEdgeEquivAllOnSide data side)
    _ = (graphEdgesAllOnSide G side).card := Fintype.card_coe _

/-- Spherical Euler arithmetic upgrades both connected-side cycle-rank bounds
to equalities and identifies the touched faces bijectively in cardinality with
the crossing edges. -/
theorem planarBond_exact_sideRanks_and_transitionCount
    (data : Data G) (deleted : Finset V)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hretainedConnected :
      (G.induce {vertex | deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex |
        Not (deletedRegionKeep deleted vertex)}).Connected) :
    (orbitFacesAllOnSide data.toRotationSystem
          (deletedRegionKeep deleted)).card +
        sideVertexCount (deletedRegionKeep deleted) =
      (graphEdgesAllOnSide G (deletedRegionKeep deleted)).card + 1 ∧
    (orbitFacesAllOnSide data.toRotationSystem
          (fun vertex ↦ Not (deletedRegionKeep deleted vertex))).card +
        sideVertexCount
          (fun vertex ↦ Not (deletedRegionKeep deleted vertex)) =
      (graphEdgesAllOnSide G
          (fun vertex ↦ Not (deletedRegionKeep deleted vertex))).card + 1 ∧
    (cutSideTransitionFaces data.toRotationSystem deleted).card =
      (vertexSetCrossingEdges data.toRotationSystem deleted).card := by
  have hprimal :
      (rotationPrimalGraph data.toRotationSystem).Connected := by
    rw [rotationPrimalGraph_toRotationSystem_eq]
    exact hconnected
  have hdual := orbitFaceInteriorDual_connected
    data.toRotationSystem hsphere.cubic hprimal hrotation
  rcases hretainedConnected.nonempty with ⟨retainedVertex⟩
  rcases hdeletedConnected.nonempty with ⟨deletedVertex⟩
  have hretained : ∃ vertex, deletedRegionKeep deleted vertex :=
    ⟨retainedVertex.1, by
      simpa only [Set.mem_setOf_eq] using retainedVertex.2⟩
  have hdeleted : ∃ vertex,
      Not (deletedRegionKeep deleted vertex) :=
    ⟨deletedVertex.1, by
      simpa only [Set.mem_setOf_eq] using deletedVertex.2⟩
  rcases cutSideTransitionFaces_nonempty_of_connected
      data deleted hconnected hretained hdeleted with
    ⟨touchedFace, htouchedFace⟩
  have hretainedNotPure : ∃ face : OrbitFace data.toRotationSystem,
      face ∉ orbitFacesAllOnSide data.toRotationSystem
        (deletedRegionKeep deleted) := by
    refine ⟨touchedFace, ?_⟩
    intro hpure
    exact (Finset.disjoint_left.1
      (cutSideTransitionFaces_disjoint_allOnSide
        data.toRotationSystem deleted)) htouchedFace hpure
  have hdeletedNotPure : ∃ face : OrbitFace data.toRotationSystem,
      face ∉ orbitFacesAllOnSide data.toRotationSystem
        (fun vertex ↦ Not (deletedRegionKeep deleted vertex)) := by
    refine ⟨touchedFace, ?_⟩
    intro hpure
    exact (Finset.disjoint_left.1
      (cutSideTransitionFaces_disjoint_allOffSide
        data.toRotationSystem deleted)) htouchedFace hpure
  have hretainedRank := pureSideFace_cycleRankBound_of_connected
    data htwoSided hdual (deletedRegionKeep deleted)
      hretainedConnected hretainedNotPure
  have hdeletedRank := pureSideFace_cycleRankBound_of_connected
    data htwoSided hdual
      (fun vertex ↦ Not (deletedRegionKeep deleted vertex))
      hdeletedConnected hdeletedNotPure
  have hcrossingLe :=
    crossingEdges_le_transitionFaces_of_sideCycleRankBounds
      data deleted hsphere hretainedRank hdeletedRank
  have htransitionLe :=
    card_cutSideTransitionFaces_le_crossingEdges
      data.toRotationSystem deleted
  have hfaces := card_transition_add_allOnSide_add_allOffSide_eq_faces
    data.toRotationSystem deleted
  have hedges := card_allOnSide_add_allOffSide_add_crossing_eq_edges
    data deleted
  have hvertices := sideVertexCount_add_complement
    (deletedRegionKeep deleted)
  have heuler := hsphere.euler
  have heulerNat : Fintype.card V +
      Fintype.card (OrbitFace data.toRotationSystem) =
        Fintype.card G.edgeSet + 2 := by
    omega
  have htransitionEq :
      (cutSideTransitionFaces data.toRotationSystem deleted).card =
        (vertexSetCrossingEdges data.toRotationSystem deleted).card :=
    Nat.le_antisymm htransitionLe hcrossingLe
  have hsumRanks :
      ((orbitFacesAllOnSide data.toRotationSystem
            (deletedRegionKeep deleted)).card +
          sideVertexCount (deletedRegionKeep deleted)) +
        ((orbitFacesAllOnSide data.toRotationSystem
            (fun vertex ↦ Not (deletedRegionKeep deleted vertex))).card +
          sideVertexCount
            (fun vertex ↦ Not (deletedRegionKeep deleted vertex))) =
      ((graphEdgesAllOnSide G (deletedRegionKeep deleted)).card + 1) +
        ((graphEdgesAllOnSide G
            (fun vertex ↦ Not (deletedRegionKeep deleted vertex))).card +
          1) := by
    omega
  constructor
  · omega
  constructor
  · omega
  · exact htransitionEq

/-- Removing one side of a planar bond satisfies the exact Euler balance
before any seam is chosen: removed edges plus one equal deleted vertices plus
ambient faces meeting the deleted side. -/
theorem planarBond_deletedRegionEulerBalance
    (data : Data G) (deleted : Finset V)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hretainedConnected :
      (G.induce {vertex | deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex |
        Not (deletedRegionKeep deleted vertex)}).Connected) :
    Fintype.card
        (RemovedEdge data.toRotationSystem (deletedRegionKeep deleted)) + 1 =
      Fintype.card (DeletedVertex (deletedRegionKeep deleted)) +
        Fintype.card (AmbientDeletedFaceOrbit data.toRotationSystem
          (deletedRegionKeep deleted)) := by
  have hranks := planarBond_exact_sideRanks_and_transitionCount
    data deleted hsphere htwoSided hconnected hrotation
      hretainedConnected hdeletedConnected
  have hambientRetained := card_ambientRetainedFaceOrbit_eq_allOnSide
    data.toRotationSystem (deletedRegionKeep deleted)
  have hretainedVertices :
      Fintype.card (RetainedVertex (deletedRegionKeep deleted)) =
        sideVertexCount (deletedRegionKeep deleted) := by
    exact (sideVertexCount_eq_card_sideVertex
      (deletedRegionKeep deleted)).symm
  have hretainedEdges := card_retainedInternalEdge_eq_allOnSide
    data (deletedRegionKeep deleted)
  have hretainedEuler :
      Fintype.card (AmbientRetainedFaceOrbit data.toRotationSystem
          (deletedRegionKeep deleted)) +
        Fintype.card (RetainedVertex (deletedRegionKeep deleted)) =
      Fintype.card (RetainedInternalEdge data.toRotationSystem
          (deletedRegionKeep deleted)) + 1 := by
    omega
  have hvertices := card_retainedVertex_add_card_deletedVertex
    (deletedRegionKeep deleted)
  have hedges := card_retainedInternalEdge_add_card_removedEdge
    data.toRotationSystem (deletedRegionKeep deleted)
  have hfaces := card_ambientRetained_add_deletedFaceOrbit
    data.toRotationSystem (deletedRegionKeep deleted)
  have heuler := hsphere.euler
  have hfaceCard := card_orbitFace_eq_faceCycleLengths_card
    data.toRotationSystem
  have heulerNat : Fintype.card V +
      (faceCycleLengths data.toRotationSystem).card =
        Fintype.card G.edgeSet + 2 := by
    omega
  omega

/-- For a planar bond presented as two equally sized ordered interfaces, the
actual splice face-return permutation has exactly `n + 1` cycles. The count is
derived from the ambient graph rotation: connectedness of both induced sides
reverses the deleted boundary order, while the seam cap is an involution. -/
theorem card_actualOrderedCutFaceReturnSuccessor_partition_of_planar_bond
    (data : Data G) (deleted : Finset V)
    (leftCrossing rightCrossing : Fin n → G.edgeSet)
    (hboundary : orderedCut leftCrossing ∪ orderedCut rightCrossing =
      vertexSetCrossingEdges data.toRotationSystem deleted)
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (hn : 0 < n)
    (horder : CutsFollowOppositeDeletedBoundaryOrder data.toRotationSystem
      deleted leftCrossing rightCrossing hboundary hleftInjective
      hrightInjective hdisjoint)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hretainedConnected :
      (G.induce {vertex | deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex |
        Not (deletedRegionKeep deleted vertex)}).Connected)
    (houter : data.toRotationSystem.vertOf data.toRotationSystem.outer ∉
      deleted) :
    let hleftCrosses := leftCrossing_outward data.toRotationSystem deleted
      leftCrossing rightCrossing hboundary
    let hrightCrosses := rightCrossing_outward data.toRotationSystem deleted
      leftCrossing rightCrossing hboundary
    let hcover := deletedRegionBoundaryCover data.toRotationSystem deleted
      leftCrossing rightCrossing hboundary
    (actualOrderedCutFaceReturnSuccessor data.toRotationSystem
      (deletedRegionKeep deleted) leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter).partition.parts.card = n + 1 := by
  dsimp only
  let positionEquiv := orderedRetainedBoundaryPositionEquiv
    data.toRotationSystem (deletedRegionKeep deleted)
      leftCrossing rightCrossing
      (leftCrossing_outward data.toRotationSystem deleted
        leftCrossing rightCrossing hboundary)
      (rightCrossing_outward data.toRotationSystem deleted
        leftCrossing rightCrossing hboundary)
      hleftInjective hrightInjective
      (deletedRegionBoundaryCover data.toRotationSystem deleted
        leftCrossing rightCrossing hboundary) hdisjoint
  let seamSwap := orderedBoundarySeamSwap data.toRotationSystem
    (deletedRegionKeep deleted) leftCrossing rightCrossing
      (leftCrossing_outward data.toRotationSystem deleted
        leftCrossing rightCrossing hboundary)
      (rightCrossing_outward data.toRotationSystem deleted
        leftCrossing rightCrossing hboundary)
      hleftInjective hrightInjective
      (deletedRegionBoundaryCover data.toRotationSystem deleted
        leftCrossing rightCrossing hboundary) hdisjoint
  have hretainedBoundary :
      retainedRegionBoundarySuccessor data.toRotationSystem
          (deletedRegionKeep deleted) =
        positionEquiv.permCongr (oppositeBoundaryCycle n)⁻¹ := by
    rw [retained_boundarySuccessor_eq_deleted_inverse_of_planar_bond
      data deleted hsphere htwoSided hconnected hrotation
      hretainedConnected hdeletedConnected, horder]
    rfl
  have hseamCoordinate :
      positionEquiv.symm.permCongr seamSwap =
        orderedPositionSeamSwap n := by
    exact orderedRetainedBoundaryPosition_seamSwap_congr
      data.toRotationSystem deleted leftCrossing rightCrossing hboundary
        hleftInjective hrightInjective hdisjoint
  have hactual :
      actualOrderedCutFaceReturnSuccessor data.toRotationSystem
          (deletedRegionKeep deleted) leftCrossing rightCrossing
          (leftCrossing_outward data.toRotationSystem deleted
            leftCrossing rightCrossing hboundary)
          (rightCrossing_outward data.toRotationSystem deleted
            leftCrossing rightCrossing hboundary)
          hleftInjective hrightInjective
          (deletedRegionBoundaryCover data.toRotationSystem deleted
            leftCrossing rightCrossing hboundary) hdisjoint houter =
        (oppositeBoundaryCycle n)⁻¹ * orderedPositionSeamSwap n := by
    rw [actualOrderedCutFaceReturnSuccessor_eq_retainedBoundarySuccessor,
      hretainedBoundary]
    change positionEquiv.symm.permCongr
        (positionEquiv.permCongr (oppositeBoundaryCycle n)⁻¹ * seamSwap) =
      (oppositeBoundaryCycle n)⁻¹ * orderedPositionSeamSwap n
    apply Equiv.ext
    intro position
    simp only [Equiv.permCongr_apply, Equiv.Perm.mul_apply,
      Equiv.symm_symm, Equiv.symm_apply_apply]
    exact congrArg
      (fun point => ((oppositeBoundaryCycle n)⁻¹ :
        Equiv.Perm (OrderedSeamPosition n)) point)
      (DFunLike.congr_fun hseamCoordinate position)
  rw [hactual]
  apply (card_inv_mul_involution_partition_eq
    (oppositeBoundaryCycle n) (orderedPositionSeamSwap n) ?_).trans
  exact card_oppositeBoundary_capPerm_partition hn
  apply Equiv.ext
  intro position
  rcases position with step | step <;>
    rfl

/-- The local annulus Euler equation required by the shortening splice is a
theorem for an actual planar bond; it is not an additional splice premise. -/
theorem retainedSpliceLocalEulerBalance_of_planar_bond
    (data : Data G) (deleted : Finset V)
    (leftCrossing rightCrossing : Fin n → G.edgeSet)
    (hboundary : orderedCut leftCrossing ∪ orderedCut rightCrossing =
      vertexSetCrossingEdges data.toRotationSystem deleted)
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (hn : 0 < n)
    (horder : CutsFollowOppositeDeletedBoundaryOrder data.toRotationSystem
      deleted leftCrossing rightCrossing hboundary hleftInjective
      hrightInjective hdisjoint)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hretainedConnected :
      (G.induce {vertex | deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex |
        Not (deletedRegionKeep deleted vertex)}).Connected)
    (houter : data.toRotationSystem.vertOf data.toRotationSystem.outer ∉
      deleted) :
    let hleftCrosses := leftCrossing_outward data.toRotationSystem deleted
      leftCrossing rightCrossing hboundary
    let hrightCrosses := rightCrossing_outward data.toRotationSystem deleted
      leftCrossing rightCrossing hboundary
    let hcover := deletedRegionBoundaryCover data.toRotationSystem deleted
      leftCrossing rightCrossing hboundary
    RetainedSpliceLocalEulerBalance data.toRotationSystem
      (deletedRegionKeep deleted) leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter := by
  dsimp only
  have hreturns :=
    card_actualOrderedCutFaceReturnSuccessor_partition_of_planar_bond
      data deleted leftCrossing rightCrossing hboundary hleftInjective
      hrightInjective hdisjoint hn horder hsphere htwoSided hconnected
      hrotation hretainedConnected hdeletedConnected houter
  have hdeletedEuler := planarBond_deletedRegionEulerBalance
    data deleted hsphere htwoSided hconnected hrotation
      hretainedConnected hdeletedConnected
  unfold RetainedSpliceLocalEulerBalance
  rw [hreturns]
  omega

/-- Shortening and gluing along an ordered planar bond preserves the
spherical cubic map class. The local Euler premise of the generic splice
constructor is discharged by the ambient planar-bond theorem above. -/
theorem orbitSphericalCubicMapData_orderedCutSplice_of_planar_bond
    (data : Data G) (deleted : Finset V)
    (leftCrossing rightCrossing : Fin n → G.edgeSet)
    (hboundary : orderedCut leftCrossing ∪ orderedCut rightCrossing =
      vertexSetCrossingEdges data.toRotationSystem deleted)
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (hn : 0 < n)
    (horder : CutsFollowOppositeDeletedBoundaryOrder data.toRotationSystem
      deleted leftCrossing rightCrossing hboundary hleftInjective
      hrightInjective hdisjoint)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hretainedConnected :
      (G.induce {vertex | deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex |
        Not (deletedRegionKeep deleted vertex)}).Connected)
    (houter : data.toRotationSystem.vertOf data.toRotationSystem.outer ∉
      deleted)
    (hseamEndpoints : ∀ step,
      data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (deletedRegionKeep deleted) leftCrossing
            (leftCrossing_outward data.toRotationSystem deleted
              leftCrossing rightCrossing hboundary) step).1.1.1 ≠
        data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (deletedRegionKeep deleted) rightCrossing
            (rightCrossing_outward data.toRotationSystem deleted
              leftCrossing rightCrossing hboundary) step).1.1.1) :
    OrbitSphericalCubicMapData
      (orderedCutRetainedVertexRotationSystem data.toRotationSystem
        (deletedRegionKeep deleted) leftCrossing rightCrossing
        (leftCrossing_outward data.toRotationSystem deleted
          leftCrossing rightCrossing hboundary)
        (rightCrossing_outward data.toRotationSystem deleted
          leftCrossing rightCrossing hboundary)
        hleftInjective hrightInjective
        (deletedRegionBoundaryCover data.toRotationSystem deleted
          leftCrossing rightCrossing hboundary)
        hdisjoint houter hseamEndpoints) := by
  have hbalance := retainedSpliceLocalEulerBalance_of_planar_bond
    data deleted leftCrossing rightCrossing hboundary hleftInjective
      hrightInjective hdisjoint hn horder hsphere htwoSided hconnected
      hrotation hretainedConnected hdeletedConnected houter
  have hambient : SphericalCubicMapData data.toRotationSystem := by
    refine ⟨hsphere.cubic, ?_⟩
    have hfaceCard := card_orbitFace_eq_faceCycleLengths_card
      data.toRotationSystem
    have heuler := hsphere.euler
    omega
  let shortened := orderedCutRetainedVertexRotationSystem
    data.toRotationSystem (deletedRegionKeep deleted)
      leftCrossing rightCrossing
      (leftCrossing_outward data.toRotationSystem deleted
        leftCrossing rightCrossing hboundary)
      (rightCrossing_outward data.toRotationSystem deleted
        leftCrossing rightCrossing hboundary)
      hleftInjective hrightInjective
      (deletedRegionBoundaryCover data.toRotationSystem deleted
        leftCrossing rightCrossing hboundary)
      hdisjoint houter hseamEndpoints
  have hshortened : SphericalCubicMapData shortened :=
    sphericalCubicMapData_orderedCutRetainedVertexRotationSystem
      data.toRotationSystem (deletedRegionKeep deleted)
        leftCrossing rightCrossing
        (leftCrossing_outward data.toRotationSystem deleted
          leftCrossing rightCrossing hboundary)
        (rightCrossing_outward data.toRotationSystem deleted
          leftCrossing rightCrossing hboundary)
        hleftInjective hrightInjective
        (deletedRegionBoundaryCover data.toRotationSystem deleted
          leftCrossing rightCrossing hboundary)
        hdisjoint houter hseamEndpoints hambient hbalance
  exact OrbitSphericalCubicMapData.ofSphericalCubicMapData
    shortened hshortened

end

end GoertzelV24PlanarBondSpliceEuler

end Mettapedia.GraphTheory.FourColor
