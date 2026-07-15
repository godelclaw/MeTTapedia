import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedRegionRotationSplice
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedSpliceEuler

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DeletedRegionEuler

open scoped BigOperators

open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24RetainedSpliceEuler
open GoertzelV24RetainedSpliceEdgeCount
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The abstract deleted-vertex carrier specializes to the actual finite
deleted region. -/
def deletedVertexEquivFinset
    (deleted : Finset V) :
    DeletedVertex (deletedRegionKeep deleted) ≃ ↥deleted where
  toFun vertex := ⟨vertex.1, by
    simpa [deletedRegionKeep] using vertex.2⟩
  invFun vertex := ⟨vertex.1, by
    simpa [deletedRegionKeep] using vertex.2⟩
  left_inv vertex := Subtype.ext rfl
  right_inv vertex := Subtype.ext rfl

/-- Consequently the abstract deleted-vertex count is the finset card. -/
theorem card_deletedVertex_deletedRegionKeep
    (deleted : Finset V) :
    Fintype.card (DeletedVertex (deletedRegionKeep deleted)) =
      deleted.card := by
  rw [Fintype.card_congr (deletedVertexEquivFinset deleted)]
  exact Fintype.card_coe deleted

/-- For a concrete finite deletion, an edge lacks a complete retained dart
fiber exactly when it meets the deleted vertex set. -/
theorem removedEdge_iff_mem_vertexSetRegionEdges
    (RS : RotationSystem V E) (deleted : Finset V) (edge : E) :
    Not (exists dart : InternalDart RS (deletedRegionKeep deleted),
        RS.edgeOf dart.1.1 = edge) ↔
      edge ∈ vertexSetRegionEdges RS deleted := by
  constructor
  · intro hremoved
    rw [mem_vertexSetRegionEdges_iff]
    by_contra houtside
    rcases RS.dartsOn_nonempty edge with ⟨dart, hdart⟩
    have hdartKeep : deletedRegionKeep deleted (RS.vertOf dart) := by
      intro hdartDeleted
      apply houtside
      refine ⟨RS.vertOf dart, ?_, hdartDeleted⟩
      exact (RS.mem_endpoints_iff).2 ⟨dart, hdart, rfl⟩
    have halphaKeep :
        deletedRegionKeep deleted (RS.vertOf (RS.alpha dart)) := by
      intro halphaDeleted
      apply houtside
      refine ⟨RS.vertOf (RS.alpha dart), ?_, halphaDeleted⟩
      exact (RS.mem_endpoints_iff).2
        ⟨RS.alpha dart, RS.alpha_mem_dartsOn hdart, rfl⟩
    apply hremoved
    exact ⟨⟨⟨dart, hdartKeep⟩, halphaKeep⟩,
      (RS.mem_dartsOn).1 hdart⟩
  · intro hregion
    intro hinterior
    rcases hinterior with ⟨dart, hedge⟩
    rw [mem_vertexSetRegionEdges_iff] at hregion
    rcases hregion with ⟨vertex, hvertexEndpoint, hvertexDeleted⟩
    have hdartOn : dart.1.1 ∈ RS.dartsOn edge := by
      rw [RS.mem_dartsOn, hedge]
    have hendpoints := RS.endpoints_eq_pair_of_mem hdartOn
    rw [hendpoints] at hvertexEndpoint
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvertexEndpoint
    rcases hvertexEndpoint with rfl | rfl
    · exact dart.1.2 hvertexDeleted
    · exact dart.2 hvertexDeleted

/-- Removed edges are canonically the actual endpoint-computed regional edge
finset. -/
def removedEdgeEquivVertexSetRegionEdge
    (RS : RotationSystem V E) (deleted : Finset V) :
    RemovedEdge RS (deletedRegionKeep deleted) ≃
      ↥(vertexSetRegionEdges RS deleted) where
  toFun edge := ⟨edge.1,
    (removedEdge_iff_mem_vertexSetRegionEdges RS deleted edge.1).1 edge.2⟩
  invFun edge := ⟨edge.1,
    (removedEdge_iff_mem_vertexSetRegionEdges RS deleted edge.1).2 edge.2⟩
  left_inv edge := Subtype.ext rfl
  right_inv edge := Subtype.ext rfl

/-- Hence the removed-edge count is the regional-edge finset card. -/
theorem card_removedEdge_deletedRegionKeep
    (RS : RotationSystem V E) (deleted : Finset V) :
    Fintype.card (RemovedEdge RS (deletedRegionKeep deleted)) =
      (vertexSetRegionEdges RS deleted).card := by
  rw [Fintype.card_congr
    (removedEdgeEquivVertexSetRegionEdge RS deleted)]
  exact Fintype.card_coe _

/-- Endpoint incidence over a finite vertex region can be counted either by
vertices or by ambient edges. -/
theorem sum_incidentEdgeCards_eq_sum_endpointMultiplicities
    (RS : RotationSystem V E) (deleted : Finset V) :
    ∑ vertex ∈ deleted, (RS.incidentEdges vertex).card =
      ∑ edge : E, (RS.endpoints edge ∩ deleted).card := by
  classical
  calc
    ∑ vertex ∈ deleted, (RS.incidentEdges vertex).card =
        ∑ vertex ∈ deleted,
          ∑ edge : E, if edge ∈ RS.incidentEdges vertex then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro vertex _
      rw [← Finset.sum_filter]
      have hfilter :
          Finset.univ.filter
              (fun edge : E => edge ∈ RS.incidentEdges vertex) =
            RS.incidentEdges vertex := by
        ext edge
        simp
      rw [hfilter]
      simp
    _ = ∑ edge : E,
          ∑ vertex ∈ deleted,
            if edge ∈ RS.incidentEdges vertex then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ edge : E, (RS.endpoints edge ∩ deleted).card := by
      apply Finset.sum_congr rfl
      intro edge _
      rw [← Finset.sum_filter]
      have hfilter :
          deleted.filter (fun vertex => edge ∈ RS.incidentEdges vertex) =
            deleted ∩ RS.endpoints edge := by
        ext vertex
        simp only [Finset.mem_filter, Finset.mem_inter]
        rw [← RS.mem_endpoints_iff_mem_incidentEdges]
      rw [hfilter]
      simp [Finset.inter_comm]

/-- A regional edge contributes two endpoint incidences, except that a
crossing edge contributes one. This is the cardinality form before cubicity
is used. -/
theorem twice_regionEdges_card_eq_endpointMultiplicities_add_crossingEdges
    (RS : RotationSystem V E) (deleted : Finset V) :
    2 * (vertexSetRegionEdges RS deleted).card =
      (∑ edge : E, (RS.endpoints edge ∩ deleted).card) +
        (vertexSetCrossingEdges RS deleted).card := by
  classical
  let region := vertexSetRegionEdges RS deleted
  let crossing := vertexSetCrossingEdges RS deleted
  calc
    2 * region.card = ∑ edge ∈ region, 2 := by simp [Nat.mul_comm]
    _ = ∑ edge : E, if edge ∈ region then 2 else 0 := by
      rw [← Finset.sum_filter]
      simp
    _ = ∑ edge : E,
          ((RS.endpoints edge ∩ deleted).card +
            if edge ∈ crossing then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro edge _
      by_cases hcrossing : edge ∈ crossing
      · have hregion : edge ∈ region :=
          vertexSetCrossingEdges_subset_regionEdges RS deleted hcrossing
        have hintersection :
            (RS.endpoints edge ∩ deleted).card = 1 :=
          (edgeCrossesVertexSet_iff_card_inter_eq_one RS deleted edge).1
            ((mem_vertexSetCrossingEdges_iff RS deleted edge).1 hcrossing)
        simp [hregion, hcrossing, hintersection]
      · by_cases hregion : edge ∈ region
        · have hsubset : RS.endpoints edge ⊆ deleted :=
            endpoints_subset_of_mem_region_not_mem_crossing RS deleted
              hregion hcrossing
          have hintersection : RS.endpoints edge ∩ deleted =
              RS.endpoints edge := Finset.inter_eq_left.2 hsubset
          simp [hregion, hcrossing, hintersection,
            RS.endpoints_card_two edge]
        · have hdisjoint : Disjoint (RS.endpoints edge) deleted :=
            endpoints_disjoint_of_not_mem_region RS deleted hregion
          have hintersection : RS.endpoints edge ∩ deleted = ∅ := by
            ext vertex
            simp only [Finset.mem_inter]
            constructor
            · rintro ⟨hendpoint, hdeleted⟩
              exact (Finset.disjoint_left.1 hdisjoint
                hendpoint hdeleted).elim
            · intro hempty
              simp at hempty
          simp [hregion, hcrossing, hintersection]
    _ = (∑ edge : E, (RS.endpoints edge ∩ deleted).card) +
          ∑ edge : E, if edge ∈ crossing then 1 else 0 := by
      rw [Finset.sum_add_distrib]
    _ = (∑ edge : E, (RS.endpoints edge ∩ deleted).card) +
          crossing.card := by
      rw [← Finset.sum_filter]
      simp

/-- Cubicity turns the regional incidence count into the exact finite-slab
identity `2 E_region = 3 V_region + boundary`. -/
theorem twice_regionEdges_card_eq_three_vertices_add_crossingEdges
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (deleted : Finset V) :
    2 * (vertexSetRegionEdges RS deleted).card =
      3 * deleted.card + (vertexSetCrossingEdges RS deleted).card := by
  rw [twice_regionEdges_card_eq_endpointMultiplicities_add_crossingEdges,
    ← sum_incidentEdgeCards_eq_sum_endpointMultiplicities]
  congr 1
  calc
    ∑ vertex ∈ deleted, (RS.incidentEdges vertex).card =
        ∑ _vertex ∈ deleted, 3 := by
      apply Finset.sum_congr rfl
      intro vertex _
      exact RS.incidentEdges_card_eq_three_of_isCubic hcubic vertex
    _ = 3 * deleted.card := by simp [Nat.mul_comm]

/-- An injective ordered cut has exactly its declared width. -/
theorem card_orderedCut_of_injective
    (crossing : Fin n → E) (hinjective : Function.Injective crossing) :
    (orderedCut crossing).card = n := by
  unfold orderedCut
  rw [Finset.card_image_iff.mpr hinjective.injOn]
  simp

/-- Two disjoint injective ordered cuts that cover the actual vertex boundary
give exactly twice the declared width in crossing edges. -/
theorem card_vertexSetCrossingEdges_eq_twice_width
    (RS : RotationSystem V E) (deleted : Finset V)
    (leftCrossing rightCrossing : Fin n → E)
    (hboundary : orderedCut leftCrossing ∪ orderedCut rightCrossing =
      vertexSetCrossingEdges RS deleted)
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing)) :
    (vertexSetCrossingEdges RS deleted).card = 2 * n := by
  calc
    (vertexSetCrossingEdges RS deleted).card =
        (orderedCut leftCrossing ∪ orderedCut rightCrossing).card := by
      rw [hboundary]
    _ = (orderedCut leftCrossing).card +
          (orderedCut rightCrossing).card :=
      Finset.card_union_of_disjoint hdisjoint
    _ = n + n := by
      rw [card_orderedCut_of_injective leftCrossing hleftInjective,
        card_orderedCut_of_injective rightCrossing hrightInjective]
    _ = 2 * n := by omega

/-- In a cubic region with a boundary of size `2 * width`, the regional Euler
count is equivalent to a pure face-return count. This is the remaining local
geometry required by the shortening splice. -/
theorem regionalEulerCount_iff_deletedVertices_add_twice_returnFaces
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (deleted : Finset V) (width returnFaces touchedFaces : Nat)
    (hboundaryCard :
      (vertexSetCrossingEdges RS deleted).card = 2 * width) :
    (vertexSetRegionEdges RS deleted).card + returnFaces =
        deleted.card + width + touchedFaces ↔
      deleted.card + 2 * returnFaces = 2 * touchedFaces := by
  have hincidence :=
    twice_regionEdges_card_eq_three_vertices_add_crossingEdges
      RS hcubic deleted
  rw [hboundaryCard] at hincidence
  omega

/-- The local Euler predicate for a finite deleted region is exactly the
literal regional count: regional edges plus completed return faces equal
deleted vertices, seam width, and ambient faces meeting the region. -/
theorem retainedSpliceLocalEulerBalance_deletedRegionKeep_iff
    (RS : RotationSystem V E) (deleted : Finset V)
    (leftCrossing rightCrossing : Fin n -> E)
    (hleftCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = leftCrossing step /\
      deletedRegionKeep deleted (RS.vertOf dart) /\
      Not (deletedRegionKeep deleted
        (RS.vertOf (RS.alpha dart))))
    (hrightCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = rightCrossing step /\
      deletedRegionKeep deleted (RS.vertOf dart) /\
      Not (deletedRegionKeep deleted
        (RS.vertOf (RS.alpha dart))))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : forall dart : BoundaryDart RS (deletedRegionKeep deleted),
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing \/
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (houter : deletedRegionKeep deleted (RS.vertOf RS.outer)) :
    RetainedSpliceLocalEulerBalance RS (deletedRegionKeep deleted)
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter ↔
      (vertexSetRegionEdges RS deleted).card +
          (GoertzelV24OrderedCutFaceReturnProfile.actualOrderedCutFaceReturnSuccessor
            RS (deletedRegionKeep deleted)
            leftCrossing rightCrossing hleftCrosses hrightCrosses
            hleftInjective hrightInjective hcover hdisjoint houter).partition.parts.card =
        deleted.card + n +
          Fintype.card
            (AmbientDeletedFaceOrbit RS (deletedRegionKeep deleted)) := by
  unfold RetainedSpliceLocalEulerBalance
  rw [card_removedEdge_deletedRegionKeep RS deleted,
    card_deletedVertex_deletedRegionKeep deleted]

/-- For an actual cubic deleted region bounded by two ordered transversals,
Euler preservation of the shortened rotation system is equivalent to the
remaining face-return equation. All vertex, edge, and boundary terms have
been discharged from rotation-system incidence. -/
theorem retainedSpliceLocalEulerBalance_of_boundary_iff_faceReturnCount
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (deleted : Finset V) (leftCrossing rightCrossing : Fin n → E)
    (hboundary : orderedCut leftCrossing ∪ orderedCut rightCrossing =
      vertexSetCrossingEdges RS deleted)
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (houter : RS.vertOf RS.outer ∉ deleted) :
    let hleftCrosses := leftCrossing_outward RS deleted
      leftCrossing rightCrossing hboundary
    let hrightCrosses := rightCrossing_outward RS deleted
      leftCrossing rightCrossing hboundary
    let hcover := deletedRegionBoundaryCover RS deleted
      leftCrossing rightCrossing hboundary
    let houterKeep : deletedRegionKeep deleted (RS.vertOf RS.outer) := houter
    RetainedSpliceLocalEulerBalance RS (deletedRegionKeep deleted)
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houterKeep ↔
      deleted.card + 2 *
          (GoertzelV24OrderedCutFaceReturnProfile.actualOrderedCutFaceReturnSuccessor
            RS (deletedRegionKeep deleted)
            leftCrossing rightCrossing hleftCrosses hrightCrosses
            hleftInjective hrightInjective hcover hdisjoint
            houterKeep).partition.parts.card =
        2 * Fintype.card
          (AmbientDeletedFaceOrbit RS (deletedRegionKeep deleted)) := by
  dsimp only
  rw [retainedSpliceLocalEulerBalance_deletedRegionKeep_iff]
  exact regionalEulerCount_iff_deletedVertices_add_twice_returnFaces
    RS hcubic deleted n
    (GoertzelV24OrderedCutFaceReturnProfile.actualOrderedCutFaceReturnSuccessor
      RS (deletedRegionKeep deleted)
      leftCrossing rightCrossing
      (leftCrossing_outward RS deleted leftCrossing rightCrossing hboundary)
      (rightCrossing_outward RS deleted leftCrossing rightCrossing hboundary)
      hleftInjective hrightInjective
      (deletedRegionBoundaryCover RS deleted leftCrossing rightCrossing
        hboundary)
      hdisjoint houter).partition.parts.card
    (Fintype.card
      (AmbientDeletedFaceOrbit RS (deletedRegionKeep deleted)))
    (card_vertexSetCrossingEdges_eq_twice_width RS deleted
      leftCrossing rightCrossing hboundary hleftInjective hrightInjective
      hdisjoint)

end

end GoertzelV24DeletedRegionEuler

end Mettapedia.GraphTheory.FourColor
