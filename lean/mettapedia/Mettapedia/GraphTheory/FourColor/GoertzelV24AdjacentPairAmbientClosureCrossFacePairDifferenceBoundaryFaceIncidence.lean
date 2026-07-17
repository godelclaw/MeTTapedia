import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceCentralReturnTransfer

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Among the restored boundary edges, an indexed central return uses
exactly its selected first- and second-side edges. -/
theorem boundaryEdgeValue_mem_crossSidePortCentralReturn_edges_iff
    (data : AdjacentPairData G) (first second : Fin 2) (port : Fin 4) :
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdgeValue
        data port ∈ (data.crossSidePortCentralReturn first second).edges ↔
      port = firstSidePort first ∨ port = secondSidePort second := by
  rw [data.crossSidePortCentralReturn_edges]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (hsecond | hcentral | hfirst)
    · exact Or.inr
        (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdgeValue_injective
          data hsecond)
    · exact False.elim
        (GoertzelV24AdjacentPairInsertion.AdjacentPairData.centralEdgeValue_ne_boundaryEdgeValue
          data port hcentral.symm)
    · exact Or.inl
        (GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdgeValue_injective
          data hfirst)
  · rintro (rfl | rfl)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Closing a retained indexed channel adds exactly its two selected
boundary edges and no other restored boundary edge. -/
theorem boundaryEdgeValue_mem_crossSidePortClosure_edges_iff
    (data : AdjacentPairData G) (first second : Fin 2)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk
        (data.retainedPort (firstSidePort first))
        (data.retainedPort (secondSidePort second)))
    (port : Fin 4) :
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.boundaryEdgeValue
        data port ∈ (data.crossSidePortClosure first second path).edges ↔
      port = firstSidePort first ∨ port = secondSidePort second := by
  rw [data.crossSidePortClosure_edges, List.mem_append]
  constructor
  · rintro (hretained | hreturn)
    · exact False.elim
        (data.boundaryEdgeValue_not_mem_retainedWalkToAmbient_edges
          path port hretained)
    · exact
        (data.boundaryEdgeValue_mem_crossSidePortCentralReturn_edges_iff
          first second port).1 hreturn
  · intro hport
    exact Or.inr
      ((data.boundaryEdgeValue_mem_crossSidePortCentralReturn_edges_iff
        first second port).2 hport)

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24MinimalFaceIntersections
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality

/-- The original opposite closures use the boundary index corresponding to
the selected binary cut coordinate. -/
def crossFaceCoordinateSideIndex (coordinate : Bool) : Fin 2 :=
  finTwoEquiv.symm coordinate

@[simp] theorem finTwoEquiv_crossFaceCoordinateSideIndex
    (coordinate : Bool) :
    finTwoEquiv (crossFaceCoordinateSideIndex coordinate) = coordinate := by
  exact finTwoEquiv.apply_symm_apply coordinate

@[simp] theorem crossFaceCoordinateSideIndex_false :
    crossFaceCoordinateSideIndex false = 0 := by
  rfl

@[simp] theorem crossFaceCoordinateSideIndex_true :
    crossFaceCoordinateSideIndex true = 1 := by
  rfl

private theorem f2_ne_zero_iff_eq_one (value : F2) :
    value ≠ 0 ↔ value = 1 := by
  constructor
  · intro hvalue
    fin_cases value
    · exact False.elim (hvalue rfl)
    · rfl
  · intro hvalue hzero
    exact zero_ne_one (hzero.symm.trans hvalue)

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- On the first restored side, the exact paired closure coordinate is
nonzero exactly at its original coordinate-indexed boundary edge. -/
theorem CrossCentralExactFaceCutPair.crossFaceCoordinate_edgeTransfer_firstSide_ne_zero_iff
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (coordinate : Bool) (candidate : Fin 2) :
    crossFaceCoordinate coordinate
        (pair.edgeTransfer
          (boundaryEdge data (firstSidePort candidate))) ≠ 0 ↔
      candidate = crossFaceCoordinateSideIndex coordinate := by
  cases coordinate
  · change (pair.edgeTransfer
      (boundaryEdge data (firstSidePort candidate))).1 ≠ 0 ↔ _
    rw [f2_ne_zero_iff_eq_one,
      pair.edgeTransfer_fst_eq_one_iff minimal]
    change boundaryEdgeValue data (firstSidePort candidate) ∈
        (data.oppositePortClosure pair.prefixTrail).edges ↔ _
    rw [data.boundaryEdgeValue_mem_oppositePortClosure_edges_iff]
    fin_cases candidate <;> simp
  · change (pair.edgeTransfer
      (boundaryEdge data (firstSidePort candidate))).2 ≠ 0 ↔ _
    rw [f2_ne_zero_iff_eq_one,
      pair.edgeTransfer_snd_eq_one_iff minimal]
    change boundaryEdgeValue data (firstSidePort candidate) ∈
        (data.crossSidePortClosure 1 1 pair.suffixTrail).edges ↔ _
    rw [data.boundaryEdgeValue_mem_crossSidePortClosure_edges_iff]
    fin_cases candidate <;> simp

/-- The same exact coordinate-indexed boundary support holds on the second
restored side. -/
theorem CrossCentralExactFaceCutPair.crossFaceCoordinate_edgeTransfer_secondSide_ne_zero_iff
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (coordinate : Bool) (candidate : Fin 2) :
    crossFaceCoordinate coordinate
        (pair.edgeTransfer
          (boundaryEdge data (secondSidePort candidate))) ≠ 0 ↔
      candidate = crossFaceCoordinateSideIndex coordinate := by
  cases coordinate
  · change (pair.edgeTransfer
      (boundaryEdge data (secondSidePort candidate))).1 ≠ 0 ↔ _
    rw [f2_ne_zero_iff_eq_one,
      pair.edgeTransfer_fst_eq_one_iff minimal]
    change boundaryEdgeValue data (secondSidePort candidate) ∈
        (data.oppositePortClosure pair.prefixTrail).edges ↔ _
    rw [data.boundaryEdgeValue_mem_oppositePortClosure_edges_iff]
    fin_cases candidate <;> simp
  · change (pair.edgeTransfer
      (boundaryEdge data (secondSidePort candidate))).2 ≠ 0 ↔ _
    rw [f2_ne_zero_iff_eq_one,
      pair.edgeTransfer_snd_eq_one_iff minimal]
    change boundaryEdgeValue data (secondSidePort candidate) ∈
        (data.crossSidePortClosure 1 1 pair.suffixTrail).edges ↔ _
    rw [data.boundaryEdgeValue_mem_crossSidePortClosure_edges_iff]
    fin_cases candidate <;> simp

/-- Coordinate projection commutes with the decomposition of the difference
profile into its exact-closure and singleton cross-face summands. -/
theorem CrossCentralExactFaceCutPair.crossFaceCoordinate_differenceProfile
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (coordinate : Bool) (edge : G.edgeSet) :
    crossFaceCoordinate coordinate
        (pair.crossFaceDifferenceProfile edge) =
      crossFaceCoordinate coordinate (pair.edgeTransfer edge) +
        crossFaceCoordinate coordinate
          (edgeCrossFaceProfile graphData
            (retainedEdgeToAmbientEdge data cross) edge) := by
  cases coordinate
  · rfl
  · rfl

private theorem f2_face_ne_zero_iff_xor_support
    (exact face : F2) :
    face ≠ 0 ↔ Xor (exact ≠ 0) (exact + face ≠ 0) := by
  constructor
  · intro hface
    have hfaceOne := (f2_ne_zero_iff_eq_one face).1 hface
    by_cases hexact : exact = 0
    · exact Or.inr ⟨by simp [hexact, hfaceOne],
        fun hnonzero => hnonzero hexact⟩
    · have hexactOne := (f2_ne_zero_iff_eq_one exact).1 hexact
      exact Or.inl ⟨hexact, by simp [hexactOne, hfaceOne]⟩
  · intro hxor hface
    subst face
    rcases hxor with hleft | hright
    · exact hleft.2 (by simpa using hleft.1)
    · exact hright.2 (by simpa using hright.1)

private theorem finTwo_xor_candidate_eq_iff_ne
    (candidate original selected : Fin 2) :
    Xor (candidate = original) (candidate = selected) ↔
      original ≠ selected := by
  fin_cases candidate <;> fin_cases original <;>
    fin_cases selected <;> decide

private theorem f2_face_support_iff_originalIndex_ne_selectedIndex
    (candidate original selected : Fin 2) (exact face : F2)
    (hexact : exact ≠ 0 ↔ candidate = original)
    (hdifference : exact + face ≠ 0 ↔ candidate = selected) :
    face ≠ 0 ↔ original ≠ selected := by
  rw [f2_face_ne_zero_iff_xor_support, hexact, hdifference,
    finTwo_xor_candidate_eq_iff_ne]

/-- On the first restored side, toggling the selected singleton cross face
either changes neither boundary edge or changes both. It changes both
exactly when the new channel index differs from the original coordinate
index. -/
theorem CrossCentralExactFaceCutPair.crossFaceCoordinate_singletonProfile_firstSide_ne_zero_iff
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (coordinate : Bool) (firstIndex : Fin 2)
    (hfirstExact : ∀ candidate : Fin 2,
      crossFaceCoordinate coordinate
          (pair.crossFaceDifferenceProfile
            (boundaryEdge data (firstSidePort candidate))) ≠ 0 ↔
        candidate = firstIndex) :
    ∀ candidate : Fin 2,
      crossFaceCoordinate coordinate
          (edgeCrossFaceProfile graphData
            (retainedEdgeToAmbientEdge data cross)
            (boundaryEdge data (firstSidePort candidate))) ≠ 0 ↔
        crossFaceCoordinateSideIndex coordinate ≠ firstIndex := by
  intro candidate
  have hdifference := hfirstExact candidate
  rw [pair.crossFaceCoordinate_differenceProfile] at hdifference
  exact f2_face_support_iff_originalIndex_ne_selectedIndex candidate
    (crossFaceCoordinateSideIndex coordinate) firstIndex
    (crossFaceCoordinate coordinate
      (pair.edgeTransfer
        (boundaryEdge data (firstSidePort candidate))))
    (crossFaceCoordinate coordinate
      (edgeCrossFaceProfile graphData
        (retainedEdgeToAmbientEdge data cross)
        (boundaryEdge data (firstSidePort candidate))))
    (pair.crossFaceCoordinate_edgeTransfer_firstSide_ne_zero_iff
      minimal coordinate candidate) hdifference

/-- The corresponding singleton cross face changes both or neither boundary
edges on the second restored side, with the same index criterion. -/
theorem CrossCentralExactFaceCutPair.crossFaceCoordinate_singletonProfile_secondSide_ne_zero_iff
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (coordinate : Bool) (secondIndex : Fin 2)
    (hsecondExact : ∀ candidate : Fin 2,
      crossFaceCoordinate coordinate
          (pair.crossFaceDifferenceProfile
            (boundaryEdge data (secondSidePort candidate))) ≠ 0 ↔
        candidate = secondIndex) :
    ∀ candidate : Fin 2,
      crossFaceCoordinate coordinate
          (edgeCrossFaceProfile graphData
            (retainedEdgeToAmbientEdge data cross)
            (boundaryEdge data (secondSidePort candidate))) ≠ 0 ↔
        crossFaceCoordinateSideIndex coordinate ≠ secondIndex := by
  intro candidate
  have hdifference := hsecondExact candidate
  rw [pair.crossFaceCoordinate_differenceProfile] at hdifference
  exact f2_face_support_iff_originalIndex_ne_selectedIndex candidate
    (crossFaceCoordinateSideIndex coordinate) secondIndex
    (crossFaceCoordinate coordinate
      (pair.edgeTransfer
        (boundaryEdge data (secondSidePort candidate))))
    (crossFaceCoordinate coordinate
      (edgeCrossFaceProfile graphData
        (retainedEdgeToAmbientEdge data cross)
        (boundaryEdge data (secondSidePort candidate))))
    (pair.crossFaceCoordinate_edgeTransfer_secondSide_ne_zero_iff
      minimal coordinate candidate) hdifference

/-- The quotient face selected by one coordinate of the two singleton
cross-face generators. -/
def edgeCrossFaceCoordinateOrbitFace
    (graphData : SimpleGraphDartRotation.Data G) (source : G.edgeSet)
    (coordinate : Bool) :
    OrbitFace graphData.toRotationSystem :=
  if coordinate then edgeRightOrbitFace graphData source
  else edgeLeftOrbitFace graphData source

/-- A coordinate of the singleton cross-face profile is nonzero on an edge
exactly when its selected quotient face is incident to that edge. -/
theorem crossFaceCoordinate_edgeCrossFaceProfile_ne_zero_iff
    (graphData : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (source edge : G.edgeSet) (coordinate : Bool) :
    crossFaceCoordinate coordinate
        (edgeCrossFaceProfile graphData source edge) ≠ 0 ↔
      edgeCrossFaceCoordinateOrbitFace graphData source coordinate ∈
        edgeOrbitFacePair graphData edge := by
  rw [f2_ne_zero_iff_eq_one]
  cases coordinate
  · exact orbitFaceBoundaryLinearMap_singletonOrbitFaceLabels_eq_one_iff
      graphData minimal.facesTwoSided (edgeLeftOrbitFace graphData source) edge
  · exact orbitFaceBoundaryLinearMap_singletonOrbitFaceLabels_eq_one_iff
      graphData minimal.facesTwoSided (edgeRightOrbitFace graphData source) edge

private theorem one_add_f2_ne_zero_iff_eq_zero (value : F2) :
    1 + value ≠ 0 ↔ value = 0 := by
  constructor
  · intro hsum
    by_contra hvalue
    have hone := (f2_ne_zero_iff_eq_one value).1 hvalue
    apply hsum
    rw [hone, zmod2_add_self]
  · rintro rfl
    exact one_ne_zero

/-- The quotient face selected by either singleton coordinate is one of the
two quotient faces incident to its source edge. -/
theorem edgeCrossFaceCoordinateOrbitFace_mem_source
    (graphData : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (source : G.edgeSet) (coordinate : Bool) :
    edgeCrossFaceCoordinateOrbitFace graphData source coordinate ∈
      edgeOrbitFacePair graphData source := by
  apply (crossFaceCoordinate_edgeCrossFaceProfile_ne_zero_iff
    graphData minimal source source coordinate).1
  rw [edgeCrossFaceProfile_source graphData minimal source]
  cases coordinate <;> decide

/-- If the repaired difference keeps a coordinate on the restored central
edge, then the corresponding singleton cross face avoids that edge.  The
exact closure contributes one there, so nonvanishing forces the singleton
face contribution to be zero. -/
theorem CrossCentralExactFaceCutPair.selectedFace_not_mem_centralFacePair
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (coordinate : Bool)
    (hcentral : crossFaceCoordinate coordinate
      (pair.crossFaceDifferenceProfile (centralEdge data)) ≠ 0) :
    edgeCrossFaceCoordinateOrbitFace graphData
        (retainedEdgeToAmbientEdge data cross) coordinate ∉
      edgeOrbitFacePair graphData (centralEdge data) := by
  intro hmem
  have hface : crossFaceCoordinate coordinate
      (edgeCrossFaceProfile graphData
        (retainedEdgeToAmbientEdge data cross) (centralEdge data)) ≠ 0 :=
    (crossFaceCoordinate_edgeCrossFaceProfile_ne_zero_iff
      graphData minimal (retainedEdgeToAmbientEdge data cross)
        (centralEdge data) coordinate).2 hmem
  have hdifference := hcentral
  rw [pair.crossFaceCoordinate_differenceProfile] at hdifference
  have hexact : crossFaceCoordinate coordinate
      (pair.edgeTransfer (centralEdge data)) = 1 := by
    rw [pair.edgeTransfer_centralEdge minimal]
    cases coordinate <;> rfl
  rw [hexact] at hdifference
  exact hface ((one_add_f2_ne_zero_iff_eq_zero _).1 hdifference)

/-- The selected cross-side singleton face uses the exterior turn through
the two first-side boundary edges. -/
def CrossCentralExactFaceCutPair.CrossFaceUsesFirstExteriorTurn
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (_pair : CrossCentralExactFaceCutPair graphData data cross)
    (coordinate : Bool) : Prop :=
  crossFaceCoordinate coordinate
      (edgeCrossFaceProfile graphData
        (retainedEdgeToAmbientEdge data cross)
        (boundaryEdge data (firstSidePort 0))) ≠ 0

/-- The analogous exterior-turn incidence at the second restored vertex. -/
def CrossCentralExactFaceCutPair.CrossFaceUsesSecondExteriorTurn
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (_pair : CrossCentralExactFaceCutPair graphData data cross)
    (coordinate : Bool) : Prop :=
  crossFaceCoordinate coordinate
      (edgeCrossFaceProfile graphData
        (retainedEdgeToAmbientEdge data cross)
        (boundaryEdge data (secondSidePort 0))) ≠ 0

/-- First-side exterior-turn incidence is exactly a change of boundary
channel index from the original cut coordinate. -/
theorem CrossCentralExactFaceCutPair.crossFaceUsesFirstExteriorTurn_iff
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (coordinate : Bool) (firstIndex : Fin 2)
    (hfirstExact : ∀ candidate : Fin 2,
      crossFaceCoordinate coordinate
          (pair.crossFaceDifferenceProfile
            (boundaryEdge data (firstSidePort candidate))) ≠ 0 ↔
        candidate = firstIndex) :
    pair.CrossFaceUsesFirstExteriorTurn coordinate ↔
      crossFaceCoordinateSideIndex coordinate ≠ firstIndex := by
  exact pair.crossFaceCoordinate_singletonProfile_firstSide_ne_zero_iff
    minimal coordinate firstIndex hfirstExact 0

/-- Second-side exterior-turn incidence has the identical index
characterization. -/
theorem CrossCentralExactFaceCutPair.crossFaceUsesSecondExteriorTurn_iff
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (coordinate : Bool) (secondIndex : Fin 2)
    (hsecondExact : ∀ candidate : Fin 2,
      crossFaceCoordinate coordinate
          (pair.crossFaceDifferenceProfile
            (boundaryEdge data (secondSidePort candidate))) ≠ 0 ↔
        candidate = secondIndex) :
    pair.CrossFaceUsesSecondExteriorTurn coordinate ↔
      crossFaceCoordinateSideIndex coordinate ≠ secondIndex := by
  exact pair.crossFaceCoordinate_singletonProfile_secondSide_ne_zero_iff
    minimal coordinate secondIndex hsecondExact 0

/-- Under the exact boundary signature, first-side exterior-turn incidence
means that the selected cross face is incident to both first-side boundary
edges. -/
theorem CrossCentralExactFaceCutPair.crossFaceUsesFirstExteriorTurn_iff_selectedFace_incident_both
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (coordinate : Bool) (firstIndex : Fin 2)
    (hfirstExact : ∀ candidate : Fin 2,
      crossFaceCoordinate coordinate
          (pair.crossFaceDifferenceProfile
            (boundaryEdge data (firstSidePort candidate))) ≠ 0 ↔
        candidate = firstIndex) :
    pair.CrossFaceUsesFirstExteriorTurn coordinate ↔
      ∀ candidate : Fin 2,
        edgeCrossFaceCoordinateOrbitFace graphData
            (retainedEdgeToAmbientEdge data cross) coordinate ∈
          edgeOrbitFacePair graphData
            (boundaryEdge data (firstSidePort candidate)) := by
  constructor
  · intro hturn candidate
    have hindex := (pair.crossFaceUsesFirstExteriorTurn_iff minimal
      coordinate firstIndex hfirstExact).1 hturn
    have hprofile :=
      (pair.crossFaceCoordinate_singletonProfile_firstSide_ne_zero_iff
        minimal coordinate firstIndex hfirstExact candidate).2 hindex
    exact (crossFaceCoordinate_edgeCrossFaceProfile_ne_zero_iff
      graphData minimal (retainedEdgeToAmbientEdge data cross)
        (boundaryEdge data (firstSidePort candidate)) coordinate).1 hprofile
  · intro hboth
    have hprofile :=
      (crossFaceCoordinate_edgeCrossFaceProfile_ne_zero_iff
        graphData minimal (retainedEdgeToAmbientEdge data cross)
          (boundaryEdge data (firstSidePort 0)) coordinate).2 (hboth 0)
    have hindex :=
      (pair.crossFaceCoordinate_singletonProfile_firstSide_ne_zero_iff
        minimal coordinate firstIndex hfirstExact 0).1 hprofile
    exact (pair.crossFaceUsesFirstExteriorTurn_iff minimal coordinate
      firstIndex hfirstExact).2 hindex

/-- The same actual quotient-face incidence characterization holds at the
second restored vertex. -/
theorem CrossCentralExactFaceCutPair.crossFaceUsesSecondExteriorTurn_iff_selectedFace_incident_both
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (coordinate : Bool) (secondIndex : Fin 2)
    (hsecondExact : ∀ candidate : Fin 2,
      crossFaceCoordinate coordinate
          (pair.crossFaceDifferenceProfile
            (boundaryEdge data (secondSidePort candidate))) ≠ 0 ↔
        candidate = secondIndex) :
    pair.CrossFaceUsesSecondExteriorTurn coordinate ↔
      ∀ candidate : Fin 2,
        edgeCrossFaceCoordinateOrbitFace graphData
            (retainedEdgeToAmbientEdge data cross) coordinate ∈
          edgeOrbitFacePair graphData
            (boundaryEdge data (secondSidePort candidate)) := by
  constructor
  · intro hturn candidate
    have hindex := (pair.crossFaceUsesSecondExteriorTurn_iff minimal
      coordinate secondIndex hsecondExact).1 hturn
    have hprofile :=
      (pair.crossFaceCoordinate_singletonProfile_secondSide_ne_zero_iff
        minimal coordinate secondIndex hsecondExact candidate).2 hindex
    exact (crossFaceCoordinate_edgeCrossFaceProfile_ne_zero_iff
      graphData minimal (retainedEdgeToAmbientEdge data cross)
        (boundaryEdge data (secondSidePort candidate)) coordinate).1 hprofile
  · intro hboth
    have hprofile :=
      (crossFaceCoordinate_edgeCrossFaceProfile_ne_zero_iff
        graphData minimal (retainedEdgeToAmbientEdge data cross)
          (boundaryEdge data (secondSidePort 0)) coordinate).2 (hboth 0)
    have hindex :=
      (pair.crossFaceCoordinate_singletonProfile_secondSide_ne_zero_iff
        minimal coordinate secondIndex hsecondExact 0).1 hprofile
    exact (pair.crossFaceUsesSecondExteriorTurn_iff minimal coordinate
      secondIndex hsecondExact).2 hindex

/-- The exact mixed-channel condition is geometric: the selected singleton
cross face uses the exterior turn at exactly one of the two restored
vertices. -/
theorem CrossCentralExactFaceCutPair.mixedChannel_iff_crossFaceUsesExactlyOneExteriorTurn
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (coordinate : Bool) (firstIndex secondIndex : Fin 2)
    (hfirstExact : ∀ candidate : Fin 2,
      crossFaceCoordinate coordinate
          (pair.crossFaceDifferenceProfile
            (boundaryEdge data (firstSidePort candidate))) ≠ 0 ↔
        candidate = firstIndex)
    (hsecondExact : ∀ candidate : Fin 2,
      crossFaceCoordinate coordinate
          (pair.crossFaceDifferenceProfile
            (boundaryEdge data (secondSidePort candidate))) ≠ 0 ↔
        candidate = secondIndex) :
    firstIndex ≠ secondIndex ↔
      Xor (pair.CrossFaceUsesFirstExteriorTurn coordinate)
        (pair.CrossFaceUsesSecondExteriorTurn coordinate) := by
  rw [pair.crossFaceUsesFirstExteriorTurn_iff minimal coordinate
      firstIndex hfirstExact,
    pair.crossFaceUsesSecondExteriorTurn_iff minimal coordinate
      secondIndex hsecondExact]
  fin_cases coordinate <;> fin_cases firstIndex <;>
    fin_cases secondIndex <;> decide

/-- The exact closed-transfer criterion stated entirely in quotient-face
geometry: after the route parity is compensated, identity means that the
selected cross face is incident to both boundary edges at exactly one
restored vertex. -/
theorem CrossCentralExactFaceCutPair.exists_exactCrossSideClosedTransfer_faceIncidenceCriterion
    {graphData : SimpleGraphDartRotation.Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    ∃ (coordinate : Bool) (firstIndex secondIndex : Fin 2)
        (path : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort (firstSidePort firstIndex))
            (data.retainedPort (secondSidePort secondIndex))),
      path.IsPath ∧
        (cross : Sym2 (retainedVertexSet data.firstVertex
          data.secondVertex)) ∉ path.edges ∧
        crossFaceCoordinate coordinate
            (pair.crossFaceDifferenceProfile (centralEdge data)) ≠ 0 ∧
        (∀ candidate : Fin 2,
          crossFaceCoordinate coordinate
              (pair.crossFaceDifferenceProfile
                (boundaryEdge data (firstSidePort candidate))) ≠ 0 ↔
            candidate = firstIndex) ∧
        (∀ candidate : Fin 2,
          crossFaceCoordinate coordinate
              (pair.crossFaceDifferenceProfile
                (boundaryEdge data (secondSidePort candidate))) ≠ 0 ↔
            candidate = secondIndex) ∧
        (data.crossSidePortClosure firstIndex secondIndex path).IsCycle ∧
        pair.centralReturnCoordinateParity coordinate
            firstIndex secondIndex = 1 ∧
        (rejectedCrossCentralReturnClosedTransfer firstIndex secondIndex =
              Equiv.refl (Bool × Bool) ↔
          Xor
            (∀ candidate : Fin 2,
              edgeCrossFaceCoordinateOrbitFace graphData
                  (retainedEdgeToAmbientEdge data cross) coordinate ∈
                edgeOrbitFacePair graphData
                  (boundaryEdge data (firstSidePort candidate)))
            (∀ candidate : Fin 2,
              edgeCrossFaceCoordinateOrbitFace graphData
                  (retainedEdgeToAmbientEdge data cross) coordinate ∈
                edgeOrbitFacePair graphData
                  (boundaryEdge data (secondSidePort candidate)))) := by
  rcases pair.exists_exactCrossSideClosedTransfer minimal with
    ⟨coordinate, firstIndex, secondIndex, path, hpath, hcross,
      hcentral, hfirstExact, hsecondExact, hcycle, hparity,
      _hreturnApply, hclosed⟩
  have hmixed :=
    pair.mixedChannel_iff_crossFaceUsesExactlyOneExteriorTurn minimal
      coordinate firstIndex secondIndex hfirstExact hsecondExact
  have hfirstFace :=
    pair.crossFaceUsesFirstExteriorTurn_iff_selectedFace_incident_both
      minimal coordinate firstIndex hfirstExact
  have hsecondFace :=
    pair.crossFaceUsesSecondExteriorTurn_iff_selectedFace_incident_both
      minimal coordinate secondIndex hsecondExact
  refine ⟨coordinate, firstIndex, secondIndex, path, hpath, hcross, hcentral,
    hfirstExact, hsecondExact, hcycle, hparity, ?_⟩
  calc
    rejectedCrossCentralReturnClosedTransfer firstIndex secondIndex =
          Equiv.refl (Bool × Bool) ↔
        firstIndex ≠ secondIndex := hclosed
    _ ↔ Xor (pair.CrossFaceUsesFirstExteriorTurn coordinate)
          (pair.CrossFaceUsesSecondExteriorTurn coordinate) := hmixed
    _ ↔ Xor
          (∀ candidate : Fin 2,
            edgeCrossFaceCoordinateOrbitFace graphData
                (retainedEdgeToAmbientEdge data cross) coordinate ∈
              edgeOrbitFacePair graphData
                (boundaryEdge data (firstSidePort candidate)))
          (∀ candidate : Fin 2,
            edgeCrossFaceCoordinateOrbitFace graphData
                (retainedEdgeToAmbientEdge data cross) coordinate ∈
              edgeOrbitFacePair graphData
                (boundaryEdge data (secondSidePort candidate))) := by
            rw [hfirstFace, hsecondFace]

/-- The compensated cross witness also identifies the selected quotient
face globally: it is incident to the retained cross and avoids the restored
central edge.  Its closed transfer is trivial exactly when that face takes
the exterior turn at one, and only one, restored vertex. -/
theorem CrossCentralExactFaceCutPair.exists_exactCrossSideClosedTransfer_selectedFaceGeometry
    {graphData : SimpleGraphDartRotation.Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    ∃ (coordinate : Bool) (firstIndex secondIndex : Fin 2)
        (path : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort (firstSidePort firstIndex))
            (data.retainedPort (secondSidePort secondIndex))),
      path.IsPath ∧
        (cross : Sym2 (retainedVertexSet data.firstVertex
          data.secondVertex)) ∉ path.edges ∧
        crossFaceCoordinate coordinate
            (pair.crossFaceDifferenceProfile (centralEdge data)) ≠ 0 ∧
        (∀ candidate : Fin 2,
          crossFaceCoordinate coordinate
              (pair.crossFaceDifferenceProfile
                (boundaryEdge data (firstSidePort candidate))) ≠ 0 ↔
            candidate = firstIndex) ∧
        (∀ candidate : Fin 2,
          crossFaceCoordinate coordinate
              (pair.crossFaceDifferenceProfile
                (boundaryEdge data (secondSidePort candidate))) ≠ 0 ↔
            candidate = secondIndex) ∧
        (data.crossSidePortClosure firstIndex secondIndex path).IsCycle ∧
        pair.centralReturnCoordinateParity coordinate
            firstIndex secondIndex = 1 ∧
        edgeCrossFaceCoordinateOrbitFace graphData
            (retainedEdgeToAmbientEdge data cross) coordinate ∈
          edgeOrbitFacePair graphData
            (retainedEdgeToAmbientEdge data cross) ∧
        edgeCrossFaceCoordinateOrbitFace graphData
            (retainedEdgeToAmbientEdge data cross) coordinate ∉
          edgeOrbitFacePair graphData (centralEdge data) ∧
        (rejectedCrossCentralReturnClosedTransfer firstIndex secondIndex =
              Equiv.refl (Bool × Bool) ↔
          Xor
            (∀ candidate : Fin 2,
              edgeCrossFaceCoordinateOrbitFace graphData
                  (retainedEdgeToAmbientEdge data cross) coordinate ∈
                edgeOrbitFacePair graphData
                  (boundaryEdge data (firstSidePort candidate)))
            (∀ candidate : Fin 2,
              edgeCrossFaceCoordinateOrbitFace graphData
                  (retainedEdgeToAmbientEdge data cross) coordinate ∈
                edgeOrbitFacePair graphData
                  (boundaryEdge data (secondSidePort candidate)))) := by
  rcases pair.exists_exactCrossSideClosedTransfer_faceIncidenceCriterion
      minimal with
    ⟨coordinate, firstIndex, secondIndex, path, hpath, hcross,
      hcentral, hfirstExact, hsecondExact, hcycle, hparity, hcriterion⟩
  exact ⟨coordinate, firstIndex, secondIndex, path, hpath, hcross,
    hcentral, hfirstExact, hsecondExact, hcycle, hparity,
    edgeCrossFaceCoordinateOrbitFace_mem_source graphData minimal
      (retainedEdgeToAmbientEdge data cross) coordinate,
    pair.selectedFace_not_mem_centralFacePair minimal coordinate hcentral,
    hcriterion⟩

/-- In the rejected zero-fusion `bc` residual, the selected face is incident
to the actual cross and avoids the central edge; the actual combined
transfer closes trivially exactly when this face uses the two boundary edges
at exactly one restored vertex. -/
theorem EvenKempeFusionLens.exists_bcClosedTransfer_faceIncidenceCriterion_of_rejected_of_zeroFusion
    (graphData : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hcount : (lens01.bcCrossSites lens23).length ≤ 1)
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (hfalse : EvenKempeFusionLens.bcCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false)
    (hzero01 : lens01.fusionSiteCount = 0)
    (hzero23 : lens23.fusionSiteCount = 0) :
    ∃ (pair : CrossCentralExactFaceCutPair graphData data site.1)
        (coordinate : Bool) (firstIndex secondIndex : Fin 2)
        (path : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort (firstSidePort firstIndex))
            (data.retainedPort (secondSidePort secondIndex))),
      path.IsPath ∧
        (site.1 : Sym2 (retainedVertexSet data.firstVertex
          data.secondVertex)) ∉ path.edges ∧
        (data.crossSidePortClosure firstIndex secondIndex path).IsCycle ∧
        pair.centralReturnCoordinateParity coordinate
            firstIndex secondIndex = 1 ∧
        edgeCrossFaceCoordinateOrbitFace graphData
            (retainedEdgeToAmbientEdge data site.1) coordinate ∈
          edgeOrbitFacePair graphData
            (retainedEdgeToAmbientEdge data site.1) ∧
        edgeCrossFaceCoordinateOrbitFace graphData
            (retainedEdgeToAmbientEdge data site.1) coordinate ∉
          edgeOrbitFacePair graphData (centralEdge data) ∧
        (crossSideCentralReturnCutTransfer firstIndex secondIndex *
              EvenKempeFusionLens.bcCombinedSignedTransfer
                lens01 graphData lens23 hab hac hbc site =
              Equiv.refl (Bool × Bool) ↔
          Xor
            (∀ candidate : Fin 2,
              edgeCrossFaceCoordinateOrbitFace graphData
                  (retainedEdgeToAmbientEdge data site.1) coordinate ∈
                edgeOrbitFacePair graphData
                  (boundaryEdge data (firstSidePort candidate)))
            (∀ candidate : Fin 2,
              edgeCrossFaceCoordinateOrbitFace graphData
                  (retainedEdgeToAmbientEdge data site.1) coordinate ∈
                edgeOrbitFacePair graphData
                  (boundaryEdge data (secondSidePort candidate)))) := by
  rcases EvenKempeFusionLens.exists_bcCrossCentralExactFaceCutPair_of_rejected
      graphData minimal data lens01 lens23 hdata hab hac hbc hbDisjoint
        hcDisjoint hcount site hfalse with
    ⟨pair, _hprefixEdges, _hsuffixEdges⟩
  rcases pair.exists_exactCrossSideClosedTransfer_selectedFaceGeometry
      minimal with
    ⟨coordinate, firstIndex, secondIndex, path, hpath, hcross,
      _hcentral, _hfirstExact, _hsecondExact, hcycle, hparity,
      hsource, hnotCentral, hcriterion⟩
  refine ⟨pair, coordinate, firstIndex, secondIndex, path, hpath, hcross,
    hcycle, hparity, hsource, hnotCentral, ?_⟩
  rw [EvenKempeFusionLens.bcCombinedSignedTransfer_eq_diagonal_of_rejected_of_fusionSiteCounts_eq_zero
    graphData data lens01 lens23 hab hac hbc site hfalse hzero01 hzero23]
  simpa only [rejectedCrossCentralReturnClosedTransfer] using hcriterion

/-- The complementary rejected zero-fusion `cb` residual satisfies the same
source incidence, central-edge avoidance, and exact quotient-face
criterion. -/
theorem EvenKempeFusionLens.exists_cbClosedTransfer_faceIncidenceCriterion_of_rejected_of_zeroFusion
    (graphData : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hcount : (lens01.cbCrossSites lens23).length ≤ 1)
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (hfalse : EvenKempeFusionLens.cbCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false)
    (hzero01 : lens01.fusionSiteCount = 0)
    (hzero23 : lens23.fusionSiteCount = 0) :
    ∃ (pair : CrossCentralExactFaceCutPair graphData data site.1)
        (coordinate : Bool) (firstIndex secondIndex : Fin 2)
        (path : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort (firstSidePort firstIndex))
            (data.retainedPort (secondSidePort secondIndex))),
      path.IsPath ∧
        (site.1 : Sym2 (retainedVertexSet data.firstVertex
          data.secondVertex)) ∉ path.edges ∧
        (data.crossSidePortClosure firstIndex secondIndex path).IsCycle ∧
        pair.centralReturnCoordinateParity coordinate
            firstIndex secondIndex = 1 ∧
        edgeCrossFaceCoordinateOrbitFace graphData
            (retainedEdgeToAmbientEdge data site.1) coordinate ∈
          edgeOrbitFacePair graphData
            (retainedEdgeToAmbientEdge data site.1) ∧
        edgeCrossFaceCoordinateOrbitFace graphData
            (retainedEdgeToAmbientEdge data site.1) coordinate ∉
          edgeOrbitFacePair graphData (centralEdge data) ∧
        (crossSideCentralReturnCutTransfer firstIndex secondIndex *
              EvenKempeFusionLens.cbCombinedSignedTransfer
                lens01 graphData lens23 hab hac hbc site =
              Equiv.refl (Bool × Bool) ↔
          Xor
            (∀ candidate : Fin 2,
              edgeCrossFaceCoordinateOrbitFace graphData
                  (retainedEdgeToAmbientEdge data site.1) coordinate ∈
                edgeOrbitFacePair graphData
                  (boundaryEdge data (firstSidePort candidate)))
            (∀ candidate : Fin 2,
              edgeCrossFaceCoordinateOrbitFace graphData
                  (retainedEdgeToAmbientEdge data site.1) coordinate ∈
                edgeOrbitFacePair graphData
                  (boundaryEdge data (secondSidePort candidate)))) := by
  rcases EvenKempeFusionLens.exists_cbCrossCentralExactFaceCutPair_of_rejected
      graphData minimal data lens01 lens23 hdata hab hac hbc hbDisjoint
        hcDisjoint hcount site hfalse with
    ⟨pair, _hprefixEdges, _hsuffixEdges⟩
  rcases pair.exists_exactCrossSideClosedTransfer_selectedFaceGeometry
      minimal with
    ⟨coordinate, firstIndex, secondIndex, path, hpath, hcross,
      _hcentral, _hfirstExact, _hsecondExact, hcycle, hparity,
      hsource, hnotCentral, hcriterion⟩
  refine ⟨pair, coordinate, firstIndex, secondIndex, path, hpath, hcross,
    hcycle, hparity, hsource, hnotCentral, ?_⟩
  rw [EvenKempeFusionLens.cbCombinedSignedTransfer_eq_diagonal_of_rejected_of_fusionSiteCounts_eq_zero
    graphData data lens01 lens23 hab hac hbc site hfalse hzero01 hzero23]
  simpa only [rejectedCrossCentralReturnClosedTransfer] using hcriterion

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
