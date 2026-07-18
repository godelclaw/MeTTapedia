import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceSupport

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
open GoertzelV24SharedFacesTwoEdgeSeparator
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

private theorem edgeOrbitFacePairProfile_eq_disjoint_of_facePairs_disjoint
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {first second : G.edgeSet} (hne : first ≠ second)
    (hdisjoint : Disjoint (edgeOrbitFacePair graphData first)
      (edgeOrbitFacePair graphData second)) :
    edgeOrbitFacePairProfile graphData first second =
      EdgeOrbitFacePairProfile.disjoint := by
  have hcard := card_edgeOrbitFacePair_inter_eq_profile_of_minimal
    graphData minimal hne
  have hinter : (edgeOrbitFacePair graphData first) ∩
      (edgeOrbitFacePair graphData second) = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.mp hdisjoint
  have hzero : ((edgeOrbitFacePair graphData first) ∩
      (edgeOrbitFacePair graphData second)).card = 0 := by
    rw [hinter]
    rfl
  generalize hprofile : edgeOrbitFacePairProfile graphData first second =
    profile at hcard ⊢
  cases profile <;> simp_all

/-- The source cross of a fixed-face certified transition lies on that
face. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.source_cross_mem_face
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    {source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (transition : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData face source target) :
    retainedEdgeToAmbientEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) source.1 ∈
      orbitFaceBoundary graphData.toRotationSystem face := by
  rcases transition with ⟨step, _htarget, hface⟩
  rw [← hface]
  exact step.source_cross_mem_selectedFace

/-- The target cross of a fixed-face certified transition lies on that
face. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.target_cross_mem_face
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    {source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (transition : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData face source target) :
    retainedEdgeToAmbientEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) target.1 ∈
      orbitFaceBoundary graphData.toRotationSystem face := by
  rcases transition with ⟨step, rfl, hface⟩
  rw [← hface]
  exact step.target_cross_mem_selectedFace

/-- The face label of a fixed-face transition is one of the two faces
incident to its source cross. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.face_mem_source_facePair
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    {source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (transition : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData face source target) :
    face ∈ edgeOrbitFacePair graphData
      (retainedEdgeToAmbientEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) source.1) := by
  exact (mem_edgeOrbitFacePair_iff_mem_orbitFaceBoundary graphData minimal
    face _).2 transition.source_cross_mem_face

/-- The face label remains incident to the target cross. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.face_mem_target_facePair
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    {source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (transition : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData face source target) :
    face ∈ edgeOrbitFacePair graphData
      (retainedEdgeToAmbientEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) target.1) := by
  exact (mem_edgeOrbitFacePair_iff_mem_orbitFaceBoundary graphData minimal
    face _).2 transition.target_cross_mem_face

/-- Every selected transition face avoids the restored central edge. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.central_not_mem_face
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    {source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (transition : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData face source target) :
    centralEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) ∉
      orbitFaceBoundary graphData.toRotationSystem face := by
  rcases transition with ⟨step, _htarget, hface⟩
  rw [← hface]
  exact step.central_not_mem_selectedFace

/-- Every selected transition face avoids each restored boundary edge. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.boundary_not_mem_face
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    {source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (transition : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData face source target) (port : Fin 4) :
    boundaryEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) port ∉
      orbitFaceBoundary graphData.toRotationSystem face := by
  rcases transition with ⟨step, _htarget, hface⟩
  rw [← hface]
  exact step.boundary_not_mem_selectedFace port

/-- Equivalently, the selected face is absent from the central edge's
incident-face pair. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.face_not_mem_central_facePair
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    {source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (transition : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData face source target) :
    face ∉ edgeOrbitFacePair graphData
      (centralEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic)) := by
  rw [mem_edgeOrbitFacePair_iff_mem_orbitFaceBoundary graphData minimal]
  exact transition.central_not_mem_face

/-- The selected face is likewise absent from every restored boundary
edge's incident-face pair. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.face_not_mem_boundary_facePair
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    {source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (transition : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData face source target) (port : Fin 4) :
    face ∉ edgeOrbitFacePair graphData
      (boundaryEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) port) := by
  rw [mem_edgeOrbitFacePair_iff_mem_orbitFaceBoundary graphData minimal]
  exact transition.boundary_not_mem_face port

/-- A face-changing pair of consecutive certified rebases crosses the
middle retained edge between its two distinct face labels. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.middle_cross_mem_both_faces
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {firstFace secondFace : OrbitFace graphData.toRotationSystem}
    {source middle target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (first : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData firstFace source middle)
    (second : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData secondFace middle target) :
    retainedEdgeToAmbientEdge
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) middle.1 ∈
        orbitFaceBoundary graphData.toRotationSystem firstFace ∧
      retainedEdgeToAmbientEdge
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) middle.1 ∈
        orbitFaceBoundary graphData.toRotationSystem secondFace :=
  ⟨first.target_cross_mem_face, second.source_cross_mem_face⟩

/-- At a genuine face change, the two labels are exactly the full
incident-face pair of the middle cross. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.middle_cross_facePair_eq
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {firstFace secondFace : OrbitFace graphData.toRotationSystem}
    {source middle target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (first : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData firstFace source middle)
    (second : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData secondFace middle target)
    (hfaces : firstFace ≠ secondFace) :
    edgeOrbitFacePair graphData
        (retainedEdgeToAmbientEdge
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) middle.1) =
      {firstFace, secondFace} := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  have hincident := orbitFace_incidentFaces_eq_pair_of_mem
    graphData.toRotationSystem minimal.facesTwoSided hfaces
      (retainedEdgeToAmbientEdge data middle.1)
      first.target_cross_mem_face second.source_cross_mem_face
  ext face
  rw [mem_edgeOrbitFacePair_iff_mem_orbitFaceBoundary graphData minimal]
  have hmem := congrArg (fun faces => face ∈ faces) hincident
  simpa using hmem

/-- A face change can occur only at a fully remote cross: neither of its
incident faces is incident to the restored central edge. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.middle_cross_facePair_disjoint_central
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {firstFace secondFace : OrbitFace graphData.toRotationSystem}
    {source middle target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (first : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData firstFace source middle)
    (second : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData secondFace middle target)
    (hfaces : firstFace ≠ secondFace) :
    Disjoint (edgeOrbitFacePair graphData
      (retainedEdgeToAmbientEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) middle.1))
      (edgeOrbitFacePair graphData
        (centralEdge
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic))) := by
  rw [first.middle_cross_facePair_eq second hfaces,
    Finset.disjoint_left]
  intro face hpair hcentral
  simp only [Finset.mem_insert, Finset.mem_singleton] at hpair
  rcases hpair with rfl | rfl
  · exact first.face_not_mem_central_facePair hcentral
  · exact second.face_not_mem_central_facePair hcentral

/-- The same fully remote cross avoids the incident-face pair of every
restored boundary edge. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.middle_cross_facePair_disjoint_boundary
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {firstFace secondFace : OrbitFace graphData.toRotationSystem}
    {source middle target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (first : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData firstFace source middle)
    (second : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData secondFace middle target)
    (hfaces : firstFace ≠ secondFace) (port : Fin 4) :
    Disjoint (edgeOrbitFacePair graphData
      (retainedEdgeToAmbientEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) middle.1))
      (edgeOrbitFacePair graphData
        (boundaryEdge
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) port)) := by
  rw [first.middle_cross_facePair_eq second hfaces,
    Finset.disjoint_left]
  intro face hpair hboundary
  simp only [Finset.mem_insert, Finset.mem_singleton] at hpair
  rcases hpair with rfl | rfl
  · exact first.face_not_mem_boundary_facePair port hboundary
  · exact second.face_not_mem_boundary_facePair port hboundary

/-- Thus a face-changing middle cross is in the disjoint entry of the
exact cross/central face-pair profile table. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.middle_cross_central_profile_eq_disjoint
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {firstFace secondFace : OrbitFace graphData.toRotationSystem}
    {source middle target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (first : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData firstFace source middle)
    (second : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData secondFace middle target)
    (hfaces : firstFace ≠ secondFace) :
    edgeOrbitFacePairProfile graphData
        (retainedEdgeToAmbientEdge
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) middle.1)
        (centralEdge
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic)) =
      EdgeOrbitFacePairProfile.disjoint := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  exact edgeOrbitFacePairProfile_eq_disjoint_of_facePairs_disjoint
    graphData minimal
      (retainedEdgeToAmbientEdge_ne_centralEdge data middle.1)
      (first.middle_cross_facePair_disjoint_central second hfaces)

/-- Its profile against each restored boundary edge is disjoint as well. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.middle_cross_boundary_profile_eq_disjoint
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {firstFace secondFace : OrbitFace graphData.toRotationSystem}
    {source middle target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (first : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData firstFace source middle)
    (second : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData secondFace middle target)
    (hfaces : firstFace ≠ secondFace) (port : Fin 4) :
    edgeOrbitFacePairProfile graphData
        (retainedEdgeToAmbientEdge
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) middle.1)
        (boundaryEdge
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) port) =
      EdgeOrbitFacePairProfile.disjoint := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  exact edgeOrbitFacePairProfile_eq_disjoint_of_facePairs_disjoint
    graphData minimal
      (retainedEdgeToAmbientEdge_ne_boundaryEdge data middle.1 port)
      (first.middle_cross_facePair_disjoint_boundary second hfaces port)

/-- Face changes cannot immediately reverse across the same dual
adjacency: the unique common primal edge would have to be both the source
and target cross of the intervening rebase. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.no_immediate_face_backtrack
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {firstFace secondFace : OrbitFace graphData.toRotationSystem}
    {firstState secondState thirdState fourthState :
      CrossCentralExactFaceCutState graphData
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic)}
    (first : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData firstFace firstState secondState)
    (second : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData secondFace secondState thirdState)
    (third : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData firstFace thirdState fourthState)
    (hfaces : firstFace ≠ secondFace) : False := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  have hsecondCross : retainedEdgeToAmbientEdge data secondState.1 =
      retainedEdgeToAmbientEdge data thirdState.1 := by
    exact edge_eq_of_mem_distinct_orbitFace_pair graphData minimal hfaces
      first.target_cross_mem_face second.source_cross_mem_face
      third.source_cross_mem_face second.target_cross_mem_face
  have hcross : secondState.1 = thirdState.1 :=
    data.retainedEdgeToAmbientEdge_injective hsecondCross
  exact second.cross_ne hcross.symm

/-- A two-step closed certified rebase chain cannot change its selected
face. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.faces_eq_of_twoStep_cycle
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {firstFace secondFace : OrbitFace graphData.toRotationSystem}
    {firstState secondState : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (first : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData firstFace firstState secondState)
    (second : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData secondFace secondState firstState) :
    firstFace = secondFace := by
  by_contra hfaces
  exact first.no_immediate_face_backtrack second first hfaces

/-- If the first two labels differ in a three-step closed chain, then all
three labels are pairwise distinct.  Thus its face projection is a genuine
dual triangle rather than a two-face oscillation. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.pairwise_faces_ne_of_threeStep_cycle
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {firstFace secondFace thirdFace :
      OrbitFace graphData.toRotationSystem}
    {firstState secondState thirdState :
      CrossCentralExactFaceCutState graphData
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic)}
    (first : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData firstFace firstState secondState)
    (second : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData secondFace secondState thirdState)
    (third : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData thirdFace thirdState firstState)
    (hfirstSecond : firstFace ≠ secondFace) :
    firstFace ≠ secondFace ∧ secondFace ≠ thirdFace ∧
      thirdFace ≠ firstFace := by
  refine ⟨hfirstSecond, ?_, ?_⟩
  · intro hsecondThird
    let data := baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic
    have hambient : retainedEdgeToAmbientEdge data firstState.1 =
        retainedEdgeToAmbientEdge data secondState.1 := by
      exact edge_eq_of_mem_distinct_orbitFace_pair graphData minimal
        hfirstSecond first.source_cross_mem_face
          (hsecondThird ▸ third.target_cross_mem_face)
          first.target_cross_mem_face second.source_cross_mem_face
    have hcross : firstState.1 = secondState.1 :=
      data.retainedEdgeToAmbientEdge_injective hambient
    exact first.cross_ne hcross.symm
  · intro hthirdFirst
    subst thirdFace
    exact first.no_immediate_face_backtrack second third hfirstSecond

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
