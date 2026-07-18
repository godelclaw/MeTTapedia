import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceWalk

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
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

theorem CrossCentralExactFaceCutPair.prefixLabels_ne_iff_mem_of_facePair_eq
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (edge : G.edgeSet)
    (left right : OrbitFace graphData.toRotationSystem)
    (hpair : edgeOrbitFacePair graphData edge = {left, right}) :
    pair.prefixLabels left ≠ pair.prefixLabels right ↔
      edge.1 ∈ (data.oppositePortClosure pair.prefixTrail).edges := by
  let RS := graphData.toRotationSystem
  let dart := RS.dartRepresentative edge
  have hedge : RS.edgeOf dart = edge := RS.dartRepresentative_edgeOf edge
  have hdartFaces : dartOrbitFace RS dart ≠
      dartOrbitFace RS (RS.alpha dart) := minimal.facesTwoSided dart
  have hleftMem : dartOrbitFace RS dart = left ∨
      dartOrbitFace RS dart = right := by
    have hmem : dartOrbitFace RS dart ∈ edgeOrbitFacePair graphData edge := by
      simp [edgeOrbitFacePair, RS, dart]
    rw [hpair] at hmem
    simpa using hmem
  have hrightMem : dartOrbitFace RS (RS.alpha dart) = left ∨
      dartOrbitFace RS (RS.alpha dart) = right := by
    have hmem : dartOrbitFace RS (RS.alpha dart) ∈
        edgeOrbitFacePair graphData edge := by
      simp [edgeOrbitFacePair, RS, dart]
    rw [hpair] at hmem
    simpa using hmem
  have hexact := pair.prefixExact dart
  rw [hedge] at hexact
  change pair.prefixLabels (dartOrbitFace RS dart) ≠
      pair.prefixLabels (dartOrbitFace RS (RS.alpha dart)) ↔
    edge.1 ∈ (data.oppositePortClosure pair.prefixTrail).edges at hexact
  rcases hleftMem with hleft | hleft <;>
      rcases hrightMem with hright | hright
  · exact False.elim (hdartFaces (hleft.trans hright.symm))
  · simpa [hleft, hright] using hexact
  · simpa [hleft, hright, ne_comm] using hexact
  · exact False.elim (hdartFaces (hleft.trans hright.symm))

/-- A provenance-certified three-step closed rebase chain cannot change
face on its first step. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.not_threeStep_cycle_of_faces_ne
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
    (hfirstSecond : firstFace ≠ secondFace) : False := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  rcases first.pairwise_faces_ne_of_threeStep_cycle second third hfirstSecond with
    ⟨hfirstSecond, hsecondThird, hthirdFirst⟩
  have hfirstPair := third.middle_cross_facePair_eq first hthirdFirst
  have hsecondPair := first.middle_cross_facePair_eq second hfirstSecond
  have hthirdPair := second.middle_cross_facePair_eq third hsecondThird
  have hsecondOffThird : retainedEdgeToAmbientEdge data secondState.1 ∉
      orbitFaceBoundary graphData.toRotationSystem thirdFace := by
    intro hmem
    have hface : thirdFace ∈ edgeOrbitFacePair graphData
        (retainedEdgeToAmbientEdge data secondState.1) :=
      (mem_edgeOrbitFacePair_iff_mem_orbitFaceBoundary
        graphData minimal thirdFace _).2 hmem
    rw [hsecondPair] at hface
    simp only [Finset.mem_insert, Finset.mem_singleton] at hface
    rcases hface with hthirdFirst' | hthirdSecond
    · exact hthirdFirst hthirdFirst'
    · exact hsecondThird hthirdSecond.symm
  have hsecondNotFirstPrefix : secondState.1.1 ∉
      firstState.2.prefixTrail.edges := by
    intro hmem
    have hsource := third.target_prefix_offFace_subset_source
      secondState.1 hsecondOffThird hmem
    exact second.to_transition.target_trails_avoid_source_cross.1 hsource
  have hthirdNotFirstPrefix : thirdState.1.1 ∉
      firstState.2.prefixTrail.edges :=
    third.to_transition.target_trails_avoid_source_cross.1
  have hsecondNotFirstClosure :
      (retainedEdgeToAmbientEdge data secondState.1).1 ∉
        (data.oppositePortClosure firstState.2.prefixTrail).edges := by
    intro hmem
    exact hsecondNotFirstPrefix
      ((retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff
        data firstState.2.prefixTrail secondState.1).1 hmem)
  have hthirdNotFirstClosure :
      (retainedEdgeToAmbientEdge data thirdState.1).1 ∉
        (data.oppositePortClosure firstState.2.prefixTrail).edges := by
    intro hmem
    exact hthirdNotFirstPrefix
      ((retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff
        data firstState.2.prefixTrail thirdState.1).1 hmem)
  have hfirstLabelsNe :
      firstState.2.prefixLabels thirdFace ≠
        firstState.2.prefixLabels firstFace :=
    (firstState.2.prefixLabels_ne_iff_mem_of_facePair_eq minimal
      (retainedEdgeToAmbientEdge data firstState.1)
      thirdFace firstFace hfirstPair).2
        firstState.2.cross_mem_oppositePortClosure
  have hfirstSecondLabelsEq :
      firstState.2.prefixLabels firstFace =
        firstState.2.prefixLabels secondFace := by
    by_contra hne
    exact hsecondNotFirstClosure
      ((firstState.2.prefixLabels_ne_iff_mem_of_facePair_eq minimal
        (retainedEdgeToAmbientEdge data secondState.1)
        firstFace secondFace hsecondPair).1 hne)
  have hsecondThirdLabelsEq :
      firstState.2.prefixLabels secondFace =
        firstState.2.prefixLabels thirdFace := by
    by_contra hne
    exact hthirdNotFirstClosure
      ((firstState.2.prefixLabels_ne_iff_mem_of_facePair_eq minimal
        (retainedEdgeToAmbientEdge data thirdState.1)
        secondFace thirdFace hthirdPair).1 hne)
  exact hfirstLabelsNe
    (hsecondThirdLabelsEq.symm.trans hfirstSecondLabelsEq.symm)

/-- The first two face labels in every three-step closed certified rebase
chain coincide. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.first_second_faces_eq_of_threeStep_cycle
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
      graphData minimal baseData thirdFace thirdState firstState) :
    firstFace = secondFace := by
  by_contra hfaces
  exact first.not_threeStep_cycle_of_faces_ne second third hfaces

/-- All three face labels in a three-step closed certified rebase chain
coincide. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.faces_eq_of_threeStep_cycle
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
      graphData minimal baseData thirdFace thirdState firstState) :
    firstFace = secondFace ∧ secondFace = thirdFace :=
  ⟨first.first_second_faces_eq_of_threeStep_cycle second third,
    second.first_second_faces_eq_of_threeStep_cycle third first⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData
end
end Mettapedia.GraphTheory.FourColor
