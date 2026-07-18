import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicFaceBoundaryCycleRigidity
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseTriangularMonodromy

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24PrimalCycleSpace
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24WalkCycleParity
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

/-- Along a same-face three-step closed rebase chain, the binary difference
of two consecutive prefix closures is exactly the selected facial boundary. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.prefixParity_add_support_eq_face_of_threeStep_cycle
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    {firstState secondState thirdState :
      CrossCentralExactFaceCutState graphData
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic)}
    (first : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData face firstState secondState)
    (second : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData face secondState thirdState)
    (third : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData face thirdState firstState) :
    let data := baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic
    ∀ edge : G.edgeSet,
      ((walkEdgeParity
          (data.oppositePortClosure firstState.2.prefixTrail) +
        walkEdgeParity
          (data.oppositePortClosure secondState.2.prefixTrail)) edge ≠ 0 ↔
        edge ∈ orbitFaceBoundary graphData.toRotationSystem face) := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  let firstClosure := data.oppositePortClosure firstState.2.prefixTrail
  let secondClosure := data.oppositePortClosure secondState.2.prefixTrail
  let thirdClosure := data.oppositePortClosure thirdState.2.prefixTrail
  let difference :=
    walkEdgeParity firstClosure + walkEdgeParity secondClosure
  change ∀ edge : G.edgeSet, difference edge ≠ 0 ↔
    edge ∈ orbitFaceBoundary graphData.toRotationSystem face
  have hdifferenceCycle : difference ∈ f2CycleSpace G := by
    exact (f2CycleSpace G).add_mem
      (walkEdgeParity_mem_f2CycleSpace_of_closed firstClosure)
      (walkEdgeParity_mem_f2CycleSpace_of_closed secondClosure)
  have hdifferenceSupport : ∀ edge : G.edgeSet, difference edge ≠ 0 →
      edge ∈ orbitFaceBoundary graphData.toRotationSystem face := by
    intro edge hnonzero
    by_contra hoff
    have hmemIff : edge.1 ∈ firstClosure.edges ↔
        edge.1 ∈ secondClosure.edges := by
      constructor
      · intro hfirst
        have hthird : edge.1 ∈ thirdClosure.edges := by
          exact third.target_prefixClosure_offFace_subset_source edge hoff
            hfirst
        exact second.target_prefixClosure_offFace_subset_source edge hoff
          hthird
      · intro hsecond
        exact first.target_prefixClosure_offFace_subset_source edge hoff
          hsecond
    have hparity :=
      walkEdgeParity_apply_eq_of_isTrail_of_mem_edges_iff
        firstState.2.prefixTrail_isTrail
        secondState.2.prefixTrail_isTrail edge hmemIff
    apply hnonzero
    change walkEdgeParity firstClosure edge +
      walkEdgeParity secondClosure edge = 0
    rw [hparity, zmod2_add_self]
  let anchor := retainedEdgeToAmbientEdge data firstState.1
  have hanchorFirst : anchor.1 ∈ firstClosure.edges := by
    exact firstState.2.cross_mem_oppositePortClosure
  have hanchorSecond : anchor.1 ∉ secondClosure.edges := by
    intro hmem
    apply first.to_transition.target_trails_avoid_source_cross.1
    exact
      ((retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff
        data secondState.2.prefixTrail firstState.1).1 hmem)
  have hanchorFirstParity : walkEdgeParity firstClosure anchor = 1 :=
    walkEdgeParity_apply_eq_one_of_isTrail_of_mem_edges
      firstState.2.prefixTrail_isTrail anchor hanchorFirst
  have hanchorSecondParity : walkEdgeParity secondClosure anchor = 0 :=
    walkEdgeParity_apply_eq_zero_of_not_mem_edges secondClosure anchor
      hanchorSecond
  have hanchorNonzero : difference anchor ≠ 0 := by
    change walkEdgeParity firstClosure anchor +
      walkEdgeParity secondClosure anchor ≠ 0
    rw [hanchorFirstParity, hanchorSecondParity]
    exact one_ne_zero
  exact f2CycleSpace_support_eq_orbitFaceBoundary_of_subset graphData
    minimal.spherical.cubic minimal.facesTwoSided face difference
      hdifferenceCycle hdifferenceSupport anchor hanchorNonzero

private theorem f2_eq_one_of_ne_zero
    (value : F2) (hvalue : value ≠ 0) : value = 1 := by
  fin_cases value
  · exact False.elim (hvalue rfl)
  · rfl

/-- No provenance-certified rebase dynamics can close after exactly three
steps. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.not_threeStep_cycle
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
      graphData minimal baseData thirdFace thirdState firstState) : False := by
  rcases first.faces_eq_of_threeStep_cycle second third with
    ⟨hfirstSecond, hsecondThird⟩
  subst secondFace
  subst thirdFace
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  let firstClosure := data.oppositePortClosure firstState.2.prefixTrail
  let secondClosure := data.oppositePortClosure secondState.2.prefixTrail
  let thirdClosure := data.oppositePortClosure thirdState.2.prefixTrail
  let firstSecond :=
    walkEdgeParity firstClosure + walkEdgeParity secondClosure
  let secondThird :=
    walkEdgeParity secondClosure + walkEdgeParity thirdClosure
  let thirdFirst :=
    walkEdgeParity thirdClosure + walkEdgeParity firstClosure
  have hfirstSecondSupport : ∀ edge : G.edgeSet,
      firstSecond edge ≠ 0 ↔
        edge ∈ orbitFaceBoundary graphData.toRotationSystem firstFace := by
    exact first.prefixParity_add_support_eq_face_of_threeStep_cycle
      second third
  have hsecondThirdSupport : ∀ edge : G.edgeSet,
      secondThird edge ≠ 0 ↔
        edge ∈ orbitFaceBoundary graphData.toRotationSystem firstFace := by
    exact second.prefixParity_add_support_eq_face_of_threeStep_cycle
      third first
  have hthirdFirstSupport : ∀ edge : G.edgeSet,
      thirdFirst edge ≠ 0 ↔
        edge ∈ orbitFaceBoundary graphData.toRotationSystem firstFace := by
    exact third.prefixParity_add_support_eq_face_of_threeStep_cycle
      first second
  let anchor := retainedEdgeToAmbientEdge data firstState.1
  have hanchorFace :
      anchor ∈ orbitFaceBoundary graphData.toRotationSystem firstFace :=
    first.source_cross_mem_face
  have hfirstSecondNonzero : firstSecond anchor ≠ 0 :=
    (hfirstSecondSupport anchor).2 hanchorFace
  have hsecondThirdNonzero : secondThird anchor ≠ 0 :=
    (hsecondThirdSupport anchor).2 hanchorFace
  have hthirdFirstNonzero : thirdFirst anchor ≠ 0 :=
    (hthirdFirstSupport anchor).2 hanchorFace
  have hfirstSecondOne : firstSecond anchor = 1 :=
    f2_eq_one_of_ne_zero _ hfirstSecondNonzero
  have hsecondThirdOne : secondThird anchor = 1 :=
    f2_eq_one_of_ne_zero _ hsecondThirdNonzero
  have hthirdFirstOne : thirdFirst anchor = 1 :=
    f2_eq_one_of_ne_zero _ hthirdFirstNonzero
  have hsum : firstSecond anchor + secondThird anchor +
      thirdFirst anchor = 0 := by
    change
      (walkEdgeParity firstClosure anchor +
          walkEdgeParity secondClosure anchor) +
        (walkEdgeParity secondClosure anchor +
          walkEdgeParity thirdClosure anchor) +
        (walkEdgeParity thirdClosure anchor +
          walkEdgeParity firstClosure anchor) = 0
    calc
      _ =
          (walkEdgeParity firstClosure anchor +
              walkEdgeParity firstClosure anchor) +
            (walkEdgeParity secondClosure anchor +
              walkEdgeParity secondClosure anchor) +
            (walkEdgeParity thirdClosure anchor +
              walkEdgeParity thirdClosure anchor) := by abel
      _ = 0 := by simp [zmod2_add_self]
  rw [hfirstSecondOne, hsecondThirdOne, hthirdFirstOne] at hsum
  exact (by decide : (3 : F2) ≠ 0) hsum

end GoertzelV24AdjacentPairInsertion.AdjacentPairData
end
end Mettapedia.GraphTheory.FourColor
