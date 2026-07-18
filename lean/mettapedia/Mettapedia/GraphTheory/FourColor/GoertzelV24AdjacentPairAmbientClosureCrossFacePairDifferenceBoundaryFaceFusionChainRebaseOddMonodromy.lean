import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicFaceBoundaryCycleRigidity
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseTriangularMonodromy

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24OrbitFaceCycleSpace
open GoertzelV24PrimalCycleSpace
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24WalkCycleParity
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace ExactRebaseRelation

/-- A relation chain with an explicit number of steps. -/
inductive ExactSteps {State : Type*} (relation : State → State → Prop) :
    Nat → State → State → Prop
  | refl (state : State) : ExactSteps relation 0 state state
  | tail {length : Nat} {source middle target : State} :
      ExactSteps relation length source middle →
        relation middle target →
          ExactSteps relation (length + 1) source target

/-- Forgetting the explicit length gives reflexive transitive reachability. -/
theorem ExactSteps.to_reflTransGen
    {State : Type*} {relation : State → State → Prop}
    {length : Nat} {source target : State}
    (run : ExactSteps relation length source target) :
    Relation.ReflTransGen relation source target := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact ih.tail step

/-- Every nonempty transitive chain admits a positive explicit length. -/
theorem transGen_exists_exactSteps_pos
    {State : Type*} {relation : State → State → Prop}
    {source target : State}
    (run : Relation.TransGen relation source target) :
    ∃ length, 0 < length ∧ ExactSteps relation length source target := by
  induction run with
  | single step =>
      exact ⟨1, Nat.zero_lt_succ 0,
        ExactSteps.tail (ExactSteps.refl _) step⟩
  | tail _ step ih =>
      rcases ih with ⟨length, hpositive, explicit⟩
      exact ⟨length + 1, Nat.zero_lt_succ length,
        ExactSteps.tail explicit step⟩

end ExactRebaseRelation

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

private theorem f2_eq_one_of_ne_zero
    (value : F2) (hvalue : value ≠ 0) : value = 1 := by
  fin_cases value
  · exact False.elim (hvalue rfl)
  · rfl

/-- If a fixed-face rebase preserves complete prefix support away from its
selected face, its binary prefix-parity change is exactly that facial
boundary indicator. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.prefixParity_add_eq_faceBoundaryIndicator_of_offFace_support_eq
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    {source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (transition : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData face source target)
    (hoffSupport : ∀ edge : G.edgeSet,
      edge ∉ orbitFaceBoundary graphData.toRotationSystem face →
        (edge.1 ∈
            ((baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic).oppositePortClosure
                source.2.prefixTrail).edges ↔
          edge.1 ∈
            ((baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic).oppositePortClosure
                target.2.prefixTrail).edges)) :
    let data := baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic
    walkEdgeParity (data.oppositePortClosure source.2.prefixTrail) +
        walkEdgeParity (data.oppositePortClosure target.2.prefixTrail) =
      orbitFaceBoundaryIndicator graphData face := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  let sourceClosure := data.oppositePortClosure source.2.prefixTrail
  let targetClosure := data.oppositePortClosure target.2.prefixTrail
  let difference :=
    walkEdgeParity sourceClosure + walkEdgeParity targetClosure
  change difference = orbitFaceBoundaryIndicator graphData face
  have hdifferenceCycle : difference ∈ f2CycleSpace G := by
    exact (f2CycleSpace G).add_mem
      (walkEdgeParity_mem_f2CycleSpace_of_closed sourceClosure)
      (walkEdgeParity_mem_f2CycleSpace_of_closed targetClosure)
  have hdifferenceSupport : ∀ edge : G.edgeSet, difference edge ≠ 0 →
      edge ∈ orbitFaceBoundary graphData.toRotationSystem face := by
    intro edge hnonzero
    by_contra hoff
    have hparity :=
      walkEdgeParity_apply_eq_of_isTrail_of_mem_edges_iff
        source.2.prefixTrail_isTrail target.2.prefixTrail_isTrail edge
          (hoffSupport edge hoff)
    apply hnonzero
    change walkEdgeParity sourceClosure edge +
      walkEdgeParity targetClosure edge = 0
    rw [hparity, zmod2_add_self]
  let anchor := retainedEdgeToAmbientEdge data source.1
  have hanchorSource : anchor.1 ∈ sourceClosure.edges := by
    exact source.2.cross_mem_oppositePortClosure
  have hanchorTarget : anchor.1 ∉ targetClosure.edges := by
    intro hmem
    apply transition.to_transition.target_trails_avoid_source_cross.1
    exact
      ((retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff
        data target.2.prefixTrail source.1).1 hmem)
  have hanchorSourceParity : walkEdgeParity sourceClosure anchor = 1 :=
    walkEdgeParity_apply_eq_one_of_isTrail_of_mem_edges
      source.2.prefixTrail_isTrail anchor hanchorSource
  have hanchorTargetParity : walkEdgeParity targetClosure anchor = 0 :=
    walkEdgeParity_apply_eq_zero_of_not_mem_edges targetClosure anchor
      hanchorTarget
  have hanchorNonzero : difference anchor ≠ 0 := by
    change walkEdgeParity sourceClosure anchor +
      walkEdgeParity targetClosure anchor ≠ 0
    rw [hanchorSourceParity, hanchorTargetParity]
    exact one_ne_zero
  have hexact :=
    f2CycleSpace_support_eq_orbitFaceBoundary_of_subset graphData
      minimal.spherical.cubic minimal.facesTwoSided face difference
        hdifferenceCycle hdifferenceSupport anchor hanchorNonzero
  funext edge
  by_cases hface : edge ∈
      orbitFaceBoundary graphData.toRotationSystem face
  · have hnonzero := (hexact edge).2 hface
    have hone := f2_eq_one_of_ne_zero (difference edge) hnonzero
    simp [orbitFaceBoundaryIndicator, hface, hone]
  · have hzero : difference edge = 0 := by
      by_contra hnonzero
      exact hface ((hexact edge).1 hnonzero)
    simp [orbitFaceBoundaryIndicator, hface, hzero]

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

/-- Along an explicitly counted fixed-face run whose endpoint closures agree
away from that face, endpoint prefix parity differs by the facial boundary
multiplied by the run length modulo two. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.exactSteps_prefixParity_monodromy
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    {length : Nat}
    {source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (run : ExactRebaseRelation.ExactSteps
      (CrossCentralExactFaceCertifiedRebaseTransitionOnFace graphData
        minimal baseData face) length source target)
    (hoffEndpoints : ∀ edge : G.edgeSet,
      edge ∉ orbitFaceBoundary graphData.toRotationSystem face →
        (edge.1 ∈
            ((baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic).oppositePortClosure
                source.2.prefixTrail).edges ↔
          edge.1 ∈
            ((baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic).oppositePortClosure
                target.2.prefixTrail).edges)) :
    let data := baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic
    ∀ edge : G.edgeSet,
      walkEdgeParity (data.oppositePortClosure source.2.prefixTrail) edge +
          walkEdgeParity (data.oppositePortClosure target.2.prefixTrail) edge =
        (length : F2) * orbitFaceBoundaryIndicator graphData face edge := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  change ∀ edge : G.edgeSet,
    walkEdgeParity (data.oppositePortClosure source.2.prefixTrail) edge +
        walkEdgeParity (data.oppositePortClosure target.2.prefixTrail) edge =
      (length : F2) * orbitFaceBoundaryIndicator graphData face edge
  revert hoffEndpoints
  induction run with
  | refl =>
      intro _ edge
      simp [zmod2_add_self]
  | @tail length source middle target initial last ih =>
      intro hoffEndpoints edge
      have hsourceMiddle : ∀ other : G.edgeSet,
          other ∉ orbitFaceBoundary graphData.toRotationSystem face →
            (other.1 ∈
                (data.oppositePortClosure source.2.prefixTrail).edges ↔
              other.1 ∈
                (data.oppositePortClosure middle.2.prefixTrail).edges) := by
        intro other hoff
        constructor
        · intro hsource
          have htarget := (hoffEndpoints other hoff).1 hsource
          exact last.target_prefixClosure_offFace_subset_source other hoff
            htarget
        · intro hmiddle
          exact
            CrossCentralExactFaceCertifiedRebaseTransitionOnFace.reflTransGen_prefixClosure_offFace_subset
              initial.to_reflTransGen other hoff hmiddle
      have hmiddleTarget : ∀ other : G.edgeSet,
          other ∉ orbitFaceBoundary graphData.toRotationSystem face →
            (other.1 ∈
                (data.oppositePortClosure middle.2.prefixTrail).edges ↔
              other.1 ∈
                (data.oppositePortClosure target.2.prefixTrail).edges) := by
        intro other hoff
        constructor
        · intro hmiddle
          have hsource :=
            CrossCentralExactFaceCertifiedRebaseTransitionOnFace.reflTransGen_prefixClosure_offFace_subset
              initial.to_reflTransGen other hoff hmiddle
          exact (hoffEndpoints other hoff).1 hsource
        · intro htarget
          exact last.target_prefixClosure_offFace_subset_source other hoff
            htarget
      have hinitial := ih hsourceMiddle edge
      have hlast :
          walkEdgeParity
                (data.oppositePortClosure middle.2.prefixTrail) edge +
              walkEdgeParity
                (data.oppositePortClosure target.2.prefixTrail) edge =
            orbitFaceBoundaryIndicator graphData face edge := by
        simpa only [Pi.add_apply] using congrFun
          (last.prefixParity_add_eq_faceBoundaryIndicator_of_offFace_support_eq
            hmiddleTarget) edge
      calc
        walkEdgeParity
              (data.oppositePortClosure source.2.prefixTrail) edge +
            walkEdgeParity
              (data.oppositePortClosure target.2.prefixTrail) edge =
            (walkEdgeParity
                  (data.oppositePortClosure source.2.prefixTrail) edge +
                walkEdgeParity
                  (data.oppositePortClosure middle.2.prefixTrail) edge) +
              (walkEdgeParity
                  (data.oppositePortClosure middle.2.prefixTrail) edge +
                walkEdgeParity
                  (data.oppositePortClosure target.2.prefixTrail) edge) := by
                    calc
                      _ = walkEdgeParity
                              (data.oppositePortClosure
                                source.2.prefixTrail) edge +
                            (walkEdgeParity
                                (data.oppositePortClosure
                                  middle.2.prefixTrail) edge +
                              walkEdgeParity
                                (data.oppositePortClosure
                                  middle.2.prefixTrail) edge) +
                            walkEdgeParity
                              (data.oppositePortClosure
                                target.2.prefixTrail) edge := by
                                  rw [zmod2_add_self]
                                  simp
                      _ = _ := by abel
        _ = (length : F2) *
              orbitFaceBoundaryIndicator graphData face edge +
            orbitFaceBoundaryIndicator graphData face edge := by
              rw [hinitial, hlast]
        _ = ((length + 1 : Nat) : F2) *
              orbitFaceBoundaryIndicator graphData face edge := by
              simp [Nat.cast_add, add_mul]

/-- Every explicitly counted closed rebase run on one fixed face has even
length. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.exactSteps_cycle_length_even
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    {length : Nat}
    {state : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (run : ExactRebaseRelation.ExactSteps
      (CrossCentralExactFaceCertifiedRebaseTransitionOnFace graphData
        minimal baseData face) length state state) :
    Even length := by
  cases run with
  | refl => exact ⟨0, rfl⟩
  | @tail length state middle _ initial last =>
      let data := baseData.rotationOrderedData graphData
        minimal.spherical.cubic minimal.vertexRotationCyclic
      have hmonodromy :=
        CrossCentralExactFaceCertifiedRebaseTransitionOnFace.exactSteps_prefixParity_monodromy
          (ExactRebaseRelation.ExactSteps.tail initial last)
          (fun _edge _hoff => Iff.rfl)
      let anchor := retainedEdgeToAmbientEdge data state.1
      have hanchorFace :
          anchor ∈ orbitFaceBoundary graphData.toRotationSystem face :=
        last.target_cross_mem_face
      have hvalue := hmonodromy anchor
      have hcastZero : (((length + 1 : Nat) : F2)) = 0 := by
        rw [zmod2_add_self, orbitFaceBoundaryIndicator, if_pos hanchorFace,
          mul_one] at hvalue
        exact hvalue.symm
      rw [even_iff_two_dvd]
      exact (ZMod.natCast_eq_zero_iff (length + 1) 2).mp hcastZero

/-- A nonempty closed fixed-face rebase chain therefore has a positive even
explicit length. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.transGen_cycle_exists_even_exactSteps
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    {state : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (cycle : Relation.TransGen
      (CrossCentralExactFaceCertifiedRebaseTransitionOnFace graphData
        minimal baseData face) state state) :
    ∃ length, 0 < length ∧
      ExactRebaseRelation.ExactSteps
          (CrossCentralExactFaceCertifiedRebaseTransitionOnFace graphData
            minimal baseData face) length state state ∧
        Even length := by
  rcases ExactRebaseRelation.transGen_exists_exactSteps_pos cycle with
    ⟨length, hpositive, explicit⟩
  exact ⟨length, hpositive, explicit,
    CrossCentralExactFaceCertifiedRebaseTransitionOnFace.exactSteps_cycle_length_even
      explicit⟩

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
