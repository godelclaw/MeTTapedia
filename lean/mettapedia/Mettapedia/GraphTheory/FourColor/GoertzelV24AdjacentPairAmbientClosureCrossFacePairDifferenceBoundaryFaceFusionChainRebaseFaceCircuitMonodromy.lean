import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuit

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
open GoertzelV24OrbitFaceCycleSpace
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24WalkCycleParity
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace ExactRebaseRelation

/-- A first relation step can be prepended to an explicitly counted run. -/
theorem ExactSteps.head
    {State : Type*} {relation : State → State → Prop}
    {length : Nat} {source middle target : State}
    (first : relation source middle)
    (rest : ExactSteps relation length middle target) :
    ExactSteps relation (length + 1) source target := by
  induction rest generalizing source with
  | refl =>
      exact ExactSteps.tail (ExactSteps.refl source) first
  | tail initial last ih =>
      exact ExactSteps.tail (ih first) last

end ExactRebaseRelation

namespace GoertzelV24RebaseFaceCircuit

/-- If a nonempty labelled list is not constant, two adjacent entries
already witness a label change. -/
theorem exists_adjacent_label_ne_of_not_forall_eq_head
    {Entry Label : Type*} (label : Entry → Label)
    (first : Entry) (rest : List Entry)
    (hnotConstant : ¬ ∀ entry ∈ first :: rest,
      label entry = label first) :
    ∃ left right before after,
      first :: rest = before ++ left :: right :: after ∧
        label left ≠ label right := by
  induction rest generalizing first with
  | nil =>
      exfalso
      apply hnotConstant
      intro entry hentry
      simp only [List.mem_singleton] at hentry
      subst entry
      rfl
  | cons second rest ih =>
      by_cases hchange : label first ≠ label second
      · exact ⟨first, second, [], rest, rfl, hchange⟩
      · have hsame : label first = label second := not_ne_iff.mp hchange
        have htailNotConstant : ¬ ∀ entry ∈ second :: rest,
            label entry = label second := by
          intro htailConstant
          apply hnotConstant
          intro entry hentry
          rcases List.mem_cons.mp hentry with rfl | hentry
          · rfl
          · exact (htailConstant entry hentry).trans hsame.symm
        rcases ih second htailNotConstant with
          ⟨left, right, before, after, hdecomposition, hlabels⟩
        exact ⟨left, right, first :: before, after,
          by simp only [List.cons_append, hdecomposition], hlabels⟩

end GoertzelV24RebaseFaceCircuit

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- In a minimal counterexample, two retained crosses incident with the
same two distinct faces are the same retained edge. -/
theorem CrossCentralExactFaceCutState.cross_eq_of_mem_distinct_face_pair
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    (source target : CrossCentralExactFaceCutState graphData data)
    {firstFace secondFace : OrbitFace graphData.toRotationSystem}
    (hfaces : firstFace ≠ secondFace)
    (hsourceFirst : retainedEdgeToAmbientEdge data source.1 ∈
      orbitFaceBoundary graphData.toRotationSystem firstFace)
    (hsourceSecond : retainedEdgeToAmbientEdge data source.1 ∈
      orbitFaceBoundary graphData.toRotationSystem secondFace)
    (htargetFirst : retainedEdgeToAmbientEdge data target.1 ∈
      orbitFaceBoundary graphData.toRotationSystem firstFace)
    (htargetSecond : retainedEdgeToAmbientEdge data target.1 ∈
      orbitFaceBoundary graphData.toRotationSystem secondFace) :
    source.1 = target.1 := by
  apply data.retainedEdgeToAmbientEdge_injective
  exact edge_eq_of_mem_distinct_orbitFace_pair graphData minimal hfaces
    hsourceFirst hsourceSecond htargetFirst htargetSecond

/-- Fixed-face monodromy has even length as soon as its endpoint crosses
agree and its endpoint prefix closures agree away from the selected face;
the rest of the exact-cut state need not agree. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.exactSteps_length_even_of_cross_eq
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
    (hcross : source.1 = target.1)
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
    Even length := by
  cases run with
  | refl => exact ⟨0, rfl⟩
  | @tail length source middle target initial last =>
      let data := baseData.rotationOrderedData graphData
        minimal.spherical.cubic minimal.vertexRotationCyclic
      have hmonodromy :=
        CrossCentralExactFaceCertifiedRebaseTransitionOnFace.exactSteps_prefixParity_monodromy
          (ExactRebaseRelation.ExactSteps.tail initial last) hoffEndpoints
      let anchor := retainedEdgeToAmbientEdge data source.1
      have hsourceMem : anchor.1 ∈
          (data.oppositePortClosure source.2.prefixTrail).edges :=
        source.2.cross_mem_oppositePortClosure
      have htargetMem : anchor.1 ∈
          (data.oppositePortClosure target.2.prefixTrail).edges := by
        change (retainedEdgeToAmbientEdge data source.1).1 ∈
          (data.oppositePortClosure target.2.prefixTrail).edges
        rw [hcross]
        exact target.2.cross_mem_oppositePortClosure
      have hsourceParity : walkEdgeParity
          (data.oppositePortClosure source.2.prefixTrail) anchor = 1 :=
        walkEdgeParity_apply_eq_one_of_isTrail_of_mem_edges
          source.2.prefixTrail_isTrail anchor hsourceMem
      have htargetParity : walkEdgeParity
          (data.oppositePortClosure target.2.prefixTrail) anchor = 1 :=
        walkEdgeParity_apply_eq_one_of_isTrail_of_mem_edges
          target.2.prefixTrail_isTrail anchor htargetMem
      have hanchorFace : anchor ∈
          orbitFaceBoundary graphData.toRotationSystem face := by
        change retainedEdgeToAmbientEdge data source.1 ∈
          orbitFaceBoundary graphData.toRotationSystem face
        rw [hcross]
        exact last.target_cross_mem_face
      have hvalue := hmonodromy anchor
      have hcastZero : (((length + 1 : Nat) : F2)) = 0 := by
        rw [hsourceParity, htargetParity, zmod2_add_self,
          orbitFaceBoundaryIndicator, if_pos hanchorFace, mul_one] at hvalue
        exact hvalue.symm
      rw [even_iff_two_dvd]
      exact (ZMod.natCast_eq_zero_iff (length + 1) 2).mp hcastZero

namespace CrossCentralExactFaceCertifiedRebaseCircuit

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

/-- A nonempty chain of arcs carrying one selected face is an explicitly
counted fixed-face rebase run. -/
theorem exactSteps_of_arc_chain_on_face
    (face : OrbitFace graphData.toRotationSystem)
    (first : CrossCentralExactFaceCertifiedRebaseArc graphData minimal
      baseData)
    (rest : List (CrossCentralExactFaceCertifiedRebaseArc graphData minimal
      baseData))
    (chain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows (first :: rest))
    (hfaces : ∀ arc ∈ first :: rest, arc.selectedFace = face) :
    ExactRebaseRelation.ExactSteps
      (CrossCentralExactFaceCertifiedRebaseTransitionOnFace graphData
        minimal baseData face)
      (first :: rest).length first.source
      ((first :: rest).getLast (by simp)).target := by
  induction rest generalizing first with
  | nil =>
      have hface : first.selectedFace = face := hfaces first (by simp)
      have step : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
          graphData minimal baseData face first.source first.target := by
        simpa [hface] using first.transition
      simpa using ExactRebaseRelation.ExactSteps.tail
        (ExactRebaseRelation.ExactSteps.refl first.source) step
  | cons second rest ih =>
      have hparts := List.isChain_cons_cons.mp chain
      have hface : first.selectedFace = face := hfaces first (by simp)
      have firstTransition :
          CrossCentralExactFaceCertifiedRebaseTransitionOnFace graphData
            minimal baseData face first.source first.target := by
        simpa [hface] using first.transition
      have firstStep :
          CrossCentralExactFaceCertifiedRebaseTransitionOnFace graphData
            minimal baseData face first.source second.source := by
        rw [← hparts.1]
        exact firstTransition
      have restFaces : ∀ arc ∈ second :: rest,
          arc.selectedFace = face := by
        intro arc harc
        exact hfaces arc (List.mem_cons_of_mem first harc)
      have run := ih second hparts.2 restFaces
      simpa using ExactRebaseRelation.ExactSteps.head firstStep run

/-- A facial-dual excursion from one face through a constant block on a
distinct face returns to the same retained crossing edge. -/
theorem cross_eq_across_constantFace_excursion
    (firstFace secondFace : OrbitFace graphData.toRotationSystem)
    (hfaces : firstFace ≠ secondFace)
    (left middleFirst right :
      CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
    (middleRest : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))
    (chain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        (left :: ((middleFirst :: middleRest) ++ [right])))
    (hleftFace : left.selectedFace = firstFace)
    (hmiddleFaces : ∀ arc ∈ middleFirst :: middleRest,
      arc.selectedFace = secondFace)
    (hrightFace : right.selectedFace = firstFace) :
    middleFirst.source.1 = right.source.1 := by
  let middleArcs := middleFirst :: middleRest
  have hmiddleNe : middleArcs ≠ [] := by simp [middleArcs]
  let middleLast := middleArcs.getLast hmiddleNe
  have hparts := List.isChain_cons_cons.mp chain
  have hleftFollows :
      CrossCentralExactFaceCertifiedRebaseArc.Follows left middleFirst := by
    exact hparts.1
  have hmiddleWithRight : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        (middleArcs ++ [right]) := by
    simpa [middleArcs] using hparts.2
  have hlastMemGetLast : middleLast ∈ middleArcs.getLast? := by
    rw [List.getLast?_eq_getLast_of_ne_nil hmiddleNe]
    simp [middleLast]
  have hlastFollows :
      CrossCentralExactFaceCertifiedRebaseArc.Follows middleLast right := by
    exact (List.isChain_append.mp hmiddleWithRight).2.2 middleLast
      hlastMemGetLast right (by simp)
  have hmiddleLastMem : middleLast ∈ middleFirst :: middleRest := by
    exact List.getLast_mem hmiddleNe
  have hmiddleFirstFace : middleFirst.selectedFace = secondFace :=
    hmiddleFaces middleFirst (by simp)
  have hmiddleLastFace : middleLast.selectedFace = secondFace :=
    hmiddleFaces middleLast hmiddleLastMem
  have hsourceFirst : retainedEdgeToAmbientEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) middleFirst.source.1 ∈
      orbitFaceBoundary graphData.toRotationSystem firstFace := by
    rw [← hleftFollows]
    simpa [hleftFace] using left.transition.target_cross_mem_face
  have hsourceSecond : retainedEdgeToAmbientEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) middleFirst.source.1 ∈
      orbitFaceBoundary graphData.toRotationSystem secondFace := by
    simpa [hmiddleFirstFace] using
      middleFirst.transition.source_cross_mem_face
  have htargetFirst : retainedEdgeToAmbientEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) right.source.1 ∈
      orbitFaceBoundary graphData.toRotationSystem firstFace := by
    simpa [hrightFace] using right.transition.source_cross_mem_face
  have htargetSecond : retainedEdgeToAmbientEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) right.source.1 ∈
      orbitFaceBoundary graphData.toRotationSystem secondFace := by
    rw [← hlastFollows]
    simpa [hmiddleLastFace] using
      middleLast.transition.target_cross_mem_face
  exact CrossCentralExactFaceCutState.cross_eq_of_mem_distinct_face_pair
    minimal middleFirst.source right.source hfaces hsourceFirst
      hsourceSecond htargetFirst htargetSecond

/-- Consequently, a genuine facial-dual backtrack must dwell for at least
two rebase arcs on its middle face. -/
theorem middleRest_ne_nil_of_constantFace_excursion
    (firstFace secondFace : OrbitFace graphData.toRotationSystem)
    (hfaces : firstFace ≠ secondFace)
    (left middleFirst right :
      CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
    (middleRest : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))
    (chain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        (left :: ((middleFirst :: middleRest) ++ [right])))
    (hleftFace : left.selectedFace = firstFace)
    (hmiddleFaces : ∀ arc ∈ middleFirst :: middleRest,
      arc.selectedFace = secondFace)
    (hrightFace : right.selectedFace = firstFace) :
    middleRest ≠ [] := by
  intro hnil
  subst middleRest
  have hparts := List.isChain_cons_cons.mp chain
  have htailParts := List.isChain_cons_cons.mp hparts.2
  have hleftMiddle : left.selectedFace ≠ middleFirst.selectedFace := by
    simpa [hleftFace, hmiddleFaces middleFirst (by simp)] using hfaces
  apply left.no_selectedFace_backtrack hparts.1 htailParts.1
    hleftMiddle
  exact hrightFace.trans hleftFace.symm

/-- If every arc of a circuit selects one face, the cyclic arc list is an
explicitly counted closed run on that face. -/
theorem exactSteps_on_face
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (face : OrbitFace graphData.toRotationSystem)
    (hfaces : ∀ arc ∈ circuit.first :: circuit.rest,
      arc.selectedFace = face) :
    ExactRebaseRelation.ExactSteps
      (CrossCentralExactFaceCertifiedRebaseTransitionOnFace graphData
        minimal baseData face)
      (circuit.first :: circuit.rest).length
      circuit.first.source circuit.first.source := by
  have run := exactSteps_of_arc_chain_on_face face circuit.first
    circuit.rest circuit.consecutive hfaces
  have hclosing :
      ((circuit.first :: circuit.rest).getLast (by simp)).target =
        circuit.first.source := by
    simpa [CrossCentralExactFaceCertifiedRebaseArc.Follows] using
      circuit.closing
  rw [hclosing] at run
  exact run

/-- A constant-face exact rebase circuit has even arc count. -/
theorem length_even_of_selectedFace_eq
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (face : OrbitFace graphData.toRotationSystem)
    (hfaces : ∀ arc ∈ circuit.first :: circuit.rest,
      arc.selectedFace = face) :
    Even (circuit.first :: circuit.rest).length := by
  exact
    CrossCentralExactFaceCertifiedRebaseTransitionOnFace.exactSteps_cycle_length_even
      (circuit.exactSteps_on_face face hfaces)

/-- A nonconstant circuit contains two consecutive arcs at which its
selected face genuinely changes. -/
theorem exists_followed_face_change_of_not_constant
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (hnotConstant : ¬ ∀ arc ∈ circuit.first :: circuit.rest,
      arc.selectedFace = circuit.first.selectedFace) :
    ∃ first second before after,
      circuit.first :: circuit.rest =
          before ++ first :: second :: after ∧
        CrossCentralExactFaceCertifiedRebaseArc.Follows first second ∧
        first.selectedFace ≠ second.selectedFace := by
  rcases
      GoertzelV24RebaseFaceCircuit.exists_adjacent_label_ne_of_not_forall_eq_head
        CrossCentralExactFaceCertifiedRebaseArc.selectedFace circuit.first
          circuit.rest hnotConstant with
    ⟨first, second, before, after, hlist, hfaces⟩
  refine ⟨first, second, before, after, hlist, ?_, hfaces⟩
  exact (List.isChain_iff_forall_rel_of_append_cons_cons.mp
    circuit.consecutive) hlist

/-- Every exact rebase circuit is either a constant-face even circuit or
contains a certified step of the full facial dual, whose crossed primal
edge is its intermediate retained cross. -/
theorem constantFace_even_or_exists_dualStep
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) :
    ((∀ arc ∈ circuit.first :: circuit.rest,
        arc.selectedFace = circuit.first.selectedFace) ∧
      Even (circuit.first :: circuit.rest).length) ∨
    ∃ first second before after,
      circuit.first :: circuit.rest =
          before ++ first :: second :: after ∧
        CrossCentralExactFaceCertifiedRebaseArc.Follows first second ∧
        first.selectedFace ≠ second.selectedFace ∧
        ∃ dualAdj :
            (interiorDualGraph
              (orbitFaceBoundary graphData.toRotationSystem)
              (Finset.univ : Finset
                (OrbitFace graphData.toRotationSystem))).Adj
                  first.dualFace second.dualFace,
          sharedInteriorEdgeOfAdjOfPairwiseUnique
              (orbitFaceBoundary graphData.toRotationSystem)
              (Finset.univ : Finset
                (OrbitFace graphData.toRotationSystem))
              (pairwiseUniqueSharedInteriorEdges graphData minimal)
              dualAdj =
            retainedEdgeToAmbientEdge
              (baseData.rotationOrderedData graphData
                minimal.spherical.cubic minimal.vertexRotationCyclic)
              first.target.1 := by
  classical
  by_cases hconstant : ∀ arc ∈ circuit.first :: circuit.rest,
      arc.selectedFace = circuit.first.selectedFace
  · exact Or.inl ⟨hconstant,
      circuit.length_even_of_selectedFace_eq
        circuit.first.selectedFace hconstant⟩
  · right
    rcases circuit.exists_followed_face_change_of_not_constant hconstant with
      ⟨first, second, before, after, hlist, hfollows, hfaces⟩
    let dualAdj := hfollows.dual_adj_of_selectedFace_ne hfaces
    refine ⟨first, second, before, after, hlist, hfollows, hfaces,
      dualAdj, ?_⟩
    exact hfollows.sharedInteriorEdge_eq_intermediate_cross hfaces

end CrossCentralExactFaceCertifiedRebaseCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
