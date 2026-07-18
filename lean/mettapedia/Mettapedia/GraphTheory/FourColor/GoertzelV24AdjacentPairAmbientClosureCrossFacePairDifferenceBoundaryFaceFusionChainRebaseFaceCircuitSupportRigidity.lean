import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitSupportFlow

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceDualConnectedness
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

namespace GoertzelV24RebaseFaceCircuit

/-- Two simple paths with the same ordered endpoints and the same
unoriented edge support are the same walk. -/
theorem walk_eq_of_isPath_of_edges_mem_iff
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : SimpleGraph Vertex} {start finish : Vertex}
    {first second : graph.Walk start finish}
    (hfirst : first.IsPath) (hsecond : second.IsPath)
    (hedges : ∀ edge : Sym2 Vertex,
      edge ∈ first.edges ↔ edge ∈ second.edges) :
    first = second := by
  induction first with
  | nil =>
      exact (SimpleGraph.Walk.isPath_iff_nil.mp hsecond).eq_nil.symm
  | @cons start next finish adjacent tail ih =>
      cases second with
      | nil =>
          exfalso
          have hmem : s(start, next) ∈
              (SimpleGraph.Walk.cons adjacent tail).edges := by simp
          have := (hedges s(start, next)).1 hmem
          simpa using this
      | @cons _ secondNext _ secondAdjacent secondTail =>
          have hfirstEdge : s(start, next) ∈
              (SimpleGraph.Walk.cons adjacent tail).edges := by simp
          have hfirstEdgeSecond :=
            (hedges s(start, next)).1 hfirstEdge
          have hnext : next = secondNext := by
            have := hsecond.eq_snd_of_mem_edges hfirstEdgeSecond
            simpa using this
          subst secondNext
          have hfirstParts :=
            (SimpleGraph.Walk.cons_isPath_iff adjacent tail).1 hfirst
          have hsecondParts :=
            (SimpleGraph.Walk.cons_isPath_iff secondAdjacent
              secondTail).1 hsecond
          have hfirstNoHead : s(start, next) ∉ tail.edges := by
            have hnodup := hfirst.isTrail.edges_nodup
            simp only [SimpleGraph.Walk.edges_cons,
              List.nodup_cons] at hnodup
            exact hnodup.1
          have hsecondNoHead : s(start, next) ∉ secondTail.edges := by
            have hnodup := hsecond.isTrail.edges_nodup
            simp only [SimpleGraph.Walk.edges_cons,
              List.nodup_cons] at hnodup
            exact hnodup.1
          have htailEdges : ∀ edge : Sym2 Vertex,
              edge ∈ tail.edges ↔ edge ∈ secondTail.edges := by
            intro edge
            constructor
            · intro htail
              have hfull : edge ∈
                  (SimpleGraph.Walk.cons adjacent tail).edges := by
                simp [htail]
              have hsecondFull := (hedges edge).1 hfull
              simp only [SimpleGraph.Walk.edges_cons,
                List.mem_cons] at hsecondFull
              rcases hsecondFull with hhead | hsecondTail
              · subst edge
                exact False.elim (hfirstNoHead htail)
              · exact hsecondTail
            · intro hsecondTail
              have hfull : edge ∈
                  (SimpleGraph.Walk.cons secondAdjacent
                    secondTail).edges := by
                simp [hsecondTail]
              have hfirstFull := (hedges edge).2 hfull
              simp only [SimpleGraph.Walk.edges_cons,
                List.mem_cons] at hfirstFull
              rcases hfirstFull with hhead | htail
              · subst edge
                exact False.elim (hsecondNoHead hsecondTail)
              · exact htail
          have htailEq := ih hfirstParts.1 hsecondParts.1 htailEdges
          subst secondTail
          rfl

end GoertzelV24RebaseFaceCircuit

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

private theorem f2_eq_one_of_ne_zero_supportRigidity
    (value : F2) (hvalue : value ≠ 0) : value = 1 := by
  fin_cases value
  · exact False.elim (hvalue rfl)
  · rfl

/-- Every exact rebase target carries the simple prefix path constructed
by its localized successor resolution. -/
theorem CrossCentralExactFaceCertifiedRebaseStep.target_prefix_isPath
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {source : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (step : CrossCentralExactFaceCertifiedRebaseStep graphData minimal
      baseData source) :
    step.target.2.prefixTrail.IsPath := by
  change step.rebase.targetPair.prefixTrail.IsPath
  rw [step.rebase.target_prefixTrail]
  exact step.successors.prefix_isPath

/-- Every exact rebase target likewise carries the constructed simple
suffix path. -/
theorem CrossCentralExactFaceCertifiedRebaseStep.target_suffix_isPath
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {source : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (step : CrossCentralExactFaceCertifiedRebaseStep graphData minimal
      baseData source) :
    step.target.2.suffixTrail.IsPath := by
  change step.rebase.targetPair.suffixTrail.IsPath
  rw [step.rebase.target_suffixTrail]
  exact step.successors.suffix_isPath

/-- Target prefix simplicity in relation form. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.target_prefix_isPath
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    {source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (transition : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData face source target) :
    target.2.prefixTrail.IsPath := by
  rcases transition with ⟨step, rfl, _⟩
  exact step.target_prefix_isPath

/-- Target suffix simplicity in relation form. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.target_suffix_isPath
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    {source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (transition : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData face source target) :
    target.2.suffixTrail.IsPath := by
  rcases transition with ⟨step, rfl, _⟩
  exact step.target_suffix_isPath

/-- Equality of complete prefix-closure support rigidifies to equality of
the retained prefix paths once both endpoints are known to be simple. -/
theorem CrossCentralExactFaceCutState.prefixTrail_eq_of_isPath_of_closure_support_eq
    {graphData : Data G} {data : AdjacentPairData G}
    (source target : CrossCentralExactFaceCutState graphData data)
    (hsourcePath : source.2.prefixTrail.IsPath)
    (htargetPath : target.2.prefixTrail.IsPath)
    (hsupport : ∀ edge : G.edgeSet,
      edge.1 ∈ (data.oppositePortClosure
          source.2.prefixTrail).edges ↔
        edge.1 ∈ (data.oppositePortClosure
          target.2.prefixTrail).edges) :
    source.2.prefixTrail = target.2.prefixTrail := by
  apply GoertzelV24RebaseFaceCircuit.walk_eq_of_isPath_of_edges_mem_iff
    hsourcePath htargetPath
  intro edge
  constructor
  · intro hsource
    let retained : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).edgeSet :=
      ⟨edge, source.2.prefixTrail.edges_subset_edgeSet hsource⟩
    have hsourceClosure : (retainedEdgeToAmbientEdge data retained).1 ∈
        (data.oppositePortClosure source.2.prefixTrail).edges :=
      (retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff
        data source.2.prefixTrail retained).2 hsource
    have htargetClosure :=
      (hsupport (retainedEdgeToAmbientEdge data retained)).1
        hsourceClosure
    exact
      (retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff
        data target.2.prefixTrail retained).1 htargetClosure
  · intro htarget
    let retained : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).edgeSet :=
      ⟨edge, target.2.prefixTrail.edges_subset_edgeSet htarget⟩
    have htargetClosure : (retainedEdgeToAmbientEdge data retained).1 ∈
        (data.oppositePortClosure target.2.prefixTrail).edges :=
      (retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff
        data target.2.prefixTrail retained).2 htarget
    have hsourceClosure :=
      (hsupport (retainedEdgeToAmbientEdge data retained)).2
        htargetClosure
    exact
      (retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff
        data source.2.prefixTrail retained).1 hsourceClosure

/-- The corresponding rigidity theorem for alternate suffix closures. -/
theorem CrossCentralExactFaceCutState.suffixTrail_eq_of_isPath_of_closure_support_eq
    {graphData : Data G} {data : AdjacentPairData G}
    (source target : CrossCentralExactFaceCutState graphData data)
    (hsourcePath : source.2.suffixTrail.IsPath)
    (htargetPath : target.2.suffixTrail.IsPath)
    (hsupport : ∀ edge : G.edgeSet,
      edge.1 ∈ (data.alternateOppositePortClosure
          source.2.suffixTrail).edges ↔
        edge.1 ∈ (data.alternateOppositePortClosure
          target.2.suffixTrail).edges) :
    source.2.suffixTrail = target.2.suffixTrail := by
  apply GoertzelV24RebaseFaceCircuit.walk_eq_of_isPath_of_edges_mem_iff
    hsourcePath htargetPath
  intro edge
  constructor
  · intro hsource
    let retained : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).edgeSet :=
      ⟨edge, source.2.suffixTrail.edges_subset_edgeSet hsource⟩
    have hsourceClosure : (retainedEdgeToAmbientEdge data retained).1 ∈
        (data.alternateOppositePortClosure source.2.suffixTrail).edges :=
      (retainedEdgeToAmbientEdge_mem_alternateOppositePortClosure_edges_iff
        (data := data) source.2.suffixTrail retained).2 hsource
    have htargetClosure :=
      (hsupport (retainedEdgeToAmbientEdge data retained)).1
        hsourceClosure
    exact
      (retainedEdgeToAmbientEdge_mem_alternateOppositePortClosure_edges_iff
        (data := data) target.2.suffixTrail retained).1 htargetClosure
  · intro htarget
    let retained : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).edgeSet :=
      ⟨edge, target.2.suffixTrail.edges_subset_edgeSet htarget⟩
    have htargetClosure : (retainedEdgeToAmbientEdge data retained).1 ∈
        (data.alternateOppositePortClosure target.2.suffixTrail).edges :=
      (retainedEdgeToAmbientEdge_mem_alternateOppositePortClosure_edges_iff
        (data := data) target.2.suffixTrail retained).2 htarget
    have hsourceClosure :=
      (hsupport (retainedEdgeToAmbientEdge data retained)).2
        htargetClosure
    exact
      (retainedEdgeToAmbientEdge_mem_alternateOppositePortClosure_edges_iff
        (data := data) source.2.suffixTrail retained).1 hsourceClosure

/-- If a fixed-face rebase preserves complete suffix support away from its
selected face, its binary suffix-parity change is exactly that facial
boundary indicator. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.suffixParity_add_eq_faceBoundaryIndicator_of_offFace_support_eq
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
              minimal.vertexRotationCyclic).alternateOppositePortClosure
                source.2.suffixTrail).edges ↔
          edge.1 ∈
            ((baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic).alternateOppositePortClosure
                target.2.suffixTrail).edges)) :
    let data := baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic
    walkEdgeParity (data.alternateOppositePortClosure source.2.suffixTrail) +
        walkEdgeParity (data.alternateOppositePortClosure target.2.suffixTrail) =
      orbitFaceBoundaryIndicator graphData face := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  let sourceClosure :=
    data.alternateOppositePortClosure source.2.suffixTrail
  let targetClosure :=
    data.alternateOppositePortClosure target.2.suffixTrail
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
        source.2.suffixTrail_isTrail target.2.suffixTrail_isTrail edge
          (hoffSupport edge hoff)
    apply hnonzero
    change walkEdgeParity sourceClosure edge +
      walkEdgeParity targetClosure edge = 0
    rw [hparity, zmod2_add_self]
  let anchor := retainedEdgeToAmbientEdge data source.1
  have hanchorSource : anchor.1 ∈ sourceClosure.edges := by
    have hsourceTrail : source.1.1 ∈ source.2.suffixTrail.edges :=
      ((source.2.retainedIntersectionExact source.1.1).2 rfl).2
    exact
      (retainedEdgeToAmbientEdge_mem_alternateOppositePortClosure_edges_iff
        (data := data) source.2.suffixTrail source.1).2 hsourceTrail
  have hanchorTarget : anchor.1 ∉ targetClosure.edges := by
    intro hmem
    apply transition.to_transition.target_trails_avoid_source_cross.2
    exact
      ((retainedEdgeToAmbientEdge_mem_alternateOppositePortClosure_edges_iff
        (data := data) target.2.suffixTrail source.1).1 hmem)
  have hanchorSourceParity : walkEdgeParity sourceClosure anchor = 1 :=
    walkEdgeParity_apply_eq_one_of_isTrail_of_mem_edges
      source.2.suffixTrail_isTrail anchor hanchorSource
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
    have hone := f2_eq_one_of_ne_zero_supportRigidity
      (difference edge) hnonzero
    simp [orbitFaceBoundaryIndicator, hface, hone]
  · have hzero : difference edge = 0 := by
      by_contra hnonzero
      exact hface ((hexact edge).1 hnonzero)
    simp [orbitFaceBoundaryIndicator, hface, hzero]

/-- Along an explicitly counted fixed-face run whose endpoint closures agree
away from that face, endpoint suffix parity differs by the facial boundary
multiplied by the run length modulo two. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.exactSteps_suffixParity_monodromy
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
              minimal.vertexRotationCyclic).alternateOppositePortClosure
                source.2.suffixTrail).edges ↔
          edge.1 ∈
            ((baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic).alternateOppositePortClosure
                target.2.suffixTrail).edges)) :
    let data := baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic
    ∀ edge : G.edgeSet,
      walkEdgeParity
            (data.alternateOppositePortClosure source.2.suffixTrail) edge +
          walkEdgeParity
            (data.alternateOppositePortClosure target.2.suffixTrail) edge =
        (length : F2) *
          orbitFaceBoundaryIndicator graphData face edge := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  change ∀ edge : G.edgeSet,
    walkEdgeParity
          (data.alternateOppositePortClosure source.2.suffixTrail) edge +
        walkEdgeParity
          (data.alternateOppositePortClosure target.2.suffixTrail) edge =
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
                (data.alternateOppositePortClosure
                  source.2.suffixTrail).edges ↔
              other.1 ∈
                (data.alternateOppositePortClosure
                  middle.2.suffixTrail).edges) := by
        intro other hoff
        constructor
        · intro hsource
          have htarget := (hoffEndpoints other hoff).1 hsource
          exact last.target_suffixClosure_offFace_subset_source other hoff
            htarget
        · intro hmiddle
          exact
            CrossCentralExactFaceCertifiedRebaseTransitionOnFace.reflTransGen_suffixClosure_offFace_subset
              initial.to_reflTransGen other hoff hmiddle
      have hmiddleTarget : ∀ other : G.edgeSet,
          other ∉ orbitFaceBoundary graphData.toRotationSystem face →
            (other.1 ∈
                (data.alternateOppositePortClosure
                  middle.2.suffixTrail).edges ↔
              other.1 ∈
                (data.alternateOppositePortClosure
                  target.2.suffixTrail).edges) := by
        intro other hoff
        constructor
        · intro hmiddle
          have hsource :=
            CrossCentralExactFaceCertifiedRebaseTransitionOnFace.reflTransGen_suffixClosure_offFace_subset
              initial.to_reflTransGen other hoff hmiddle
          exact (hoffEndpoints other hoff).1 hsource
        · intro htarget
          exact last.target_suffixClosure_offFace_subset_source other hoff
            htarget
      have hinitial := ih hsourceMiddle edge
      have hlast :
          walkEdgeParity
                (data.alternateOppositePortClosure
                  middle.2.suffixTrail) edge +
              walkEdgeParity
                (data.alternateOppositePortClosure
                  target.2.suffixTrail) edge =
            orbitFaceBoundaryIndicator graphData face edge := by
        simpa only [Pi.add_apply] using congrFun
          (last.suffixParity_add_eq_faceBoundaryIndicator_of_offFace_support_eq
            hmiddleTarget) edge
      calc
        walkEdgeParity
              (data.alternateOppositePortClosure
                source.2.suffixTrail) edge +
            walkEdgeParity
              (data.alternateOppositePortClosure
                target.2.suffixTrail) edge =
            (walkEdgeParity
                  (data.alternateOppositePortClosure
                    source.2.suffixTrail) edge +
                walkEdgeParity
                  (data.alternateOppositePortClosure
                    middle.2.suffixTrail) edge) +
              (walkEdgeParity
                  (data.alternateOppositePortClosure
                    middle.2.suffixTrail) edge +
                walkEdgeParity
                  (data.alternateOppositePortClosure
                    target.2.suffixTrail) edge) := by
                    calc
                      _ = walkEdgeParity
                              (data.alternateOppositePortClosure
                                source.2.suffixTrail) edge +
                            (walkEdgeParity
                                (data.alternateOppositePortClosure
                                  middle.2.suffixTrail) edge +
                              walkEdgeParity
                                (data.alternateOppositePortClosure
                                  middle.2.suffixTrail) edge) +
                            walkEdgeParity
                              (data.alternateOppositePortClosure
                                target.2.suffixTrail) edge := by
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

/-- Even fixed-face monodromy with off-face endpoint agreement has equal
suffix-closure support everywhere, including on the selected face. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.exactSteps_suffixClosure_support_eq_of_even
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
    (heven : Even length)
    (hoffEndpoints : ∀ edge : G.edgeSet,
      edge ∉ orbitFaceBoundary graphData.toRotationSystem face →
        (edge.1 ∈
            ((baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic).alternateOppositePortClosure
                source.2.suffixTrail).edges ↔
          edge.1 ∈
            ((baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic).alternateOppositePortClosure
                target.2.suffixTrail).edges)) :
    ∀ edge : G.edgeSet,
      edge.1 ∈
          ((baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic).alternateOppositePortClosure
              source.2.suffixTrail).edges ↔
        edge.1 ∈
          ((baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic).alternateOppositePortClosure
              target.2.suffixTrail).edges := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  have hmonodromy :=
    CrossCentralExactFaceCertifiedRebaseTransitionOnFace.exactSteps_suffixParity_monodromy
      run hoffEndpoints
  rcases heven with ⟨half, rfl⟩
  intro edge
  have hvalue := hmonodromy edge
  have hsumZero :
      walkEdgeParity
            (data.alternateOppositePortClosure source.2.suffixTrail) edge +
          walkEdgeParity
            (data.alternateOppositePortClosure target.2.suffixTrail) edge =
        0 := by
    simpa [Nat.cast_add, zmod2_add_self] using hvalue
  have hparity :
      walkEdgeParity
          (data.alternateOppositePortClosure source.2.suffixTrail) edge =
        walkEdgeParity
          (data.alternateOppositePortClosure target.2.suffixTrail) edge := by
    calc
      walkEdgeParity
          (data.alternateOppositePortClosure source.2.suffixTrail) edge =
          walkEdgeParity
              (data.alternateOppositePortClosure source.2.suffixTrail) edge +
            (walkEdgeParity
                (data.alternateOppositePortClosure
                  target.2.suffixTrail) edge +
              walkEdgeParity
                (data.alternateOppositePortClosure
                  target.2.suffixTrail) edge) := by
                  rw [zmod2_add_self]
                  simp
      _ = (walkEdgeParity
              (data.alternateOppositePortClosure
                source.2.suffixTrail) edge +
            walkEdgeParity
              (data.alternateOppositePortClosure
                target.2.suffixTrail) edge) +
          walkEdgeParity
            (data.alternateOppositePortClosure
              target.2.suffixTrail) edge := by
              abel
      _ = walkEdgeParity
            (data.alternateOppositePortClosure
              target.2.suffixTrail) edge := by
              rw [hsumZero]
              simp
  constructor
  · intro hsource
    have hone : walkEdgeParity
        (data.alternateOppositePortClosure target.2.suffixTrail) edge = 1 := by
      rw [← hparity]
      exact walkEdgeParity_apply_eq_one_of_isTrail_of_mem_edges
        source.2.suffixTrail_isTrail edge hsource
    exact (walkEdgeParity_apply_eq_one_iff_mem_edges_of_isTrail
      target.2.suffixTrail_isTrail edge).1 hone
  · intro htarget
    have hone : walkEdgeParity
        (data.alternateOppositePortClosure source.2.suffixTrail) edge = 1 := by
      rw [hparity]
      exact walkEdgeParity_apply_eq_one_of_isTrail_of_mem_edges
        target.2.suffixTrail_isTrail edge htarget
    exact (walkEdgeParity_apply_eq_one_iff_mem_edges_of_isTrail
      source.2.suffixTrail_isTrail edge).1 hone

/-- On a connected two-sided facial dual, two face-label functions with the
same boundary differ by addition of one constant binary label. -/
theorem orbitFaceLabels_eq_add_constant_of_boundary_eq
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (first second : OrbitFace graphData.toRotationSystem → F2)
    (hboundary :
      orbitFaceBoundaryLinearMap graphData.toRotationSystem first =
        orbitFaceBoundaryLinearMap graphData.toRotationSystem second) :
    ∃ shift : F2, ∀ face,
      second face = first face + shift := by
  let RS := graphData.toRotationSystem
  let difference := first + second
  have hkernel : difference ∈
      LinearMap.ker (orbitFaceBoundaryLinearMap RS) := by
    rw [LinearMap.mem_ker]
    change orbitFaceBoundaryLinearMap RS (first + second) = 0
    rw [map_add, hboundary]
    funext edge
    exact zmod2_add_self _
  have hdual :
      (interiorDualGraph (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).Connected :=
    orbitFaceInteriorDual_connected RS minimal.spherical.cubic
      minimal.primalConnected minimal.vertexRotationCyclic
  have hconstant :=
    (mem_ker_orbitFaceBoundaryLinearMap_iff_constant RS
      minimal.facesTwoSided hdual difference).1 hkernel
  let anchor := dartOrbitFace RS RS.outer
  refine ⟨difference anchor, ?_⟩
  intro face
  have hface := hconstant face anchor
  change first face + second face =
      first anchor + second anchor at hface
  change second face = first face +
    (first anchor + second anchor)
  calc
    second face = first face + (first face + second face) := by
      rw [← add_assoc, zmod2_add_self]
      simp
    _ = first face + (first anchor + second anchor) := by rw [hface]

/-- Once the two retained trails are fixed, the two exact face-cut label
fields differ through a unique pair of binary global complements. -/
theorem CrossCentralExactFaceCutPair.existsUnique_labelComplementProfile_of_trails_eq
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {sourceCross targetCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (source : CrossCentralExactFaceCutPair graphData data sourceCross)
    (target : CrossCentralExactFaceCutPair graphData data targetCross)
    (hprefixTrail : source.prefixTrail = target.prefixTrail)
    (hsuffixTrail : source.suffixTrail = target.suffixTrail) :
    ∃! profile : F2 × F2,
      (∀ face, target.prefixLabels face =
        source.prefixLabels face + profile.1) ∧
      (∀ face, target.suffixLabels face =
        source.suffixLabels face + profile.2) := by
  have hprefixBoundary :
      orbitFaceBoundaryLinearMap graphData.toRotationSystem
          source.prefixLabels =
        orbitFaceBoundaryLinearMap graphData.toRotationSystem
          target.prefixLabels := by
    rw [source.prefixBoundary, target.prefixBoundary, ← hprefixTrail]
  have hsuffixBoundary :
      orbitFaceBoundaryLinearMap graphData.toRotationSystem
          source.suffixLabels =
        orbitFaceBoundaryLinearMap graphData.toRotationSystem
          target.suffixLabels := by
    rw [source.suffixBoundary, target.suffixBoundary, ← hsuffixTrail]
  rcases orbitFaceLabels_eq_add_constant_of_boundary_eq minimal
      source.prefixLabels target.prefixLabels hprefixBoundary with
    ⟨prefixShift, hprefixShift⟩
  rcases orbitFaceLabels_eq_add_constant_of_boundary_eq minimal
      source.suffixLabels target.suffixLabels hsuffixBoundary with
    ⟨suffixShift, hsuffixShift⟩
  refine ⟨(prefixShift, suffixShift),
    ⟨hprefixShift, hsuffixShift⟩, ?_⟩
  intro other hother
  let anchor := dartOrbitFace graphData.toRotationSystem
    graphData.toRotationSystem.outer
  apply Prod.ext
  · exact add_left_cancel
      ((hother.1 anchor).symm.trans (hprefixShift anchor))
  · exact add_left_cancel
      ((hother.2 anchor).symm.trans (hsuffixShift anchor))

/-- An even fixed-face run with endpoint support agreement on both closure
channels and simple endpoint trails preserves both retained paths. Its only
remaining face-label freedom is the unique pair of global complements. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.exactSteps_trails_eq_and_existsUnique_labelComplementProfile_of_even
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
    (heven : Even length)
    (hprefixOff : ∀ edge : G.edgeSet,
      edge ∉ orbitFaceBoundary graphData.toRotationSystem face →
        (edge.1 ∈
            ((baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic).oppositePortClosure
                source.2.prefixTrail).edges ↔
          edge.1 ∈
            ((baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic).oppositePortClosure
                target.2.prefixTrail).edges))
    (hsuffixOff : ∀ edge : G.edgeSet,
      edge ∉ orbitFaceBoundary graphData.toRotationSystem face →
        (edge.1 ∈
            ((baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic).alternateOppositePortClosure
                source.2.suffixTrail).edges ↔
          edge.1 ∈
            ((baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic).alternateOppositePortClosure
                target.2.suffixTrail).edges))
    (hsourcePrefix : source.2.prefixTrail.IsPath)
    (htargetPrefix : target.2.prefixTrail.IsPath)
    (hsourceSuffix : source.2.suffixTrail.IsPath)
    (htargetSuffix : target.2.suffixTrail.IsPath) :
    source.2.prefixTrail = target.2.prefixTrail ∧
      source.2.suffixTrail = target.2.suffixTrail ∧
      ∃! profile : F2 × F2,
        (∀ selectedFace, target.2.prefixLabels selectedFace =
          source.2.prefixLabels selectedFace + profile.1) ∧
        (∀ selectedFace, target.2.suffixLabels selectedFace =
          source.2.suffixLabels selectedFace + profile.2) := by
  have hprefixSupport :=
    CrossCentralExactFaceCertifiedRebaseTransitionOnFace.exactSteps_prefixClosure_support_eq_of_even
      run heven hprefixOff
  have hsuffixSupport :=
    CrossCentralExactFaceCertifiedRebaseTransitionOnFace.exactSteps_suffixClosure_support_eq_of_even
      run heven hsuffixOff
  have hprefixTrail :=
    CrossCentralExactFaceCutState.prefixTrail_eq_of_isPath_of_closure_support_eq
      source target hsourcePrefix htargetPrefix hprefixSupport
  have hsuffixTrail :=
    CrossCentralExactFaceCutState.suffixTrail_eq_of_isPath_of_closure_support_eq
      source target hsourceSuffix htargetSuffix hsuffixSupport
  exact ⟨hprefixTrail, hsuffixTrail,
    CrossCentralExactFaceCutPair.existsUnique_labelComplementProfile_of_trails_eq
      minimal source.2 target.2 hprefixTrail hsuffixTrail⟩

/-- A fixed-face run returning to the same retained cross either has the
four-state label-complement normal form, or strictly loses an off-face edge
on one of its two closure channels. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.exactSteps_labelComplementProfile_or_offFace_prefixLoss_or_suffixLoss
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
    (hsourcePrefix : source.2.prefixTrail.IsPath)
    (htargetPrefix : target.2.prefixTrail.IsPath)
    (hsourceSuffix : source.2.suffixTrail.IsPath)
    (htargetSuffix : target.2.suffixTrail.IsPath) :
    (Even length ∧
      source.2.prefixTrail = target.2.prefixTrail ∧
      source.2.suffixTrail = target.2.suffixTrail ∧
      ∃! profile : F2 × F2,
        (∀ selectedFace, target.2.prefixLabels selectedFace =
          source.2.prefixLabels selectedFace + profile.1) ∧
        (∀ selectedFace, target.2.suffixLabels selectedFace =
          source.2.suffixLabels selectedFace + profile.2)) ∨
    (∃ edge : G.edgeSet,
      edge ∉ orbitFaceBoundary graphData.toRotationSystem face ∧
      edge.1 ∈
          ((baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic).oppositePortClosure
              source.2.prefixTrail).edges ∧
      edge.1 ∉
          ((baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic).oppositePortClosure
              target.2.prefixTrail).edges) ∨
    (∃ edge : G.edgeSet,
      edge ∉ orbitFaceBoundary graphData.toRotationSystem face ∧
      edge.1 ∈
          ((baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic).alternateOppositePortClosure
              source.2.suffixTrail).edges ∧
      edge.1 ∉
          ((baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic).alternateOppositePortClosure
              target.2.suffixTrail).edges) := by
  classical
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  by_cases hprefixOff : ∀ edge : G.edgeSet,
      edge ∉ orbitFaceBoundary graphData.toRotationSystem face →
        (edge.1 ∈
            (data.oppositePortClosure source.2.prefixTrail).edges ↔
          edge.1 ∈
            (data.oppositePortClosure target.2.prefixTrail).edges)
  · have heven :=
      CrossCentralExactFaceCertifiedRebaseTransitionOnFace.exactSteps_length_even_of_cross_eq
        run hcross hprefixOff
    by_cases hsuffixOff : ∀ edge : G.edgeSet,
        edge ∉ orbitFaceBoundary graphData.toRotationSystem face →
          (edge.1 ∈
              (data.alternateOppositePortClosure
                source.2.suffixTrail).edges ↔
            edge.1 ∈
              (data.alternateOppositePortClosure
                target.2.suffixTrail).edges)
    · left
      have hnormal :=
        CrossCentralExactFaceCertifiedRebaseTransitionOnFace.exactSteps_trails_eq_and_existsUnique_labelComplementProfile_of_even
          run heven hprefixOff hsuffixOff hsourcePrefix htargetPrefix
            hsourceSuffix htargetSuffix
      exact ⟨heven, hnormal.1, hnormal.2.1, hnormal.2.2⟩
    · right
      right
      push Not at hsuffixOff
      rcases hsuffixOff with ⟨edge, hedgeOff, hnotIff⟩
      have htargetSource : edge.1 ∈
            (data.alternateOppositePortClosure target.2.suffixTrail).edges →
          edge.1 ∈
            (data.alternateOppositePortClosure source.2.suffixTrail).edges :=
        CrossCentralExactFaceCertifiedRebaseTransitionOnFace.reflTransGen_suffixClosure_offFace_subset
          run.to_reflTransGen edge hedgeOff
      have hloss : edge.1 ∈
            (data.alternateOppositePortClosure source.2.suffixTrail).edges ∧
          edge.1 ∉
            (data.alternateOppositePortClosure target.2.suffixTrail).edges := by
        tauto
      exact ⟨edge, hedgeOff, hloss⟩
  · right
    left
    push Not at hprefixOff
    rcases hprefixOff with ⟨edge, hedgeOff, hnotIff⟩
    have htargetSource : edge.1 ∈
          (data.oppositePortClosure target.2.prefixTrail).edges →
        edge.1 ∈
          (data.oppositePortClosure source.2.prefixTrail).edges :=
      CrossCentralExactFaceCertifiedRebaseTransitionOnFace.reflTransGen_prefixClosure_offFace_subset
        run.to_reflTransGen edge hedgeOff
    have hloss : edge.1 ∈
          (data.oppositePortClosure source.2.prefixTrail).edges ∧
        edge.1 ∉
          (data.oppositePortClosure target.2.prefixTrail).edges := by
      tauto
    exact ⟨edge, hedgeOff, hloss⟩

namespace CrossCentralExactFaceCertifiedRebaseCircuit

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

/-- If suffix support is lost during one displayed segment of a circuit,
the complementary segment contains a localized recovery step. -/
theorem exists_outside_suffixClosure_recovery
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (left middleFirst right :
      CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
    (before middleRest after : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))
    (hsplit : circuit.first :: circuit.rest =
      before ++
        (left :: ((middleFirst :: middleRest) ++ (right :: after))))
    (edge : G.edgeSet)
    (htarget : edge.1 ∉
      ((baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).alternateOppositePortClosure
          right.source.2.suffixTrail).edges)
    (hsource : edge.1 ∈
      ((baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).alternateOppositePortClosure
          middleFirst.source.2.suffixTrail).edges) :
    ∃ arc ∈ right :: (after ++ before ++ [left]),
      edge.1 ∉
          ((baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic).alternateOppositePortClosure
              arc.source.2.suffixTrail).edges ∧
        edge.1 ∈
          ((baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic).alternateOppositePortClosure
              arc.target.2.suffixTrail).edges ∧
        edge ∈ orbitFaceBoundary graphData.toRotationSystem
          arc.selectedFace := by
  let beforeRight := before ++ (left :: middleFirst :: middleRest)
  have hsplitRight : circuit.first :: circuit.rest =
      beforeRight ++ right :: after := by
    simpa [beforeRight, List.append_assoc] using hsplit
  let rotated := circuit.rotateAtSplit right beforeRight after hsplitRight
  let outsideRest := after ++ before ++ [left]
  have hrotatedList : rotated.first :: rotated.rest =
      (right :: outsideRest) ++ (middleFirst :: middleRest) := by
    simp [rotated, outsideRest, beforeRight, List.append_assoc]
  have houtsideChain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        (right :: outsideRest) := by
    have hrotatedChain := rotated.consecutive
    rw [hrotatedList] at hrotatedChain
    exact hrotatedChain.left_of_append
  have hleftFollows :
      CrossCentralExactFaceCertifiedRebaseArc.Follows left middleFirst := by
    apply (List.isChain_iff_forall_rel_of_append_cons_cons.mp
      circuit.consecutive)
    simpa [List.append_assoc] using hsplit
  have hlastTarget : edge.1 ∈
      ((baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).alternateOppositePortClosure
          ((right :: outsideRest).getLast
            (by simp)).target.2.suffixTrail).edges := by
    have hlastArc : (right :: outsideRest).getLast (by simp) = left := by
      simp [outsideRest]
    have hleftTarget : left.target = middleFirst.source := hleftFollows
    rw [hlastArc, hleftTarget]
    exact hsource
  simpa [outsideRest] using
    (exists_suffixClosure_gain right outsideRest houtsideChain edge
      htarget hlastTarget)

end CrossCentralExactFaceCertifiedRebaseCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
