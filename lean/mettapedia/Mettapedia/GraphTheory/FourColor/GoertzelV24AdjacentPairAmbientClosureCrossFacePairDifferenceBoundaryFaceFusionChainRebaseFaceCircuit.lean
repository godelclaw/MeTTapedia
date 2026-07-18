import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseOddMonodromy
import Mathlib.Data.List.Destutter

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24RebaseFaceCircuit

variable {State : Type*} [DecidableEq State]
  {relation : State → State → Prop}

private theorem exists_destutter'_eq_cons_and_isChain
    (anchor : State) (states : List State)
    (chain : List.IsChain (fun first second =>
      first = second ∨ relation first second) (anchor :: states)) :
    ∃ tail,
      states.destutter' (· ≠ ·) anchor =
          anchor :: tail ∧
        List.IsChain relation (anchor :: tail) := by
  induction states generalizing anchor with
  | nil =>
      exact ⟨[], by simp [List.destutter'],
        List.IsChain.singleton _⟩
  | cons next states ih =>
      have hparts := List.isChain_cons_cons.mp chain
      by_cases hne : anchor ≠ next
      · have hrelation : relation anchor next :=
          hparts.1.resolve_left hne
        rcases ih next hparts.2 with ⟨tail, htail, htailChain⟩
        refine ⟨next :: tail, ?_,
          List.IsChain.cons_cons hrelation htailChain⟩
        rw [List.destutter'_cons_pos states hne, htail]
      · have heq : next = anchor := not_ne_iff.mp hne |>.symm
        subst next
        rcases ih anchor hparts.2 with ⟨tail, htail, htailChain⟩
        exact ⟨tail, by rw [List.destutter'_cons_neg states hne, htail],
          htailChain⟩

/-- Collapsing adjacent repetitions turns an equality-or-relation chain
into a genuine relation chain. -/
theorem isChain_destutter_ne_of_isChain_eq_or
    (states : List State)
    (chain : List.IsChain (fun first second =>
      first = second ∨ relation first second) states) :
    List.IsChain relation (states.destutter (· ≠ ·)) := by
  cases states with
  | nil => simp [List.destutter]
  | cons anchor states =>
      rcases exists_destutter'_eq_cons_and_isChain anchor states chain with
        ⟨tail, htail, hchain⟩
      simpa only [List.destutter_cons', htail] using hchain

private theorem head_destutter'_ne
    (anchor : State) (states : List State) :
    (states.destutter' (· ≠ ·) anchor).head
        (List.destutter'_ne_nil states (· ≠ ·)) = anchor := by
  induction states generalizing anchor with
  | nil => simp [List.destutter']
  | cons next states ih =>
      by_cases hne : anchor ≠ next
      · simp [List.destutter'_cons_pos states hne]
      · simpa only [List.destutter'_cons_neg states hne] using ih anchor

private theorem getLast?_destutter'_ne
    (anchor : State) (states : List State) :
    (states.destutter' (· ≠ ·) anchor).getLast? =
      (anchor :: states).getLast? := by
  induction states generalizing anchor with
  | nil => simp [List.destutter']
  | cons next states ih =>
      by_cases hne : anchor ≠ next
      · rw [List.destutter'_cons_pos states hne]
        rw [List.getLast?_cons_of_ne_nil
          (List.destutter'_ne_nil states (· ≠ ·)), ih next]
        simp
      · have heq : next = anchor := not_ne_iff.mp hne |>.symm
        subst next
        rw [List.destutter'_cons_neg states hne]
        rw [ih anchor]
        simp

/-- Destuttering a nonempty list preserves its first element. -/
theorem head_destutter_ne_cons
    (anchor : State) (states : List State) :
    ((anchor :: states).destutter (· ≠ ·)).head
        (by
          change states.destutter' (· ≠ ·) anchor ≠ []
          exact List.destutter'_ne_nil states (· ≠ ·)) = anchor := by
  simpa only [List.destutter_cons'] using
    head_destutter'_ne anchor states

/-- Destuttering a nonempty list preserves its last element. -/
theorem getLast_destutter_ne_cons
    (anchor : State) (states : List State) :
    ((anchor :: states).destutter (· ≠ ·)).getLast
        (by
          change states.destutter' (· ≠ ·) anchor ≠ []
          exact List.destutter'_ne_nil states (· ≠ ·)) =
      (anchor :: states).getLast (by simp) := by
  let hdestutter : (anchor :: states).destutter (· ≠ ·) ≠ [] := by
    change states.destutter' (· ≠ ·) anchor ≠ []
    exact List.destutter'_ne_nil states (· ≠ ·)
  have hlast? : ((anchor :: states).destutter (· ≠ ·)).getLast? =
      (anchor :: states).getLast? := by
    simpa only [List.destutter_cons'] using
      getLast?_destutter'_ne anchor states
  rw [List.getLast?_eq_getLast_of_ne_nil hdestutter,
    List.getLast?_eq_getLast_of_ne_nil (by simp)] at hlast?
  exact Option.some.inj hlast?

/-- Every nonempty adjacency chain is the support of a graph walk with the
computed first and last vertices. -/
theorem exists_walk_support_eq_of_isChain
    {Vertex : Type*} {graph : SimpleGraph Vertex}
    (vertices : List Vertex) (hne : vertices ≠ [])
    (chain : List.IsChain graph.Adj vertices) :
    ∃ walk : graph.Walk (vertices.head hne) (vertices.getLast hne),
      walk.support = vertices := by
  induction vertices with
  | nil => exact False.elim (hne rfl)
  | cons first rest ih =>
      cases rest with
      | nil => exact ⟨SimpleGraph.Walk.nil, rfl⟩
      | cons second rest =>
          have hparts := List.isChain_cons_cons.mp chain
          rcases ih (by simp) hparts.2 with ⟨walk, hsupport⟩
          exact ⟨walk.cons hparts.1, by simpa [hsupport]⟩

end GoertzelV24RebaseFaceCircuit

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- One directed exact rebase together with its provenance-certified
selected face. -/
structure CrossCentralExactFaceCertifiedRebaseArc
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G) where
  source : CrossCentralExactFaceCutState graphData
    (baseData.rotationOrderedData graphData minimal.spherical.cubic
      minimal.vertexRotationCyclic)
  target : CrossCentralExactFaceCutState graphData
    (baseData.rotationOrderedData graphData minimal.spherical.cubic
      minimal.vertexRotationCyclic)
  selectedFace : OrbitFace graphData.toRotationSystem
  transition : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
    graphData minimal baseData selectedFace source target

namespace CrossCentralExactFaceCertifiedRebaseArc

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

/-- Consecutive arcs meet in the same complete exact-cut state. -/
def Follows
    (first second : CrossCentralExactFaceCertifiedRebaseArc graphData
      minimal baseData) : Prop :=
  first.target = second.source

/-- The selected face packaged as a vertex of the full facial dual. -/
def dualFace
    (arc : CrossCentralExactFaceCertifiedRebaseArc graphData minimal
      baseData) :
    AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem)) :=
  ⟨arc.selectedFace, Finset.mem_univ _⟩

/-- Every provenance-certified transition has a selected-face arc. -/
theorem exists_of_transition
    {source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (transition : CrossCentralExactFaceCertifiedRebaseTransition
      graphData minimal baseData source target) :
    ∃ arc : CrossCentralExactFaceCertifiedRebaseArc graphData minimal
        baseData,
      arc.source = source ∧ arc.target = target := by
  rcases transition with ⟨step, htarget⟩
  exact ⟨{
    source := source
    target := target
    selectedFace := step.selectedFace
    transition := ⟨step, htarget, rfl⟩ }, rfl, rfl⟩

/-- A certified arc changes its retained cross. -/
theorem cross_ne
    (arc : CrossCentralExactFaceCertifiedRebaseArc graphData minimal
      baseData) :
    arc.target.1 ≠ arc.source.1 :=
  arc.transition.cross_ne

/-- At a change of selected face, two consecutive arcs give one genuine
edge of the full facial dual. -/
theorem Follows.dual_adj_of_selectedFace_ne
    {first second : CrossCentralExactFaceCertifiedRebaseArc graphData
      minimal baseData}
    (follows : Follows first second)
    (hfaces : first.selectedFace ≠ second.selectedFace) :
    (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Adj
        first.dualFace second.dualFace := by
  have secondTransition :
      CrossCentralExactFaceCertifiedRebaseTransitionOnFace graphData
        minimal baseData second.selectedFace first.target second.target := by
    rw [follows]
    exact second.transition
  apply
    interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
      (orbitFace_incidence_le_two graphData.toRotationSystem)
      hfaces
  · exact first.transition.target_cross_mem_face
  · exact secondTransition.source_cross_mem_face

/-- The primal edge crossed by the preceding dual step is exactly the
intermediate retained cross. -/
theorem Follows.sharedInteriorEdge_eq_intermediate_cross
    {first second : CrossCentralExactFaceCertifiedRebaseArc graphData
      minimal baseData}
    (follows : Follows first second)
    (hfaces : first.selectedFace ≠ second.selectedFace) :
    sharedInteriorEdgeOfAdjOfPairwiseUnique
        (orbitFaceBoundary graphData.toRotationSystem)
        (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
        (pairwiseUniqueSharedInteriorEdges graphData minimal)
        (follows.dual_adj_of_selectedFace_ne hfaces) =
      retainedEdgeToAmbientEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) first.target.1 := by
  let edge := retainedEdgeToAmbientEdge
    (baseData.rotationOrderedData graphData minimal.spherical.cubic
      minimal.vertexRotationCyclic) first.target.1
  apply sharedInteriorEdgeOfAdjOfPairwiseUnique_eq_of_mem_sharedInteriorEdges
  apply (mem_sharedInteriorEdges_iff
    (orbitFaceBoundary graphData.toRotationSystem)
    (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).2
  have secondTransition :
      CrossCentralExactFaceCertifiedRebaseTransitionOnFace graphData
        minimal baseData second.selectedFace first.target second.target := by
    rw [follows]
    exact second.transition
  have hfirst : edge ∈ orbitFaceBoundary graphData.toRotationSystem
      first.selectedFace := first.transition.target_cross_mem_face
  have hsecond : edge ∈ orbitFaceBoundary graphData.toRotationSystem
      second.selectedFace := secondTransition.source_cross_mem_face
  refine ⟨?_, hfirst, hsecond⟩
  exact (mem_interiorEdgeSupport_iff
    (orbitFaceBoundary graphData.toRotationSystem)
    (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).2
      ⟨Finset.mem_biUnion.2
          ⟨first.selectedFace, Finset.mem_univ _, hfirst⟩,
        totalIncidenceCount_eq_two_of_mem_faceBoundary_of_mem_faceBoundary_of_ne
          (orbitFaceBoundary graphData.toRotationSystem)
          (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
          (orbitFace_incidence_le_two graphData.toRotationSystem)
          (Finset.mem_univ _) (Finset.mem_univ _) hfaces hfirst hsecond⟩

/-- Three consecutive arcs cannot project to a nontrivial dual step followed
immediately by its reverse. -/
theorem no_selectedFace_backtrack
    {first second third : CrossCentralExactFaceCertifiedRebaseArc
      graphData minimal baseData}
    (firstFollows : Follows first second)
    (secondFollows : Follows second third)
    (hfirstSecond : first.selectedFace ≠ second.selectedFace)
    (hthirdFirst : third.selectedFace = first.selectedFace) : False := by
  have secondTransition :
      CrossCentralExactFaceCertifiedRebaseTransitionOnFace graphData
        minimal baseData second.selectedFace first.target second.target := by
    rw [firstFollows]
    exact second.transition
  have thirdTransition :
      CrossCentralExactFaceCertifiedRebaseTransitionOnFace graphData
        minimal baseData first.selectedFace second.target third.target := by
    rw [secondFollows, ← hthirdFirst]
    exact third.transition
  exact first.transition.no_immediate_face_backtrack secondTransition
    thirdTransition hfirstSecond

end CrossCentralExactFaceCertifiedRebaseArc

/-- A nonempty cyclic list of selected-face arcs.  Its list order is the
exact-state transition order, including the final-to-initial state match. -/
structure CrossCentralExactFaceCertifiedRebaseCircuit
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G) where
  first : CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData
  rest : List
    (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
  consecutive : List.IsChain
    CrossCentralExactFaceCertifiedRebaseArc.Follows (first :: rest)
  closing : CrossCentralExactFaceCertifiedRebaseArc.Follows
    ((first :: rest).getLast (by simp)) first

namespace CrossCentralExactFaceCertifiedRebaseCircuit

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

/-- The selected-face list with its initial face repeated at the end. -/
def cyclicDualFaces
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) :
    List (AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))) :=
  circuit.first.dualFace ::
    (circuit.rest.map
      CrossCentralExactFaceCertifiedRebaseArc.dualFace ++
        [circuit.first.dualFace])

/-- The face itinerary with adjacent repetitions collapsed. -/
def compressedDualFaces
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) :
    List (AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))) :=
  circuit.cyclicDualFaces.destutter (· ≠ ·)

/-- Before adjacent repetitions are collapsed, consecutive selected faces
are equal or adjacent in the full facial dual. -/
theorem cyclicDualFaces_isChain_eq_or_adj
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) :
    List.IsChain (fun first second =>
      first = second ∨
        (interiorDualGraph
          (orbitFaceBoundary graphData.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace graphData.toRotationSystem))).Adj first second)
      circuit.cyclicDualFaces := by
  let arcList := circuit.first :: circuit.rest
  have hArcCyclic : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        (arcList ++ [circuit.first]) := by
    apply circuit.consecutive.append (List.IsChain.singleton _)
    intro last hlast first hfirst
    have hfirstEq : first = circuit.first := by simpa using hfirst.symm
    subst first
    rcases List.mem_getLast?_eq_getLast hlast with ⟨hne, hlastEq⟩
    subst last
    exact circuit.closing
  have hFaceCyclic : List.IsChain (fun first second =>
      first = second ∨
        (interiorDualGraph
          (orbitFaceBoundary graphData.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace graphData.toRotationSystem))).Adj first second)
      ((arcList ++ [circuit.first]).map
        CrossCentralExactFaceCertifiedRebaseArc.dualFace) := by
    rw [List.isChain_map]
    exact hArcCyclic.imp (fun first second follows => by
      by_cases hfaces : first.selectedFace = second.selectedFace
      · have hdualFaces : first.dualFace = second.dualFace :=
          Subtype.ext hfaces
        exact Or.inl hdualFaces
      · exact Or.inr (follows.dual_adj_of_selectedFace_ne hfaces))
  simpa [arcList, cyclicDualFaces] using hFaceCyclic

/-- After collapsing adjacent repetitions, the selected faces form an
actual adjacency chain in the full facial dual. -/
theorem compressedDualFaces_isChain
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) :
    List.IsChain
      (interiorDualGraph
        (orbitFaceBoundary graphData.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace graphData.toRotationSystem))).Adj
      circuit.compressedDualFaces := by
  exact GoertzelV24RebaseFaceCircuit.isChain_destutter_ne_of_isChain_eq_or
    circuit.cyclicDualFaces circuit.cyclicDualFaces_isChain_eq_or_adj

/-- The compressed facial itinerary is nonempty. -/
theorem compressedDualFaces_ne_nil
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) :
    circuit.compressedDualFaces ≠ [] := by
  unfold compressedDualFaces cyclicDualFaces
  rw [List.destutter_cons']
  exact List.destutter'_ne_nil _ _

/-- The compressed facial itinerary begins at the circuit's first selected
face. -/
theorem compressedDualFaces_head
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) :
    circuit.compressedDualFaces.head circuit.compressedDualFaces_ne_nil =
      circuit.first.dualFace := by
  simpa only [compressedDualFaces, cyclicDualFaces] using
    GoertzelV24RebaseFaceCircuit.head_destutter_ne_cons
      circuit.first.dualFace
      (circuit.rest.map
        CrossCentralExactFaceCertifiedRebaseArc.dualFace ++
          [circuit.first.dualFace])

/-- The repeated final face survives compression as the last face. -/
theorem compressedDualFaces_getLast
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) :
    circuit.compressedDualFaces.getLast circuit.compressedDualFaces_ne_nil =
      circuit.first.dualFace := by
  calc
    circuit.compressedDualFaces.getLast circuit.compressedDualFaces_ne_nil =
        circuit.cyclicDualFaces.getLast (by simp [cyclicDualFaces]) := by
      simpa only [compressedDualFaces, cyclicDualFaces] using
        GoertzelV24RebaseFaceCircuit.getLast_destutter_ne_cons
          circuit.first.dualFace
          (circuit.rest.map
            CrossCentralExactFaceCertifiedRebaseArc.dualFace ++
              [circuit.first.dualFace])
    _ = circuit.first.dualFace := by simp [cyclicDualFaces]

/-- Every exact rebase circuit therefore has a closed walk in the full
facial dual whose support is precisely its compressed face itinerary. -/
theorem exists_closedDualWalk
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) :
    ∃ walk :
        (interiorDualGraph
          (orbitFaceBoundary graphData.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace graphData.toRotationSystem))).Walk
          circuit.first.dualFace circuit.first.dualFace,
      walk.support = circuit.compressedDualFaces := by
  rcases GoertzelV24RebaseFaceCircuit.exists_walk_support_eq_of_isChain
      circuit.compressedDualFaces circuit.compressedDualFaces_ne_nil
        circuit.compressedDualFaces_isChain with ⟨walk, hsupport⟩
  let closed := walk.copy circuit.compressedDualFaces_head
    circuit.compressedDualFaces_getLast
  exact ⟨closed, by simpa [closed] using hsupport⟩

/-- A transitive closed exact-state run retains all of its selected-face
provenance as a cyclic arc list. -/
theorem exists_of_transGen_cycle
    {state : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (cycle : Relation.TransGen
      (CrossCentralExactFaceCertifiedRebaseTransition graphData minimal
        baseData) state state) :
    Nonempty (CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) := by
  have existsArcChain : ∀ {source target :
      CrossCentralExactFaceCutState graphData
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic)},
      Relation.TransGen
          (CrossCentralExactFaceCertifiedRebaseTransition graphData minimal
            baseData) source target →
        ∃ (first : CrossCentralExactFaceCertifiedRebaseArc graphData
              minimal baseData)
            (rest : List (CrossCentralExactFaceCertifiedRebaseArc graphData
              minimal baseData)),
          List.IsChain CrossCentralExactFaceCertifiedRebaseArc.Follows
              (first :: rest) ∧
            first.source = source ∧
            ((first :: rest).getLast (by simp)).target = target := by
    intro source target run
    induction run using Relation.TransGen.head_induction_on with
    | single transition =>
        rcases
            CrossCentralExactFaceCertifiedRebaseArc.exists_of_transition
              transition with ⟨arc, hsource, htarget⟩
        exact ⟨arc, [], List.IsChain.singleton _, hsource, by simpa using htarget⟩
    | @head source middle transition run ih =>
        rcases ih with ⟨first, rest, hchain, hsource, htarget⟩
        rcases
            CrossCentralExactFaceCertifiedRebaseArc.exists_of_transition
              transition with ⟨arc, harcSource, harcTarget⟩
        refine ⟨arc, first :: rest, ?_, harcSource, ?_⟩
        · apply List.IsChain.cons_cons
          · exact harcTarget.trans hsource.symm
          · exact hchain
        · simpa using htarget
  rcases existsArcChain cycle with
    ⟨first, rest, hchain, hsource, htarget⟩
  exact ⟨{
    first := first
    rest := rest
    consecutive := hchain
    closing := htarget.trans hsource.symm }⟩

end CrossCentralExactFaceCertifiedRebaseCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
