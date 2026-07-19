import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferSuccessor
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitConstantFaceCellBoundaryArc
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.List.Destutter

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

private theorem isChain_ne_append_head_of_nodup
    {α : Type*}
    (head : α) (tail : List α)
    (htail : tail ≠ [])
    (hnodup : (head :: tail).Nodup) :
    List.IsChain (· ≠ ·) (head :: tail ++ [head]) := by
  have hheadNotMem : head ∉ tail := (List.nodup_cons.mp hnodup).1
  have hchain : List.IsChain (· ≠ ·) (head :: tail) :=
    (List.nodup_iff_pairwise_ne.mp hnodup).isChain
  apply hchain.append (List.IsChain.singleton head)
  intro last hlast first hfirst
  have hfirstEq : first = head := by simpa using hfirst.symm
  subst first
  have hlastTail : last ∈ tail := by
    rcases List.mem_getLast?_eq_getLast hlast with ⟨hne, hlastEq⟩
    subst last
    rw [List.getLast_cons htail]
    exact List.getLast_mem htail
  exact fun hlastEq => hheadNotMem (hlastEq ▸ hlastTail)

private theorem mem_destutter_ne_iff
    {α : Type*} [DecidableEq α] (element : α) (entries : List α) :
    element ∈ entries.destutter (· ≠ ·) ↔ element ∈ entries := by
  have mem_destutter'_ne_iff : ∀ (anchor : α) (tail : List α),
      element ∈ tail.destutter' (· ≠ ·) anchor ↔
        element = anchor ∨ element ∈ tail := by
    intro anchor tail
    induction tail generalizing anchor with
    | nil => simp
    | cons next tail ih =>
        by_cases hnext : anchor ≠ next
        · rw [List.destutter'_cons_pos tail hnext, List.mem_cons, ih]
          simp only [List.mem_cons]
        · have hnextEq : next = anchor := not_ne_iff.mp hnext |>.symm
          subst next
          rw [List.destutter'_cons_neg tail hnext, ih]
          simp
  cases entries with
  | nil => simp
  | cons anchor tail =>
      rw [List.destutter_cons', mem_destutter'_ne_iff]
      simp

private theorem getVert_add_two_eq_of_consecutive_edges_eq
    {Vertex : Type*} {graph : SimpleGraph Vertex}
    {start finish : Vertex} (walk : graph.Walk start finish)
    {index : ℕ} (hindex : index + 1 < walk.edges.length)
    (hedges : walk.edges[index] = walk.edges[index + 1]) :
    walk.getVert index = walk.getVert (index + 2) := by
  have hfirst : index < walk.darts.length := by
    rw [walk.length_darts]
    rw [walk.length_edges] at hindex
    omega
  have hsecond : index + 1 < walk.darts.length := by
    simpa [walk.length_darts, walk.length_edges] using hindex
  have hindexLength : index < walk.length := by
    simpa [walk.length_darts] using hfirst
  have hedges' : walk.darts[index].edge =
      walk.darts[index + 1].edge := by
    simpa [SimpleGraph.Walk.edges] using hedges
  rw [walk.darts_getElem_eq_getVert index hfirst,
    walk.darts_getElem_eq_getVert (index + 1) hsecond] at hedges'
  simp only [SimpleGraph.Dart.edge_mk] at hedges'
  rcases Sym2.eq_iff.mp hedges' with hforward | hreverse
  · exact False.elim
      ((walk.adj_getVert_succ hindexLength).ne hforward.1)
  · simpa [Nat.add_assoc] using hreverse.1

private theorem exists_tail_destutter'_eq_cons
    {α : Type*} {relation : α → α → Prop}
    [DecidableRel relation]
    (anchor : α) (states : List α) :
    ∃ output, states.destutter' relation anchor = anchor :: output := by
  induction states generalizing anchor with
  | nil => exact ⟨[], rfl⟩
  | cons next states ih =>
      by_cases hrel : relation anchor next
      · rcases ih next with ⟨output, houtput⟩
        exact ⟨next :: output, by
          rw [List.destutter'_cons_pos states hrel, houtput]⟩
      · rcases ih anchor with ⟨output, houtput⟩
        exact ⟨output, by
          rw [List.destutter'_cons_neg states hrel, houtput]⟩

private theorem exists_first_change_of_destutter'_eq_cons_cons
    {α : Type*} {relation : α → α → Prop}
    [DecidableRel relation]
    (anchor next : α) (states output : List α)
    (hdestutter : states.destutter' relation anchor =
      anchor :: next :: output) :
    ∃ front suffix,
      states = front ++ next :: suffix ∧
      (∀ state ∈ front, ¬ relation anchor state) ∧
      suffix.destutter' relation next = next :: output := by
  induction states generalizing anchor with
  | nil => simp at hdestutter
  | cons current states ih =>
      by_cases hrel : relation anchor current
      · rw [List.destutter'_cons_pos states hrel] at hdestutter
        have htail : states.destutter' relation current =
            next :: output := (List.cons.inj hdestutter).2
        rcases exists_tail_destutter'_eq_cons
            (relation := relation) current states with
          ⟨tail, hhead⟩
        have hcurrent : current = next := by
          rw [hhead] at htail
          exact (List.cons.inj htail).1
        subst current
        exact ⟨[], states, by simp, by simp, htail⟩
      · rw [List.destutter'_cons_neg states hrel] at hdestutter
        rcases ih anchor hdestutter with
          ⟨front, suffix, hstates, hfront, hsuffix⟩
        refine ⟨current :: front, suffix, ?_, ?_, hsuffix⟩
        · simp [hstates]
        · intro state hstate
          rcases List.mem_cons.mp hstate with rfl | hstate
          · exact hrel
          · exact hfront state hstate

private theorem exists_two_runs_of_destutter'_eq_backtrack
    {α : Type*} {relation : α → α → Prop}
    [DecidableRel relation]
    (outer middle returning : α) (states after : List α)
    (hdestutter : states.destutter' relation outer =
      outer :: middle :: returning :: after) :
    ∃ outerTail middleTail suffix,
      states = outerTail ++ middle :: middleTail ++ returning :: suffix ∧
      (∀ state ∈ outerTail, ¬ relation outer state) ∧
      (∀ state ∈ middleTail, ¬ relation middle state) := by
  rcases exists_first_change_of_destutter'_eq_cons_cons
      outer middle states (returning :: after) hdestutter with
    ⟨outerTail, middleSuffix, hstates, houter, hmiddleDestutter⟩
  rcases exists_first_change_of_destutter'_eq_cons_cons
      middle returning middleSuffix after hmiddleDestutter with
    ⟨middleTail, suffix, hmiddleSuffix, hmiddle, _⟩
  refine ⟨outerTail, middleTail, suffix, ?_, houter, hmiddle⟩
  rw [hstates, hmiddleSuffix]
  simp only [List.cons_append, List.append_assoc]

private theorem exists_runs_of_destutter_eq_append_backtrack
    {α : Type*} {relation : α → α → Prop}
    [DecidableRel relation]
    (anchor outer middle returning : α)
    (states before after : List α)
    (hdestutter : (anchor :: states).destutter relation =
      before ++ outer :: middle :: returning :: after) :
    ∃ physicalBefore outerTail middleTail physicalAfter,
      anchor :: states =
        physicalBefore ++
          outer :: outerTail ++ middle :: middleTail ++
            returning :: physicalAfter ∧
      (∀ state ∈ outerTail, ¬ relation outer state) ∧
      (∀ state ∈ middleTail, ¬ relation middle state) := by
  induction before generalizing anchor states with
  | nil =>
      rw [List.destutter_cons'] at hdestutter
      rcases exists_tail_destutter'_eq_cons
          (relation := relation) anchor states with ⟨output, hhead⟩
      have hanchor : anchor = outer := by
        rw [hhead] at hdestutter
        exact (List.cons.inj hdestutter).1
      subst anchor
      rcases exists_two_runs_of_destutter'_eq_backtrack
          outer middle returning states after hdestutter with
        ⟨outerTail, middleTail, physicalAfter, hstates, houter, hmiddle⟩
      exact ⟨[], outerTail, middleTail, physicalAfter,
        by simp [hstates], houter, hmiddle⟩
  | cons first before ih =>
      rw [List.destutter_cons'] at hdestutter
      rcases exists_tail_destutter'_eq_cons
          (relation := relation) anchor states with ⟨output, hhead⟩
      have hanchor : anchor = first := by
        rw [hhead] at hdestutter
        exact (List.cons.inj hdestutter).1
      subst first
      cases before with
      | nil =>
          rcases exists_first_change_of_destutter'_eq_cons_cons
              anchor outer states (middle :: returning :: after)
                hdestutter with
            ⟨initialTail, suffix, hstates, hinitial, hsuffix⟩
          have hrecursive :
              (outer :: suffix).destutter relation =
                outer :: middle :: returning :: after := by
            simpa [List.destutter_cons'] using hsuffix
          rcases ih outer suffix hrecursive with
            ⟨physicalBefore, outerTail, middleTail, physicalAfter,
              hphysical, houter, hmiddle⟩
          refine ⟨anchor :: initialTail ++ physicalBefore,
            outerTail, middleTail, physicalAfter, ?_, houter, hmiddle⟩
          rw [hstates, hphysical]
          simp only [List.cons_append, List.append_assoc]
      | cons second before =>
          rcases exists_first_change_of_destutter'_eq_cons_cons
              anchor second states
                (before ++ outer :: middle :: returning :: after)
                hdestutter with
            ⟨initialTail, suffix, hstates, hinitial, hsuffix⟩
          have hrecursive :
              (second :: suffix).destutter relation =
                (second :: before) ++
                  outer :: middle :: returning :: after := by
            simpa [List.destutter_cons'] using hsuffix
          rcases ih second suffix hrecursive with
            ⟨physicalBefore, outerTail, middleTail, physicalAfter,
              hphysical, houter, hmiddle⟩
          refine ⟨anchor :: initialTail ++ physicalBefore,
            outerTail, middleTail, physicalAfter, ?_, houter, hmiddle⟩
          rw [hstates, hphysical]
          simp only [List.cons_append, List.append_assoc]

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace CrossCentralExactFaceCertifiedRebaseCircuit

/-- The certified rebase arc displayed at a physical circuit position. -/
def arcAt
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (position : Fin circuit.arcLength) :
    CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData :=
  (circuit.first :: circuit.rest).get position

/-- The selected face displayed at a physical circuit position. -/
def selectedFaceAt
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (position : Fin circuit.arcLength) :
    OrbitFace graphData.toRotationSystem :=
  (circuit.arcAt position).selectedFace

/-- The physical selected-face word of a certified rebase circuit. -/
def selectedFaceWord
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) :
    List (OrbitFace graphData.toRotationSystem) :=
  (circuit.first :: circuit.rest).map
    CrossCentralExactFaceCertifiedRebaseArc.selectedFace

/-- The same physical word, with faces packaged as vertices of the full
facial dual. -/
def dualFaceWord
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) :
    List (AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))) :=
  (circuit.first :: circuit.rest).map
    CrossCentralExactFaceCertifiedRebaseArc.dualFace

@[simp] theorem selectedFaceWord_length
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) :
    circuit.selectedFaceWord.length = circuit.arcLength := by
  simp [selectedFaceWord, arcLength]

/-- The set underlying the physical selected-face word is exactly the
previously defined selected-face finset. -/
theorem selectedFaceWord_toFinset
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) :
    circuit.selectedFaceWord.toFinset = circuit.selectedFaces := by
  classical
  ext face
  simp [selectedFaceWord,
    CrossCentralExactFaceCertifiedRebaseCircuit.mem_selectedFaces, eq_comm]

@[simp] theorem dualFaceWord_length
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) :
    circuit.dualFaceWord.length = circuit.arcLength := by
  simp [dualFaceWord, arcLength]

/-- The pre-compression closed dual itinerary is the dual-face word with
its first face repeated once at the end. -/
theorem cyclicDualFaces_eq_dualFaceWord_append
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) :
    circuit.cyclicDualFaces =
      circuit.dualFaceWord ++ [circuit.first.dualFace] := by
  simp [cyclicDualFaces, dualFaceWord]

/-- Every face in the pre-compression closed itinerary avoids the restored
central edge. -/
theorem central_not_mem_of_mem_cyclicDualFaces
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    {face : AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))}
    (hface : face ∈ circuit.cyclicDualFaces) :
    centralEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) ∉
      orbitFaceBoundary graphData.toRotationSystem face.1 := by
  have hword : face ∈ circuit.dualFaceWord := by
    rw [circuit.cyclicDualFaces_eq_dualFaceWord_append] at hface
    rcases List.mem_append.1 hface with hface | hface
    · exact hface
    · have hfirst : face = circuit.first.dualFace := by simpa using hface
      rw [hfirst]
      exact List.mem_map_of_mem (f :=
        CrossCentralExactFaceCertifiedRebaseArc.dualFace) (by simp)
  rcases List.mem_map.1 hword with ⟨arc, _harc, rfl⟩
  exact arc.transition.central_not_mem_face

/-- Every face in the pre-compression closed itinerary likewise avoids
all four restored boundary edges. -/
theorem boundary_not_mem_of_mem_cyclicDualFaces
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    {face : AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))}
    (hface : face ∈ circuit.cyclicDualFaces)
    (port : Fin 4) :
    boundaryEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) port ∉
      orbitFaceBoundary graphData.toRotationSystem face.1 := by
  have hword : face ∈ circuit.dualFaceWord := by
    rw [circuit.cyclicDualFaces_eq_dualFaceWord_append] at hface
    rcases List.mem_append.1 hface with hface | hface
    · exact hface
    · have hfirst : face = circuit.first.dualFace := by simpa using hface
      rw [hfirst]
      exact List.mem_map_of_mem (f :=
        CrossCentralExactFaceCertifiedRebaseArc.dualFace) (by simp)
  rcases List.mem_map.1 hword with ⟨arc, _harc, rfl⟩
  exact arc.transition.boundary_not_mem_face port

/-- A simple facial-dual cycle extracted from the rebase itinerary,
together with its avoidance of the restored adjacent-pair frame. -/
structure RemoteDualCycle
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) where
  start : AmbientFace
    (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
  walk :
    (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Walk
      start start
  isCycle : walk.IsCycle
  central_not_mem : ∀ face ∈ walk.support,
    centralEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) ∉
      orbitFaceBoundary graphData.toRotationSystem face.1
  boundary_not_mem : ∀ face ∈ walk.support, ∀ port : Fin 4,
    boundaryEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) port ∉
      orbitFaceBoundary graphData.toRotationSystem face.1

/-- A nontrivial remote closed facial-dual walk whose repeated edge is
the obstruction to immediate simple-cycle extraction. -/
structure RemoteNontrailDualWalk
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) where
  walk :
    (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Walk
      circuit.first.dualFace circuit.first.dualFace
  support_eq : walk.support = circuit.compressedDualFaces
  ne_nil : walk ≠ .nil
  not_isTrail : ¬walk.IsTrail
  central_not_mem : ∀ face ∈ walk.support,
    centralEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) ∉
      orbitFaceBoundary graphData.toRotationSystem face.1
  boundary_not_mem : ∀ face ∈ walk.support, ∀ port : Fin 4,
    boundaryEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) port ∉
      orbitFaceBoundary graphData.toRotationSystem face.1

/-- A literal two-step return in the compressed selected-face itinerary. -/
structure CompressedFaceBacktrack
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) where
  index : ℕ
  index_add_two_lt : index + 2 < circuit.compressedDualFaces.length
  outer_eq : circuit.compressedDualFaces[index] =
    circuit.compressedDualFaces[index + 2]
  adjacent_ne : circuit.compressedDualFaces[index] ≠
    circuit.compressedDualFaces[index + 1]

/-- A remote nontrail itinerary contains a concrete repeated unoriented
edge of the full facial dual. -/
theorem RemoteNontrailDualWalk.exists_duplicate_edge
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (nontrail : RemoteNontrailDualWalk circuit) :
    ∃ edge, List.Duplicate edge nontrail.walk.edges := by
  apply List.exists_duplicate_iff_not_nodup.mpr
  intro hnodup
  exact nontrail.not_isTrail
    ((SimpleGraph.Walk.isTrail_def nontrail.walk).2 hnodup)

/-- In an acyclic support, the repeated edge of a remote closed walk is
already an immediate return across one unoriented dual edge. -/
theorem RemoteNontrailDualWalk.exists_immediate_return_of_acyclic
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (nontrail : RemoteNontrailDualWalk circuit)
    (hacyclic : nontrail.walk.toSubgraph.coe.IsAcyclic) :
    ∃ index, index + 1 < nontrail.walk.edges.length ∧
      nontrail.walk.getVert index =
        nontrail.walk.getVert (index + 2) := by
  let supportedWalk := nontrail.walk.mapToSubgraph
  have hnotTrail : ¬ supportedWalk.IsTrail := by
    intro htrail
    have hmapped := SimpleGraph.Walk.map_isTrail_of_injective
      nontrail.walk.toSubgraph.hom_injective htrail
    rw [nontrail.walk.map_mapToSubgraph_hom] at hmapped
    exact nontrail.not_isTrail hmapped
  have hnotChain : ¬ List.IsChain (· ≠ ·) supportedWalk.edges := by
    intro hchain
    exact hnotTrail
      (((hacyclic.isPath_iff_isChain supportedWalk).2 hchain).isTrail)
  rcases List.exists_not_getElem_of_not_isChain hnotChain with
    ⟨index, hindex, hedges⟩
  have hedgesEq : supportedWalk.edges[index] =
      supportedWalk.edges[index + 1] := not_ne_iff.mp hedges
  have hreturn := getVert_add_two_eq_of_consecutive_edges_eq
    supportedWalk hindex hedgesEq
  have hmappedReturn := congrArg
    (fun face => nontrail.walk.toSubgraph.hom face) hreturn
  rw [← SimpleGraph.Walk.getVert_map,
    ← SimpleGraph.Walk.getVert_map,
    nontrail.walk.map_mapToSubgraph_hom] at hmappedReturn
  have hlength : supportedWalk.length = nontrail.walk.length := by
    calc
      supportedWalk.length =
          (supportedWalk.map nontrail.walk.toSubgraph.hom).length :=
        (SimpleGraph.Walk.length_map
          (p := supportedWalk)
          (f := nontrail.walk.toSubgraph.hom)).symm
      _ = nontrail.walk.length := by
        simpa [supportedWalk] using congrArg SimpleGraph.Walk.length
          nontrail.walk.map_mapToSubgraph_hom
  have hindexOriginal : index + 1 < nontrail.walk.edges.length := by
    rw [supportedWalk.length_edges, hlength,
      ← nontrail.walk.length_edges] at hindex
    exact hindex
  exact ⟨index, hindexOriginal, hmappedReturn⟩

/-- Pure tree backtracking therefore appears as a literal `F,G,F`
segment of the compressed selected-face word. -/
theorem RemoteNontrailDualWalk.exists_compressedFaceBacktrack_of_acyclic
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (nontrail : RemoteNontrailDualWalk circuit)
    (hacyclic : nontrail.walk.toSubgraph.coe.IsAcyclic) :
    Nonempty (CompressedFaceBacktrack circuit) := by
  rcases nontrail.exists_immediate_return_of_acyclic hacyclic with
    ⟨index, hindex, hreturn⟩
  have hindexSupport : index + 2 < nontrail.walk.support.length := by
    rw [nontrail.walk.length_support, ← nontrail.walk.length_edges]
    omega
  have hindexZero : index < nontrail.walk.support.length := by omega
  have hindexOne : index + 1 < nontrail.walk.support.length := by omega
  have hindexCompressed : index + 2 <
      circuit.compressedDualFaces.length := by
    rw [← nontrail.support_eq]
    exact hindexSupport
  have houter : nontrail.walk.support[index] =
      nontrail.walk.support[index + 2] := by
    rw [nontrail.walk.support_getElem_eq_getVert
        (n := index) hindexZero,
      nontrail.walk.support_getElem_eq_getVert
        (n := index + 2) hindexSupport]
    exact hreturn
  have hadjacent : nontrail.walk.support[index] ≠
      nontrail.walk.support[index + 1] := by
    rw [nontrail.walk.support_getElem_eq_getVert
        (n := index) hindexZero,
      nontrail.walk.support_getElem_eq_getVert
        (n := index + 1) hindexOne]
    exact (nontrail.walk.adj_getVert_succ (by
      rw [← nontrail.walk.length_edges]
      omega)).ne
  refine ⟨{
    index := index
    index_add_two_lt := hindexCompressed
    outer_eq := ?_
    adjacent_ne := ?_ }⟩
  · simpa [nontrail.support_eq] using houter
  · simpa [nontrail.support_eq] using hadjacent

/-- Unless its edge support is a forest, a remote nontrail itinerary
already contains a remote simple dual cycle. -/
theorem RemoteNontrailDualWalk.acyclic_toSubgraph_or_exists_remoteDualCycle
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (nontrail : RemoteNontrailDualWalk circuit) :
    nontrail.walk.toSubgraph.coe.IsAcyclic ∨
      Nonempty (RemoteDualCycle circuit) := by
  classical
  by_cases hacyclic : nontrail.walk.toSubgraph.coe.IsAcyclic
  · exact Or.inl hacyclic
  · right
    simp only [SimpleGraph.IsAcyclic, not_forall, not_not] at hacyclic
    rcases hacyclic with ⟨vertex, cycle, hcycle⟩
    let ambientCycle := cycle.map nontrail.walk.toSubgraph.hom
    have hambientCycle : ambientCycle.IsCycle :=
      (SimpleGraph.Walk.map_isCycle_iff_of_injective
        nontrail.walk.toSubgraph.hom_injective).2 hcycle
    refine ⟨{
      start := nontrail.walk.toSubgraph.hom vertex
      walk := ambientCycle
      isCycle := hambientCycle
      central_not_mem := ?_
      boundary_not_mem := ?_ }⟩
    · intro face hface
      rw [SimpleGraph.Walk.support_map] at hface
      rcases List.mem_map.1 hface with ⟨subface, hsubface, hfaceEq⟩
      subst face
      exact nontrail.central_not_mem subface.1
        ((nontrail.walk.mem_verts_toSubgraph).1 subface.2)
    · intro face hface port
      rw [SimpleGraph.Walk.support_map] at hface
      rcases List.mem_map.1 hface with ⟨subface, hsubface, hfaceEq⟩
      subst face
      exact nontrail.boundary_not_mem subface.1
        ((nontrail.walk.mem_verts_toSubgraph).1 subface.2) port

/-- Every certified rebase circuit has one of three exact facial forms.
Its selected face is constant; or its remote closed facial itinerary
contains a simple dual cycle; or that itinerary repeats an unoriented
dual edge. -/
theorem constantFace_or_exists_remote_dualCycle_or_remote_nontrail
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) :
    (∀ arc ∈ circuit.first :: circuit.rest,
        arc.selectedFace = circuit.first.selectedFace) ∨
      Nonempty (RemoteDualCycle circuit) ∨
      Nonempty (RemoteNontrailDualWalk circuit) := by
  classical
  by_cases hconstant : ∀ arc ∈ circuit.first :: circuit.rest,
      arc.selectedFace = circuit.first.selectedFace
  · exact Or.inl hconstant
  · right
    rcases circuit.exists_closedDualWalk with ⟨walk, hsupport⟩
    have hcompressedSubset : ∀ {face},
        face ∈ circuit.compressedDualFaces →
          face ∈ circuit.cyclicDualFaces := by
      intro face hface
      exact (circuit.cyclicDualFaces.destutter_sublist
        (· ≠ ·)).subset hface
    have hwalkNe : walk ≠ .nil := by
      intro hnil
      apply hconstant
      intro arc harc
      have hcyclic : arc.dualFace ∈ circuit.cyclicDualFaces := by
        rcases List.mem_cons.1 harc with rfl | harc
        · simp [cyclicDualFaces]
        · unfold cyclicDualFaces
          exact List.mem_cons_of_mem circuit.first.dualFace
            (List.mem_append_left [circuit.first.dualFace]
              (List.mem_map_of_mem
                (f := CrossCentralExactFaceCertifiedRebaseArc.dualFace)
                harc))
      have hcompressed : arc.dualFace ∈
          circuit.compressedDualFaces := by
        exact (mem_destutter_ne_iff arc.dualFace
          circuit.cyclicDualFaces).2 hcyclic
      have hwalkMem : arc.dualFace ∈ walk.support := by
        rw [hsupport]
        exact hcompressed
      have hdual : arc.dualFace = circuit.first.dualFace := by
        simpa [hnil] using hwalkMem
      exact congrArg Subtype.val hdual
    have hremoteWalk :
        (∀ face ∈ walk.support,
          centralEdge
              (baseData.rotationOrderedData graphData
                minimal.spherical.cubic minimal.vertexRotationCyclic) ∉
            orbitFaceBoundary graphData.toRotationSystem face.1) ∧
        (∀ face ∈ walk.support, ∀ port : Fin 4,
          boundaryEdge
              (baseData.rotationOrderedData graphData
                minimal.spherical.cubic minimal.vertexRotationCyclic)
                port ∉
            orbitFaceBoundary graphData.toRotationSystem face.1) := by
      constructor
      · intro face hface
        apply circuit.central_not_mem_of_mem_cyclicDualFaces
        apply hcompressedSubset
        rw [← hsupport]
        exact hface
      · intro face hface port
        apply circuit.boundary_not_mem_of_mem_cyclicDualFaces
        apply hcompressedSubset
        rw [← hsupport]
        exact hface
    by_cases htrail : walk.IsTrail
    · left
      let cycle := walk.cycleBypass
      have hcycle : cycle.IsCycle :=
        htrail.isCycle_cycleBypass hwalkNe
      exact ⟨{
        start := circuit.first.dualFace
        walk := cycle
        isCycle := hcycle
        central_not_mem := fun face hface =>
          hremoteWalk.1 face
            (walk.support_cycleBypass_sublist_support.subset hface)
        boundary_not_mem := fun face hface port =>
          hremoteWalk.2 face
            (walk.support_cycleBypass_sublist_support.subset hface) port }⟩
    · right
      exact ⟨{
        walk := walk
        support_eq := hsupport
        ne_nil := hwalkNe
        not_isTrail := htrail
        central_not_mem := hremoteWalk.1
        boundary_not_mem := hremoteWalk.2 }⟩

/-- Thus the only nonconstant facial itinerary not already yielding a
remote simple dual cycle is pure backtracking inside an acyclic support
subgraph. -/
theorem constantFace_or_exists_remote_dualCycle_or_remote_acyclic_nontrail
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) :
    (∀ arc ∈ circuit.first :: circuit.rest,
        arc.selectedFace = circuit.first.selectedFace) ∨
      Nonempty (RemoteDualCycle circuit) ∨
      ∃ nontrail : RemoteNontrailDualWalk circuit,
        nontrail.walk.toSubgraph.coe.IsAcyclic := by
  rcases circuit.constantFace_or_exists_remote_dualCycle_or_remote_nontrail with
    hconstant | hrest
  · exact Or.inl hconstant
  · rcases hrest with hcycle | hnontrail
    · exact Or.inr (Or.inl hcycle)
    · rcases hnontrail with ⟨nontrail⟩
      rcases nontrail.acyclic_toSubgraph_or_exists_remoteDualCycle with
        hacyclic | hcycle
      · exact Or.inr (Or.inr ⟨nontrail, hacyclic⟩)
      · exact Or.inr (Or.inl hcycle)

/-- Equivalently, the residual tree branch carries a concrete compressed
face backtrack `F,G,F`; no abstract repeated-edge obstruction remains. -/
theorem constantFace_or_exists_remote_dualCycle_or_compressedFaceBacktrack
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) :
    (∀ arc ∈ circuit.first :: circuit.rest,
        arc.selectedFace = circuit.first.selectedFace) ∨
      Nonempty (RemoteDualCycle circuit) ∨
      Nonempty (CompressedFaceBacktrack circuit) := by
  rcases
      circuit.constantFace_or_exists_remote_dualCycle_or_remote_acyclic_nontrail with
    hconstant | hrest
  · exact Or.inl hconstant
  · rcases hrest with hcycle | ⟨nontrail, hacyclic⟩
    · exact Or.inr (Or.inl hcycle)
    · exact Or.inr (Or.inr
        (nontrail.exists_compressedFaceBacktrack_of_acyclic hacyclic))

/-- Three physical constant-face runs lifting one compressed backtrack. -/
structure CyclicPhysicalFaceBacktrack
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) where
  outer :
    CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData
  middle :
    CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData
  returning :
    CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData
  physicalBefore : List
    (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
  outerTail : List
    (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
  middleTail : List
    (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
  physicalAfter : List
    (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
  split : (circuit.first :: circuit.rest) ++ [circuit.first] =
    physicalBefore ++
      (outer :: (outerTail ++
        (middle :: (middleTail ++ (returning :: physicalAfter)))))
  returningFace : returning.selectedFace = outer.selectedFace
  middleFace_ne : outer.selectedFace ≠ middle.selectedFace
  outerTail_faces : ∀ arc ∈ outerTail,
    arc.selectedFace = outer.selectedFace
  middleTail_faces : ∀ arc ∈ middleTail,
    arc.selectedFace = middle.selectedFace

/-- Destutter inversion turns a compressed backtrack into three
contiguous physical constant-face runs in the closed arc word. -/
theorem CompressedFaceBacktrack.exists_cyclicPhysicalFaceBacktrack
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (backtrack : CompressedFaceBacktrack circuit) :
    Nonempty (CyclicPhysicalFaceBacktrack circuit) := by
  let cyclicArcs := (circuit.first :: circuit.rest) ++ [circuit.first]
  let faceRelation := fun first second :
      CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData =>
    first.selectedFace ≠ second.selectedFace
  let compressedArcs := cyclicArcs.destutter faceRelation
  have hcyclicMap : cyclicArcs.map
      CrossCentralExactFaceCertifiedRebaseArc.dualFace =
      circuit.cyclicDualFaces := by
    simp [cyclicArcs,
      CrossCentralExactFaceCertifiedRebaseCircuit.cyclicDualFaces]
  have hcompressedMap : compressedArcs.map
      CrossCentralExactFaceCertifiedRebaseArc.dualFace =
      circuit.compressedDualFaces := by
    calc
      compressedArcs.map
            CrossCentralExactFaceCertifiedRebaseArc.dualFace =
          (cyclicArcs.map
              CrossCentralExactFaceCertifiedRebaseArc.dualFace).destutter
            (· ≠ ·) := by
        apply List.map_destutter
        intro first _ second _
        simp [faceRelation,
          CrossCentralExactFaceCertifiedRebaseArc.dualFace]
      _ = circuit.compressedDualFaces := by
        rw [hcyclicMap]
        rfl
  have hlength : compressedArcs.length =
      circuit.compressedDualFaces.length := by
    simpa using congrArg List.length hcompressedMap
  have hindex : backtrack.index + 2 < compressedArcs.length := by
    rw [hlength]
    exact backtrack.index_add_two_lt
  let outer := compressedArcs[backtrack.index]
  let middle := compressedArcs[backtrack.index + 1]
  let returning := compressedArcs[backtrack.index + 2]
  have houterIndex : backtrack.index < compressedArcs.length := by
    omega
  have hmiddleIndex : backtrack.index + 1 < compressedArcs.length := by
    omega
  have houterFaceIndex :
      backtrack.index < circuit.compressedDualFaces.length := by
    rw [← hlength]
    exact houterIndex
  have hmiddleFaceIndex :
      backtrack.index + 1 < circuit.compressedDualFaces.length := by
    rw [← hlength]
    exact hmiddleIndex
  have houterDual : outer.dualFace =
      circuit.compressedDualFaces[backtrack.index] := by
    have hmap := congrArg
      (fun entries => entries[backtrack.index]?) hcompressedMap
    simp [houterIndex, houterFaceIndex] at hmap
    exact hmap
  have hmiddleDual : middle.dualFace =
      circuit.compressedDualFaces[backtrack.index + 1] := by
    have hmap := congrArg
      (fun entries => entries[backtrack.index + 1]?) hcompressedMap
    simp [hmiddleIndex, hmiddleFaceIndex] at hmap
    exact hmap
  have hreturningDual : returning.dualFace =
      circuit.compressedDualFaces[backtrack.index + 2] := by
    have hmap := congrArg
      (fun entries => entries[backtrack.index + 2]?) hcompressedMap
    simp [hindex, backtrack.index_add_two_lt] at hmap
    exact hmap
  have hreturningFace : returning.selectedFace = outer.selectedFace := by
    have hdual : returning.dualFace = outer.dualFace :=
      hreturningDual.trans
        (backtrack.outer_eq.symm.trans houterDual.symm)
    exact congrArg Subtype.val hdual
  have hmiddleFace : outer.selectedFace ≠ middle.selectedFace := by
    intro hfaces
    apply backtrack.adjacent_ne
    rw [← houterDual, ← hmiddleDual]
    exact Subtype.ext hfaces
  have hcompressedSplit : compressedArcs =
      compressedArcs.take backtrack.index ++
        outer :: middle :: returning ::
          compressedArcs.drop (backtrack.index + 3) := by
    simp [outer, middle, returning]
  have hdestutter : cyclicArcs.destutter faceRelation =
      compressedArcs.take backtrack.index ++
        outer :: middle :: returning ::
          compressedArcs.drop (backtrack.index + 3) :=
    hcompressedSplit
  have hdestutter' :
      ((circuit.first :: circuit.rest) ++ [circuit.first]).destutter
          faceRelation =
        compressedArcs.take backtrack.index ++
          outer :: middle :: returning ::
            compressedArcs.drop (backtrack.index + 3) := by
    simpa [cyclicArcs] using hdestutter
  rcases exists_runs_of_destutter_eq_append_backtrack
      (relation := faceRelation) circuit.first outer middle returning
        (circuit.rest ++ [circuit.first])
        (compressedArcs.take backtrack.index)
        (compressedArcs.drop (backtrack.index + 3)) hdestutter' with
    ⟨physicalBefore, outerTail, middleTail, physicalAfter,
      hsplit, houterTail, hmiddleTail⟩
  refine ⟨{
    outer := outer
    middle := middle
    returning := returning
    physicalBefore := physicalBefore
    outerTail := outerTail
    middleTail := middleTail
    physicalAfter := physicalAfter
    split := ?_
    returningFace := hreturningFace
    middleFace_ne := hmiddleFace
    outerTail_faces := ?_
    middleTail_faces := ?_ }⟩
  · simpa only [List.cons_append, List.append_assoc] using hsplit
  · intro arc harc
    exact (not_ne_iff.mp (houterTail arc harc)).symm
  · intro arc harc
    exact (not_ne_iff.mp (hmiddleTail arc harc)).symm

/-- A cyclic rotation preserves the number of certified arcs. -/
@[simp] theorem rotateAtSplit_arcLength
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (first : CrossCentralExactFaceCertifiedRebaseArc graphData minimal
      baseData)
    (before after : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))
    (hsplit : circuit.first :: circuit.rest =
      before ++ first :: after) :
    (circuit.rotateAtSplit first before after hsplit).arcLength =
      circuit.arcLength := by
  simp only [arcLength, rotateAtSplit_first, rotateAtSplit_rest]
  rw [hsplit]
  simp [Nat.add_comm, Nat.add_left_comm]

/-- A displayed constant-face middle block, after choosing a cyclic
representative of the same certified rebase circuit. -/
structure RotatedConstantFaceMiddleBlock
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) where
  rotated : CrossCentralExactFaceCertifiedRebaseCircuit graphData
    minimal baseData
  arcLength_eq : rotated.arcLength = circuit.arcLength
  left : CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData
  middleFirst :
    CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData
  right : CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData
  before : List
    (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
  middleRest : List
    (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
  after : List
    (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
  split : rotated.first :: rotated.rest =
    before ++
      (left :: ((middleFirst :: middleRest) ++ (right :: after)))
  face_ne : left.selectedFace ≠ middleFirst.selectedFace
  middleFaces : ∀ arc ∈ middleFirst :: middleRest,
    arc.selectedFace = middleFirst.selectedFace
  rightFace : right.selectedFace = left.selectedFace

/-- The closed physical runs yield an ordinary displayed middle block in
a cyclic representative.  The only apparent exception would be a
two-run circuit, which is excluded by facial nonbacktracking. -/
theorem CyclicPhysicalFaceBacktrack.exists_rotatedConstantFaceMiddleBlock
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (backtrack : CyclicPhysicalFaceBacktrack circuit) :
    Nonempty (RotatedConstantFaceMiddleBlock circuit) := by
  let outerBlock := backtrack.outer :: backtrack.outerTail
  have houterBlock : outerBlock ≠ [] := by simp [outerBlock]
  let left := outerBlock.getLast houterBlock
  let before := backtrack.physicalBefore ++ outerBlock.dropLast
  have hleftMem : left ∈ outerBlock := by
    exact List.getLast_mem houterBlock
  have hleftFace : left.selectedFace = backtrack.outer.selectedFace := by
    rcases List.mem_cons.mp hleftMem with hleft | hleft
    · simpa [outerBlock] using congrArg
        CrossCentralExactFaceCertifiedRebaseArc.selectedFace hleft
    · exact backtrack.outerTail_faces left
        (by simpa [outerBlock] using hleft)
  have houterSplit : outerBlock.dropLast ++ [left] = outerBlock := by
    simpa [left] using List.dropLast_append_getLast (l := outerBlock)
      houterBlock
  have hcyclicSplit :
      (circuit.first :: circuit.rest) ++ [circuit.first] =
        before ++ left :: backtrack.middle ::
          backtrack.middleTail ++ backtrack.returning ::
            backtrack.physicalAfter := by
    rw [backtrack.split]
    calc
      backtrack.physicalBefore ++ backtrack.outer ::
            (backtrack.outerTail ++ backtrack.middle ::
              (backtrack.middleTail ++
                backtrack.returning :: backtrack.physicalAfter)) =
          backtrack.physicalBefore ++ outerBlock ++
            backtrack.middle :: backtrack.middleTail ++
              backtrack.returning :: backtrack.physicalAfter := by
        simp [outerBlock, List.append_assoc]
      _ = backtrack.physicalBefore ++
            (outerBlock.dropLast ++ [left]) ++
              backtrack.middle :: backtrack.middleTail ++
                backtrack.returning :: backtrack.physicalAfter := by
        rw [houterSplit]
      _ = before ++ left :: backtrack.middle ::
            backtrack.middleTail ++ backtrack.returning ::
              backtrack.physicalAfter := by
        simp [before, List.append_assoc]
  have hfaceNe : left.selectedFace ≠ backtrack.middle.selectedFace := by
    rw [hleftFace]
    exact backtrack.middleFace_ne
  have hmiddleFaces : ∀ arc ∈
      backtrack.middle :: backtrack.middleTail,
      arc.selectedFace = backtrack.middle.selectedFace := by
    intro arc harc
    rcases List.mem_cons.mp harc with rfl | harc
    · rfl
    · exact backtrack.middleTail_faces arc harc
  by_cases hafter : backtrack.physicalAfter = []
  · rw [hafter] at hcyclicSplit
    have hreturning : backtrack.returning = circuit.first := by
      let lastPrefix := before ++ left :: backtrack.middle ::
        backtrack.middleTail
      have hright : lastPrefix ++ [backtrack.returning] =
          before ++ left :: backtrack.middle ::
            backtrack.middleTail ++ [backtrack.returning] := by
        simp [lastPrefix, List.append_assoc]
      calc
        backtrack.returning =
            (lastPrefix ++ [backtrack.returning]).getLast (by simp) :=
          (List.getLast_append_singleton lastPrefix).symm
        _ = ((circuit.first :: circuit.rest) ++ [circuit.first]).getLast
              (by simp) := by
          exact List.getLast_congr (by simp) (by simp) (by
            rw [hright]
            exact hcyclicSplit.symm)
        _ = circuit.first :=
          List.getLast_append_singleton (circuit.first :: circuit.rest)
    have hdisplayed : circuit.first :: circuit.rest =
        before ++ left :: backtrack.middle ::
          backtrack.middleTail := by
      have hcancel :
          (circuit.first :: circuit.rest) ++ [circuit.first] =
            (before ++ left :: backtrack.middle ::
              backtrack.middleTail) ++ [circuit.first] := by
        simpa [hreturning, List.append_assoc] using hcyclicSplit
      exact List.append_cancel_right hcancel
    cases hbefore : before with
    | nil =>
        rw [hbefore] at hdisplayed
        have hfirst : circuit.first = left := (List.cons.inj hdisplayed).1
        have hrest : circuit.rest =
            backtrack.middle :: backtrack.middleTail :=
          (List.cons.inj hdisplayed).2
        let middleBlock := backtrack.middle :: backtrack.middleTail
        have hmiddleBlock : middleBlock ≠ [] := by simp [middleBlock]
        let middleLast := middleBlock.getLast hmiddleBlock
        have hmiddleLastMem : middleLast ∈ middleBlock :=
          List.getLast_mem hmiddleBlock
        have hmiddleLastFace : middleLast.selectedFace =
            backtrack.middle.selectedFace :=
          hmiddleFaces middleLast
            (by simpa [middleBlock] using hmiddleLastMem)
        have hmiddleLastFollows :
            CrossCentralExactFaceCertifiedRebaseArc.Follows
              middleLast left := by
          simpa [hfirst, hrest, middleBlock, middleLast] using
            circuit.closing
        have hleftFollows :
            CrossCentralExactFaceCertifiedRebaseArc.Follows
              left backtrack.middle := by
          have hparts :
              CrossCentralExactFaceCertifiedRebaseArc.Follows
                  left backtrack.middle ∧
                List.IsChain CrossCentralExactFaceCertifiedRebaseArc.Follows
                  (backtrack.middle :: backtrack.middleTail) := by
            simpa [hfirst, hrest] using circuit.consecutive
          exact hparts.1
        have hmiddleLastLeft :
            middleLast.selectedFace ≠ left.selectedFace := by
          intro heq
          apply hfaceNe
          exact heq.symm.trans hmiddleLastFace
        exact False.elim
          (middleLast.no_selectedFace_backtrack hmiddleLastFollows
            hleftFollows hmiddleLastLeft hmiddleLastFace.symm)
    | cons initial beforeTail =>
        have hinitial : initial = circuit.first := by
          rw [hbefore] at hdisplayed
          exact (List.cons.inj hdisplayed).1.symm
        subst initial
        have hrotateSplit : circuit.first :: circuit.rest =
            (circuit.first :: beforeTail) ++ left ::
              (backtrack.middle :: backtrack.middleTail) := by
          simpa [hbefore] using hdisplayed
        let rotated := circuit.rotateAtSplit left
          (circuit.first :: beforeTail)
          (backtrack.middle :: backtrack.middleTail) hrotateSplit
        refine ⟨{
          rotated := rotated
          arcLength_eq := circuit.rotateAtSplit_arcLength left
            (circuit.first :: beforeTail)
            (backtrack.middle :: backtrack.middleTail) hrotateSplit
          left := left
          middleFirst := backtrack.middle
          right := backtrack.returning
          before := []
          middleRest := backtrack.middleTail
          after := beforeTail
          split := ?_
          face_ne := hfaceNe
          middleFaces := hmiddleFaces
          rightFace := backtrack.returningFace.trans hleftFace.symm }⟩
        simp [rotated, hreturning]
  · have hlastAfter :
        backtrack.physicalAfter.getLast hafter = circuit.first := by
      let lastPrefix := before ++ left :: backtrack.middle ::
        backtrack.middleTail ++ [backtrack.returning]
      have hright : lastPrefix ++ backtrack.physicalAfter =
          before ++ left :: backtrack.middle ::
            backtrack.middleTail ++ backtrack.returning ::
              backtrack.physicalAfter := by
        simp [lastPrefix, List.append_assoc]
      calc
        backtrack.physicalAfter.getLast hafter =
            (lastPrefix ++ backtrack.physicalAfter).getLast
              (by simp [hafter]) :=
          (List.getLast_append_of_right_ne_nil lastPrefix
            backtrack.physicalAfter hafter).symm
        _ = ((circuit.first :: circuit.rest) ++ [circuit.first]).getLast
              (by simp) := by
          exact List.getLast_congr (by simp [hafter]) (by simp) (by
            rw [hright]
            exact hcyclicSplit.symm)
        _ = circuit.first :=
          List.getLast_append_singleton (circuit.first :: circuit.rest)
    have hafterSplit : backtrack.physicalAfter =
        backtrack.physicalAfter.dropLast ++ [circuit.first] := by
      rw [← hlastAfter]
      exact (List.dropLast_append_getLast
        (l := backtrack.physicalAfter) hafter).symm
    rw [hafterSplit] at hcyclicSplit
    have hdisplayed : circuit.first :: circuit.rest =
        before ++ left :: backtrack.middle ::
          backtrack.middleTail ++ backtrack.returning ::
            backtrack.physicalAfter.dropLast := by
      have hcancel :
          (circuit.first :: circuit.rest) ++ [circuit.first] =
            (before ++ left :: backtrack.middle ::
              backtrack.middleTail ++ backtrack.returning ::
                backtrack.physicalAfter.dropLast) ++ [circuit.first] := by
        simpa [List.append_assoc] using hcyclicSplit
      exact List.append_cancel_right hcancel
    let rotationAfter := backtrack.middle ::
      backtrack.middleTail ++ backtrack.returning ::
        backtrack.physicalAfter.dropLast
    have hrotateSplit : circuit.first :: circuit.rest =
        before ++ left :: rotationAfter := by
      simpa [rotationAfter, List.append_assoc] using hdisplayed
    let rotated := circuit.rotateAtSplit left before rotationAfter hrotateSplit
    refine ⟨{
      rotated := rotated
      arcLength_eq := circuit.rotateAtSplit_arcLength left before
        rotationAfter hrotateSplit
      left := left
      middleFirst := backtrack.middle
      right := backtrack.returning
      before := []
      middleRest := backtrack.middleTail
      after := backtrack.physicalAfter.dropLast ++ before
      split := ?_
      face_ne := hfaceNe
      middleFaces := hmiddleFaces
      rightFace := backtrack.returningFace.trans hleftFace.symm }⟩
    simp [rotated, rotationAfter, List.append_assoc]

/-- Every compressed face backtrack has a displayed constant-face middle
block in a length-preserving cyclic representative. -/
theorem CompressedFaceBacktrack.exists_rotatedConstantFaceMiddleBlock
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (backtrack : CompressedFaceBacktrack circuit) :
    Nonempty (RotatedConstantFaceMiddleBlock circuit) := by
  rcases backtrack.exists_cyclicPhysicalFaceBacktrack with ⟨physical⟩
  exact physical.exists_rotatedConstantFaceMiddleBlock

/-- On a shortest certified circuit, every compressed facial backtrack
produces a localized recovery transfer after a length-preserving cyclic
rotation. -/
theorem IsLengthMinimal.exists_rotated_recoveryFaceTransfer_of_compressedFaceBacktrack
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (hminimal : circuit.IsLengthMinimal)
    (backtrack : CompressedFaceBacktrack circuit) :
    ∃ rotated : CrossCentralExactFaceCertifiedRebaseCircuit graphData
        minimal baseData,
      rotated.arcLength = circuit.arcLength ∧
        Nonempty (ClosureRecoveryFaceTransfer rotated) := by
  rcases backtrack.exists_rotatedConstantFaceMiddleBlock with ⟨block⟩
  have hrotatedMinimal : block.rotated.IsLengthMinimal := by
    intro other
    rw [block.arcLength_eq]
    exact hminimal other
  exact ⟨block.rotated, block.arcLength_eq,
    hrotatedMinimal.middleBlock_recoveryFaceTransfer
      block.left.selectedFace block.middleFirst.selectedFace block.face_ne
        block.left block.middleFirst block.right block.before
        block.middleRest block.after block.split rfl block.middleFaces
        block.rightFace⟩

/-- The former disjunctive packaging is an immediate weakening of the
recovery-transfer theorem. -/
theorem IsLengthMinimal.exists_rotated_nonzeroComplementProfile_or_recoveryFaceTransfer_of_compressedFaceBacktrack
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (hminimal : circuit.IsLengthMinimal)
    (backtrack : CompressedFaceBacktrack circuit) :
    ∃ rotated : CrossCentralExactFaceCertifiedRebaseCircuit graphData
        minimal baseData,
      rotated.arcLength = circuit.arcLength ∧
        ((∃ middleFirst right :
              CrossCentralExactFaceCertifiedRebaseArc graphData minimal
                baseData,
            ∃ middleRest : List
              (CrossCentralExactFaceCertifiedRebaseArc graphData minimal
                baseData),
              MiddleBlockNonzeroComplementProfile middleFirst right
                middleRest) ∨
          Nonempty (ClosureRecoveryFaceTransfer rotated)) := by
  rcases
      hminimal.exists_rotated_recoveryFaceTransfer_of_compressedFaceBacktrack
        backtrack with
    ⟨rotated, hlength, htransfer⟩
  exact ⟨rotated, hlength, Or.inr htransfer⟩

/-- A shortest certified rebase circuit has exactly the three structural
branches needed by the all-face endgame: one selected face throughout, a
remote simple facial-dual cycle, or a concrete recovery transfer on an
equal-length cyclic representative. -/
theorem IsLengthMinimal.constantFace_or_exists_remoteDualCycle_or_rotated_recoveryFaceTransfer
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (hminimal : circuit.IsLengthMinimal) :
    (∀ arc ∈ circuit.first :: circuit.rest,
        arc.selectedFace = circuit.first.selectedFace) ∨
      Nonempty (RemoteDualCycle circuit) ∨
      ∃ rotated : CrossCentralExactFaceCertifiedRebaseCircuit graphData
          minimal baseData,
        rotated.arcLength = circuit.arcLength ∧
          Nonempty (ClosureRecoveryFaceTransfer rotated) := by
  rcases circuit.constantFace_or_exists_remote_dualCycle_or_compressedFaceBacktrack
    with hconstant | hrest
  · exact Or.inl hconstant
  · rcases hrest with hcycle | hbacktrack
    · exact Or.inr (Or.inl hcycle)
    · rcases hbacktrack with ⟨backtrack⟩
      exact Or.inr (Or.inr
        (hminimal.exists_rotated_recoveryFaceTransfer_of_compressedFaceBacktrack
          backtrack))

/-- The constant-face branch of the shortest-circuit classification is a
single involutive two-arc cell.  The other two branches retain their remote
dual cycle or concrete recovery-transfer witnesses. -/
theorem IsLengthMinimal.twoArc_constantFace_or_exists_remoteDualCycle_or_rotated_recoveryFaceTransfer
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (hminimal : circuit.IsLengthMinimal) :
    (circuit.arcLength = 2 ∧
      ∀ arc ∈ circuit.first :: circuit.rest,
        arc.selectedFace = circuit.first.selectedFace) ∨
      Nonempty (RemoteDualCycle circuit) ∨
      ∃ rotated : CrossCentralExactFaceCertifiedRebaseCircuit graphData
          minimal baseData,
        rotated.arcLength = circuit.arcLength ∧
          Nonempty (ClosureRecoveryFaceTransfer rotated) := by
  rcases
      hminimal.constantFace_or_exists_remoteDualCycle_or_rotated_recoveryFaceTransfer
        with hconstant | hremote | htransfer
  · exact Or.inl
      ⟨hminimal.arcLength_eq_two_of_constantFace hconstant, hconstant⟩
  · exact Or.inr (Or.inl hremote)
  · exact Or.inr (Or.inr htransfer)

/-- The shortest-circuit classification with the constant branch packaged
as its complete exact involution cell. -/
theorem IsLengthMinimal.involutionCell_or_exists_remoteDualCycle_or_rotated_recoveryFaceTransfer
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (hminimal : circuit.IsLengthMinimal) :
    Nonempty (CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
        minimal baseData) ∨
      Nonempty (RemoteDualCycle circuit) ∨
      ∃ rotated : CrossCentralExactFaceCertifiedRebaseCircuit graphData
          minimal baseData,
        rotated.arcLength = circuit.arcLength ∧
          Nonempty (ClosureRecoveryFaceTransfer rotated) := by
  rcases
      hminimal.twoArc_constantFace_or_exists_remoteDualCycle_or_rotated_recoveryFaceTransfer
        with hcell | hremote | htransfer
  · exact Or.inl (circuit.exists_involutionCell_of_arcLength_eq_two hcell.1)
  · exact Or.inr (Or.inl hremote)
  · exact Or.inr (Or.inr htransfer)

end CrossCentralExactFaceCertifiedRebaseCircuit

namespace ClosureRecoveryFaceTransferCircuit

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- The source face of the transfer displayed at a transfer-circuit
position. -/
def sourceFaceAt
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (position : Fin circuit.arcLength) :
    OrbitFace graphData.toRotationSystem :=
  (circuit.transferAt position).recovery.sourceFace

/-- Shortest transfer circuits read source faces injectively by position. -/
theorem IsLengthMinimal.sourceFaceAt_injective
    {circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    Function.Injective circuit.sourceFaceAt := by
  intro first second hface
  apply hminimal.transferAt_injective
  exact hminimal.transfer_eq_of_mem_of_mem_of_sourceFace_eq
    (circuit.transferAt_mem first) (circuit.transferAt_mem second) hface

/-- The physical face at a transfer's localized loss position is its
source face. -/
theorem selectedFaceAt_lossPositionAt
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (position : Fin circuit.arcLength) :
    rebaseCircuit.selectedFaceAt (circuit.lossPositionAt position) =
      circuit.sourceFaceAt position := by
  exact (circuit.transferAt position).selectedFace_at_lossPosition

/-- At saturation, physical rebase positions read selected faces
injectively. -/
theorem selectedFaceAt_injective_of_saturated
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength) :
    Function.Injective rebaseCircuit.selectedFaceAt := by
  intro first second hface
  have hsurjective :=
    (hminimal.lossPositionAt_bijective_of_arcLength_eq hlength).2
  rcases hsurjective first with ⟨firstTransfer, hfirst⟩
  rcases hsurjective second with ⟨secondTransfer, hsecond⟩
  have hsource : circuit.sourceFaceAt firstTransfer =
      circuit.sourceFaceAt secondTransfer := by
    calc
      circuit.sourceFaceAt firstTransfer =
          rebaseCircuit.selectedFaceAt
            (circuit.lossPositionAt firstTransfer) :=
        (circuit.selectedFaceAt_lossPositionAt firstTransfer).symm
      _ = rebaseCircuit.selectedFaceAt first := by rw [hfirst]
      _ = rebaseCircuit.selectedFaceAt second := hface
      _ = rebaseCircuit.selectedFaceAt
          (circuit.lossPositionAt secondTransfer) := by rw [hsecond]
      _ = circuit.sourceFaceAt secondTransfer :=
        circuit.selectedFaceAt_lossPositionAt secondTransfer
  have htransfer := hminimal.sourceFaceAt_injective hsource
  calc
    first = circuit.lossPositionAt firstTransfer := hfirst.symm
    _ = circuit.lossPositionAt secondTransfer := by rw [htransfer]
    _ = second := hsecond

/-- Hence saturation makes the complete physical selected-face word
duplicate-free. -/
theorem selectedFaceWord_nodup_of_saturated
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength) :
    rebaseCircuit.selectedFaceWord.Nodup := by
  rw [List.nodup_iff_injective_get]
  let hwordLength := rebaseCircuit.selectedFaceWord_length
  intro first second hface
  let first' : Fin rebaseCircuit.arcLength :=
    Fin.cast hwordLength first
  let second' : Fin rebaseCircuit.arcLength :=
    Fin.cast hwordLength second
  have hselected : rebaseCircuit.selectedFaceAt first' =
      rebaseCircuit.selectedFaceAt second' := by
    simp only [CrossCentralExactFaceCertifiedRebaseCircuit.selectedFaceWord,
      List.get_eq_getElem, List.getElem_map] at hface
    simpa [first', second',
      CrossCentralExactFaceCertifiedRebaseCircuit.selectedFaceAt,
      CrossCentralExactFaceCertifiedRebaseCircuit.arcAt,
      List.get_eq_getElem] using hface
  exact Fin.cast_injective hwordLength
    (circuit.selectedFaceAt_injective_of_saturated hminimal hlength
      hselected)

/-- Packaging physical selected faces as dual vertices preserves their
duplicate freedom. -/
theorem dualFaceWord_nodup_of_saturated
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength) :
    rebaseCircuit.dualFaceWord.Nodup := by
  have hmap : rebaseCircuit.dualFaceWord.map Subtype.val =
      rebaseCircuit.selectedFaceWord := by
    simp [CrossCentralExactFaceCertifiedRebaseCircuit.dualFaceWord,
      CrossCentralExactFaceCertifiedRebaseCircuit.selectedFaceWord,
      CrossCentralExactFaceCertifiedRebaseArc.dualFace]
  apply List.Nodup.of_map Subtype.val
  rw [hmap]
  exact circuit.selectedFaceWord_nodup_of_saturated hminimal hlength

/-- In the saturated branch, every selected face occurs exactly once on
the physical rebase trace. -/
theorem selectedFaces_card_eq_rebase_arcLength_of_saturated
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength) :
    rebaseCircuit.selectedFaces.card = rebaseCircuit.arcLength := by
  rw [← rebaseCircuit.selectedFaceWord_toFinset]
  exact List.toFinset_card_of_nodup
    (circuit.selectedFaceWord_nodup_of_saturated hminimal hlength)
    |>.trans rebaseCircuit.selectedFaceWord_length

/-- The physical selected-face word is a permutation of the shortest
transfer circuit's source-face word. -/
theorem selectedFaceWord_perm_sourceFaces_of_saturated
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength) :
    rebaseCircuit.selectedFaceWord.Perm circuit.sourceFaces := by
  apply List.perm_of_nodup_nodup_toFinset_eq
    (circuit.selectedFaceWord_nodup_of_saturated hminimal hlength)
    hminimal.sourceFaces_nodup
  rw [rebaseCircuit.selectedFaceWord_toFinset]
  apply Finset.Subset.antisymm
  · intro face hface
    rcases rebaseCircuit.mem_selectedFaces face |>.1 hface with
      ⟨arc, harc, hselected⟩
    have hsurjective :=
      (hminimal.lossPositionAt_bijective_of_arcLength_eq hlength).2
    obtain ⟨position, hposition⟩ := List.get_of_mem harc
    rcases hsurjective position with ⟨transferPosition, htransferPosition⟩
    have harcAt : rebaseCircuit.arcAt position = arc := by
      exact hposition
    have hsource : circuit.sourceFaceAt transferPosition = face := by
      calc
        circuit.sourceFaceAt transferPosition =
            rebaseCircuit.selectedFaceAt
              (circuit.lossPositionAt transferPosition) :=
          (circuit.selectedFaceAt_lossPositionAt transferPosition).symm
        _ = rebaseCircuit.selectedFaceAt position := by
          rw [htransferPosition]
        _ = arc.selectedFace := by
          rw [CrossCentralExactFaceCertifiedRebaseCircuit.selectedFaceAt,
            harcAt]
        _ = face := hselected
    have hmem : circuit.transferAt transferPosition ∈
        circuit.first :: circuit.rest := circuit.transferAt_mem _
    exact List.mem_toFinset.2 <| by
      rw [← hsource]
      exact List.mem_map_of_mem
        (f := fun transfer : ClosureRecoveryFaceTransfer rebaseCircuit =>
          transfer.recovery.sourceFace) hmem
  · intro face hface
    have hlist : face ∈ circuit.sourceFaces := List.mem_toFinset.1 hface
    rcases List.mem_map.1 hlist with ⟨transfer, htransfer, rfl⟩
    exact circuit.sourceFace_mem_selectedFaces_of_mem htransfer

/-- Saturation cannot occur on a two-arc rebase circuit: two distinct
selected faces would make the second exact rebase immediately backtrack
the first in the facial dual. -/
theorem three_le_rebase_arcLength_of_saturated
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength) :
    3 ≤ rebaseCircuit.arcLength := by
  have htwo : 2 ≤ rebaseCircuit.arcLength := by
    rw [← hlength]
    exact circuit.two_le_arcLength
  by_contra hthree
  have heq : rebaseCircuit.arcLength = 2 := by omega
  have hrestLength : rebaseCircuit.rest.length = 1 := by
    rw [rebaseCircuit.arcLength_eq_rest_length_add_one] at heq
    omega
  rcases List.length_eq_one_iff.mp hrestLength with ⟨second, hrest⟩
  have hnodup :=
    circuit.selectedFaceWord_nodup_of_saturated hminimal hlength
  have hfaces : rebaseCircuit.first.selectedFace ≠ second.selectedFace := by
    simpa [CrossCentralExactFaceCertifiedRebaseCircuit.selectedFaceWord,
      hrest]
      using hnodup
  have hfirstSecond :
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        rebaseCircuit.first second := by
    simpa [hrest] using rebaseCircuit.consecutive
  have hsecondFirst :
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        second rebaseCircuit.first := by
    simpa [hrest] using rebaseCircuit.closing
  exact rebaseCircuit.first.no_selectedFace_backtrack
    hfirstSecond hsecondFirst hfaces rfl

/-- The physical rebase word has a nonempty tail in the saturated branch. -/
theorem rebase_rest_ne_nil_of_saturated
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength) :
    rebaseCircuit.rest ≠ [] := by
  intro hrest
  have hthree :=
    circuit.three_le_rebase_arcLength_of_saturated hminimal hlength
  rw [rebaseCircuit.arcLength_eq_rest_length_add_one, hrest] at hthree
  simp at hthree

/-- No adjacent equality remains in the pre-compression closed dual
itinerary of a saturated shortest transfer circuit. -/
theorem cyclicDualFaces_isChain_ne_of_saturated
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength) :
    List.IsChain (· ≠ ·) rebaseCircuit.cyclicDualFaces := by
  let tail := rebaseCircuit.rest.map
    CrossCentralExactFaceCertifiedRebaseArc.dualFace
  have htail : tail ≠ [] := by
    simp [tail, circuit.rebase_rest_ne_nil_of_saturated hminimal hlength]
  have hnodup : (rebaseCircuit.first.dualFace :: tail).Nodup := by
    simpa [tail,
      CrossCentralExactFaceCertifiedRebaseCircuit.dualFaceWord] using
      circuit.dualFaceWord_nodup_of_saturated hminimal hlength
  simpa [CrossCentralExactFaceCertifiedRebaseCircuit.cyclicDualFaces, tail]
    using isChain_ne_append_head_of_nodup
      rebaseCircuit.first.dualFace tail htail hnodup

/-- Thus adjacent-repeat compression does nothing in the saturated
branch. -/
theorem compressedDualFaces_eq_cyclicDualFaces_of_saturated
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength) :
    rebaseCircuit.compressedDualFaces = rebaseCircuit.cyclicDualFaces := by
  unfold CrossCentralExactFaceCertifiedRebaseCircuit.compressedDualFaces
  exact List.destutter_of_isChain (· ≠ ·) _
    (circuit.cyclicDualFaces_isChain_ne_of_saturated hminimal hlength)

/-- Apart from the intended repeated endpoint, the saturated closed dual
itinerary has no repeated face. -/
theorem cyclicDualFaces_tail_nodup_of_saturated
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength) :
    rebaseCircuit.cyclicDualFaces.tail.Nodup := by
  let tail := rebaseCircuit.rest.map
    CrossCentralExactFaceCertifiedRebaseArc.dualFace
  have hnodup : (rebaseCircuit.first.dualFace :: tail).Nodup := by
    simpa [tail,
      CrossCentralExactFaceCertifiedRebaseCircuit.dualFaceWord] using
      circuit.dualFaceWord_nodup_of_saturated hminimal hlength
  have hparts := List.nodup_cons.mp hnodup
  have hconcat : (tail.concat rebaseCircuit.first.dualFace).Nodup :=
    List.nodup_concat tail rebaseCircuit.first.dualFace |>.2
      ⟨hparts.1, hparts.2⟩
  simpa [CrossCentralExactFaceCertifiedRebaseCircuit.cyclicDualFaces,
    tail, List.concat_eq_append] using hconcat

/-- The closed walk already extracted from any rebase circuit is a
genuine simple cycle in the full facial dual under saturation. -/
theorem exists_isCycle_closedDualWalk_of_saturated
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength) :
    ∃ walk :
        (interiorDualGraph
          (orbitFaceBoundary graphData.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace graphData.toRotationSystem))).Walk
          rebaseCircuit.first.dualFace rebaseCircuit.first.dualFace,
      walk.IsCycle ∧ walk.support = rebaseCircuit.cyclicDualFaces := by
  rcases rebaseCircuit.exists_closedDualWalk with ⟨walk, hsupport⟩
  have hcompressed :=
    circuit.compressedDualFaces_eq_cyclicDualFaces_of_saturated
      hminimal hlength
  have hsupportCyclic : walk.support = rebaseCircuit.cyclicDualFaces :=
    hsupport.trans hcompressed
  have hsupportTail : walk.support.tail.Nodup := by
    rw [hsupportCyclic]
    exact circuit.cyclicDualFaces_tail_nodup_of_saturated hminimal hlength
  have hwalkLength : walk.length = rebaseCircuit.arcLength := by
    have hsupportLength := walk.length_support
    rw [hsupportCyclic] at hsupportLength
    simp [CrossCentralExactFaceCertifiedRebaseCircuit.cyclicDualFaces]
      at hsupportLength
    rw [rebaseCircuit.arcLength_eq_rest_length_add_one]
    omega
  have hthree : 3 ≤ walk.length := by
    rw [hwalkLength]
    exact circuit.three_le_rebase_arcLength_of_saturated hminimal hlength
  have hnotNil : ¬ walk.Nil :=
    SimpleGraph.Walk.not_nil_iff_lt_length.mpr (by omega)
  have htailPath : walk.tail.IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    rw [walk.support_tail_of_not_nil hnotNil]
    exact hsupportTail
  refine ⟨walk, SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    ⟨htailPath, hthree⟩, hsupportCyclic⟩

/-- The saturated simple dual cycle is remote from the restored central
edge and all four restored boundary edges. -/
theorem exists_remote_isCycle_closedDualWalk_of_saturated
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength) :
    ∃ walk :
        (interiorDualGraph
          (orbitFaceBoundary graphData.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace graphData.toRotationSystem))).Walk
          rebaseCircuit.first.dualFace rebaseCircuit.first.dualFace,
      walk.IsCycle ∧
        (∀ face ∈ walk.support,
          centralEdge
              (baseData.rotationOrderedData graphData
                minimal.spherical.cubic minimal.vertexRotationCyclic) ∉
            orbitFaceBoundary graphData.toRotationSystem face.1) ∧
        (∀ face ∈ walk.support, ∀ port : Fin 4,
          boundaryEdge
              (baseData.rotationOrderedData graphData
                minimal.spherical.cubic minimal.vertexRotationCyclic) port ∉
            orbitFaceBoundary graphData.toRotationSystem face.1) := by
  rcases circuit.exists_isCycle_closedDualWalk_of_saturated hminimal hlength
    with ⟨walk, hcycle, hsupport⟩
  refine ⟨walk, hcycle, ?_, ?_⟩
  · intro face hface
    apply rebaseCircuit.central_not_mem_of_mem_cyclicDualFaces
    rwa [← hsupport]
  · intro face hface port
    apply rebaseCircuit.boundary_not_mem_of_mem_cyclicDualFaces
    rwa [← hsupport]

end ClosureRecoveryFaceTransferCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
