import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferSuccessor
import Mathlib.Combinatorics.SimpleGraph.Acyclic

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
