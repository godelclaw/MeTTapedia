import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryCodeRigidity

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
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

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace ClosureRecoveryFaceArc

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- An anchor recovery dependency can be redirected from any selected
face lying off its support edge. -/
def redirectFromSelectedFaceOffEdge
    (anchor : ClosureRecoveryFaceArc rebaseCircuit)
    (arc : CrossCentralExactFaceCertifiedRebaseArc graphData minimal
      baseData)
    (hoff : anchor.edge ∉
      orbitFaceBoundary graphData.toRotationSystem arc.selectedFace) :
    ClosureRecoveryFaceArc rebaseCircuit := {
  sourceFace := arc.selectedFace
  targetFace := anchor.targetFace
  channel := anchor.channel
  edge := anchor.edge
  recoveryArc := anchor.recoveryArc
  recoveryArc_mem_displayed := anchor.recoveryArc_mem_displayed
  recoveryArc_selectedFace := anchor.recoveryArc_selectedFace
  edge_not_mem_sourceFace := hoff
  edge_not_mem_recoverySource := anchor.edge_not_mem_recoverySource
  edge_mem_recoveryTarget := anchor.edge_mem_recoveryTarget
  edge_mem_targetFace := anchor.edge_mem_targetFace
  targetFace_ne_sourceFace := by
    intro heq
    apply hoff
    rw [← heq]
    exact anchor.edge_mem_targetFace }

@[simp] theorem redirectFromSelectedFaceOffEdge_sourceFace
    (anchor : ClosureRecoveryFaceArc rebaseCircuit)
    (arc : CrossCentralExactFaceCertifiedRebaseArc graphData minimal
      baseData)
    (hoff : anchor.edge ∉
      orbitFaceBoundary graphData.toRotationSystem arc.selectedFace) :
    (anchor.redirectFromSelectedFaceOffEdge arc hoff).sourceFace =
      arc.selectedFace := rfl

@[simp] theorem redirectFromSelectedFaceOffEdge_targetFace
    (anchor : ClosureRecoveryFaceArc rebaseCircuit)
    (arc : CrossCentralExactFaceCertifiedRebaseArc graphData minimal
      baseData)
    (hoff : anchor.edge ∉
      orbitFaceBoundary graphData.toRotationSystem arc.selectedFace) :
    (anchor.redirectFromSelectedFaceOffEdge arc hoff).targetFace =
      anchor.targetFace := rfl

end ClosureRecoveryFaceArc

namespace ClosureRecoveryFaceCircuit

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- The support edge displayed at a recovery-cycle position. -/
def supportEdgeAt
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (position : Fin circuit.arcLength) : G.edgeSet :=
  (circuit.dependencyAt position).edge

/-- If two distinct recovery positions use the same support edge, every
source face belongs to the earlier source and the two target faces. -/
theorem IsLengthMinimal.sourceFace_mem_supportTriple_of_supportEdge_eq
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal)
    (first second : Fin circuit.arcLength)
    (hne : first ≠ second)
    (hedgeAt : circuit.supportEdgeAt first =
      circuit.supportEdgeAt second)
    (sourceArc : ClosureRecoveryFaceArc rebaseCircuit)
    (hsourceMem : sourceArc ∈ circuit.first :: circuit.rest) :
    sourceArc.sourceFace ∈
      ({(circuit.dependencyAt first).sourceFace,
        (circuit.dependencyAt first).targetFace,
        (circuit.dependencyAt second).targetFace} :
          Finset (OrbitFace graphData.toRotationSystem)) := by
  have hedge : (circuit.dependencyAt first).edge =
      (circuit.dependencyAt second).edge := by
    simpa [supportEdgeAt] using hedgeAt
  have htargetNe : (circuit.dependencyAt first).targetFace ≠
      (circuit.dependencyAt second).targetFace := by
    intro htarget
    apply hne
    apply hminimal.targetFaceAt_injective
    simpa [targetFaceAt] using htarget
  have hsecondEdgeMem : (circuit.dependencyAt first).edge ∈
      orbitFaceBoundary graphData.toRotationSystem
        (circuit.dependencyAt second).targetFace := by
    rw [hedge]
    exact (circuit.dependencyAt second).edge_mem_targetFace
  have hincident :
      (Finset.univ.filter fun face :
          OrbitFace graphData.toRotationSystem =>
        (circuit.dependencyAt first).edge ∈
          orbitFaceBoundary graphData.toRotationSystem face) =
        {(circuit.dependencyAt first).targetFace,
          (circuit.dependencyAt second).targetFace} :=
    orbitFace_incidentFaces_eq_pair_of_mem
      graphData.toRotationSystem minimal.facesTwoSided htargetNe
      (circuit.dependencyAt first).edge
      (circuit.dependencyAt first).edge_mem_targetFace
      hsecondEdgeMem
  have hselected : sourceArc.sourceFace ∈ rebaseCircuit.selectedFaces :=
    circuit.sourceFace_mem_selectedFaces_of_mem hsourceMem
  rcases (rebaseCircuit.mem_selectedFaces sourceArc.sourceFace).mp hselected with
    ⟨selectedArc, hselectedArcMem, hselectedFace⟩
  by_cases hoff : (circuit.dependencyAt first).edge ∉
      orbitFaceBoundary graphData.toRotationSystem selectedArc.selectedFace
  · let chord := (circuit.dependencyAt first).redirectFromSelectedFaceOffEdge
      selectedArc hoff
    have hsourceEq : chord.sourceFace = sourceArc.sourceFace := by
      simpa [chord] using hselectedFace
    have htargetEq : chord.targetFace =
        (circuit.dependencyAt first).targetFace := by
      simp [chord]
    have harcEq := hminimal.sourceArc_eq_of_chord_to_target sourceArc
      (circuit.dependencyAt first) chord hsourceMem
      (circuit.dependencyAt_mem first) hsourceEq htargetEq
    simp [harcEq]
  · have hon : (circuit.dependencyAt first).edge ∈
        orbitFaceBoundary graphData.toRotationSystem
          selectedArc.selectedFace := by
      simpa only [not_not] using hoff
    have hmem : selectedArc.selectedFace ∈
        Finset.univ.filter fun face :
            OrbitFace graphData.toRotationSystem =>
          (circuit.dependencyAt first).edge ∈
            orbitFaceBoundary graphData.toRotationSystem face :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hon⟩
    rw [hincident] at hmem
    rcases Finset.mem_insert.mp hmem with hfirst | hsecond
    · have hsourceEq : sourceArc.sourceFace =
          (circuit.dependencyAt first).targetFace :=
        hselectedFace.symm.trans hfirst
      simp [hsourceEq]
    · have hsourceEq : sourceArc.sourceFace =
          (circuit.dependencyAt second).targetFace := by
        have : selectedArc.selectedFace =
            (circuit.dependencyAt second).targetFace := by
          simpa using hsecond
        exact hselectedFace.symm.trans this
      simp [hsourceEq]

/-- Reusing a support edge at two distinct positions confines a shortest
recovery circuit to at most three arcs. -/
theorem IsLengthMinimal.arcLength_le_three_of_supportEdge_eq
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal)
    (first second : Fin circuit.arcLength)
    (hne : first ≠ second)
    (hedge : circuit.supportEdgeAt first =
      circuit.supportEdgeAt second) :
    circuit.arcLength ≤ 3 := by
  classical
  have hsubset : circuit.sourceFaces.toFinset ⊆
      ({(circuit.dependencyAt first).sourceFace,
        (circuit.dependencyAt first).targetFace,
        (circuit.dependencyAt second).targetFace} :
          Finset (OrbitFace graphData.toRotationSystem)) := by
    intro face hface
    have hfaceList : face ∈ circuit.sourceFaces := by simpa using hface
    rcases List.mem_map.mp hfaceList with ⟨sourceArc, hsourceMem, rfl⟩
    exact hminimal.sourceFace_mem_supportTriple_of_supportEdge_eq
      first second hne hedge sourceArc hsourceMem
  calc
    circuit.arcLength = circuit.sourceFaces.length :=
      circuit.sourceFaces_length.symm
    _ = circuit.sourceFaces.toFinset.card :=
      (List.toFinset_card_of_nodup hminimal.sourceFaces_nodup).symm
    _ ≤ ({(circuit.dependencyAt first).sourceFace,
          (circuit.dependencyAt first).targetFace,
          (circuit.dependencyAt second).targetFace} :
            Finset (OrbitFace graphData.toRotationSystem)).card :=
      Finset.card_le_card hsubset
    _ ≤ 3 := Finset.card_le_three

/-- The displayed support-edge word of a recovery circuit with at most
three arcs has no repetition. -/
theorem supportEdgeValues_nodup_of_arcLength_le_three
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (hlength : circuit.arcLength ≤ 3) :
    ((circuit.first :: circuit.rest).map
      ClosureRecoveryFaceArc.edge).Nodup := by
  cases hrest : circuit.rest with
  | nil =>
      exact (circuit.rest_ne_nil hrest).elim
  | cons second tail =>
      cases htail : tail with
      | nil =>
          have hfollow : ClosureRecoveryFaceArc.Follows
              circuit.first second := by
            simpa [hrest, htail] using circuit.consecutive
          simpa [hrest, htail] using hfollow.edge_ne
      | cons third final =>
          cases hfinal : final with
          | nil =>
              have hchain := circuit.consecutive
              rw [hrest, htail, hfinal] at hchain
              have hfirstSecond : ClosureRecoveryFaceArc.Follows
                  circuit.first second :=
                (List.isChain_cons_cons.mp hchain).1
              have hsecondThird : ClosureRecoveryFaceArc.Follows
                  second third := by
                simpa using (List.isChain_cons_cons.mp hchain).2
              have hthirdFirst : ClosureRecoveryFaceArc.Follows
                  third circuit.first := by
                simpa [hrest, htail, hfinal] using circuit.closing
              simpa [hrest, htail, hfinal] using
                And.intro
                  ⟨hfirstSecond.edge_ne, hthirdFirst.edge_ne.symm⟩
                  hsecondThird.edge_ne
          | cons fourth more =>
              have hfour : 4 ≤ circuit.arcLength := by
                simp [arcLength, hrest, htail, hfinal]
              omega

/-- Hence support-edge positions are injective for every recovery
circuit of length at most three. -/
theorem supportEdgeAt_injective_of_arcLength_le_three
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (hlength : circuit.arcLength ≤ 3) :
    Function.Injective circuit.supportEdgeAt := by
  have hnodup :=
    circuit.supportEdgeValues_nodup_of_arcLength_le_three hlength
  have hinjective : Function.Injective
      (((circuit.first :: circuit.rest).map
        ClosureRecoveryFaceArc.edge).get) :=
    List.nodup_iff_injective_get.mp hnodup
  have hedgeLength :
      ((circuit.first :: circuit.rest).map
          ClosureRecoveryFaceArc.edge).length = circuit.arcLength := by
    simp [arcLength]
  intro first second hedge
  let first' : Fin
      ((circuit.first :: circuit.rest).map
        ClosureRecoveryFaceArc.edge).length :=
    Fin.cast hedgeLength.symm first
  let second' : Fin
      ((circuit.first :: circuit.rest).map
        ClosureRecoveryFaceArc.edge).length :=
    Fin.cast hedgeLength.symm second
  have hget :
      ((circuit.first :: circuit.rest).map
          ClosureRecoveryFaceArc.edge).get first' =
        ((circuit.first :: circuit.rest).map
          ClosureRecoveryFaceArc.edge).get second' := by
    simp only [List.get_eq_getElem, List.getElem_map]
    simpa [first', second', supportEdgeAt, dependencyAt,
      List.get_eq_getElem] using hedge
  exact Fin.cast_injective hedgeLength.symm (hinjective hget)

/-- Every support edge occurs at most once on a shortest recovery
circuit, even when the two closure channels differ. -/
theorem IsLengthMinimal.supportEdgeAt_injective
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    Function.Injective circuit.supportEdgeAt := by
  intro first second hedge
  by_contra hne
  have hlength := hminimal.arcLength_le_three_of_supportEdge_eq
    first second hne hedge
  exact hne
    (circuit.supportEdgeAt_injective_of_arcLength_le_three hlength hedge)

/-- A shortest recovery circuit embeds in the ambient support-edge set. -/
theorem IsLengthMinimal.arcLength_le_card_edges
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    circuit.arcLength ≤ Fintype.card G.edgeSet := by
  simpa using Fintype.card_le_of_injective
    circuit.supportEdgeAt hminimal.supportEdgeAt_injective

end ClosureRecoveryFaceCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
