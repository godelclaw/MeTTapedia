import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryEdgeRigidity

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

namespace ClosureRecoveryFaceCircuit

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- Relative to any anchor of a shortest recovery circuit, every other
source face is incident to the anchor's support edge. -/
theorem IsLengthMinimal.sourceArc_eq_anchor_or_anchorEdge_mem_sourceFace
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal)
    (anchor sourceArc : ClosureRecoveryFaceArc rebaseCircuit)
    (hanchorMem : anchor ∈ circuit.first :: circuit.rest)
    (hsourceMem : sourceArc ∈ circuit.first :: circuit.rest) :
    sourceArc = anchor ∨
      anchor.edge ∈ orbitFaceBoundary graphData.toRotationSystem
        sourceArc.sourceFace := by
  by_cases harc : sourceArc = anchor
  · exact Or.inl harc
  · right
    by_contra hoff
    have hselected : sourceArc.sourceFace ∈ rebaseCircuit.selectedFaces :=
      circuit.sourceFace_mem_selectedFaces_of_mem hsourceMem
    rcases (rebaseCircuit.mem_selectedFaces sourceArc.sourceFace).mp
        hselected with ⟨selectedArc, hselectedArcMem, hselectedFace⟩
    have hoffSelected : anchor.edge ∉
        orbitFaceBoundary graphData.toRotationSystem
          selectedArc.selectedFace := by
      simpa [hselectedFace] using hoff
    let chord := anchor.redirectFromSelectedFaceOffEdge
      selectedArc hoffSelected
    have hsourceEq : chord.sourceFace = sourceArc.sourceFace := by
      simpa [chord] using hselectedFace
    have htargetEq : chord.targetFace = anchor.targetFace := by
      simp [chord]
    exact harc (hminimal.sourceArc_eq_of_chord_to_target
      sourceArc anchor chord hsourceMem hanchorMem hsourceEq htargetEq)

/-- Every shortest recovery circuit is supported on the anchor source
face and the at most two faces incident to the anchor edge. -/
theorem IsLengthMinimal.sourceFaces_subset_anchor_and_incidentFaces
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal)
    (anchor : ClosureRecoveryFaceArc rebaseCircuit)
    (hanchorMem : anchor ∈ circuit.first :: circuit.rest) :
    circuit.sourceFaces.toFinset ⊆
      insert anchor.sourceFace
        (Finset.univ.filter fun face :
          OrbitFace graphData.toRotationSystem =>
            anchor.edge ∈
              orbitFaceBoundary graphData.toRotationSystem face) := by
  intro face hface
  have hfaceList : face ∈ circuit.sourceFaces := by simpa using hface
  rcases List.mem_map.mp hfaceList with ⟨sourceArc, hsourceMem, rfl⟩
  rcases hminimal.sourceArc_eq_anchor_or_anchorEdge_mem_sourceFace
      anchor sourceArc hanchorMem hsourceMem with harc | hedge
  · rw [harc]
    exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hedge⟩)

/-- Facial two-sidedness and chordlessness leave only recovery digons or
triangles: every shortest recovery circuit has at most three arcs. -/
theorem IsLengthMinimal.arcLength_le_three
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    circuit.arcLength ≤ 3 := by
  classical
  let incidentFaces : Finset (OrbitFace graphData.toRotationSystem) :=
    Finset.univ.filter fun face =>
      circuit.first.edge ∈
        orbitFaceBoundary graphData.toRotationSystem face
  have hsubset : circuit.sourceFaces.toFinset ⊆
      insert circuit.first.sourceFace incidentFaces := by
    exact hminimal.sourceFaces_subset_anchor_and_incidentFaces
      circuit.first (by simp)
  have hincident : incidentFaces.card ≤ 2 := by
    simpa [incidentFaces, totalIncidenceCount] using
      orbitFace_totalIncidenceCount_le_two
        graphData.toRotationSystem circuit.first.edge
  calc
    circuit.arcLength = circuit.sourceFaces.length :=
      circuit.sourceFaces_length.symm
    _ = circuit.sourceFaces.toFinset.card :=
      (List.toFinset_card_of_nodup hminimal.sourceFaces_nodup).symm
    _ ≤ (insert circuit.first.sourceFace incidentFaces).card :=
      Finset.card_le_card hsubset
    _ ≤ incidentFaces.card + 1 := Finset.card_insert_le _ _
    _ ≤ 3 := by omega

/-- Together with the absence of self-dependencies, the shortest recovery
length is exactly two or three. -/
theorem IsLengthMinimal.arcLength_eq_two_or_three
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    circuit.arcLength = 2 ∨ circuit.arcLength = 3 := by
  have hlower := circuit.two_le_arcLength
  have hupper := hminimal.arcLength_le_three
  omega

end ClosureRecoveryFaceCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
