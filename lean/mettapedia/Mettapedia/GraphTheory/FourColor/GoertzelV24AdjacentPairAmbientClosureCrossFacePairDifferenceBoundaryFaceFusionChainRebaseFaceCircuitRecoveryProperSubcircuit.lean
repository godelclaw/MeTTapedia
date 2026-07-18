import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryComplementLoss

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

/-- Every displayed selected face of a two-arc rebase circuit equals the
first selected face. -/
theorem selectedFace_eq_first_of_arcLength_eq_two
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (hlength : circuit.arcLength = 2)
    (arc : CrossCentralExactFaceCertifiedRebaseArc graphData minimal
      baseData)
    (harc : arc ∈ circuit.first :: circuit.rest) :
    arc.selectedFace = circuit.first.selectedFace := by
  cases hrest : circuit.rest with
  | nil =>
      have hone : circuit.arcLength = 1 := by simp [arcLength, hrest]
      omega
  | cons second tail =>
      cases htail : tail with
      | nil =>
          have hfirstSecond :
              CrossCentralExactFaceCertifiedRebaseArc.Follows
                circuit.first second := by
            simpa [hrest, htail] using circuit.consecutive
          have hsecondFirst :
              CrossCentralExactFaceCertifiedRebaseArc.Follows
                second circuit.first := by
            simpa [hrest, htail] using circuit.closing
          have secondTransition :
              CrossCentralExactFaceCertifiedRebaseTransitionOnFace
                graphData minimal baseData second.selectedFace
                circuit.first.target circuit.first.source := by
            rw [hfirstSecond, ← hsecondFirst]
            exact second.transition
          have hfaces : circuit.first.selectedFace = second.selectedFace :=
            circuit.first.transition.faces_eq_of_twoStep_cycle
              secondTransition
          rw [hrest, htail] at harc
          rcases List.mem_cons.mp harc with rfl | harc
          · rfl
          · have harcEq : arc = second := by simpa using harc
            subst arc
            exact hfaces.symm
      | cons third more =>
          have hthree : 3 ≤ circuit.arcLength := by
            simp [arcLength, hrest, htail]
          omega

/-- Every displayed selected face of a three-arc rebase circuit equals
the first selected face. -/
theorem selectedFace_eq_first_of_arcLength_eq_three
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (hlength : circuit.arcLength = 3)
    (arc : CrossCentralExactFaceCertifiedRebaseArc graphData minimal
      baseData)
    (harc : arc ∈ circuit.first :: circuit.rest) :
    arc.selectedFace = circuit.first.selectedFace := by
  cases hrest : circuit.rest with
  | nil =>
      have hone : circuit.arcLength = 1 := by simp [arcLength, hrest]
      omega
  | cons second tail =>
      cases htail : tail with
      | nil =>
          have htwo : circuit.arcLength = 2 := by
            simp [arcLength, hrest, htail]
          omega
      | cons third final =>
          cases hfinal : final with
          | nil =>
              have hchain := circuit.consecutive
              rw [hrest, htail, hfinal] at hchain
              have hfirstSecond :
                  CrossCentralExactFaceCertifiedRebaseArc.Follows
                    circuit.first second :=
                (List.isChain_cons_cons.mp hchain).1
              have hsecondThird :
                  CrossCentralExactFaceCertifiedRebaseArc.Follows
                    second third := by
                simpa using (List.isChain_cons_cons.mp hchain).2
              have hthirdFirst :
                  CrossCentralExactFaceCertifiedRebaseArc.Follows
                    third circuit.first := by
                simpa [hrest, htail, hfinal] using circuit.closing
              have secondTransition :
                  CrossCentralExactFaceCertifiedRebaseTransitionOnFace
                    graphData minimal baseData second.selectedFace
                    circuit.first.target second.target := by
                rw [hfirstSecond]
                exact second.transition
              have thirdTransition :
                  CrossCentralExactFaceCertifiedRebaseTransitionOnFace
                    graphData minimal baseData third.selectedFace
                    second.target circuit.first.source := by
                rw [hsecondThird, ← hthirdFirst]
                exact third.transition
              have hfaces :=
                circuit.first.transition.faces_eq_of_threeStep_cycle
                  secondTransition thirdTransition
              rw [hrest, htail, hfinal] at harc
              rcases List.mem_cons.mp harc with rfl | harc
              · rfl
              · rcases List.mem_cons.mp harc with harc | harc
                · subst arc
                  exact hfaces.1.symm
                · have harcEq : arc = third := by simpa using harc
                  subst arc
                  exact hfaces.2.symm.trans hfaces.1.symm
          | cons fourth more =>
              have hfour : 4 ≤ circuit.arcLength := by
                simp [arcLength, hrest, htail, hfinal]
              omega

end CrossCentralExactFaceCertifiedRebaseCircuit

namespace ClosureRecoveryFaceCircuit

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- The restoring positions of a shortest recovery circuit form a proper
subset of the underlying rebase positions.  Equality would turn a recovery
digon or triangle into a forbidden two- or three-step rebase monodromy. -/
theorem IsLengthMinimal.arcLength_lt_rebase_arcLength
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    circuit.arcLength < rebaseCircuit.arcLength := by
  have hle := hminimal.arcLength_le_rebase_arcLength
  by_contra hnot
  have hrebaseLe : rebaseCircuit.arcLength ≤ circuit.arcLength :=
    Nat.le_of_not_gt hnot
  have hlengthEq : circuit.arcLength = rebaseCircuit.arcLength :=
    Nat.le_antisymm hle hrebaseLe
  rcases hminimal.isDigon_or_isTriangle with hdigon | htriangle
  · rcases hdigon with
      ⟨second, hrest, hfirstSecond, hsecondFirst⟩
    have hcircuitLength : circuit.arcLength = 2 := by
      simp [arcLength, hrest]
    have hrebaseLength : rebaseCircuit.arcLength = 2 := by
      rw [← hlengthEq]
      exact hcircuitLength
    have hfirstSelected :=
      rebaseCircuit.selectedFace_eq_first_of_arcLength_eq_two
        hrebaseLength circuit.first.recoveryArc
        circuit.first.recoveryArc_mem_displayed
    have hsecondSelected :=
      rebaseCircuit.selectedFace_eq_first_of_arcLength_eq_two
        hrebaseLength second.recoveryArc
        second.recoveryArc_mem_displayed
    have htargetEq : circuit.first.targetFace = second.targetFace := by
      calc
        circuit.first.targetFace =
            circuit.first.recoveryArc.selectedFace :=
          circuit.first.recoveryArc_selectedFace.symm
        _ = rebaseCircuit.first.selectedFace := hfirstSelected
        _ = second.recoveryArc.selectedFace := hsecondSelected.symm
        _ = second.targetFace := second.recoveryArc_selectedFace
    exact circuit.first.targetFace_ne_sourceFace
      (htargetEq.trans hsecondFirst)
  · rcases htriangle with
      ⟨second, third, hrest, hfirstSecond, hsecondThird, _hthirdFirst⟩
    have hcircuitLength : circuit.arcLength = 3 := by
      simp [arcLength, hrest]
    have hrebaseLength : rebaseCircuit.arcLength = 3 := by
      rw [← hlengthEq]
      exact hcircuitLength
    have hfirstSelected :=
      rebaseCircuit.selectedFace_eq_first_of_arcLength_eq_three
        hrebaseLength circuit.first.recoveryArc
        circuit.first.recoveryArc_mem_displayed
    have hsecondSelected :=
      rebaseCircuit.selectedFace_eq_first_of_arcLength_eq_three
        hrebaseLength second.recoveryArc
        second.recoveryArc_mem_displayed
    have htargetEq : circuit.first.targetFace = second.targetFace := by
      calc
        circuit.first.targetFace =
            circuit.first.recoveryArc.selectedFace :=
          circuit.first.recoveryArc_selectedFace.symm
        _ = rebaseCircuit.first.selectedFace := hfirstSelected
        _ = second.recoveryArc.selectedFace := hsecondSelected.symm
        _ = second.targetFace := second.recoveryArc_selectedFace
    have hsourceEq : second.sourceFace = third.sourceFace := by
      calc
        second.sourceFace = circuit.first.targetFace := hfirstSecond.symm
        _ = second.targetFace := htargetEq
        _ = third.sourceFace := hsecondThird
    exact second.targetFace_ne_sourceFace
      (hsecondThird.trans hsourceEq.symm)

/-- A rebase circuit carrying a shortest recovery circuit has at least
four arcs.  In the digon case, strict containment leaves only a
three-arc exception below four, and three-step rebase monodromy makes
all selected faces equal. -/
theorem IsLengthMinimal.four_le_rebase_arcLength
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    4 ≤ rebaseCircuit.arcLength := by
  rcases hminimal.isDigon_or_isTriangle with hdigon | htriangle
  · rcases hdigon with
      ⟨second, hrest, _hfirstSecond, hsecondFirst⟩
    have hcircuitLength : circuit.arcLength = 2 := by
      simp [arcLength, hrest]
    have hstrict := hminimal.arcLength_lt_rebase_arcLength
    by_contra hnot
    have hrebaseLength : rebaseCircuit.arcLength = 3 := by omega
    have hfirstSelected :=
      rebaseCircuit.selectedFace_eq_first_of_arcLength_eq_three
        hrebaseLength circuit.first.recoveryArc
        circuit.first.recoveryArc_mem_displayed
    have hsecondSelected :=
      rebaseCircuit.selectedFace_eq_first_of_arcLength_eq_three
        hrebaseLength second.recoveryArc
        second.recoveryArc_mem_displayed
    have htargetEq : circuit.first.targetFace = second.targetFace := by
      calc
        circuit.first.targetFace =
            circuit.first.recoveryArc.selectedFace :=
          circuit.first.recoveryArc_selectedFace.symm
        _ = rebaseCircuit.first.selectedFace := hfirstSelected
        _ = second.recoveryArc.selectedFace := hsecondSelected.symm
        _ = second.targetFace := second.recoveryArc_selectedFace
    exact circuit.first.targetFace_ne_sourceFace
      (htargetEq.trans hsecondFirst)
  · rcases htriangle with
      ⟨second, third, hrest, _hfirstSecond, _hsecondThird,
        _hthirdFirst⟩
    have hcircuitLength : circuit.arcLength = 3 := by
      simp [arcLength, hrest]
    have hstrict := hminimal.arcLength_lt_rebase_arcLength
    omega

/-- A shortest recovery digon leaves a gap of at least two positions
inside its underlying rebase circuit. -/
theorem IsLengthMinimal.arcLength_add_two_le_rebase_arcLength_of_isDigon
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal)
    (hdigon : circuit.IsDigon) :
    circuit.arcLength + 2 ≤ rebaseCircuit.arcLength := by
  rcases hdigon with ⟨second, hrest, _hfirstSecond, _hsecondFirst⟩
  have hcircuitLength : circuit.arcLength = 2 := by
    simp [arcLength, hrest]
  have hfour := hminimal.four_le_rebase_arcLength
  omega

/-- Rebase positions claimed as restoring locations by a recovery
circuit. -/
noncomputable def claimedRebasePositions
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit) :
    Finset (Fin rebaseCircuit.arcLength) :=
  Finset.univ.image circuit.restoringPositionAt

/-- Rebase positions not claimed as restoring locations by a recovery
circuit. -/
noncomputable def unclaimedRebasePositions
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit) :
    Finset (Fin rebaseCircuit.arcLength) :=
  circuit.claimedRebasePositionsᶜ

@[simp]
theorem mem_claimedRebasePositions_iff
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (position : Fin rebaseCircuit.arcLength) :
    position ∈ circuit.claimedRebasePositions ↔
      ∃ recoveryPosition : Fin circuit.arcLength,
        circuit.restoringPositionAt recoveryPosition = position := by
  classical
  simp [claimedRebasePositions]

@[simp]
theorem mem_unclaimedRebasePositions_iff
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (position : Fin rebaseCircuit.arcLength) :
    position ∈ circuit.unclaimedRebasePositions ↔
      ∀ recoveryPosition : Fin circuit.arcLength,
        circuit.restoringPositionAt recoveryPosition ≠ position := by
  classical
  simp [unclaimedRebasePositions]

/-- Injectivity makes the number of claimed rebase positions exactly
the length of a shortest recovery circuit. -/
theorem IsLengthMinimal.card_claimedRebasePositions
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    circuit.claimedRebasePositions.card = circuit.arcLength := by
  classical
  calc
    circuit.claimedRebasePositions.card =
        (Finset.univ : Finset (Fin circuit.arcLength)).card :=
      Finset.card_image_of_injective _
        hminimal.restoringPositionAt_injective
    _ = circuit.arcLength := by simp

/-- The unclaimed carrier has the exact length difference between the
rebase circuit and the shortest recovery circuit. -/
theorem IsLengthMinimal.card_unclaimedRebasePositions
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    circuit.unclaimedRebasePositions.card =
      rebaseCircuit.arcLength - circuit.arcLength := by
  classical
  rw [unclaimedRebasePositions, Finset.card_compl,
    hminimal.card_claimedRebasePositions]
  simp

/-- A shortest recovery digon leaves at least two distinct unclaimed
rebase positions. -/
theorem IsLengthMinimal.two_le_card_unclaimedRebasePositions_of_isDigon
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal)
    (hdigon : circuit.IsDigon) :
    2 ≤ circuit.unclaimedRebasePositions.card := by
  rw [hminimal.card_unclaimedRebasePositions]
  have hgap :=
    hminimal.arcLength_add_two_le_rebase_arcLength_of_isDigon hdigon
  omega

/-- The two-position digon gap can be exposed as two concrete, distinct
positions missed by every restoring map entry. -/
theorem IsLengthMinimal.exists_two_unclaimed_rebasePositions_of_isDigon
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal)
    (hdigon : circuit.IsDigon) :
    ∃ first second : Fin rebaseCircuit.arcLength,
      first ≠ second ∧
        (∀ recoveryPosition : Fin circuit.arcLength,
          circuit.restoringPositionAt recoveryPosition ≠ first) ∧
        (∀ recoveryPosition : Fin circuit.arcLength,
          circuit.restoringPositionAt recoveryPosition ≠ second) := by
  have hcard :=
    hminimal.two_le_card_unclaimedRebasePositions_of_isDigon hdigon
  have hone : 1 < circuit.unclaimedRebasePositions.card := by omega
  rcases Finset.one_lt_card.mp hone with
    ⟨first, hfirst, second, hsecond, hne⟩
  exact ⟨first, second, hne,
    (circuit.mem_unclaimedRebasePositions_iff first).mp hfirst,
    (circuit.mem_unclaimedRebasePositions_iff second).mp hsecond⟩

/-- Hence at least one underlying rebase position is not the restoring
position of any recovery dependency. -/
theorem IsLengthMinimal.exists_unclaimed_rebasePosition
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    ∃ position : Fin rebaseCircuit.arcLength,
      ∀ recoveryPosition : Fin circuit.arcLength,
        circuit.restoringPositionAt recoveryPosition ≠ position := by
  have hnonempty : circuit.unclaimedRebasePositions.Nonempty := by
    rw [← Finset.card_pos]
    rw [hminimal.card_unclaimedRebasePositions]
    have hstrict := hminimal.arcLength_lt_rebase_arcLength
    omega
  rcases hnonempty with ⟨position, hposition⟩
  exact ⟨position,
    (circuit.mem_unclaimedRebasePositions_iff position).mp hposition⟩

end ClosureRecoveryFaceCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
