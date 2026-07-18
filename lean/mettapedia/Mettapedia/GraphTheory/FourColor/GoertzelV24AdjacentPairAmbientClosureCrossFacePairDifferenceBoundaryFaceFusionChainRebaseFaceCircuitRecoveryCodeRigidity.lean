import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryChord

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

/-- The displayed code word of a recovery circuit with at most three
arcs has no repetition. -/
theorem codeValues_nodup_of_arcLength_le_three
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (hlength : circuit.arcLength ≤ 3) :
    ((circuit.first :: circuit.rest).map
      ClosureRecoveryFaceArc.code).Nodup := by
  cases hrest : circuit.rest with
  | nil =>
      exact (circuit.rest_ne_nil hrest).elim
  | cons second tail =>
      cases htail : tail with
      | nil =>
          have hfollow : ClosureRecoveryFaceArc.Follows
              circuit.first second := by
            simpa [hrest, htail] using circuit.consecutive
          simpa [hrest, htail] using hfollow.code_ne
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
                  ⟨hfirstSecond.code_ne, hthirdFirst.code_ne.symm⟩
                  hsecondThird.code_ne
          | cons fourth more =>
              have hfour : 4 ≤ circuit.arcLength := by
                simp [arcLength, hrest, htail, hfinal]
              omega

/-- Hence the position-to-code map of any recovery circuit of length at
most three is injective. -/
theorem codeAt_injective_of_arcLength_le_three
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (hlength : circuit.arcLength ≤ 3) :
    Function.Injective circuit.codeAt := by
  have hnodup := circuit.codeValues_nodup_of_arcLength_le_three hlength
  have hinjective : Function.Injective
      (((circuit.first :: circuit.rest).map
        ClosureRecoveryFaceArc.code).get) :=
    List.nodup_iff_injective_get.mp hnodup
  have hcodeLength :
      ((circuit.first :: circuit.rest).map
          ClosureRecoveryFaceArc.code).length = circuit.arcLength := by
    simp [arcLength]
  intro first second hcode
  let first' : Fin
      ((circuit.first :: circuit.rest).map
        ClosureRecoveryFaceArc.code).length :=
    Fin.cast hcodeLength.symm first
  let second' : Fin
      ((circuit.first :: circuit.rest).map
        ClosureRecoveryFaceArc.code).length :=
    Fin.cast hcodeLength.symm second
  have hget :
      ((circuit.first :: circuit.rest).map
          ClosureRecoveryFaceArc.code).get first' =
        ((circuit.first :: circuit.rest).map
          ClosureRecoveryFaceArc.code).get second' := by
    simp only [List.get_eq_getElem, List.getElem_map]
    simpa [first', second', codeAt, dependencyAt,
      List.get_eq_getElem] using hcode
  exact Fin.cast_injective hcodeLength.symm (hinjective hget)

/-- The repeated-code alternative is impossible on a shortest recovery
circuit. -/
theorem IsLengthMinimal.not_exists_code_collision
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    ¬ ∃ first second : Fin circuit.arcLength,
      first ≠ second ∧ circuit.codeAt first = circuit.codeAt second := by
  intro collision
  have hlength :=
    hminimal.arcLength_le_three_of_code_collision collision
  have hinjective := circuit.codeAt_injective_of_arcLength_le_three hlength
  rcases collision with ⟨first, second, hne, hcode⟩
  exact hne (hinjective hcode)

/-- Thus every channel/edge code occurs at most once on a shortest
recovery circuit. -/
theorem IsLengthMinimal.codeAt_injective
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    Function.Injective circuit.codeAt := by
  by_contra hinjective
  rcases Function.not_injective_iff.mp hinjective with
    ⟨first, second, hcode, hne⟩
  exact hminimal.not_exists_code_collision
    ⟨first, second, hne, hcode⟩

/-- The injective recovery-code map embeds every shortest recovery
circuit in the finite channel/edge alphabet. -/
theorem IsLengthMinimal.arcLength_le_card_codeAlphabet
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    circuit.arcLength ≤
      Fintype.card (ExactClosureChannel × G.edgeSet) := by
  simpa using Fintype.card_le_of_injective
    circuit.codeAt hminimal.codeAt_injective

end ClosureRecoveryFaceCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
