import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryEdgeIncidence

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

/-- Any representative of the same intrinsic dependency cycle defines
the same recovery circuit with a different chosen first arc. -/
def rotateToRepresentative
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (first : ClosureRecoveryFaceArc rebaseCircuit)
    (rest : List (ClosureRecoveryFaceArc rebaseCircuit))
    (hsameCycle : ((first :: rest : List
      (ClosureRecoveryFaceArc rebaseCircuit)) : Cycle _) =
        circuit.dependencyCycle) :
    ClosureRecoveryFaceCircuit rebaseCircuit := by
  have hcycleChain : Cycle.Chain ClosureRecoveryFaceArc.Follows
      ((first :: rest : List
        (ClosureRecoveryFaceArc rebaseCircuit)) : Cycle
          (ClosureRecoveryFaceArc rebaseCircuit)) := by
    rw [hsameCycle]
    exact circuit.dependencyCycle_chain
  have hcyclic : List.IsChain ClosureRecoveryFaceArc.Follows
      ((first :: rest) ++ [first]) := by
    have := (Cycle.chain_coe_cons ClosureRecoveryFaceArc.Follows
      first rest).mp hcycleChain
    simpa only [List.cons_append] using this
  have hparts := List.isChain_append.mp hcyclic
  refine {
    first := first
    rest := rest
    consecutive := hparts.1
    closing := ?_ }
  exact hparts.2.2 ((first :: rest).getLast (by simp))
    (by
      rw [List.getLast?_eq_getLast_of_ne_nil (by simp)]
      simp) first (by simp)

@[simp] theorem rotateToRepresentative_arcLength
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (first : ClosureRecoveryFaceArc rebaseCircuit)
    (rest : List (ClosureRecoveryFaceArc rebaseCircuit))
    (hsameCycle : ((first :: rest : List
      (ClosureRecoveryFaceArc rebaseCircuit)) : Cycle _) =
        circuit.dependencyCycle) :
    (circuit.rotateToRepresentative first rest hsameCycle).arcLength =
      circuit.arcLength := by
  have hlength := congrArg Cycle.length hsameCycle
  simpa [rotateToRepresentative, dependencyCycle, arcLength] using hlength

/-- Splitting the displayed recovery list at an occurrence and moving its
prefix to the end gives a certified cyclic rotation. -/
def rotateAtSplit
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (first : ClosureRecoveryFaceArc rebaseCircuit)
    (before after : List (ClosureRecoveryFaceArc rebaseCircuit))
    (hsplit : circuit.first :: circuit.rest =
      before ++ first :: after) :
    ClosureRecoveryFaceCircuit rebaseCircuit := by
  refine circuit.rotateToRepresentative first (after ++ before) ?_
  change (↑(first :: after ++ before) : Cycle
      (ClosureRecoveryFaceArc rebaseCircuit)) =
    ↑(circuit.first :: circuit.rest)
  apply Cycle.coe_eq_coe.mpr
  rw [hsplit]
  exact List.isRotated_append.symm

@[simp] theorem rotateAtSplit_first
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (first : ClosureRecoveryFaceArc rebaseCircuit)
    (before after : List (ClosureRecoveryFaceArc rebaseCircuit))
    (hsplit : circuit.first :: circuit.rest =
      before ++ first :: after) :
    (circuit.rotateAtSplit first before after hsplit).first = first := by
  simp [rotateAtSplit, rotateToRepresentative]

@[simp] theorem rotateAtSplit_rest
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (first : ClosureRecoveryFaceArc rebaseCircuit)
    (before after : List (ClosureRecoveryFaceArc rebaseCircuit))
    (hsplit : circuit.first :: circuit.rest =
      before ++ first :: after) :
    (circuit.rotateAtSplit first before after hsplit).rest =
      after ++ before := by
  simp [rotateAtSplit, rotateToRepresentative]

@[simp] theorem rotateAtSplit_arcLength
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (first : ClosureRecoveryFaceArc rebaseCircuit)
    (before after : List (ClosureRecoveryFaceArc rebaseCircuit))
    (hsplit : circuit.first :: circuit.rest =
      before ++ first :: after) :
    (circuit.rotateAtSplit first before after hsplit).arcLength =
      circuit.arcLength := by
  simp only [arcLength, rotateAtSplit_first, rotateAtSplit_rest]
  rw [hsplit]
  simp [Nat.add_comm, Nat.add_left_comm]

/-- A cyclic chord closes the displayed segment preceding its source into
a new recovery circuit. -/
theorem exists_subcircuit_of_chord_split
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (first sourceArc chord : ClosureRecoveryFaceArc rebaseCircuit)
    (before between after : List (ClosureRecoveryFaceArc rebaseCircuit))
    (hsplit : circuit.first :: circuit.rest =
      before ++ (first :: (between ++ (sourceArc :: after))))
    (hchordSource : chord.sourceFace = sourceArc.sourceFace)
    (hchordTarget : chord.targetFace = first.sourceFace) :
    ∃ subcircuit : ClosureRecoveryFaceCircuit rebaseCircuit,
      subcircuit.first :: subcircuit.rest =
        first :: (between ++ [chord]) := by
  let segment := first :: between
  have hfullChain : List.IsChain ClosureRecoveryFaceArc.Follows
      (before ++ (segment ++ (sourceArc :: after))) := by
    have hchain := circuit.consecutive
    rw [hsplit] at hchain
    simpa [segment, List.append_assoc] using hchain
  have hsegmentAfterChain : List.IsChain ClosureRecoveryFaceArc.Follows
      (segment ++ (sourceArc :: after)) :=
    (List.isChain_append.mp hfullChain).2.1
  have hparts := List.isChain_append.mp hsegmentAfterChain
  have hsegmentNe : segment ≠ [] := by simp [segment]
  let last := segment.getLast hsegmentNe
  have hlastMem : last ∈ segment.getLast? := by
    rw [List.getLast?_eq_getLast_of_ne_nil hsegmentNe]
    simp [last]
  have hlastFollows : ClosureRecoveryFaceArc.Follows last sourceArc :=
    hparts.2.2 last hlastMem sourceArc (by simp)
  have hlastChord : ClosureRecoveryFaceArc.Follows last chord := by
    change last.targetFace = chord.sourceFace
    exact hlastFollows.trans hchordSource.symm
  let subcircuit : ClosureRecoveryFaceCircuit rebaseCircuit := {
    first := first
    rest := between ++ [chord]
    consecutive := by
      have hsegmentChain := hparts.1
      apply hsegmentChain.append (List.IsChain.singleton _)
      intro last' hlast' chord' hchord'
      have hlastEq : last' = last := by
        rcases List.mem_getLast?_eq_getLast hlast' with ⟨hne, heq⟩
        simpa [last, segment] using heq
      have hchordEq : chord' = chord := by simpa using hchord'.symm
      simpa [hlastEq, hchordEq] using hlastChord
    closing := by
      simpa [ClosureRecoveryFaceArc.Follows] using hchordTarget }
  exact ⟨subcircuit, rfl⟩

/-- If either complementary displayed piece is nonempty, the chord
subcircuit is strictly shorter. -/
theorem exists_strict_subcircuit_of_chord_split
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (first sourceArc chord : ClosureRecoveryFaceArc rebaseCircuit)
    (before between after : List (ClosureRecoveryFaceArc rebaseCircuit))
    (hsplit : circuit.first :: circuit.rest =
      before ++ (first :: (between ++ (sourceArc :: after))))
    (hchordSource : chord.sourceFace = sourceArc.sourceFace)
    (hchordTarget : chord.targetFace = first.sourceFace)
    (houtside : before ≠ [] ∨ after ≠ []) :
    ∃ subcircuit : ClosureRecoveryFaceCircuit rebaseCircuit,
      subcircuit.arcLength < circuit.arcLength := by
  rcases circuit.exists_subcircuit_of_chord_split first sourceArc chord
      before between after hsplit hchordSource hchordTarget with
    ⟨subcircuit, hsubcircuit⟩
  refine ⟨subcircuit, ?_⟩
  have hsubLength : subcircuit.arcLength = between.length + 2 := by
    rw [arcLength, hsubcircuit]
    simp
  have hcircuitLength : circuit.arcLength =
      before.length + between.length + after.length + 2 := by
    rw [arcLength, hsplit]
    simp
    omega
  rw [hsubLength, hcircuitLength]
  rcases houtside with hbefore | hafter
  · have hbeforeLength : before.length ≠ 0 := by
      intro hzero
      exact hbefore (List.length_eq_zero_iff.mp hzero)
    omega
  · have hafterLength : after.length ≠ 0 := by
      intro hzero
      exact hafter (List.length_eq_zero_iff.mp hzero)
    omega

/-- Chordlessness of a shortest recovery circuit: a recovery dependency
aimed at the target of a displayed arc can only originate at that same
displayed arc. -/
theorem dependencyAt_mem
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (position : Fin circuit.arcLength) :
    circuit.dependencyAt position ∈ circuit.first :: circuit.rest := by
  exact List.get_mem _ _

theorem IsLengthMinimal.sourceArc_eq_of_chord_to_target
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal)
    (sourceArc predecessor chord : ClosureRecoveryFaceArc rebaseCircuit)
    (hsourceMem : sourceArc ∈ circuit.first :: circuit.rest)
    (hpredecessorMem : predecessor ∈ circuit.first :: circuit.rest)
    (hchordSource : chord.sourceFace = sourceArc.sourceFace)
    (hchordTarget : chord.targetFace = predecessor.targetFace) :
    sourceArc = predecessor := by
  by_contra hne
  rcases List.mem_iff_append.mp hpredecessorMem with
    ⟨before, after, hsplit⟩
  let rotated := circuit.rotateAtSplit predecessor before after hsplit
  have hrotatedList : rotated.first :: rotated.rest =
      predecessor :: (after ++ before) := by
    simp [rotated]
  have hsourceTail : sourceArc ∈ after ++ before := by
    rw [hsplit] at hsourceMem
    rcases List.mem_append.mp hsourceMem with hbefore | htail
    · exact List.mem_append_right after hbefore
    · rcases List.mem_cons.mp htail with heq | hafter
      · exact (hne heq).elim
      · exact List.mem_append_left before hafter
  cases htailEq : after ++ before with
  | nil =>
      simp [htailEq] at hsourceTail
  | cons next tailRest =>
      have hfollow : ClosureRecoveryFaceArc.Follows predecessor next := by
        have hchain := rotated.consecutive
        rw [hrotatedList, htailEq] at hchain
        exact (List.isChain_cons_cons.mp hchain).1
      have hsourceNeNext : sourceArc ≠ next := by
        intro heq
        apply chord.targetFace_ne_sourceFace
        calc
          chord.targetFace = predecessor.targetFace := hchordTarget
          _ = next.sourceFace := hfollow
          _ = sourceArc.sourceFace := by rw [heq]
          _ = chord.sourceFace := hchordSource.symm
      have hsourceTailRest : sourceArc ∈ tailRest := by
        have hmem : sourceArc ∈ next :: tailRest := by
          simpa only [htailEq] using hsourceTail
        rcases List.mem_cons.mp hmem with heq | hmem
        · exact (hsourceNeNext heq).elim
        · exact hmem
      rcases List.mem_iff_append.mp hsourceTailRest with
        ⟨between, final, htailSplit⟩
      have hrotatedSplit : rotated.first :: rotated.rest =
          [predecessor] ++
            (next :: (between ++ (sourceArc :: final))) := by
        rw [hrotatedList, htailEq, htailSplit]
        simp
      have hchordTargetNext : chord.targetFace = next.sourceFace :=
        hchordTarget.trans hfollow
      rcases rotated.exists_strict_subcircuit_of_chord_split
          next sourceArc chord [predecessor] between final
          hrotatedSplit hchordSource hchordTargetNext (Or.inl (by simp)) with
        ⟨subcircuit, hshort⟩
      have hshort' : subcircuit.arcLength < circuit.arcLength := by
        have hrotatedLength : rotated.arcLength = circuit.arcLength := by
          exact circuit.rotateAtSplit_arcLength predecessor before after hsplit
        rw [hrotatedLength] at hshort
        exact hshort
      exact (Nat.not_lt_of_ge (hminimal subcircuit)) hshort'

end ClosureRecoveryFaceCircuit

namespace ClosureRecoveryCodeAlternation

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
  {recoveryCircuit : ClosureRecoveryFaceCircuit rebaseCircuit}

/-- Every source face of a shortest recovery circuit with a repeated
code is one of the repeated gain targets or the source of the earlier
gain. -/
theorem sourceFace_mem_supportTriple
    (alternation : ClosureRecoveryCodeAlternation rebaseCircuit
      recoveryCircuit)
    (hrecoveryMinimal : recoveryCircuit.IsLengthMinimal)
    (sourceArc : ClosureRecoveryFaceArc rebaseCircuit)
    (hsourceMem : sourceArc ∈
      recoveryCircuit.first :: recoveryCircuit.rest) :
    sourceArc.sourceFace ∈
      ({(recoveryCircuit.dependencyAt alternation.earlier).sourceFace,
        (recoveryCircuit.dependencyAt alternation.earlier).targetFace,
        (recoveryCircuit.dependencyAt alternation.later).targetFace} :
          Finset (OrbitFace graphData.toRotationSystem)) := by
  have hselected : sourceArc.sourceFace ∈ rebaseCircuit.selectedFaces :=
    recoveryCircuit.sourceFace_mem_selectedFaces_of_mem hsourceMem
  rcases (rebaseCircuit.mem_selectedFaces sourceArc.sourceFace).mp hselected with
    ⟨selectedArc, hselectedArcMem, hselectedFace⟩
  rcases alternation.selectedFace_off_or_eq_targetFace
      hrecoveryMinimal selectedArc with hoff | htarget
  · let chord := alternation.recoveryFromSelectedFaceOffEdge selectedArc hoff
    have hsourceEq : chord.sourceFace = sourceArc.sourceFace := by
      simpa [chord] using hselectedFace
    have htargetEq : chord.targetFace =
        (recoveryCircuit.dependencyAt alternation.earlier).targetFace := by
      simp [chord]
    have harcEq :=
      hrecoveryMinimal.sourceArc_eq_of_chord_to_target sourceArc
        (recoveryCircuit.dependencyAt alternation.earlier) chord
        hsourceMem
        (recoveryCircuit.dependencyAt_mem alternation.earlier)
        hsourceEq htargetEq
    simp [harcEq]
  · rcases htarget with htarget | htarget
    · have hsourceEq : sourceArc.sourceFace =
          (recoveryCircuit.dependencyAt alternation.earlier).targetFace :=
        hselectedFace.symm.trans htarget
      simp [hsourceEq]
    · have hsourceEq : sourceArc.sourceFace =
          (recoveryCircuit.dependencyAt alternation.later).targetFace :=
        hselectedFace.symm.trans htarget
      simp [hsourceEq]

/-- Consequently, any repeated recovery code confines a shortest
recovery circuit to at most three arcs. -/
theorem arcLength_le_three
    (alternation : ClosureRecoveryCodeAlternation rebaseCircuit
      recoveryCircuit)
    (hrecoveryMinimal : recoveryCircuit.IsLengthMinimal) :
    recoveryCircuit.arcLength ≤ 3 := by
  classical
  have hsubset : recoveryCircuit.sourceFaces.toFinset ⊆
      ({(recoveryCircuit.dependencyAt alternation.earlier).sourceFace,
        (recoveryCircuit.dependencyAt alternation.earlier).targetFace,
        (recoveryCircuit.dependencyAt alternation.later).targetFace} :
          Finset (OrbitFace graphData.toRotationSystem)) := by
    intro face hface
    have hfaceList : face ∈ recoveryCircuit.sourceFaces := by
      simpa using hface
    rcases List.mem_map.mp hfaceList with ⟨sourceArc, hsourceMem, rfl⟩
    exact alternation.sourceFace_mem_supportTriple
      hrecoveryMinimal sourceArc hsourceMem
  calc
    recoveryCircuit.arcLength = recoveryCircuit.sourceFaces.length :=
      recoveryCircuit.sourceFaces_length.symm
    _ = recoveryCircuit.sourceFaces.toFinset.card :=
      (List.toFinset_card_of_nodup
        hrecoveryMinimal.sourceFaces_nodup).symm
    _ ≤ ({(recoveryCircuit.dependencyAt alternation.earlier).sourceFace,
          (recoveryCircuit.dependencyAt alternation.earlier).targetFace,
          (recoveryCircuit.dependencyAt alternation.later).targetFace} :
            Finset (OrbitFace graphData.toRotationSystem)).card :=
      Finset.card_le_card hsubset
    _ ≤ 3 := Finset.card_le_three

end ClosureRecoveryCodeAlternation

namespace ClosureRecoveryFaceCircuit

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- The collision branch of the recovery-code dichotomy is genuinely
small: it has at most three dependencies. -/
theorem IsLengthMinimal.arcLength_le_three_of_code_collision
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal)
    (collision : ∃ first second : Fin circuit.arcLength,
      first ≠ second ∧ circuit.codeAt first = circuit.codeAt second) :
    circuit.arcLength ≤ 3 := by
  rcases hminimal.exists_codeAlternation_of_code_collision collision with
    ⟨alternation⟩
  exact alternation.arcLength_le_three hminimal

/-- Thus a shortest recovery circuit is either bounded by the finite
channel/edge alphabet, or belongs to the three-arc exceptional regime. -/
theorem IsLengthMinimal.arcLength_le_twice_card_edges_or_le_three
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    circuit.arcLength ≤ 2 * Fintype.card G.edgeSet ∨
      circuit.arcLength ≤ 3 := by
  rcases circuit.arcLength_le_twice_card_edges_or_exists_code_collision with
    hbound | hcollision
  · exact Or.inl hbound
  · exact Or.inr
      (hminimal.arcLength_le_three_of_code_collision hcollision)

end ClosureRecoveryFaceCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
