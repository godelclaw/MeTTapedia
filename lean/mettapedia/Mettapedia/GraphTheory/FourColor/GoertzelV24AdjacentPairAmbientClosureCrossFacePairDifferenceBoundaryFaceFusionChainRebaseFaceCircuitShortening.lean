import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitComplementMonoid

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

/-- Returned cross and retained paths together with the zero complement
profile force literal equality of complete exact-cut states. -/
theorem CrossCentralExactFaceCutState.eq_of_cross_eq_of_trails_eq_of_labelComplementProfile_eq_zero
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    (source target : CrossCentralExactFaceCutState graphData data)
    (hcross : source.1 = target.1)
    (hprefixTrail : source.2.prefixTrail = target.2.prefixTrail)
    (hsuffixTrail : source.2.suffixTrail = target.2.suffixTrail)
    (hprofile :
      CrossCentralExactFaceCutPair.labelComplementProfile minimal
        source.2 target.2 hprefixTrail hsuffixTrail = 0) :
    source = target := by
  rcases source with ⟨sourceCross, sourcePair⟩
  rcases target with ⟨targetCross, targetPair⟩
  dsimp at hcross hprefixTrail hsuffixTrail hprofile ⊢
  subst targetCross
  have hspec := CrossCentralExactFaceCutPair.labelComplementProfile_spec
    minimal sourcePair targetPair hprefixTrail hsuffixTrail
  have hprefixLabels : sourcePair.prefixLabels = targetPair.prefixLabels := by
    funext face
    have hvalue := hspec.1 face
    rw [hprofile] at hvalue
    simpa using hvalue.symm
  have hsuffixLabels : sourcePair.suffixLabels = targetPair.suffixLabels := by
    funext face
    have hvalue := hspec.2 face
    rw [hprofile] at hvalue
    simpa using hvalue.symm
  have hpairs : sourcePair = targetPair :=
    CrossCentralExactFaceCutPair.ext_data sourcePair targetPair
      hprefixTrail hsuffixTrail hprefixLabels hsuffixLabels
  subst targetPair
  rfl

namespace CrossCentralExactFaceCertifiedRebaseCircuit

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

/-- The number of directed certified arcs in a rebase circuit. -/
def arcLength
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) : Nat :=
  (circuit.first :: circuit.rest).length

@[simp] theorem arcLength_eq_rest_length_add_one
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) :
    circuit.arcLength = circuit.rest.length + 1 := by
  simp [arcLength, Nat.add_comm]

/-- A rebase circuit is length-minimal when no certified circuit for the
same minimal counterexample and adjacent pair uses fewer arcs. -/
def IsLengthMinimal
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) : Prop :=
  ∀ other : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData,
    circuit.arcLength ≤ other.arcLength

/-- Every nonempty collection of certified rebase circuits has a member of
minimum arc length. -/
theorem exists_lengthMinimal
    (circuits : Nonempty
      (CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal
        baseData)) :
    ∃ circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
        minimal baseData,
      circuit.IsLengthMinimal := by
  classical
  rcases circuits with ⟨seed⟩
  let occurs : Nat → Prop := fun length =>
    ∃ circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
        minimal baseData,
      circuit.arcLength = length
  have hexists : ∃ length, occurs length :=
    ⟨seed.arcLength, seed, rfl⟩
  rcases Nat.find_spec hexists with ⟨circuit, hcircuit⟩
  refine ⟨circuit, ?_⟩
  intro other
  rw [hcircuit]
  exact Nat.find_min' hexists ⟨other, rfl⟩

/-- Every transitive exact-state cycle contains a certified rebase circuit
of globally minimum arc length. -/
theorem exists_lengthMinimal_of_transGen_cycle
    {state : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (cycle : Relation.TransGen
      (CrossCentralExactFaceCertifiedRebaseTransition graphData minimal
        baseData) state state) :
    ∃ circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
        minimal baseData,
      circuit.IsLengthMinimal :=
  exists_lengthMinimal (exists_of_transGen_cycle cycle)

/-- If a displayed middle arc block returns to its initial exact state, it
is itself a certified circuit strictly shorter than the surrounding circuit. -/
theorem exists_strict_subcircuit_of_middleBlock_endpoint_eq
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (left middleFirst right :
      CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
    (before middleRest after : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))
    (hsplit : circuit.first :: circuit.rest =
      before ++
        (left :: ((middleFirst :: middleRest) ++ (right :: after))))
    (hendpoint : middleFirst.source = right.source) :
    ∃ subcircuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
        minimal baseData,
      subcircuit.arcLength < circuit.arcLength ∧
      subcircuit.first :: subcircuit.rest = middleFirst :: middleRest := by
  let middleArcs := middleFirst :: middleRest
  have hfullChain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        (before ++ (left :: (middleArcs ++ (right :: after)))) := by
    rw [← hsplit]
    exact circuit.consecutive
  have htailChain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        (left :: (middleArcs ++ (right :: after))) :=
    (List.isChain_append.mp hfullChain).2.1
  have hleftParts := List.isChain_cons_cons.mp htailChain
  have hmiddleAfterChain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        (middleArcs ++ (right :: after)) := by
    simpa [middleArcs] using hleftParts.2
  have hmiddleParts := List.isChain_append.mp hmiddleAfterChain
  have hmiddleChain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows middleArcs :=
    hmiddleParts.1
  have hmiddleNe : middleArcs ≠ [] := by simp [middleArcs]
  let middleLast := middleArcs.getLast hmiddleNe
  have hlastMem : middleLast ∈ middleArcs.getLast? := by
    rw [List.getLast?_eq_getLast_of_ne_nil hmiddleNe]
    simp [middleLast]
  have hlastFollows :
      CrossCentralExactFaceCertifiedRebaseArc.Follows middleLast right :=
    hmiddleParts.2.2 middleLast hlastMem right (by simp)
  let subcircuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData := {
    first := middleFirst
    rest := middleRest
    consecutive := by simpa [middleArcs] using hmiddleChain
    closing := by
      change middleLast.target = middleFirst.source
      exact hlastFollows.trans hendpoint.symm }
  refine ⟨subcircuit, ?_, rfl⟩
  change middleArcs.length < (circuit.first :: circuit.rest).length
  rw [hsplit]
  simp [middleArcs]
  omega

/-- More generally, any two displayed arc positions with equal source states
cut out the circuit segment beginning at the first position and ending just
before the second. -/
theorem exists_strict_subcircuit_of_split_source_eq
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (first second :
      CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
    (before between after : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))
    (hsplit : circuit.first :: circuit.rest =
      before ++ (first :: (between ++ (second :: after))))
    (hsource : first.source = second.source) :
    ∃ subcircuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
        minimal baseData,
      subcircuit.arcLength < circuit.arcLength ∧
      subcircuit.first :: subcircuit.rest = first :: between := by
  let segment := first :: between
  have hfullChain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        (before ++ (segment ++ (second :: after))) := by
    have hchain := circuit.consecutive
    rw [hsplit] at hchain
    simpa [segment, List.append_assoc] using hchain
  have hsegmentAfterChain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        (segment ++ (second :: after)) :=
    (List.isChain_append.mp hfullChain).2.1
  have hparts := List.isChain_append.mp hsegmentAfterChain
  have hsegmentChain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows segment := hparts.1
  have hsegmentNe : segment ≠ [] := by simp [segment]
  let last := segment.getLast hsegmentNe
  have hlastMem : last ∈ segment.getLast? := by
    rw [List.getLast?_eq_getLast_of_ne_nil hsegmentNe]
    simp [last]
  have hlastFollows :
      CrossCentralExactFaceCertifiedRebaseArc.Follows last second :=
    hparts.2.2 last hlastMem second (by simp)
  let subcircuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData := {
    first := first
    rest := between
    consecutive := by simpa [segment] using hsegmentChain
    closing := by
      change last.target = first.source
      exact hlastFollows.trans hsource.symm }
  refine ⟨subcircuit, ?_, rfl⟩
  change segment.length < (circuit.first :: circuit.rest).length
  rw [hsplit]
  simp [segment]
  omega

/-- Hence sources at two distinct displayed positions of a length-minimal
circuit cannot agree. -/
theorem IsLengthMinimal.source_ne_of_split
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (hminimal : circuit.IsLengthMinimal)
    (first second :
      CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
    (before between after : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))
    (hsplit : circuit.first :: circuit.rest =
      before ++ (first :: (between ++ (second :: after)))) :
    first.source ≠ second.source := by
  intro hsource
  rcases circuit.exists_strict_subcircuit_of_split_source_eq first second
      before between after hsplit hsource with
    ⟨subcircuit, hshorter, _⟩
  exact (Nat.not_lt_of_ge (hminimal subcircuit)) hshorter

/-- A zero complement profile in the rigid middle-block branch creates a
strict certified subcircuit. -/
theorem exists_strict_subcircuit_of_middleBlockComplementProfile_of_profile_eq_zero
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (left middleFirst right :
      CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
    (before middleRest after : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))
    (hsplit : circuit.first :: circuit.rest =
      before ++
        (left :: ((middleFirst :: middleRest) ++ (right :: after))))
    (hnormal : MiddleBlockComplementProfile middleFirst right middleRest)
    (hzero : CrossCentralExactFaceCutPair.labelComplementProfile minimal
      middleFirst.source.2 right.source.2 hnormal.2.2.1
        hnormal.2.2.2.1 = 0) :
    ∃ subcircuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
        minimal baseData,
      subcircuit.arcLength < circuit.arcLength ∧
      subcircuit.first :: subcircuit.rest = middleFirst :: middleRest := by
  have hendpoint :=
    CrossCentralExactFaceCutState.eq_of_cross_eq_of_trails_eq_of_labelComplementProfile_eq_zero
      minimal middleFirst.source right.source hnormal.1 hnormal.2.2.1
        hnormal.2.2.2.1 hzero
  exact circuit.exists_strict_subcircuit_of_middleBlock_endpoint_eq left
    middleFirst right before middleRest after hsplit hendpoint

/-- Therefore a length-minimal rebase circuit assigns a nonzero complement
profile to every rigid middle block. -/
theorem IsLengthMinimal.labelComplementProfile_ne_zero_of_middleBlockComplementProfile
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (hminimal : circuit.IsLengthMinimal)
    (left middleFirst right :
      CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
    (before middleRest after : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))
    (hsplit : circuit.first :: circuit.rest =
      before ++
        (left :: ((middleFirst :: middleRest) ++ (right :: after))))
    (hnormal : MiddleBlockComplementProfile middleFirst right middleRest) :
    CrossCentralExactFaceCutPair.labelComplementProfile minimal
      middleFirst.source.2 right.source.2 hnormal.2.2.1
        hnormal.2.2.2.1 ≠ 0 := by
  intro hzero
  rcases circuit.exists_strict_subcircuit_of_middleBlockComplementProfile_of_profile_eq_zero
      left middleFirst right before middleRest after hsplit hnormal hzero with
    ⟨subcircuit, hshorter, _⟩
  exact (Nat.not_lt_of_ge (hminimal subcircuit)) hshorter

/-- The rigid middle-block normal form sharpened by exclusion of its neutral
transfer. -/
def MiddleBlockNonzeroComplementProfile
    (middleFirst right :
      CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
    (middleRest : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)) :
    Prop :=
  ∃ hnormal : MiddleBlockComplementProfile middleFirst right middleRest,
    CrossCentralExactFaceCutPair.labelComplementProfile minimal
      middleFirst.source.2 right.source.2 hnormal.2.2.1
        hnormal.2.2.2.1 ≠ 0

/-- On a length-minimal rebase circuit, every two-face excursion therefore
has a nonzero complement transfer or a localized outside recovery. -/
theorem IsLengthMinimal.middleBlock_nonzeroComplementProfile_or_outside_prefixRecovery_or_suffixRecovery
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (hminimal : circuit.IsLengthMinimal)
    (firstFace secondFace : OrbitFace graphData.toRotationSystem)
    (hfaces : firstFace ≠ secondFace)
    (left middleFirst right :
      CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
    (before middleRest after : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))
    (hsplit : circuit.first :: circuit.rest =
      before ++
        (left :: ((middleFirst :: middleRest) ++ (right :: after))))
    (hleftFace : left.selectedFace = firstFace)
    (hmiddleFaces : ∀ arc ∈ middleFirst :: middleRest,
      arc.selectedFace = secondFace)
    (hrightFace : right.selectedFace = firstFace) :
    MiddleBlockNonzeroComplementProfile middleFirst right middleRest ∨
      OutsidePrefixClosureRecovery secondFace middleFirst.source
        right.source (right :: (after ++ before ++ [left])) ∨
      OutsideSuffixClosureRecovery secondFace middleFirst.source
        right.source (right :: (after ++ before ++ [left])) := by
  rcases circuit.middleBlock_complementProfile_or_outside_prefixRecovery_or_suffixRecovery
      firstFace secondFace hfaces left middleFirst right before middleRest
        after hsplit hleftFace hmiddleFaces hrightFace with
    hnormal | hprefix | hsuffix
  · left
    exact ⟨hnormal,
      hminimal.labelComplementProfile_ne_zero_of_middleBlockComplementProfile
        left middleFirst right before middleRest after hsplit hnormal⟩
  · exact Or.inr (Or.inl hprefix)
  · exact Or.inr (Or.inr hsuffix)

/-- A nonzero complement transfer is one of the three nonidentity elements
of the binary product. -/
theorem nonzero_labelComplementProfile_cases
    (profile : F2 × F2) (hnonzero : profile ≠ 0) :
    profile = (1, 0) ∨ profile = (0, 1) ∨ profile = (1, 1) := by
  rcases profile with ⟨firstShift, secondShift⟩
  fin_cases firstShift <;> fin_cases secondShift
  · exact False.elim (hnonzero rfl)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl
  · exact Or.inr (Or.inr rfl)

end CrossCentralExactFaceCertifiedRebaseCircuit

/-- Exact finite-state pumping sharpened by choosing a globally shortest
certified circuit in the nonterminal branch. -/
theorem CrossCentralExactFaceCutState.exists_reachable_certifiedStopping_or_lengthMinimalRebaseCircuit
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G)
    (start : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)) :
    (∃ finish,
        Relation.ReflTransGen
            (CrossCentralExactFaceCertifiedRebaseTransition graphData
              minimal baseData) start finish ∧
          finish.CertifiedStoppingOutcome graphData minimal baseData) ∨
      ∃ cycleState,
        Relation.ReflTransGen
            (CrossCentralExactFaceCertifiedRebaseTransition graphData
              minimal baseData) start cycleState ∧
          ∃ circuit : CrossCentralExactFaceCertifiedRebaseCircuit
              graphData minimal baseData,
            circuit.IsLengthMinimal := by
  rcases
      CrossCentralExactFaceCutState.exists_reachable_certifiedStopping_or_rebaseCycle
        graphData minimal baseData start with hstop | hcycle
  · exact Or.inl hstop
  · rcases hcycle with ⟨cycleState, hreachable, hclosed⟩
    exact Or.inr ⟨cycleState, hreachable,
      CrossCentralExactFaceCertifiedRebaseCircuit.exists_lengthMinimal_of_transGen_cycle
        hclosed⟩

/-- Among five exact-cut states sharing one retained cross and the same two
retained paths, two complete states are equal. -/
theorem CrossCentralExactFaceCutState.exists_eq_of_five_same_cross_and_trails
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    (states : Fin 5 → CrossCentralExactFaceCutState graphData data)
    (hcross : ∀ index, (states 0).1 = (states index).1)
    (hprefixTrail : ∀ index,
      (states 0).2.prefixTrail = (states index).2.prefixTrail)
    (hsuffixTrail : ∀ index,
      (states 0).2.suffixTrail = (states index).2.suffixTrail) :
    ∃ first second, first ≠ second ∧ states first = states second := by
  let profiles : Fin 5 → F2 × F2 := fun index =>
    CrossCentralExactFaceCutPair.labelComplementProfile minimal
      (states 0).2 (states index).2 (hprefixTrail index)
        (hsuffixTrail index)
  rcases
      CrossCentralExactFaceCutPair.exists_repeated_labelComplementProfile_of_five
        profiles with
    ⟨first, second, hne, hprofiles⟩
  refine ⟨first, second, hne, ?_⟩
  have hfirstSpec :=
    CrossCentralExactFaceCutPair.labelComplementProfile_spec minimal
      (states 0).2 (states first).2 (hprefixTrail first)
        (hsuffixTrail first)
  have hsecondSpec :=
    CrossCentralExactFaceCutPair.labelComplementProfile_spec minimal
      (states 0).2 (states second).2 (hprefixTrail second)
        (hsuffixTrail second)
  have hprefixLabels :
      (states first).2.prefixLabels =
        (states second).2.prefixLabels := by
    funext face
    calc
      (states first).2.prefixLabels face =
          (states 0).2.prefixLabels face + (profiles first).1 :=
        hfirstSpec.1 face
      _ = (states 0).2.prefixLabels face + (profiles second).1 := by
        rw [hprofiles]
      _ = (states second).2.prefixLabels face :=
        (hsecondSpec.1 face).symm
  have hsuffixLabels :
      (states first).2.suffixLabels =
        (states second).2.suffixLabels := by
    funext face
    calc
      (states first).2.suffixLabels face =
          (states 0).2.suffixLabels face + (profiles first).2 :=
        hfirstSpec.2 face
      _ = (states 0).2.suffixLabels face + (profiles second).2 := by
        rw [hprofiles]
      _ = (states second).2.suffixLabels face :=
        (hsecondSpec.2 face).symm
  have hprefixFirstSecond :
      (states first).2.prefixTrail =
        (states second).2.prefixTrail :=
    (hprefixTrail first).symm.trans (hprefixTrail second)
  have hsuffixFirstSecond :
      (states first).2.suffixTrail =
        (states second).2.suffixTrail :=
    (hsuffixTrail first).symm.trans (hsuffixTrail second)
  have hprofileZero :
      CrossCentralExactFaceCutPair.labelComplementProfile minimal
        (states first).2 (states second).2 hprefixFirstSecond
          hsuffixFirstSecond = 0 := by
    apply CrossCentralExactFaceCutPair.labelComplementProfile_eq_of_spec
      minimal (states first).2 (states second).2 hprefixFirstSecond
        hsuffixFirstSecond 0
    constructor
    · intro face
      simpa using (congrFun hprefixLabels face).symm
    · intro face
      simpa using (congrFun hsuffixLabels face).symm
  apply
    CrossCentralExactFaceCutState.eq_of_cross_eq_of_trails_eq_of_labelComplementProfile_eq_zero
      minimal (states first) (states second)
        ((hcross first).symm.trans (hcross second)) hprefixFirstSecond
          hsuffixFirstSecond hprofileZero

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
