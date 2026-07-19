import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarColorSymmetry

/-! Fixed overlap and Kirchhoff-terminal coordinates for an intrinsic
source-target collar. -/

namespace Mettapedia.GraphTheory.FourColor

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

namespace IntrinsicShortTargetEscapeCollar

/-- The side of an adjacent-pair boundary port: ports `0,1` lie on the
first restored vertex and ports `2,3` on the second. -/
def intrinsicCollarPortSide (port : Fin 4) : Bool := port < 2

/-- A graph-independent record of literal coincidences between the four
source ports and the four target ports. -/
abbrev IntrinsicCollarPortOverlapProfile := Finset (Fin 4 × Fin 4)

/-- The finite geometric conditions forced on a singleton-reentry overlap
profile.  It is a partial matching, all target ports lie on one target
side, and two distinct overlaps use opposite source sides. -/
def IntrinsicCollarPortOverlapProfile.Admissible
    (profile : IntrinsicCollarPortOverlapProfile) : Prop :=
  (∀ first second, first ∈ profile → second ∈ profile →
    first.1 = second.1 → first = second) ∧
  (∀ first second, first ∈ profile → second ∈ profile →
    first.2 = second.2 → first = second) ∧
  (∃ side : Bool, ∀ ports ∈ profile,
    intrinsicCollarPortSide ports.2 = side) ∧
  (∀ first second, first ∈ profile → second ∈ profile →
    first ≠ second →
      intrinsicCollarPortSide first.1 ≠
        intrinsicCollarPortSide second.1)

instance (profile : IntrinsicCollarPortOverlapProfile) :
    Decidable profile.Admissible := by
  unfold IntrinsicCollarPortOverlapProfile.Admissible
  letI sourceFunctional : Decidable
      (∀ first second : Fin 4 × Fin 4,
        first ∈ profile → second ∈ profile →
          first.1 = second.1 → first = second) :=
    Fintype.decidableForallFintype
  letI targetFunctional : Decidable
      (∀ first second : Fin 4 × Fin 4,
        first ∈ profile → second ∈ profile →
          first.2 = second.2 → first = second) :=
    Fintype.decidableForallFintype
  letI targetSide : Decidable
      (∃ side : Bool, ∀ ports ∈ profile,
        intrinsicCollarPortSide ports.2 = side) :=
    Fintype.decidableExistsFintype
  letI sourceSides : Decidable
      (∀ first second : Fin 4 × Fin 4,
        first ∈ profile → second ∈ profile → first ≠ second →
          intrinsicCollarPortSide first.1 ≠
            intrinsicCollarPortSide second.1) :=
    Fintype.decidableForallFintype
  infer_instance

/-- The fixed type of geometrically admissible singleton-reentry overlap
profiles. -/
abbrev AdmissibleIntrinsicCollarPortOverlapProfile :=
  {profile : IntrinsicCollarPortOverlapProfile // profile.Admissible}

/-- The port with a prescribed side and binary index. -/
def intrinsicCollarPortOnSide : Bool → Fin 2 → Fin 4
  | true, index => ⟨index.1, by omega⟩
  | false, index => ⟨index.1 + 2, by omega⟩

/-- The other binary index. -/
def intrinsicCollarOppositeFinTwo (index : Fin 2) : Fin 2 :=
  finTwoEquiv.symm (!(finTwoEquiv index))

/-- The sixteen possible two-overlap geometries: choose a target side,
one source port on each source side, and which target port meets the
first source side. -/
structure IntrinsicCollarDoubleOverlapIndex where
  targetSide : Bool
  sourceTrueIndex : Fin 2
  sourceFalseIndex : Fin 2
  targetTrueIndex : Fin 2
  deriving DecidableEq, Fintype

/-- The two-pair profile encoded by a double-overlap index. -/
def intrinsicCollarDoubleOverlapProfile
    (index : IntrinsicCollarDoubleOverlapIndex) :
    IntrinsicCollarPortOverlapProfile :=
  {(intrinsicCollarPortOnSide true index.sourceTrueIndex,
      intrinsicCollarPortOnSide index.targetSide index.targetTrueIndex),
    (intrinsicCollarPortOnSide false index.sourceFalseIndex,
      intrinsicCollarPortOnSide index.targetSide
        (intrinsicCollarOppositeFinTwo index.targetTrueIndex))}

@[simp]
theorem empty_intrinsicCollarPortOverlapProfile_admissible :
    (∅ : IntrinsicCollarPortOverlapProfile).Admissible := by
  simp [IntrinsicCollarPortOverlapProfile.Admissible]

@[simp]
theorem singleton_intrinsicCollarPortOverlapProfile_admissible
    (ports : Fin 4 × Fin 4) :
    ({ports} : IntrinsicCollarPortOverlapProfile).Admissible := by
  simp [IntrinsicCollarPortOverlapProfile.Admissible]

/-- Every generated double-overlap profile is admissible. -/
theorem intrinsicCollarDoubleOverlapProfile_admissible
    (index : IntrinsicCollarDoubleOverlapIndex) :
    (intrinsicCollarDoubleOverlapProfile index).Admissible := by
  decide +revert

/-- Every admissible profile has at most two literal coincidences. -/
theorem AdmissibleIntrinsicCollarPortOverlapProfile.card_le_two
    (profile : AdmissibleIntrinsicCollarPortOverlapProfile) :
    profile.1.card ≤ 2 := by
  classical
  rcases profile.2.2.2.1 with ⟨side, hside⟩
  have hinjective : Set.InjOn Prod.snd
      (profile.1 : Set (Fin 4 × Fin 4)) := by
    intro first hfirst second hsecond htarget
    exact profile.2.2.1 first second hfirst hsecond htarget
  rw [← Finset.card_image_of_injOn hinjective]
  calc
    (profile.1.image Prod.snd).card ≤
        (Finset.univ.filter fun port : Fin 4 =>
          intrinsicCollarPortSide port = side).card := by
      apply Finset.card_le_card
      intro port hport
      rcases Finset.mem_image.mp hport with ⟨ports, hports, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ ports.2, hside ports hports⟩
    _ = 2 := by
      cases side <;> decide

/-- A two-element admissible profile has one of the sixteen explicit
double-overlap forms. -/
theorem admissible_pairProfile_exists_doubleOverlapIndex
    (first second : Fin 4 × Fin 4) (hfirstSecond : first ≠ second)
    (hadmissible :
      ({first, second} : IntrinsicCollarPortOverlapProfile).Admissible) :
    ∃ index : IntrinsicCollarDoubleOverlapIndex,
      {first, second} = intrinsicCollarDoubleOverlapProfile index := by
  decide +revert

/-- The explicit complete list: the empty profile, all sixteen singleton
profiles, and the sixteen generated double profiles. -/
def explicitAdmissibleIntrinsicCollarPortOverlapProfiles :
    Finset IntrinsicCollarPortOverlapProfile :=
  insert ∅
    ((Finset.univ.image fun ports : Fin 4 × Fin 4 => {ports}) ∪
      (Finset.univ.image intrinsicCollarDoubleOverlapProfile))

/-- The explicit thirty-three-profile list is extensionally exactly the
admissibility predicate. -/
theorem mem_explicitAdmissibleIntrinsicCollarPortOverlapProfiles_iff
    (profile : IntrinsicCollarPortOverlapProfile) :
    profile ∈ explicitAdmissibleIntrinsicCollarPortOverlapProfiles ↔
      profile.Admissible := by
  classical
  constructor
  · rw [explicitAdmissibleIntrinsicCollarPortOverlapProfiles,
      Finset.mem_insert, Finset.mem_union]
    rintro (rfl | hprofile)
    · exact empty_intrinsicCollarPortOverlapProfile_admissible
    · rcases hprofile with hsingleton | hdouble
      · rcases Finset.mem_image.mp hsingleton with
          ⟨ports, _hports, rfl⟩
        exact singleton_intrinsicCollarPortOverlapProfile_admissible ports
      · rcases Finset.mem_image.mp hdouble with
          ⟨index, _hindex, rfl⟩
        exact intrinsicCollarDoubleOverlapProfile_admissible index
  · intro hadmissible
    have hle :=
      AdmissibleIntrinsicCollarPortOverlapProfile.card_le_two
        ⟨profile, hadmissible⟩
    change profile.card ≤ 2 at hle
    have hcases : profile.card = 0 ∨
        profile.card = 1 ∨ profile.card = 2 := by
      omega
    rw [explicitAdmissibleIntrinsicCollarPortOverlapProfiles,
      Finset.mem_insert, Finset.mem_union]
    rcases hcases with hzero | hone | htwo
    · exact Or.inl (Finset.card_eq_zero.mp hzero)
    · rcases Finset.card_eq_one.mp hone with ⟨ports, hprofile⟩
      exact Or.inr (Or.inl (Finset.mem_image.mpr
        ⟨ports, Finset.mem_univ ports, hprofile.symm⟩))
    · rcases Finset.card_eq_two.mp htwo with
        ⟨first, second, hfirstSecond, hprofile⟩
      have hpairAdmissible :
          ({first, second} : IntrinsicCollarPortOverlapProfile).Admissible := by
        simpa [← hprofile] using hadmissible
      rcases admissible_pairProfile_exists_doubleOverlapIndex
          first second hfirstSecond hpairAdmissible with ⟨index, hindex⟩
      exact Or.inr (Or.inr (Finset.mem_image.mpr
        ⟨index, Finset.mem_univ index,
          hindex.symm.trans hprofile.symm⟩))

/-- The explicit powerset enumeration of all sixteen possible port pairs. -/
@[reducible] def intrinsicCollarPortOverlapProfileFintype :
    Fintype IntrinsicCollarPortOverlapProfile :=
  Finset.fintype

/-- The computable subtype enumeration of admissible overlap profiles. -/
@[reducible] def admissibleIntrinsicCollarPortOverlapProfileFintype :
    Fintype AdmissibleIntrinsicCollarPortOverlapProfile :=
  Fintype.ofFinset explicitAdmissibleIntrinsicCollarPortOverlapProfiles
    mem_explicitAdmissibleIntrinsicCollarPortOverlapProfiles_iff

instance (priority := 2000) :
    Fintype AdmissibleIntrinsicCollarPortOverlapProfile :=
  admissibleIntrinsicCollarPortOverlapProfileFintype

/-- There are exactly thirty-three admissible source-target port-overlap
profiles. -/
theorem card_admissibleIntrinsicCollarPortOverlapProfile :
    @Fintype.card AdmissibleIntrinsicCollarPortOverlapProfile
      admissibleIntrinsicCollarPortOverlapProfileFintype = 33 := by
  decide

/-- The literal overlap profile of an actual intrinsic-short collar. -/
noncomputable def intrinsicCollarPortOverlapProfile
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {rebaseCircuit :
      CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    IntrinsicCollarPortOverlapProfile :=
  Finset.univ.filter fun ports =>
    collar.PortOverlap ports.1 ports.2

@[simp]
theorem mem_intrinsicCollarPortOverlapProfile_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {rebaseCircuit :
      CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (ports : Fin 4 × Fin 4) :
    ports ∈ collar.intrinsicCollarPortOverlapProfile ↔
      collar.PortOverlap ports.1 ports.2 := by
  simp [intrinsicCollarPortOverlapProfile]

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}
  {rebaseCircuit :
    CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- Every actual singleton-reentry collar produces one of the thirty-three
admissible overlap profiles. -/
theorem intrinsicCollarPortOverlapProfile_admissible
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    collar.intrinsicCollarPortOverlapProfile.Admissible := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨firstSource, firstTarget⟩ ⟨secondSource, secondTarget⟩
      hfirst hsecond hsource
    rw [collar.mem_intrinsicCollarPortOverlapProfile_iff] at hfirst hsecond
    dsimp only at hsource
    subst secondSource
    exact Prod.ext rfl
      (collar.portOverlap_target_unique hfirst hsecond)
  · rintro ⟨firstSource, firstTarget⟩ ⟨secondSource, secondTarget⟩
      hfirst hsecond htarget
    rw [collar.mem_intrinsicCollarPortOverlapProfile_iff] at hfirst hsecond
    dsimp only at htarget
    subst secondTarget
    exact Prod.ext
      (collar.portOverlap_source_unique hfirst hsecond) rfl
  · rcases collar.portOverlap_targetPort_pair with
      ⟨_singleton, hports⟩ | ⟨_singleton, hports⟩
    · refine ⟨false, ?_⟩
      rintro ⟨sourcePort, targetPort⟩ hprofile
      rw [collar.mem_intrinsicCollarPortOverlapProfile_iff] at hprofile
      rcases hports hprofile with rfl | rfl <;>
        rfl
    · refine ⟨true, ?_⟩
      rintro ⟨sourcePort, targetPort⟩ hprofile
      rw [collar.mem_intrinsicCollarPortOverlapProfile_iff] at hprofile
      rcases hports hprofile with rfl | rfl <;>
        rfl
  · rintro ⟨firstSource, firstTarget⟩
      ⟨secondSource, secondTarget⟩ hfirst hsecond hne
    rw [collar.mem_intrinsicCollarPortOverlapProfile_iff] at hfirst hsecond
    let firstOverlap : collar.PortOverlapPair :=
      ⟨(firstSource, firstTarget), hfirst⟩
    let secondOverlap : collar.PortOverlapPair :=
      ⟨(secondSource, secondTarget), hsecond⟩
    have hoverlapsNe : firstOverlap ≠ secondOverlap := by
      intro heq
      apply hne
      exact congrArg Subtype.val heq
    have hbases :=
      collar.sourceBoundaryDeletedVertex_ne_of_distinct_portOverlaps
        firstOverlap secondOverlap hoverlapsNe
    change intrinsicCollarPortSide firstSource ≠
      intrinsicCollarPortSide secondSource
    fin_cases firstSource <;> fin_cases secondSource <;>
      simp [intrinsicCollarPortSide, firstOverlap, secondOverlap,
        boundaryDeletedVertex] at hbases ⊢

/-- The actual geometry as an element of the fixed thirty-three-profile
type. -/
noncomputable def admissibleIntrinsicCollarPortOverlapProfile
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    AdmissibleIntrinsicCollarPortOverlapProfile :=
  ⟨collar.intrinsicCollarPortOverlapProfile,
    collar.intrinsicCollarPortOverlapProfile_admissible⟩

/-- The eight fixed source and target port occurrences before literal
overlaps are identified. -/
abbrev IntrinsicCollarTerminalCoordinate := Sum (Fin 4) (Fin 4)

/-- A color word on the eight fixed port occurrences. -/
abbrev IntrinsicCollarTerminalBoundaryWord :=
  IntrinsicCollarTerminalCoordinate → Color

/-- The Kirchhoff boundary word computed from a ten-symbol correction word
and a literal port-overlap profile.  At a port it sums its own collar edge
with every boundary edge from the other presentation meeting it. -/
def intrinsicCollarTerminalBoundaryWord
    (profile : IntrinsicCollarPortOverlapProfile)
    (word : IntrinsicCollarCorrectionWord) :
    IntrinsicCollarTerminalBoundaryWord
  | Sum.inl sourcePort =>
      word (Sum.inl (some sourcePort)) +
        ∑ targetPort : Fin 4,
          if (sourcePort, targetPort) ∈ profile then
            word (Sum.inr (some targetPort)) else 0
  | Sum.inr targetPort =>
      word (Sum.inr (some targetPort)) +
        ∑ sourcePort : Fin 4,
          if (sourcePort, targetPort) ∈ profile then
            word (Sum.inl (some sourcePort)) else 0

/-- A color-name symmetry commutes with a finite color sum. -/
theorem colorNameSymmetry_smul_finset_sum
    {Index : Type*} [DecidableEq Index]
    (symmetry : ColorNameSymmetry) (indices : Finset Index)
    (word : Index → Color) :
    symmetry • (∑ index ∈ indices, word index) =
      ∑ index ∈ indices, symmetry • word index := by
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices hindex ih =>
      simp [hindex, colorNameSymmetry_smul_add, ih]

/-- The fixed terminal formula is equivariant under simultaneous
renaming of the three nonzero colors. -/
theorem smul_intrinsicCollarTerminalBoundaryWord
    (symmetry : ColorNameSymmetry)
    (profile : IntrinsicCollarPortOverlapProfile)
    (word : IntrinsicCollarCorrectionWord) :
    symmetry • intrinsicCollarTerminalBoundaryWord profile word =
      intrinsicCollarTerminalBoundaryWord profile (symmetry • word) := by
  funext coordinate
  rcases coordinate with sourcePort | targetPort
  · simp only [ColorNameSymmetry.smul_word_apply,
      intrinsicCollarTerminalBoundaryWord]
    rw [colorNameSymmetry_smul_add,
      colorNameSymmetry_smul_finset_sum]
    apply congrArg₂ (· + ·) rfl
    apply Finset.sum_congr rfl
    intro port _
    by_cases hoverlap : (sourcePort, port) ∈ profile <;>
      simp [hoverlap]
  · simp only [ColorNameSymmetry.smul_word_apply,
      intrinsicCollarTerminalBoundaryWord]
    rw [colorNameSymmetry_smul_add,
      colorNameSymmetry_smul_finset_sum]
    apply congrArg₂ (· + ·) rfl
    apply Finset.sum_congr rfl
    intro port _
    by_cases hoverlap : (port, targetPort) ∈ profile <;>
      simp [hoverlap]

/-- Target ports not already represented by a coincident source port. -/
def intrinsicCollarUnmatchedTargetPorts
    (profile : IntrinsicCollarPortOverlapProfile) : Finset (Fin 4) :=
  Finset.univ.filter fun targetPort =>
    ∀ sourcePort : Fin 4, (sourcePort, targetPort) ∉ profile

/-- Target ports represented by a literal source-target coincidence. -/
def intrinsicCollarMatchedTargetPorts
    (profile : IntrinsicCollarPortOverlapProfile) : Finset (Fin 4) :=
  profile.image Prod.snd

/-- In an admissible profile, summing target symbols over all source-target
coincidences is the same as summing once over the matched target ports. -/
theorem sum_overlapTargetSymbols_eq_sum_matchedTargetPorts
    (profile : AdmissibleIntrinsicCollarPortOverlapProfile)
    (targetWord : Fin 4 → Color) :
    (∑ sourcePort : Fin 4, ∑ targetPort : Fin 4,
        if (sourcePort, targetPort) ∈ profile.1 then
          targetWord targetPort else 0) =
      ∑ targetPort ∈ intrinsicCollarMatchedTargetPorts profile.1,
        targetWord targetPort := by
  classical
  have hinjective : Set.InjOn Prod.snd
      (profile.1 : Set (Fin 4 × Fin 4)) := by
    intro first hfirst second hsecond htarget
    exact profile.2.2.1 first second hfirst hsecond htarget
  calc
    (∑ sourcePort : Fin 4, ∑ targetPort : Fin 4,
        if (sourcePort, targetPort) ∈ profile.1 then
          targetWord targetPort else 0) =
        ∑ ports ∈ Finset.univ ×ˢ Finset.univ,
          if ports ∈ profile.1 then targetWord ports.2 else 0 := by
      symm
      simpa using Finset.sum_product'
        (Finset.univ : Finset (Fin 4)) (Finset.univ : Finset (Fin 4))
        (fun sourcePort targetPort =>
          if (sourcePort, targetPort) ∈ profile.1 then
            targetWord targetPort else 0)
    _ = ∑ ports ∈ profile.1, targetWord ports.2 := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext ports
        simp
      · intro ports _
        rfl
    _ = ∑ targetPort ∈ intrinsicCollarMatchedTargetPorts profile.1,
          targetWord targetPort := by
      exact (Finset.sum_image hinjective).symm

/-- Matched and unmatched target ports partition the four target
occurrences. -/
theorem sum_matchedTargetPorts_add_sum_unmatchedTargetPorts
    (profile : IntrinsicCollarPortOverlapProfile)
    (targetWord : Fin 4 → Color) :
    (∑ targetPort ∈ intrinsicCollarMatchedTargetPorts profile,
        targetWord targetPort) +
      ∑ targetPort ∈ intrinsicCollarUnmatchedTargetPorts profile,
        targetWord targetPort =
      ∑ targetPort : Fin 4, targetWord targetPort := by
  classical
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin 4))
    (fun targetPort =>
      targetPort ∈ intrinsicCollarMatchedTargetPorts profile)
    targetWord
  have hmatchedFilter :
      Finset.univ.filter (fun targetPort : Fin 4 =>
        targetPort ∈ intrinsicCollarMatchedTargetPorts profile) =
        intrinsicCollarMatchedTargetPorts profile := by
    ext targetPort
    simp
  have hunmatchedFilter :
      Finset.univ.filter (fun targetPort : Fin 4 =>
        targetPort ∉ intrinsicCollarMatchedTargetPorts profile) =
        intrinsicCollarUnmatchedTargetPorts profile := by
    ext targetPort
    simp [intrinsicCollarMatchedTargetPorts,
      intrinsicCollarUnmatchedTargetPorts]
  simpa only [hmatchedFilter, hunmatchedFilter] using hpartition

/-- Deduplicated parity for an eight-occurrence terminal word: keep every
source occurrence and only the target occurrences not identified with a
source occurrence. -/
def IntrinsicCollarTerminalBoundaryWord.DeduplicatedBalanced
    (profile : IntrinsicCollarPortOverlapProfile)
    (boundary : IntrinsicCollarTerminalBoundaryWord) : Prop :=
  (∑ sourcePort : Fin 4, boundary (Sum.inl sourcePort)) +
      ∑ targetPort ∈ intrinsicCollarUnmatchedTargetPorts profile,
        boundary (Sum.inr targetPort) = 0

/-- A correction word and geometry carry an admissible terminal signature
when their computed boundary is balanced and genuinely nonzero. -/
def IntrinsicCollarCorrectionWord.HasAdmissibleTerminalSignature
    (profile : AdmissibleIntrinsicCollarPortOverlapProfile)
    (word : IntrinsicCollarCorrectionWord) : Prop :=
  (intrinsicCollarTerminalBoundaryWord profile.1 word).DeduplicatedBalanced
      profile.1 ∧
    intrinsicCollarTerminalBoundaryWord profile.1 word ≠ 0

instance (profile : AdmissibleIntrinsicCollarPortOverlapProfile)
    (word : IntrinsicCollarCorrectionWord) :
    Decidable (word.HasAdmissibleTerminalSignature profile) := by
  unfold IntrinsicCollarCorrectionWord.HasAdmissibleTerminalSignature
    IntrinsicCollarTerminalBoundaryWord.DeduplicatedBalanced
  infer_instance

/-- If the source and target four-port halves each have zero total, the
fixed terminal formula has zero total after literal overlaps are counted
once. -/
theorem intrinsicCollarTerminalBoundaryWord_deduplicatedBalanced_of_halfSums
    (profile : AdmissibleIntrinsicCollarPortOverlapProfile)
    (word : IntrinsicCollarCorrectionWord)
    (hsource :
      (∑ sourcePort : Fin 4, word (Sum.inl (some sourcePort))) = 0)
    (htarget :
      (∑ targetPort : Fin 4, word (Sum.inr (some targetPort))) = 0) :
    (intrinsicCollarTerminalBoundaryWord profile.1 word).DeduplicatedBalanced
      profile.1 := by
  classical
  have hsourceBoundary :
      (∑ sourcePort : Fin 4,
          intrinsicCollarTerminalBoundaryWord profile.1 word
            (Sum.inl sourcePort)) =
        (∑ sourcePort : Fin 4,
            word (Sum.inl (some sourcePort))) +
          ∑ targetPort ∈
              intrinsicCollarMatchedTargetPorts profile.1,
            word (Sum.inr (some targetPort)) := by
    simp only [intrinsicCollarTerminalBoundaryWord,
      Finset.sum_add_distrib]
    rw [sum_overlapTargetSymbols_eq_sum_matchedTargetPorts profile]
  have hunmatchedBoundary :
      (∑ targetPort ∈ intrinsicCollarUnmatchedTargetPorts profile.1,
          intrinsicCollarTerminalBoundaryWord profile.1 word
            (Sum.inr targetPort)) =
        ∑ targetPort ∈ intrinsicCollarUnmatchedTargetPorts profile.1,
          word (Sum.inr (some targetPort)) := by
    apply Finset.sum_congr rfl
    intro targetPort hunmatched
    have hnone : ∀ sourcePort : Fin 4,
        (sourcePort, targetPort) ∉ profile.1 := by
      simpa [intrinsicCollarUnmatchedTargetPorts] using hunmatched
    simp [intrinsicCollarTerminalBoundaryWord, hnone]
  unfold IntrinsicCollarTerminalBoundaryWord.DeduplicatedBalanced
  rw [hsourceBoundary, hunmatchedBoundary]
  calc
    ((∑ sourcePort : Fin 4,
          word (Sum.inl (some sourcePort))) +
          ∑ targetPort ∈ intrinsicCollarMatchedTargetPorts profile.1,
            word (Sum.inr (some targetPort))) +
        ∑ targetPort ∈ intrinsicCollarUnmatchedTargetPorts profile.1,
          word (Sum.inr (some targetPort)) =
      (∑ sourcePort : Fin 4,
          word (Sum.inl (some sourcePort))) +
        ((∑ targetPort ∈
              intrinsicCollarMatchedTargetPorts profile.1,
            word (Sum.inr (some targetPort))) +
          ∑ targetPort ∈
              intrinsicCollarUnmatchedTargetPorts profile.1,
            word (Sum.inr (some targetPort))) := by
      abel
    _ = (∑ sourcePort : Fin 4,
          word (Sum.inl (some sourcePort))) +
        ∑ targetPort : Fin 4,
          word (Sum.inr (some targetPort)) := by
      rw [sum_matchedTargetPorts_add_sum_unmatchedTargetPorts]
    _ = 0 := by rw [hsource, htarget, add_zero]

/-- Zero extension reads a word symbol back on the ambient edge named by
its fixed collar coordinate. -/
@[simp]
theorem intrinsicCollarCorrectionWordExtendZero_apply_coordinate
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (word : IntrinsicCollarCorrectionWord)
    (coordinate : IntrinsicCollarCoordinate) :
    collar.intrinsicCollarCorrectionWordExtendZero word
        (collar.intrinsicCollarCoordinateEdge coordinate) =
      word coordinate := by
  rw [intrinsicCollarCorrectionWordExtendZero,
    collar.intrinsicCollarCorrectionStateExtendZero_apply_mem _ _
      (collar.intrinsicCollarCoordinateEdge_mem coordinate)]
  have hedge :
      (⟨collar.intrinsicCollarCoordinateEdge coordinate,
        collar.intrinsicCollarCoordinateEdge_mem coordinate⟩ :
          collar.intrinsicCollarEdgeFinset) =
        collar.intrinsicCollarCoordinateEquiv coordinate := by
    apply Subtype.ext
    rfl
  rw [hedge]
  rw [← collar.intrinsicCollarStateEquivCorrectionWord_apply
    (collar.intrinsicCollarStateEquivCorrectionWord.symm word) coordinate]
  exact congrFun
    (collar.intrinsicCollarStateEquivCorrectionWord.apply_symm_apply word)
      coordinate

/-- The ambient Kirchhoff sum of a zero-extended correction word is the
sum of precisely those fixed collar coordinates incident to the vertex. -/
theorem vertexKirchhoffSum_correctionWordExtendZero_eq_coordinateSum
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (word : IntrinsicCollarCorrectionWord) (vertex : V) :
    vertexKirchhoffSum G
        (collar.intrinsicCollarCorrectionWordExtendZero word) vertex =
      ∑ coordinate : IntrinsicCollarCoordinate,
        if vertex ∈ (collar.intrinsicCollarCoordinateEdge coordinate).1
        then word coordinate else 0 := by
  classical
  unfold vertexKirchhoffSum incidentEdgeFinset
  calc
    (∑ edge ∈ Finset.univ.filter (fun edge : G.edgeSet => vertex ∈ edge.1),
        collar.intrinsicCollarCorrectionWordExtendZero word edge) =
        ∑ edge ∈ Finset.univ,
          if vertex ∈ edge.1 then
            collar.intrinsicCollarCorrectionWordExtendZero word edge else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ edge ∈ collar.intrinsicCollarEdgeFinset,
          if vertex ∈ edge.1 then
            collar.intrinsicCollarCorrectionWordExtendZero word edge else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro edge _hedge houtside
      by_cases hvertex : vertex ∈ edge.1
      · rw [if_pos hvertex, intrinsicCollarCorrectionWordExtendZero,
          collar.intrinsicCollarCorrectionStateExtendZero_apply_not_mem
            _ edge houtside]
      · simp [hvertex]
    _ = ∑ edge : collar.intrinsicCollarEdgeFinset,
          if vertex ∈ edge.1.1 then
            collar.intrinsicCollarCorrectionWordExtendZero word edge.1 else 0 := by
      exact Finset.sum_subtype collar.intrinsicCollarEdgeFinset
        (fun _ => Iff.rfl)
        (fun edge : G.edgeSet =>
          if vertex ∈ edge.1 then
            collar.intrinsicCollarCorrectionWordExtendZero word edge else 0)
    _ = ∑ coordinate : IntrinsicCollarCoordinate,
          if vertex ∈ (collar.intrinsicCollarCoordinateEdge coordinate).1
          then word coordinate else 0 := by
      calc
        (∑ edge : collar.intrinsicCollarEdgeFinset,
            if vertex ∈ edge.1.1 then
              collar.intrinsicCollarCorrectionWordExtendZero word edge.1
            else 0) =
            ∑ coordinate : IntrinsicCollarCoordinate,
              if vertex ∈
                  (collar.intrinsicCollarCoordinateEquiv coordinate).1.1 then
                collar.intrinsicCollarCorrectionWordExtendZero word
                  (collar.intrinsicCollarCoordinateEquiv coordinate).1
              else 0 :=
          (Equiv.sum_comp collar.intrinsicCollarCoordinateEquiv
            (fun edge : collar.intrinsicCollarEdgeFinset =>
              if vertex ∈ edge.1.1 then
                collar.intrinsicCollarCorrectionWordExtendZero word edge.1
              else 0)).symm
        _ = ∑ coordinate : IntrinsicCollarCoordinate,
              if vertex ∈
                  (collar.intrinsicCollarCoordinateEdge coordinate).1
              then word coordinate else 0 := by
          apply Fintype.sum_congr
          intro coordinate
          change (if vertex ∈
              (collar.intrinsicCollarCoordinateEdge coordinate).1 then
              collar.intrinsicCollarCorrectionWordExtendZero word
                (collar.intrinsicCollarCoordinateEdge coordinate)
            else 0) = _
          rw [collar.intrinsicCollarCorrectionWordExtendZero_apply_coordinate]

/-- A source port is incident to exactly its own source boundary edge among
the five source-collar coordinates. -/
@[simp]
theorem sourcePort_mem_sourceCollarCoordinate_iff
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourcePort : Fin 4) (coordinate : Option (Fin 4)) :
    collar.sourceData.portVertex sourcePort ∈
        (adjacentPairCollarCoordinateEdge collar.sourceData coordinate).1 ↔
      coordinate = some sourcePort := by
  cases coordinate with
  | none =>
      simp [adjacentPairCollarCoordinateEdge, centralEdge, centralEdgeValue,
        collar.sourceData.portNeFirst sourcePort,
        collar.sourceData.portNeSecond sourcePort]
  | some boundaryPort =>
      simp only [adjacentPairCollarCoordinateEdge, boundaryEdge_val,
        boundaryEdgeValue_eq, Sym2.mem_iff]
      constructor
      · intro hmem
        rcases hmem with hdeleted | hport
        · exact False.elim
            ((boundaryDeletedVertex_ne_portVertex collar.sourceData
              boundaryPort sourcePort) hdeleted.symm)
        · exact congrArg some
            (collar.sourceData.portInjective hport.symm)
      · intro hcoordinate
        injection hcoordinate with hport
        subst boundaryPort
        exact Or.inr rfl

/-- Every source port is distinct from a deleted endpoint of the target
presentation. -/
theorem sourcePort_ne_targetBoundaryDeletedVertex
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourcePort targetPort : Fin 4) :
    collar.sourceData.portVertex sourcePort ≠
      boundaryDeletedVertex collar.targetData targetPort := by
  have hretained := collar.sourcePort_mem_targetRetainedVertexSet sourcePort
  fin_cases targetPort
  · simpa [boundaryDeletedVertex] using hretained.1
  · simpa [boundaryDeletedVertex] using hretained.1
  · simpa [boundaryDeletedVertex] using hretained.2
  · simpa [boundaryDeletedVertex] using hretained.2

/-- A source port meets a target-collar coordinate exactly when that
coordinate is the boundary edge of an overlapping target port. -/
@[simp]
theorem sourcePort_mem_targetCollarCoordinate_iff
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourcePort : Fin 4) (coordinate : Option (Fin 4)) :
    collar.sourceData.portVertex sourcePort ∈
        (adjacentPairCollarCoordinateEdge collar.targetData coordinate).1 ↔
      ∃ targetPort, coordinate = some targetPort ∧
        collar.PortOverlap sourcePort targetPort := by
  cases coordinate with
  | none =>
      have hretained := collar.sourcePort_mem_targetRetainedVertexSet sourcePort
      simp [adjacentPairCollarCoordinateEdge, centralEdge, centralEdgeValue,
        hretained.1, hretained.2]
  | some targetPort =>
      simp only [adjacentPairCollarCoordinateEdge, boundaryEdge_val,
        boundaryEdgeValue_eq, Sym2.mem_iff]
      constructor
      · intro hmem
        refine ⟨targetPort, rfl, ?_⟩
        rcases hmem with hdeleted | hport
        · exact False.elim
            (collar.sourcePort_ne_targetBoundaryDeletedVertex
              sourcePort targetPort hdeleted)
        · exact hport
      · rintro ⟨overlapPort, hcoordinate, hoverlap⟩
        injection hcoordinate with hport
        subst overlapPort
        exact Or.inr hoverlap

/-- A target port is incident to exactly its own target boundary edge among
the five target-collar coordinates. -/
@[simp]
theorem targetPort_mem_targetCollarCoordinate_iff
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (targetPort : Fin 4) (coordinate : Option (Fin 4)) :
    collar.targetData.portVertex targetPort ∈
        (adjacentPairCollarCoordinateEdge collar.targetData coordinate).1 ↔
      coordinate = some targetPort := by
  cases coordinate with
  | none =>
      simp [adjacentPairCollarCoordinateEdge, centralEdge, centralEdgeValue,
        collar.targetData.portNeFirst targetPort,
        collar.targetData.portNeSecond targetPort]
  | some boundaryPort =>
      simp only [adjacentPairCollarCoordinateEdge, boundaryEdge_val,
        boundaryEdgeValue_eq, Sym2.mem_iff]
      constructor
      · intro hmem
        rcases hmem with hdeleted | hport
        · exact False.elim
            ((boundaryDeletedVertex_ne_portVertex collar.targetData
              boundaryPort targetPort) hdeleted.symm)
        · exact congrArg some
            (collar.targetData.portInjective hport.symm)
      · intro hcoordinate
        injection hcoordinate with hport
        subst boundaryPort
        exact Or.inr rfl

/-- Every target port is distinct from a deleted endpoint of the source
presentation. -/
theorem targetPort_ne_sourceBoundaryDeletedVertex
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (targetPort sourcePort : Fin 4) :
    collar.targetData.portVertex targetPort ≠
      boundaryDeletedVertex collar.sourceData sourcePort := by
  have hretained := collar.targetPort_mem_sourceRetainedVertexSet targetPort
  fin_cases sourcePort
  · simpa [boundaryDeletedVertex] using hretained.1
  · simpa [boundaryDeletedVertex] using hretained.1
  · simpa [boundaryDeletedVertex] using hretained.2
  · simpa [boundaryDeletedVertex] using hretained.2

/-- A target port meets a source-collar coordinate exactly when that
coordinate is the boundary edge of an overlapping source port. -/
@[simp]
theorem targetPort_mem_sourceCollarCoordinate_iff
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (targetPort : Fin 4) (coordinate : Option (Fin 4)) :
    collar.targetData.portVertex targetPort ∈
        (adjacentPairCollarCoordinateEdge collar.sourceData coordinate).1 ↔
      ∃ sourcePort, coordinate = some sourcePort ∧
        collar.PortOverlap sourcePort targetPort := by
  cases coordinate with
  | none =>
      have hretained := collar.targetPort_mem_sourceRetainedVertexSet targetPort
      simp [adjacentPairCollarCoordinateEdge, centralEdge, centralEdgeValue,
        hretained.1, hretained.2]
  | some sourcePort =>
      simp only [adjacentPairCollarCoordinateEdge, boundaryEdge_val,
        boundaryEdgeValue_eq, Sym2.mem_iff]
      constructor
      · intro hmem
        refine ⟨sourcePort, rfl, ?_⟩
        rcases hmem with hdeleted | hport
        · exact False.elim
            (collar.targetPort_ne_sourceBoundaryDeletedVertex
              targetPort sourcePort hdeleted)
        · exact hport.symm
      · rintro ⟨overlapPort, hcoordinate, hoverlap⟩
        injection hcoordinate with hport
        subst overlapPort
        exact Or.inr hoverlap.symm

/-- The graph-independent terminal formula computes the exact ambient
Kirchhoff boundary at every source port. -/
theorem vertexKirchhoffSum_correctionWordExtendZero_sourcePort
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (word : IntrinsicCollarCorrectionWord) (sourcePort : Fin 4) :
    vertexKirchhoffSum G
        (collar.intrinsicCollarCorrectionWordExtendZero word)
        (collar.sourceData.portVertex sourcePort) =
      intrinsicCollarTerminalBoundaryWord
        collar.intrinsicCollarPortOverlapProfile word
          (Sum.inl sourcePort) := by
  rw [collar.vertexKirchhoffSum_correctionWordExtendZero_eq_coordinateSum]
  simp [intrinsicCollarTerminalBoundaryWord,
    intrinsicCollarCoordinateEdge,
    collar.sourcePort_mem_sourceCollarCoordinate_iff,
    collar.sourcePort_mem_targetCollarCoordinate_iff,
    collar.mem_intrinsicCollarPortOverlapProfile_iff]

/-- The same graph-independent terminal formula computes the exact ambient
Kirchhoff boundary at every target port. -/
theorem vertexKirchhoffSum_correctionWordExtendZero_targetPort
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (word : IntrinsicCollarCorrectionWord) (targetPort : Fin 4) :
    vertexKirchhoffSum G
        (collar.intrinsicCollarCorrectionWordExtendZero word)
        (collar.targetData.portVertex targetPort) =
      intrinsicCollarTerminalBoundaryWord
        collar.intrinsicCollarPortOverlapProfile word
          (Sum.inr targetPort) := by
  rw [collar.vertexKirchhoffSum_correctionWordExtendZero_eq_coordinateSum]
  simp [intrinsicCollarTerminalBoundaryWord,
    intrinsicCollarCoordinateEdge,
    collar.targetPort_mem_sourceCollarCoordinate_iff,
    collar.targetPort_mem_targetCollarCoordinate_iff,
    collar.mem_intrinsicCollarPortOverlapProfile_iff]
  ac_rfl

/-- A source port as an element of the exact common terminal interface. -/
noncomputable def sourcePortCommonTerminal
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourcePort : Fin 4) : collar.commonPortVertexFinset :=
  ⟨collar.sourcePortInCommonCore sourcePort, by
    rw [commonPortVertexFinset]
    exact Finset.mem_union_left _
      (Finset.mem_image.mpr
        ⟨sourcePort, Finset.mem_univ sourcePort, rfl⟩)⟩

/-- A target port as an element of the exact common terminal interface. -/
noncomputable def targetPortCommonTerminal
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (targetPort : Fin 4) : collar.commonPortVertexFinset :=
  ⟨collar.targetPortInCommonCore targetPort, by
    rw [commonPortVertexFinset]
    exact Finset.mem_union_right _
      (Finset.mem_image.mpr
        ⟨targetPort, Finset.mem_univ targetPort, rfl⟩)⟩

/-- For an actual correction word, the fixed source occurrence is exactly
the previously constructed common-core boundary state. -/
theorem intrinsicCollarTerminalBoundaryWord_source_eq_boundaryState
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (sourcePort : Fin 4) :
    intrinsicCollarTerminalBoundaryWord
        collar.intrinsicCollarPortOverlapProfile
        (collar.intrinsicCollarCorrectionWord sourceEscape)
        (Sum.inl sourcePort) =
      (collar.commonDiscrepancyBoundaryState sourceEscape).1
        (collar.sourcePortCommonTerminal sourcePort) := by
  rw [← collar.vertexKirchhoffSum_correctionWordExtendZero_sourcePort]
  exact collar.vertexKirchhoffSum_correctionWordExtendZero_eq_boundaryState
    sourceEscape (collar.sourcePortCommonTerminal sourcePort)

/-- The analogous exact identification at every target occurrence. -/
theorem intrinsicCollarTerminalBoundaryWord_target_eq_boundaryState
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (targetPort : Fin 4) :
    intrinsicCollarTerminalBoundaryWord
        collar.intrinsicCollarPortOverlapProfile
        (collar.intrinsicCollarCorrectionWord sourceEscape)
        (Sum.inr targetPort) =
      (collar.commonDiscrepancyBoundaryState sourceEscape).1
        (collar.targetPortCommonTerminal targetPort) := by
  rw [← collar.vertexKirchhoffSum_correctionWordExtendZero_targetPort]
  exact collar.vertexKirchhoffSum_correctionWordExtendZero_eq_boundaryState
    sourceEscape (collar.targetPortCommonTerminal targetPort)

/-- Canonical representatives of the deduplicated terminal interface:
all four source ports, followed by target ports having no source overlap. -/
abbrev IntrinsicCollarTerminalRepresentative
    (profile : IntrinsicCollarPortOverlapProfile) :=
  Sum (Fin 4) ↑(intrinsicCollarUnmatchedTargetPorts profile)

/-- The canonical fixed representatives are exactly the variable-width
common-core terminal vertices. -/
noncomputable def intrinsicCollarTerminalRepresentativeEquiv
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :
    IntrinsicCollarTerminalRepresentative
        collar.intrinsicCollarPortOverlapProfile ≃
      collar.commonPortVertexFinset :=
  Equiv.ofBijective
    (fun representative =>
      match representative with
      | Sum.inl sourcePort => collar.sourcePortCommonTerminal sourcePort
      | Sum.inr targetPort => collar.targetPortCommonTerminal targetPort.1)
    ⟨by
      intro first second heq
      rcases first with sourcePort | targetPort <;>
        rcases second with secondSourcePort | secondTargetPort
      · exact congrArg Sum.inl
          (collar.sourcePortInCommonCore_injective
            (congrArg Subtype.val heq))
      · exfalso
        have hcommon :
            collar.sourcePortInCommonCore sourcePort =
              collar.targetPortInCommonCore secondTargetPort.1 :=
          congrArg Subtype.val heq
        have hoverlap :=
          (collar.sourcePortInCommonCore_eq_targetPortInCommonCore_iff
            sourcePort secondTargetPort.1).1 hcommon
        have hunmatched : ∀ otherSource : Fin 4,
            (otherSource, secondTargetPort.1) ∉
              collar.intrinsicCollarPortOverlapProfile := by
          simpa [intrinsicCollarUnmatchedTargetPorts] using
            secondTargetPort.2
        exact hunmatched sourcePort
          ((collar.mem_intrinsicCollarPortOverlapProfile_iff _).2 hoverlap)
      · exfalso
        have hcommon :
            collar.sourcePortInCommonCore secondSourcePort =
              collar.targetPortInCommonCore targetPort.1 :=
          (congrArg Subtype.val heq).symm
        have hoverlap :=
          (collar.sourcePortInCommonCore_eq_targetPortInCommonCore_iff
            secondSourcePort targetPort.1).1 hcommon
        have hunmatched : ∀ otherSource : Fin 4,
            (otherSource, targetPort.1) ∉
              collar.intrinsicCollarPortOverlapProfile := by
          simpa [intrinsicCollarUnmatchedTargetPorts] using targetPort.2
        exact hunmatched secondSourcePort
          ((collar.mem_intrinsicCollarPortOverlapProfile_iff _).2 hoverlap)
      · apply congrArg Sum.inr
        apply Subtype.ext
        exact collar.targetPortInCommonCore_injective
          (congrArg Subtype.val heq),
    by
      intro terminal
      have hterminal := terminal.2
      change terminal.1 ∈
        collar.sourcePortVertexFinset ∪ collar.targetPortVertexFinset
          at hterminal
      rw [Finset.mem_union,
        sourcePortVertexFinset, targetPortVertexFinset] at hterminal
      rcases hterminal with hsource | htarget
      · rcases Finset.mem_image.mp hsource with
          ⟨sourcePort, _hsourcePort, hsourceEq⟩
        refine ⟨Sum.inl sourcePort, ?_⟩
        apply Subtype.ext
        exact hsourceEq
      · rcases Finset.mem_image.mp htarget with
          ⟨targetPort, _htargetPort, htargetEq⟩
        by_cases hoverlap : ∃ sourcePort : Fin 4,
            collar.PortOverlap sourcePort targetPort
        · rcases hoverlap with ⟨sourcePort, hoverlap⟩
          refine ⟨Sum.inl sourcePort, ?_⟩
          apply Subtype.ext
          change collar.sourcePortInCommonCore sourcePort = terminal.1
          exact
            ((collar.sourcePortInCommonCore_eq_targetPortInCommonCore_iff
              sourcePort targetPort).2 hoverlap).trans htargetEq
        · have hunmatched : targetPort ∈
              intrinsicCollarUnmatchedTargetPorts
                collar.intrinsicCollarPortOverlapProfile := by
            rw [intrinsicCollarUnmatchedTargetPorts, Finset.mem_filter]
            refine ⟨Finset.mem_univ targetPort, ?_⟩
            intro sourcePort hprofile
            apply hoverlap
            exact ⟨sourcePort,
              (collar.mem_intrinsicCollarPortOverlapProfile_iff _).1
                hprofile⟩
          refine ⟨Sum.inr ⟨targetPort, hunmatched⟩, ?_⟩
          apply Subtype.ext
          exact htargetEq⟩

/-- Forget the no-overlap certificate while retaining the corresponding
fixed port occurrence. -/
def intrinsicCollarTerminalCoordinateOfRepresentative
    {profile : IntrinsicCollarPortOverlapProfile} :
    IntrinsicCollarTerminalRepresentative profile →
      IntrinsicCollarTerminalCoordinate
  | Sum.inl sourcePort => Sum.inl sourcePort
  | Sum.inr targetPort => Sum.inr targetPort.1

/-- On each canonical representative, the fixed terminal word and the
variable common-core boundary state agree exactly. -/
theorem intrinsicCollarTerminalBoundaryWord_representative_eq_boundaryState
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (representative : IntrinsicCollarTerminalRepresentative
      collar.intrinsicCollarPortOverlapProfile) :
    intrinsicCollarTerminalBoundaryWord
        collar.intrinsicCollarPortOverlapProfile
        (collar.intrinsicCollarCorrectionWord sourceEscape)
        (intrinsicCollarTerminalCoordinateOfRepresentative representative) =
      (collar.commonDiscrepancyBoundaryState sourceEscape).1
        (collar.intrinsicCollarTerminalRepresentativeEquiv representative) := by
  rcases representative with sourcePort | targetPort
  · exact collar.intrinsicCollarTerminalBoundaryWord_source_eq_boundaryState
      sourceEscape sourcePort
  · exact collar.intrinsicCollarTerminalBoundaryWord_target_eq_boundaryState
      sourceEscape targetPort.1

/-- The fixed eight-occurrence word of an actual collar is nonzero. -/
theorem intrinsicCollarTerminalBoundaryWord_ne_zero
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    intrinsicCollarTerminalBoundaryWord
        collar.intrinsicCollarPortOverlapProfile
        (collar.intrinsicCollarCorrectionWord sourceEscape) ≠ 0 := by
  intro hzero
  apply collar.commonDiscrepancyBoundaryState_ne_zero sourceEscape
  funext terminal
  rcases collar.intrinsicCollarTerminalRepresentativeEquiv.surjective
      terminal with ⟨representative, rfl⟩
  rw [← collar.intrinsicCollarTerminalBoundaryWord_representative_eq_boundaryState
    sourceEscape representative]
  exact congrFun hzero
    (intrinsicCollarTerminalCoordinateOfRepresentative representative)

/-- The fixed eight-occurrence word satisfies deduplicated Kirchhoff
parity. -/
theorem intrinsicCollarTerminalBoundaryWord_deduplicatedBalanced
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    (intrinsicCollarTerminalBoundaryWord
      collar.intrinsicCollarPortOverlapProfile
      (collar.intrinsicCollarCorrectionWord sourceEscape)).DeduplicatedBalanced
        collar.intrinsicCollarPortOverlapProfile := by
  letI unmatchedTargetPortFintype :
      Fintype ↑(intrinsicCollarUnmatchedTargetPorts
        collar.intrinsicCollarPortOverlapProfile) :=
    Fintype.subtype
      (intrinsicCollarUnmatchedTargetPorts
        collar.intrinsicCollarPortOverlapProfile)
      (fun _ => Iff.rfl)
  let boundary := intrinsicCollarTerminalBoundaryWord
    collar.intrinsicCollarPortOverlapProfile
    (collar.intrinsicCollarCorrectionWord sourceEscape)
  change (∑ sourcePort : Fin 4, boundary (Sum.inl sourcePort)) +
      ∑ targetPort ∈ intrinsicCollarUnmatchedTargetPorts
        collar.intrinsicCollarPortOverlapProfile,
          boundary (Sum.inr targetPort) = 0
  calc
    (∑ sourcePort : Fin 4, boundary (Sum.inl sourcePort)) +
          ∑ targetPort ∈ intrinsicCollarUnmatchedTargetPorts
            collar.intrinsicCollarPortOverlapProfile,
              boundary (Sum.inr targetPort) =
        ∑ representative : IntrinsicCollarTerminalRepresentative
            collar.intrinsicCollarPortOverlapProfile,
          boundary
            (intrinsicCollarTerminalCoordinateOfRepresentative
              representative) := by
      rw [Fintype.sum_sum_type,
        Finset.sum_subtype
          (intrinsicCollarUnmatchedTargetPorts
            collar.intrinsicCollarPortOverlapProfile)
          (fun _ => Iff.rfl)
          (fun targetPort => boundary (Sum.inr targetPort))]
      rfl
    _ = ∑ terminal : collar.commonPortVertexFinset,
          (collar.commonDiscrepancyBoundaryState sourceEscape).1 terminal := by
      rw [← Equiv.sum_comp
        collar.intrinsicCollarTerminalRepresentativeEquiv]
      apply Fintype.sum_congr
      intro representative
      exact
        collar.intrinsicCollarTerminalBoundaryWord_representative_eq_boundaryState
          sourceEscape representative
    _ = 0 := (collar.commonDiscrepancyBoundaryState sourceEscape).2

/-- Every actual locally realizable correction word carries an admissible
fixed terminal signature for its actual overlap geometry. -/
theorem intrinsicCollarCorrectionWord_hasAdmissibleTerminalSignature
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    IntrinsicCollarCorrectionWord.HasAdmissibleTerminalSignature
      collar.admissibleIntrinsicCollarPortOverlapProfile
      (collar.intrinsicCollarCorrectionWord sourceEscape) :=
  ⟨collar.intrinsicCollarTerminalBoundaryWord_deduplicatedBalanced
      sourceEscape,
    collar.intrinsicCollarTerminalBoundaryWord_ne_zero sourceEscape⟩

/-- Each of the thirty-six locally realizable correction halves has zero
total boundary and retains a nonzero boundary symbol on either side of
any prescribed port-side split. -/
theorem locallyRealizableCorrectionHalfWord_boundary_invariants
    (half : IntrinsicCollarCorrectionHalfWord)
    (hhalf : half ∈ locallyRealizableCorrectionHalfWords) :
    (∑ port : Fin 4, half (some port)) = 0 ∧
      ∀ side : Bool, ∃ port : Fin 4,
        intrinsicCollarPortSide port ≠ side ∧ half (some port) ≠ 0 := by
  decide +revert

/-- A locally realizable target half forces the fixed terminal word to be
nonzero: admissible overlaps occupy one target side, while the opposite
side contains a nonzero untouched symbol. -/
theorem intrinsicCollarTerminalBoundaryWord_ne_zero_of_targetHalf_mem
    (profile : AdmissibleIntrinsicCollarPortOverlapProfile)
    (word : IntrinsicCollarCorrectionWord)
    (htarget : targetHalfWordOfCorrectionWord word ∈
      locallyRealizableCorrectionHalfWords) :
    intrinsicCollarTerminalBoundaryWord profile.1 word ≠ 0 := by
  rcases profile.2.2.2.1 with ⟨overlapSide, hoverlapSide⟩
  rcases (locallyRealizableCorrectionHalfWord_boundary_invariants
      (targetHalfWordOfCorrectionWord word) htarget).2 overlapSide with
    ⟨targetPort, hportSide, hportNonzero⟩
  have hnone : ∀ sourcePort : Fin 4,
      (sourcePort, targetPort) ∉ profile.1 := by
    intro sourcePort hoverlap
    exact hportSide (hoverlapSide (sourcePort, targetPort) hoverlap)
  intro hzero
  have hcoordinate := congrFun hzero (Sum.inr targetPort)
  apply hportNonzero
  simpa [targetHalfWordOfCorrectionWord,
    intrinsicCollarTerminalBoundaryWord, hnone] using hcoordinate

/-- Finite-local conclusion: all 1296 locally realizable correction words
have a balanced nonzero terminal signature in every one of the thirty-three
admissible overlap geometries. -/
theorem locallyRealizableCorrectionWord_hasAdmissibleTerminalSignature
    (profile : AdmissibleIntrinsicCollarPortOverlapProfile)
    (word : IntrinsicCollarCorrectionWord)
    (hword : word ∈ locallyRealizableCorrectionWords) :
    word.HasAdmissibleTerminalSignature profile := by
  have hhalves := halfWords_mem_of_correctionWord_mem hword
  have hsource := locallyRealizableCorrectionHalfWord_boundary_invariants
    (sourceHalfWordOfCorrectionWord word) hhalves.1
  have htarget := locallyRealizableCorrectionHalfWord_boundary_invariants
    (targetHalfWordOfCorrectionWord word) hhalves.2
  refine ⟨
    intrinsicCollarTerminalBoundaryWord_deduplicatedBalanced_of_halfSums
      profile word ?_ ?_,
    intrinsicCollarTerminalBoundaryWord_ne_zero_of_targetHalf_mem
      profile word hhalves.2⟩
  · exact hsource.1
  · exact htarget.1

/-- The raw finite terminal alphabet: an admissible overlap geometry and
one locally realizable ten-symbol correction state. -/
abbrev IntrinsicCollarTerminalRawState :=
  AdmissibleIntrinsicCollarPortOverlapProfile ×
    LocallyRealizableCorrectionState

/-- The direct thirty-three by 1296 enumeration, avoiding the much larger
ambient function-space enumeration of the correction-state subtype. -/
@[reducible] noncomputable def intrinsicCollarTerminalRawStateFintype :
    Fintype IntrinsicCollarTerminalRawState :=
  @instFintypeProd AdmissibleIntrinsicCollarPortOverlapProfile
    LocallyRealizableCorrectionState
    admissibleIntrinsicCollarPortOverlapProfileFintype
    (Finset.fintypeCoeSort locallyRealizableCorrectionWords)

noncomputable instance (priority := 2500) :
    Fintype IntrinsicCollarTerminalRawState :=
  intrinsicCollarTerminalRawStateFintype

/-- Every element of the raw terminal alphabet carries the certified
balanced nonzero signature. -/
theorem IntrinsicCollarTerminalRawState.hasAdmissibleTerminalSignature
    (state : IntrinsicCollarTerminalRawState) :
    state.2.1.HasAdmissibleTerminalSignature state.1 :=
  locallyRealizableCorrectionWord_hasAdmissibleTerminalSignature
    state.1 state.2.1 state.2.2

/-- The raw terminal alphabet has exactly `33 * 1296 = 42768` states. -/
theorem card_intrinsicCollarTerminalRawState :
    @Fintype.card IntrinsicCollarTerminalRawState
      intrinsicCollarTerminalRawStateFintype = 42768 := by
  rw [Fintype.card_prod, Fintype.card_coe,
    card_admissibleIntrinsicCollarPortOverlapProfile,
    card_locallyRealizableCorrectionWords]

/-- The terminal alphabet after quotienting simultaneous renaming of the
three nonzero colors.  Geometry is retained exactly. -/
abbrev IntrinsicCollarTerminalColorState :=
  AdmissibleIntrinsicCollarPortOverlapProfile ×
    LocallyRealizableCorrectionColorOrbit

/-- The direct product enumeration of overlap geometry and correction
color orbit. -/
@[reducible] noncomputable def intrinsicCollarTerminalColorStateFintype :
    Fintype IntrinsicCollarTerminalColorState :=
  @instFintypeProd AdmissibleIntrinsicCollarPortOverlapProfile
    LocallyRealizableCorrectionColorOrbit
    admissibleIntrinsicCollarPortOverlapProfileFintype
    locallyRealizableCorrectionColorOrbitFintype

noncomputable instance (priority := 2500) :
    Fintype IntrinsicCollarTerminalColorState :=
  intrinsicCollarTerminalColorStateFintype

/-- Color symmetry reduces the terminal alphabet to exactly
`33 * 224 = 7392` states. -/
theorem card_intrinsicCollarTerminalColorState :
    @Fintype.card IntrinsicCollarTerminalColorState
      intrinsicCollarTerminalColorStateFintype = 7392 := by
  rw [Fintype.card_prod,
    card_admissibleIntrinsicCollarPortOverlapProfile,
    card_locallyRealizableCorrectionColorOrbit]

/-- Admissible profiles with a prescribed number of literal overlaps. -/
abbrev AdmissibleIntrinsicCollarPortOverlapProfileOfCard
    (overlapCount : Nat) :=
  {profile : AdmissibleIntrinsicCollarPortOverlapProfile //
    profile.1.card = overlapCount}

/-- The explicit enumeration of one overlap-cardinality stratum. -/
@[reducible] def admissibleIntrinsicCollarPortOverlapProfileOfCardFintype
    (overlapCount : Nat) :
    Fintype (AdmissibleIntrinsicCollarPortOverlapProfileOfCard
      overlapCount) :=
  @Subtype.fintype AdmissibleIntrinsicCollarPortOverlapProfile
    (fun profile => profile.1.card = overlapCount)
    (fun _ => inferInstance)
    admissibleIntrinsicCollarPortOverlapProfileFintype

/-- Exactly one admissible profile has no overlaps. -/
theorem card_admissibleIntrinsicCollarPortOverlapProfileOfCard_zero :
    @Fintype.card (AdmissibleIntrinsicCollarPortOverlapProfileOfCard 0)
      (admissibleIntrinsicCollarPortOverlapProfileOfCardFintype 0) = 1 := by
  decide

/-- Exactly sixteen admissible profiles have one overlap. -/
theorem card_admissibleIntrinsicCollarPortOverlapProfileOfCard_one :
    @Fintype.card (AdmissibleIntrinsicCollarPortOverlapProfileOfCard 1)
      (admissibleIntrinsicCollarPortOverlapProfileOfCardFintype 1) = 16 := by
  decide

/-- Exactly sixteen admissible profiles have two overlaps. -/
theorem card_admissibleIntrinsicCollarPortOverlapProfileOfCard_two :
    @Fintype.card (AdmissibleIntrinsicCollarPortOverlapProfileOfCard 2)
      (admissibleIntrinsicCollarPortOverlapProfileOfCardFintype 2) = 16 := by
  decide

/-- The color-reduced terminal stratum with a prescribed overlap count. -/
abbrev IntrinsicCollarTerminalColorStateOfOverlapCard
    (overlapCount : Nat) :=
  AdmissibleIntrinsicCollarPortOverlapProfileOfCard overlapCount ×
    LocallyRealizableCorrectionColorOrbit

/-- The direct product enumeration of an overlap stratum and the 224
correction color orbits. -/
@[reducible] noncomputable def
    intrinsicCollarTerminalColorStateOfOverlapCardFintype
    (overlapCount : Nat) :
    Fintype (IntrinsicCollarTerminalColorStateOfOverlapCard overlapCount) :=
  @instFintypeProd
    (AdmissibleIntrinsicCollarPortOverlapProfileOfCard overlapCount)
    LocallyRealizableCorrectionColorOrbit
    (admissibleIntrinsicCollarPortOverlapProfileOfCardFintype overlapCount)
    locallyRealizableCorrectionColorOrbitFintype

/-- The zero-overlap color-reduced stratum has 224 states. -/
theorem card_intrinsicCollarTerminalColorStateOfOverlapCard_zero :
    @Fintype.card (IntrinsicCollarTerminalColorStateOfOverlapCard 0)
      (intrinsicCollarTerminalColorStateOfOverlapCardFintype 0) = 224 := by
  rw [Fintype.card_prod,
    card_admissibleIntrinsicCollarPortOverlapProfileOfCard_zero,
    card_locallyRealizableCorrectionColorOrbit]

/-- The one-overlap color-reduced stratum has 3584 states. -/
theorem card_intrinsicCollarTerminalColorStateOfOverlapCard_one :
    @Fintype.card (IntrinsicCollarTerminalColorStateOfOverlapCard 1)
      (intrinsicCollarTerminalColorStateOfOverlapCardFintype 1) = 3584 := by
  rw [Fintype.card_prod,
    card_admissibleIntrinsicCollarPortOverlapProfileOfCard_one,
    card_locallyRealizableCorrectionColorOrbit]

/-- The two-overlap color-reduced stratum has 3584 states. -/
theorem card_intrinsicCollarTerminalColorStateOfOverlapCard_two :
    @Fintype.card (IntrinsicCollarTerminalColorStateOfOverlapCard 2)
      (intrinsicCollarTerminalColorStateOfOverlapCardFintype 2) = 3584 := by
  rw [Fintype.card_prod,
    card_admissibleIntrinsicCollarPortOverlapProfileOfCard_two,
    card_locallyRealizableCorrectionColorOrbit]

/-- An actual intrinsic collar and source escape as a raw terminal state. -/
noncomputable def intrinsicCollarTerminalRawState
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    IntrinsicCollarTerminalRawState :=
  (collar.admissibleIntrinsicCollarPortOverlapProfile,
    ⟨collar.intrinsicCollarCorrectionWord sourceEscape,
      collar.intrinsicCollarCorrectionWord_mem_locallyRealizable
        sourceEscape⟩)

/-- An actual intrinsic collar and source escape in the fixed 7392-state
terminal alphabet modulo color-name symmetry. -/
noncomputable def intrinsicCollarTerminalColorState
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    IntrinsicCollarTerminalColorState :=
  (collar.admissibleIntrinsicCollarPortOverlapProfile,
    collar.intrinsicCollarCorrectionColorOrbit sourceEscape)

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
