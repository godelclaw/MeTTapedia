import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarLocalStateSpace
import Mathlib.GroupTheory.GroupAction.Quotient

/-! Simultaneous global color-name symmetry of the finite intrinsic-collar
correction states. -/

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

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

namespace IntrinsicShortTargetEscapeCollar

/-- Global permutations of the four colors that fix the zero color. -/
abbrev ColorNameSymmetry :=
  MulAction.stabilizer (Equiv.Perm Color) (0 : Color)

/-- There are exactly six simultaneous permutations of the three nonzero
color names. -/
theorem card_colorNameSymmetry : Fintype.card ColorNameSymmetry = 6 := by
  decide

/-- Every color-name symmetry fixes the zero color. -/
@[simp]
theorem ColorNameSymmetry.smul_zero (symmetry : ColorNameSymmetry) :
    symmetry • (0 : Color) = 0 :=
  symmetry.property

/-- On `Color = F2 × F2`, every zero-fixing permutation preserves color
addition. -/
theorem colorNameSymmetry_smul_add (symmetry : ColorNameSymmetry)
    (left right : Color) :
    symmetry • (left + right) = symmetry • left + symmetry • right := by
  decide +revert

/-- Color relabeling is pointwise on a finite word. -/
@[simp]
theorem ColorNameSymmetry.smul_word_apply {I : Type*}
    (symmetry : ColorNameSymmetry) (word : I → Color) (index : I) :
    (symmetry • word) index = symmetry • word index :=
  rfl

/-- A zero-fixing color relabeling preserves the nonzero four-port
condition. -/
@[simp]
theorem squareBoundaryWord_nonzero_smul_iff
    (symmetry : ColorNameSymmetry) (word : SquareBoundaryWord) :
    SquareBoundaryWord.Nonzero (symmetry • word) ↔ word.Nonzero := by
  decide +revert

/-- A zero-fixing color relabeling preserves the canonical adjacent-pair
class. -/
@[simp]
theorem squareBoundaryWord_adjacent01_23_smul_iff
    (symmetry : ColorNameSymmetry) (word : SquareBoundaryWord) :
    SquareBoundaryWord.Adjacent01_23 (symmetry • word) ↔
      word.Adjacent01_23 := by
  decide +revert

/-- Relabeling both the four-port word and its bridge color preserves the
two-vertex extension condition. -/
@[simp]
theorem isTwoVertexBridgeExtension_smul_iff
    (symmetry : ColorNameSymmetry) (word : SquareBoundaryWord)
    (bridge : Color) :
    IsTwoVertexBridgeExtension (symmetry • word) (symmetry • bridge) ↔
      IsTwoVertexBridgeExtension word bridge := by
  decide +revert

/-- The local correction matrix commutes with simultaneous color
relabeling. -/
theorem smul_localCorrectionHalfWord
    (symmetry : ColorNameSymmetry) (own cross : SquareBoundaryWord)
    (bridge : Color) :
    symmetry • localCorrectionHalfWord own cross bridge =
      localCorrectionHalfWord (symmetry • own) (symmetry • cross)
        (symmetry • bridge) := by
  funext coordinate
  rcases coordinate with _ | port
  · rfl
  · exact colorNameSymmetry_smul_add symmetry (own port) (cross port)

/-- The join of the two five-symbol halves commutes with simultaneous
color relabeling. -/
theorem smul_correctionWordOfHalfWords
    (symmetry : ColorNameSymmetry)
    (source target : IntrinsicCollarCorrectionHalfWord) :
    symmetry • correctionWordOfHalfWords source target =
      correctionWordOfHalfWords (symmetry • source) (symmetry • target) := by
  funext coordinate
  rcases coordinate with coordinate | coordinate <;> rfl

/-- The thirty-six-state half-word set is closed under global color-name
symmetry. -/
theorem smul_mem_locallyRealizableCorrectionHalfWords
    (symmetry : ColorNameSymmetry)
    {word : IntrinsicCollarCorrectionHalfWord}
    (hword : word ∈ locallyRealizableCorrectionHalfWords) :
    symmetry • word ∈ locallyRealizableCorrectionHalfWords := by
  rw [locallyRealizableCorrectionHalfWords, Finset.mem_image] at hword
  rcases hword with ⟨⟨own, cross, bridge⟩, hgenerator, rfl⟩
  rw [smul_localCorrectionHalfWord]
  rcases Finset.mem_product.mp hgenerator with ⟨hown, hcross⟩
  rw [mem_canonicalOwnBoundaryWords_iff] at hown
  rw [mem_bridgeExtensionWordColors_iff] at hcross
  exact localCorrectionHalfWord_mem _ _ _
    ((squareBoundaryWord_nonzero_smul_iff symmetry own).2 hown.1)
    ((squareBoundaryWord_adjacent01_23_smul_iff symmetry own).2 hown.2)
    ((isTwoVertexBridgeExtension_smul_iff symmetry cross bridge).2 hcross)

/-- Membership in the thirty-six-state half-word set is invariant under
global color-name symmetry. -/
@[simp]
theorem smul_mem_locallyRealizableCorrectionHalfWords_iff
    (symmetry : ColorNameSymmetry)
    (word : IntrinsicCollarCorrectionHalfWord) :
    symmetry • word ∈ locallyRealizableCorrectionHalfWords ↔
      word ∈ locallyRealizableCorrectionHalfWords := by
  constructor
  · intro hword
    have hinverse :=
      smul_mem_locallyRealizableCorrectionHalfWords symmetry⁻¹ hword
    simpa using hinverse
  · exact smul_mem_locallyRealizableCorrectionHalfWords symmetry

/-- The 1296-state full correction-word set is closed under simultaneous
global color-name symmetry. -/
theorem smul_mem_locallyRealizableCorrectionWords
    (symmetry : ColorNameSymmetry)
    {word : IntrinsicCollarCorrectionWord}
    (hword : word ∈ locallyRealizableCorrectionWords) :
    symmetry • word ∈ locallyRealizableCorrectionWords := by
  rw [locallyRealizableCorrectionWords, Finset.mem_image] at hword
  rcases hword with ⟨⟨source, target⟩, hgenerator, rfl⟩
  rw [smul_correctionWordOfHalfWords]
  rcases Finset.mem_product.mp hgenerator with ⟨hsource, htarget⟩
  exact correctionWordOfHalfWords_mem _ _
    (smul_mem_locallyRealizableCorrectionHalfWords symmetry hsource)
    (smul_mem_locallyRealizableCorrectionHalfWords symmetry htarget)

/-- Membership in the 1296-state correction-word set is invariant under
simultaneous global color-name symmetry. -/
@[simp]
theorem smul_mem_locallyRealizableCorrectionWords_iff
    (symmetry : ColorNameSymmetry)
    (word : IntrinsicCollarCorrectionWord) :
    symmetry • word ∈ locallyRealizableCorrectionWords ↔
      word ∈ locallyRealizableCorrectionWords := by
  constructor
  · intro hword
    have hinverse := smul_mem_locallyRealizableCorrectionWords symmetry⁻¹ hword
    simpa using hinverse
  · exact smul_mem_locallyRealizableCorrectionWords symmetry

/-- A locally realizable half word, packaged with its thirty-six-state
membership certificate. -/
abbrev LocallyRealizableCorrectionHalfState :=
  ↥locallyRealizableCorrectionHalfWords

/-- A locally realizable full correction word, packaged with its
1296-state membership certificate. -/
abbrev LocallyRealizableCorrectionState :=
  ↥locallyRealizableCorrectionWords

/-- Global color-name symmetry acts on the thirty-six half states. -/
instance : MulAction ColorNameSymmetry LocallyRealizableCorrectionHalfState where
  smul symmetry state :=
    ⟨symmetry • state.1,
      smul_mem_locallyRealizableCorrectionHalfWords symmetry state.2⟩
  one_smul state := by
    apply Subtype.ext
    exact one_smul ColorNameSymmetry state.1
  mul_smul first second state := by
    apply Subtype.ext
    exact mul_smul first second state.1

/-- Global color-name symmetry acts on the 1296 full correction states. -/
instance : MulAction ColorNameSymmetry LocallyRealizableCorrectionState where
  smul symmetry state :=
    ⟨symmetry • state.1,
      smul_mem_locallyRealizableCorrectionWords symmetry state.2⟩
  one_smul state := by
    apply Subtype.ext
    exact one_smul ColorNameSymmetry state.1
  mul_smul first second state := by
    apply Subtype.ext
    exact mul_smul first second state.1

/-- A color-name orbit of locally realizable five-symbol half states. -/
abbrev LocallyRealizableCorrectionHalfColorOrbit :=
  MulAction.orbitRel.Quotient ColorNameSymmetry
    LocallyRealizableCorrectionHalfState

/-- A color-name orbit of locally realizable ten-symbol correction
states. -/
abbrev LocallyRealizableCorrectionColorOrbit :=
  MulAction.orbitRel.Quotient ColorNameSymmetry
    LocallyRealizableCorrectionState

local instance : DecidableEq LocallyRealizableCorrectionHalfState :=
  fun left right =>
    if h : left.1 = right.1 then
      isTrue (Subtype.ext h)
    else
      isFalse fun hstates => h (congrArg Subtype.val hstates)

local instance : DecidableEq LocallyRealizableCorrectionState :=
  fun left right =>
    if h : left.1 = right.1 then
      isTrue (Subtype.ext h)
    else
      isFalse fun hstates => h (congrArg Subtype.val hstates)

noncomputable instance (priority := 2000)
    locallyRealizableCorrectionHalfColorOrbitFintype :
    Fintype LocallyRealizableCorrectionHalfColorOrbit :=
  Fintype.ofFinite _

noncomputable instance (priority := 2000)
    locallyRealizableCorrectionColorOrbitFintype :
    Fintype LocallyRealizableCorrectionColorOrbit :=
  Fintype.ofFinite _

noncomputable local instance fixedByHalfStateFintype
    (symmetry : ColorNameSymmetry) :
    Fintype (MulAction.fixedBy
      LocallyRealizableCorrectionHalfState symmetry) :=
  Subtype.fintype _

noncomputable local instance fixedByStateFintype
    (symmetry : ColorNameSymmetry) :
    Fintype (MulAction.fixedBy LocallyRealizableCorrectionState symmetry) :=
  Subtype.fintype _

/-- Restrict a ten-symbol correction word to its source five-symbol half. -/
def sourceHalfWordOfCorrectionWord (word : IntrinsicCollarCorrectionWord) :
    IntrinsicCollarCorrectionHalfWord :=
  fun coordinate => word (Sum.inl coordinate)

/-- Restrict a ten-symbol correction word to its target five-symbol half. -/
def targetHalfWordOfCorrectionWord (word : IntrinsicCollarCorrectionWord) :
    IntrinsicCollarCorrectionHalfWord :=
  fun coordinate => word (Sum.inr coordinate)

@[simp]
theorem sourceHalfWordOfCorrectionWord_correctionWordOfHalfWords
    (source target : IntrinsicCollarCorrectionHalfWord) :
    sourceHalfWordOfCorrectionWord
      (correctionWordOfHalfWords source target) = source := by
  rfl

@[simp]
theorem targetHalfWordOfCorrectionWord_correctionWordOfHalfWords
    (source target : IntrinsicCollarCorrectionHalfWord) :
    targetHalfWordOfCorrectionWord
      (correctionWordOfHalfWords source target) = target := by
  rfl

/-- Both restrictions of a locally realizable ten-symbol word are locally
realizable half words. -/
theorem halfWords_mem_of_correctionWord_mem
    {word : IntrinsicCollarCorrectionWord}
    (hword : word ∈ locallyRealizableCorrectionWords) :
    sourceHalfWordOfCorrectionWord word ∈
        locallyRealizableCorrectionHalfWords ∧
      targetHalfWordOfCorrectionWord word ∈
        locallyRealizableCorrectionHalfWords := by
  rw [locallyRealizableCorrectionWords, Finset.mem_image] at hword
  rcases hword with ⟨⟨source, target⟩, hpair, rfl⟩
  simpa using Finset.mem_product.mp hpair

/-- A full local correction state is exactly an ordered pair of its source
and target half states. -/
def correctionStateEquivHalfStatePair :
    LocallyRealizableCorrectionState ≃
      LocallyRealizableCorrectionHalfState ×
        LocallyRealizableCorrectionHalfState where
  toFun state :=
    (⟨sourceHalfWordOfCorrectionWord state.1,
      (halfWords_mem_of_correctionWord_mem state.2).1⟩,
    ⟨targetHalfWordOfCorrectionWord state.1,
      (halfWords_mem_of_correctionWord_mem state.2).2⟩)
  invFun states :=
    ⟨correctionWordOfHalfWords states.1.1 states.2.1,
      correctionWordOfHalfWords_mem _ _ states.1.2 states.2.2⟩
  left_inv state := by
    apply Subtype.ext
    funext coordinate
    rcases coordinate with coordinate | coordinate <;> rfl
  right_inv states := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl

/-- The full-state/half-pair equivalence commutes with simultaneous color
renaming. -/
theorem correctionStateEquivHalfStatePair_smul
    (symmetry : ColorNameSymmetry)
    (state : LocallyRealizableCorrectionState) :
    correctionStateEquivHalfStatePair (symmetry • state) =
      symmetry • correctionStateEquivHalfStatePair state := by
  apply Prod.ext <;> apply Subtype.ext <;> rfl

/-- For each fixed color permutation, fixed full states are exactly pairs
of fixed half states. -/
def fixedByCorrectionStateEquiv (symmetry : ColorNameSymmetry) :
    MulAction.fixedBy LocallyRealizableCorrectionState symmetry ≃
      MulAction.fixedBy LocallyRealizableCorrectionHalfState symmetry ×
        MulAction.fixedBy LocallyRealizableCorrectionHalfState symmetry where
  toFun state := by
    let states := correctionStateEquivHalfStatePair state.1
    have hstates : symmetry • states = states := by
      rw [← correctionStateEquivHalfStatePair_smul, state.2]
    exact
      (⟨states.1, congrArg Prod.fst hstates⟩,
      ⟨states.2, congrArg Prod.snd hstates⟩)
  invFun states := by
    let state := correctionStateEquivHalfStatePair.symm
      (states.1.1, states.2.1)
    refine ⟨state, ?_⟩
    apply correctionStateEquivHalfStatePair.injective
    rw [correctionStateEquivHalfStatePair_smul,
      Equiv.apply_symm_apply]
    exact Prod.ext states.1.2 states.2.2
  left_inv state := by
    apply Subtype.ext
    exact correctionStateEquivHalfStatePair.left_inv state.1
  right_inv states := by
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst
        (correctionStateEquivHalfStatePair.apply_symm_apply
          (states.1.1, states.2.1))
    · exact congrArg Prod.snd
        (correctionStateEquivHalfStatePair.apply_symm_apply
          (states.1.1, states.2.1))

/-- A permutation fixes the square of as many full states as half states. -/
theorem card_fixedBy_locallyRealizableCorrectionState
    (symmetry : ColorNameSymmetry) :
    Fintype.card (MulAction.fixedBy
        LocallyRealizableCorrectionState symmetry) =
      Fintype.card (MulAction.fixedBy
          LocallyRealizableCorrectionHalfState symmetry) *
        Fintype.card (MulAction.fixedBy
          LocallyRealizableCorrectionHalfState symmetry) := by
  rw [← Fintype.card_prod]
  exact Fintype.card_congr (fixedByCorrectionStateEquiv symmetry)

/-- Burnside's fixed-point sum for the thirty-six half states is 48. -/
theorem sum_card_fixedBy_locallyRealizableCorrectionHalfState :
    (∑ symmetry : ColorNameSymmetry,
      Fintype.card (MulAction.fixedBy
        LocallyRealizableCorrectionHalfState symmetry)) = 48 := by
  decide

/-- Burnside's fixed-point sum for the 1296 full states is 1344. -/
theorem sum_card_fixedBy_locallyRealizableCorrectionState :
    (∑ symmetry : ColorNameSymmetry,
      Fintype.card (MulAction.fixedBy
        LocallyRealizableCorrectionState symmetry)) = 1344 := by
  simp_rw [card_fixedBy_locallyRealizableCorrectionState]
  decide

/-- The thirty-six half states have exactly eight orbits under simultaneous
renaming of the three nonzero colors. -/
theorem card_locallyRealizableCorrectionHalfColorOrbit :
    @Fintype.card LocallyRealizableCorrectionHalfColorOrbit
      locallyRealizableCorrectionHalfColorOrbitFintype = 8 := by
  have hburnside :=
    @MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
      ColorNameSymmetry LocallyRealizableCorrectionHalfState
      inferInstance inferInstance inferInstance fixedByHalfStateFintype
      locallyRealizableCorrectionHalfColorOrbitFintype
  rw [sum_card_fixedBy_locallyRealizableCorrectionHalfState,
    card_colorNameSymmetry] at hburnside
  apply Nat.mul_right_cancel (m := 6) (by norm_num)
  calc
    @Fintype.card LocallyRealizableCorrectionHalfColorOrbit
          locallyRealizableCorrectionHalfColorOrbitFintype * 6 = 48 :=
      hburnside.symm
    _ = 8 * 6 := by norm_num

/-- The 1296 full local correction states have exactly 224 orbits under
simultaneous renaming of the three nonzero colors. -/
theorem card_locallyRealizableCorrectionColorOrbit :
    @Fintype.card LocallyRealizableCorrectionColorOrbit
      locallyRealizableCorrectionColorOrbitFintype = 224 := by
  have hburnside :=
    @MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
      ColorNameSymmetry LocallyRealizableCorrectionState
      inferInstance inferInstance inferInstance fixedByStateFintype
      locallyRealizableCorrectionColorOrbitFintype
  rw [sum_card_fixedBy_locallyRealizableCorrectionState,
    card_colorNameSymmetry] at hburnside
  apply Nat.mul_right_cancel (m := 6) (by norm_num)
  calc
    @Fintype.card LocallyRealizableCorrectionColorOrbit
          locallyRealizableCorrectionColorOrbitFintype * 6 = 1344 :=
      hburnside.symm
    _ = 224 * 6 := by norm_num

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

/-- The intrinsic correction of an actual source-target collar, viewed in
the fixed 224-element state space modulo simultaneous color renaming. -/
noncomputable def intrinsicCollarCorrectionColorOrbit
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    LocallyRealizableCorrectionColorOrbit :=
  Quotient.mk''
    ⟨collar.intrinsicCollarCorrectionWord sourceEscape,
      collar.intrinsicCollarCorrectionWord_mem_locallyRealizable
        sourceEscape⟩

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
