import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedRegionBoundaryOrder
import Mathlib.GroupTheory.Perm.Finite

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RetainedRegionBoundaryOrder

open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor
open GoertzelV24SeamFaceArc

noncomputable section

/-- Before its first return to the marked set, rewiring only the marked
points changes an orbit merely by changing its marked starting point. -/
theorem mul_ofSubtype_pow_eq_pow_apply
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) [DecidablePred hit]
    (matching : Equiv.Perm {point // hit point})
    (root : {point // hit point}) {step : Nat}
    (hstepPos : 0 < step)
    (hstepLe : step ≤ firstPositiveHitTime perm hit
      (matching root).1 (matching root).2) :
    ((perm * Equiv.Perm.ofSubtype matching) ^ step) root.1 =
      (perm ^ step) (matching root).1 := by
  classical
  induction step with
  | zero => omega
  | succ previous ih =>
      by_cases hpreviousZero : previous = 0
      · subst previous
        change (perm * Equiv.Perm.ofSubtype matching) root.1 =
          perm (matching root).1
        rw [Equiv.Perm.mul_apply]
        rw [Equiv.Perm.ofSubtype_apply_of_mem matching root.2]
      · have hpreviousPos : 0 < previous := Nat.pos_of_ne_zero hpreviousZero
        have hpreviousLt : previous < firstPositiveHitTime perm hit
            (matching root).1 (matching root).2 := by
          omega
        have hnotHit : ¬ hit ((perm ^ previous) (matching root).1) :=
          not_hit_before_firstPositiveHitTime perm hit
            (matching root).1 (matching root).2 hpreviousPos hpreviousLt
        rw [pow_succ', Equiv.Perm.mul_apply, ih hpreviousPos
          (Nat.le_of_lt hpreviousLt), Equiv.Perm.mul_apply,
          Equiv.Perm.ofSubtype_apply_of_not_mem matching hnotHit,
          pow_succ', Equiv.Perm.mul_apply]

/-- Extending a matching by the identity off a marked set and composing it
before a finite permutation composes the computed next-hit permutation by
that matching. -/
theorem nextHitPerm_mul_ofSubtype
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) [DecidablePred hit]
    (matching : Equiv.Perm {point // hit point}) :
    nextHitPerm (perm * Equiv.Perm.ofSubtype matching) hit =
      nextHitPerm perm hit * matching := by
  classical
  apply Equiv.ext
  intro root
  let targetTime := firstPositiveHitTime perm hit
    (matching root).1 (matching root).2
  let rewiredTime := firstPositiveHitTime
    (perm * Equiv.Perm.ofSubtype matching) hit root.1 root.2
  have htargetPos : 0 < targetTime :=
    firstPositiveHitTime_pos perm hit
      (matching root).1 (matching root).2
  have htargetPower :
      ((perm * Equiv.Perm.ofSubtype matching) ^ targetTime) root.1 =
        (perm ^ targetTime) (matching root).1 :=
    mul_ofSubtype_pow_eq_pow_apply perm hit matching root htargetPos
      (le_refl targetTime)
  have hrewiredLe : rewiredTime ≤ targetTime := by
    apply firstPositiveHitTime_le_of_hit
    · exact htargetPos
    · rw [htargetPower]
      exact firstPositiveHitTime_hits perm hit
        (matching root).1 (matching root).2
  have htargetLe : targetTime ≤ rewiredTime := by
    by_contra hnot
    have hrewiredLt : rewiredTime < targetTime :=
      Nat.lt_of_not_ge hnot
    have hrewiredPos : 0 < rewiredTime :=
      firstPositiveHitTime_pos
        (perm * Equiv.Perm.ofSubtype matching) hit root.1 root.2
    have hrewiredPower := mul_ofSubtype_pow_eq_pow_apply
      perm hit matching root hrewiredPos (Nat.le_of_lt hrewiredLt)
    exact (not_hit_before_firstPositiveHitTime perm hit
      (matching root).1 (matching root).2 hrewiredPos hrewiredLt)
      (hrewiredPower ▸ firstPositiveHitTime_hits
        (perm * Equiv.Perm.ofSubtype matching) hit root.1 root.2)
  have htimes : rewiredTime = targetTime :=
    Nat.le_antisymm hrewiredLe htargetLe
  apply Subtype.ext
  change ((perm * Equiv.Perm.ofSubtype matching) ^ rewiredTime) root.1 =
    (perm ^ targetTime) (matching root).1
  rw [htimes]
  exact htargetPower

/-- Conjugating an ambient permutation transports the computed first-return
permutation along the induced equivalence of marked points. -/
theorem nextHitPerm_permCongr
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (equiv : A ≃ B) (perm : Equiv.Perm A)
    (hitA : A → Prop) (hitB : B → Prop)
    (hhit : ∀ point, hitA point ↔ hitB (equiv point)) :
    nextHitPerm (equiv.permCongr perm) hitB =
      (equiv.subtypeEquiv (p := hitA) (q := hitB) hhit).permCongr
        (nextHitPerm perm hitA) := by
  classical
  let markedEquiv := equiv.subtypeEquiv (p := hitA) (q := hitB) hhit
  apply Equiv.ext
  intro rootB
  let rootA := markedEquiv.symm rootB
  have hrootB : rootB = markedEquiv rootA := by
    exact (markedEquiv.apply_symm_apply rootB).symm
  rw [hrootB]
  let timeA := firstPositiveHitTime perm hitA rootA.1 rootA.2
  let timeB := firstPositiveHitTime (equiv.permCongr perm) hitB
    (equiv rootA.1) (markedEquiv rootA).2
  have htimeBLe : timeB ≤ timeA := by
    apply firstPositiveHitTime_le_of_hit
    · exact firstPositiveHitTime_pos perm hitA rootA.1 rootA.2
    · rw [permCongr_pow_apply]
      exact (hhit _).mp
        (firstPositiveHitTime_hits perm hitA rootA.1 rootA.2)
  have htimeALe : timeA ≤ timeB := by
    apply firstPositiveHitTime_le_of_hit
    · exact firstPositiveHitTime_pos (equiv.permCongr perm) hitB
        (equiv rootA.1) (markedEquiv rootA).2
    · apply (hhit _).mpr
      rw [← permCongr_pow_apply]
      exact firstPositiveHitTime_hits (equiv.permCongr perm) hitB
        (equiv rootA.1) (markedEquiv rootA).2
  have htimes : timeB = timeA := Nat.le_antisymm htimeBLe htimeALe
  apply Subtype.ext
  simp only [nextHitPerm_apply, Equiv.permCongr_apply]
  simp only [markedEquiv, Equiv.symm_apply_apply]
  change ((equiv.permCongr perm) ^ timeB) (equiv rootA.1) =
    equiv ((perm ^ timeA) rootA.1)
  rw [htimes, permCongr_pow_apply]

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- The retained-side capped edge flip crosses an internal edge and fixes an
exposed half-dart. -/
noncomputable def retainedCappedAlphaFun
    (RS : RotationSystem V E) (keep : V → Prop)
    (dart : RetainedDart RS keep) : RetainedDart RS keep := by
  classical
  exact if hopposite : keep (RS.vertOf (RS.alpha dart.1)) then
    ⟨RS.alpha dart.1, hopposite⟩
  else dart

/-- The retained-side capped flip is involutive. -/
theorem retainedCappedAlphaFun_involutive
    (RS : RotationSystem V E) (keep : V → Prop)
    (dart : RetainedDart RS keep) :
    retainedCappedAlphaFun RS keep
        (retainedCappedAlphaFun RS keep dart) = dart := by
  by_cases hopposite : keep (RS.vertOf (RS.alpha dart.1))
  · apply Subtype.ext
    simp [retainedCappedAlphaFun, hopposite, dart.2,
      RS.alpha_involutive]
  · simp [retainedCappedAlphaFun, hopposite]

/-- Capped retained-side alpha as a permutation. -/
def retainedCappedAlpha
    (RS : RotationSystem V E) (keep : V → Prop) :
    Equiv.Perm (RetainedDart RS keep) where
  toFun := retainedCappedAlphaFun RS keep
  invFun := retainedCappedAlphaFun RS keep
  left_inv := retainedCappedAlphaFun_involutive RS keep
  right_inv := retainedCappedAlphaFun_involutive RS keep

@[simp]
theorem retainedCappedAlpha_apply_internal
    (RS : RotationSystem V E) (keep : V → Prop)
    (dart : RetainedDart RS keep)
    (hopposite : keep (RS.vertOf (RS.alpha dart.1))) :
    (retainedCappedAlpha RS keep dart).1 = RS.alpha dart.1 := by
  simp [retainedCappedAlpha, retainedCappedAlphaFun, hopposite]

@[simp]
theorem retainedCappedAlpha_apply_boundary
    (RS : RotationSystem V E) (keep : V → Prop)
    (dart : RetainedDart RS keep)
    (hopposite : ¬ keep (RS.vertOf (RS.alpha dart.1))) :
    retainedCappedAlpha RS keep dart = dart := by
  simp [retainedCappedAlpha, retainedCappedAlphaFun, hopposite]

/-- Face walk of the capped retained-side ribbon submap. -/
def retainedCappedFacePerm
    (RS : RotationSystem V E) (keep : V → Prop) :
    Equiv.Perm (RetainedDart RS keep) :=
  retainedRho RS keep * retainedCappedAlpha RS keep

/-- Computed first-return boundary order of the retained-side capped ribbon
submap. -/
def retainedRegionBoundarySuccessor
    (RS : RotationSystem V E) (keep : V → Prop) :
    Equiv.Perm (BoundaryDart RS keep) :=
  nextHitPerm (retainedCappedFacePerm RS keep)
    (fun dart => ¬ keep (RS.vertOf (RS.alpha dart.1)))

/-- Extend a computed boundary permutation by the identity on internal
retained darts. -/
noncomputable def extendBoundaryPerm
    (RS : RotationSystem V E) (keep : V → Prop)
    (matching : Equiv.Perm (BoundaryDart RS keep)) :
    Equiv.Perm (RetainedDart RS keep) := by
  classical
  exact Equiv.Perm.ofSubtype matching

@[simp]
theorem extendBoundaryPerm_apply_internal
    (RS : RotationSystem V E) (keep : V → Prop)
    (matching : Equiv.Perm (BoundaryDart RS keep))
    (dart : InternalDart RS keep) :
    extendBoundaryPerm RS keep matching dart.1 = dart.1 := by
  classical
  apply Equiv.Perm.ofSubtype_apply_of_not_mem
  exact not_not_intro dart.2

@[simp]
theorem extendBoundaryPerm_apply_boundary
    (RS : RotationSystem V E) (keep : V → Prop)
    (matching : Equiv.Perm (BoundaryDart RS keep))
    (dart : BoundaryDart RS keep) :
    extendBoundaryPerm RS keep matching dart.1 = (matching dart).1 := by
  classical
  exact Equiv.Perm.ofSubtype_apply_of_mem matching dart.2

/-- The cut decomposition transports the concrete equal-position seam
matching to a permutation of all actual retained boundary darts. -/
def orderedBoundarySeamSwap
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCrossing rightCrossing : Fin n → E)
    (hleftCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = leftCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hrightCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = rightCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing ∨
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing)) :
    Equiv.Perm (BoundaryDart RS keep) :=
  (boundaryDartEquivCutSum RS keep
      (orderedCut leftCrossing) (orderedCut rightCrossing)
      hcover hdisjoint).symm.permCongr
    (MatchedSeam.seamSwap
      (orderedCutSeamMatching RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective))

/-- Ordered seam positions enumerate the same retained boundary carrier before
it is embedded as the seam subtype of the splice. -/
def orderedRetainedBoundaryPositionEquiv
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCrossing rightCrossing : Fin n → E)
    (hleftCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = leftCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hrightCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = rightCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing ∨
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing)) :
    OrderedSeamPosition n ≃ BoundaryDart RS keep :=
  (Equiv.sumCongr
    (orderedBoundaryDartEquiv RS keep leftCrossing
      hleftCrosses hleftInjective)
    (orderedBoundaryDartEquiv RS keep rightCrossing
      hrightCrosses hrightInjective)).trans
    (boundaryDartEquivCutSum RS keep
      (orderedCut leftCrossing) (orderedCut rightCrossing)
      hcover hdisjoint).symm

/-- The boundary predicate on retained darts is exactly the seam predicate
after the concrete three-part decomposition. -/
theorem retainedBoundary_iff_isSeamDart_parts
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCut rightCut : Finset E)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ leftCut ∨ RS.edgeOf dart.1.1 ∈ rightCut)
    (hdisjoint : Disjoint leftCut rightCut)
    (dart : RetainedDart RS keep) :
    ¬ keep (RS.vertOf (RS.alpha dart.1)) ↔
      IsSeamDart
        (retainedDartEquivMatchedParts RS keep leftCut rightCut
          hcover hdisjoint dart) := by
  classical
  by_cases hopposite : keep (RS.vertOf (RS.alpha dart.1))
  · simp [retainedDartEquivMatchedParts,
      retainedDartEquivInternalSumBoundary, hopposite]
  · simp [retainedDartEquivMatchedParts,
      retainedDartEquivInternalSumBoundary, hopposite,
      boundaryDartEquivCutSum, boundaryDartToCutSum]
    change True
    trivial

/-- Forgetting the retained boundary subtype into the splice seam is the cut
classification followed by the canonical seam embedding. -/
def retainedBoundaryEquivSeamDart
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCut rightCut : Finset E)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ leftCut ∨ RS.edgeOf dart.1.1 ∈ rightCut)
    (hdisjoint : Disjoint leftCut rightCut) :
    BoundaryDart RS keep ≃
      { dart : MatchedSeam.Dart (InternalDart RS keep)
          (BoundaryDartOn RS keep leftCut)
          (BoundaryDartOn RS keep rightCut) //
        IsSeamDart dart } :=
  (boundaryDartEquivCutSum RS keep leftCut rightCut
    hcover hdisjoint).trans seamDartEquiv

/-- This explicit boundary-to-seam map is exactly the subtype equivalence
induced by the full retained-dart decomposition. -/
theorem retainedBoundaryEquivSeamDart_eq_subtypeEquiv_parts
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCut rightCut : Finset E)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ leftCut ∨ RS.edgeOf dart.1.1 ∈ rightCut)
    (hdisjoint : Disjoint leftCut rightCut) :
    retainedBoundaryEquivSeamDart RS keep leftCut rightCut
        hcover hdisjoint =
      (retainedDartEquivMatchedParts RS keep leftCut rightCut
        hcover hdisjoint).subtypeEquiv
          (p := fun dart => ¬ keep (RS.vertOf (RS.alpha dart.1)))
          (q := IsSeamDart)
          (retainedBoundary_iff_isSeamDart_parts RS keep
            leftCut rightCut hcover hdisjoint) := by
  classical
  apply Equiv.ext
  intro dart
  apply Subtype.ext
  change (retainedBoundaryEquivSeamDart RS keep leftCut rightCut
      hcover hdisjoint dart).1 =
    retainedDartEquivMatchedParts RS keep leftCut rightCut
      hcover hdisjoint dart.1
  by_cases hleft : RS.edgeOf dart.1.1 ∈ leftCut
  · simp [retainedBoundaryEquivSeamDart,
      retainedDartEquivMatchedParts,
      retainedDartEquivInternalSumBoundary,
      boundaryDartEquivCutSum, boundaryDartToCutSum,
      seamDartEquiv, Equiv.trans_apply, dart.2, hleft]
  · simp [retainedBoundaryEquivSeamDart,
      retainedDartEquivMatchedParts,
      retainedDartEquivInternalSumBoundary,
      boundaryDartEquivCutSum, boundaryDartToCutSum,
      seamDartEquiv, Equiv.trans_apply, dart.2, hleft]

/-- The pre-splice boundary enumeration followed by boundary embedding is the
existing ordered seam enumeration. -/
theorem orderedRetainedBoundaryPositionEquiv_trans_seam
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCrossing rightCrossing : Fin n → E)
    (hleftCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = leftCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hrightCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = rightCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing ∨
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing)) :
    (orderedRetainedBoundaryPositionEquiv RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint).trans
      (retainedBoundaryEquivSeamDart RS keep
        (orderedCut leftCrossing) (orderedCut rightCrossing)
        hcover hdisjoint) =
      orderedSeamPositionEquiv RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective := by
  apply Equiv.ext
  intro position
  rcases position with left | right <;>
    simp [orderedRetainedBoundaryPositionEquiv,
      retainedBoundaryEquivSeamDart, orderedSeamPositionEquiv,
      Equiv.trans_apply]

@[simp]
theorem orderedBoundarySeamSwap_apply_leftDart
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCrossing rightCrossing : Fin n → E)
    (hleftCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = leftCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hrightCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = rightCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing ∨
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (dart : BoundaryDartOn RS keep (orderedCut leftCrossing)) :
    orderedBoundarySeamSwap RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint dart.1 =
      (orderedCutSeamMatching RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective dart).1 := by
  classical
  simp [orderedBoundarySeamSwap, Equiv.permCongr_apply,
    boundaryDartEquivCutSum, boundaryDartToCutSum,
    cutSumUnderlyingBoundary, dart.2]

@[simp]
theorem orderedBoundarySeamSwap_apply_rightDart
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCrossing rightCrossing : Fin n → E)
    (hleftCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = leftCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hrightCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = rightCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing ∨
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (dart : BoundaryDartOn RS keep (orderedCut rightCrossing)) :
    orderedBoundarySeamSwap RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint dart.1 =
      ((orderedCutSeamMatching RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective).symm
          dart).1 := by
  classical
  have hnotLeft : RS.edgeOf dart.1.1.1 ∉ orderedCut leftCrossing := by
    intro hleftMem
    exact Finset.disjoint_left.1 hdisjoint hleftMem dart.2
  simp [orderedBoundarySeamSwap, Equiv.permCongr_apply,
    boundaryDartEquivCutSum, boundaryDartToCutSum,
    cutSumUnderlyingBoundary, hnotLeft]

@[simp]
theorem orderedBoundarySeamSwap_apply_left
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCrossing rightCrossing : Fin n → E)
    (hleftCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = leftCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hrightCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = rightCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing ∨
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing)) (step : Fin n) :
    orderedBoundarySeamSwap RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint
        (orderedBoundaryDart RS keep leftCrossing hleftCrosses step).1 =
      (orderedBoundaryDart RS keep rightCrossing hrightCrosses step).1 := by
  classical
  rw [orderedBoundarySeamSwap_apply_leftDart,
    orderedCutSeamMatching_apply]

@[simp]
theorem orderedBoundarySeamSwap_apply_right
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCrossing rightCrossing : Fin n → E)
    (hleftCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = leftCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hrightCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = rightCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing ∨
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing)) (step : Fin n) :
    orderedBoundarySeamSwap RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint
        (orderedBoundaryDart RS keep rightCrossing hrightCrosses step).1 =
      (orderedBoundaryDart RS keep leftCrossing hleftCrosses step).1 := by
  classical
  rw [orderedBoundarySeamSwap_apply_rightDart,
    orderedCutSeamMatching_symm_apply]

@[simp]
theorem retainedDartEquivMatchedParts_symm_interior
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCut rightCut : Finset E)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ leftCut ∨ RS.edgeOf dart.1.1 ∈ rightCut)
    (hdisjoint : Disjoint leftCut rightCut)
    (dart : InternalDart RS keep) :
    (retainedDartEquivMatchedParts RS keep leftCut rightCut
      hcover hdisjoint).symm (Sum.inl dart) = dart.1 :=
  rfl

@[simp]
theorem retainedDartEquivMatchedParts_symm_left
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCut rightCut : Finset E)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ leftCut ∨ RS.edgeOf dart.1.1 ∈ rightCut)
    (hdisjoint : Disjoint leftCut rightCut)
    (dart : BoundaryDartOn RS keep leftCut) :
    (retainedDartEquivMatchedParts RS keep leftCut rightCut
      hcover hdisjoint).symm (Sum.inr (Sum.inl dart)) = dart.1.1 :=
  rfl

@[simp]
theorem retainedDartEquivMatchedParts_symm_right
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCut rightCut : Finset E)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ leftCut ∨ RS.edgeOf dart.1.1 ∈ rightCut)
    (hdisjoint : Disjoint leftCut rightCut)
    (dart : BoundaryDartOn RS keep rightCut) :
    (retainedDartEquivMatchedParts RS keep leftCut rightCut
      hcover hdisjoint).symm (Sum.inr (Sum.inr dart)) = dart.1.1 :=
  rfl

/-- The concrete splice edge flip is exactly the retained capped flip after
the ordered seam matching has rewired the exposed darts. -/
theorem orderedCutSpliceAlpha_eq_rewiredRetainedCappedAlpha
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCrossing rightCrossing : Fin n → E)
    (hleftCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = leftCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hrightCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = rightCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing ∨
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (houter : keep (RS.vertOf RS.outer)) :
    (orderedCutMatchedSeamData RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter).alpha =
      (retainedDartEquivMatchedParts RS keep
        (orderedCut leftCrossing) (orderedCut rightCrossing)
        hcover hdisjoint).permCongr
        (retainedCappedAlpha RS keep *
          extendBoundaryPerm RS keep
            (orderedBoundarySeamSwap RS keep leftCrossing rightCrossing
              hleftCrosses hrightCrosses hleftInjective hrightInjective
              hcover hdisjoint)) := by
  classical
  let parts := retainedDartEquivMatchedParts RS keep
    (orderedCut leftCrossing) (orderedCut rightCrossing)
    hcover hdisjoint
  let seam := orderedBoundarySeamSwap RS keep leftCrossing rightCrossing
    hleftCrosses hrightCrosses hleftInjective hrightInjective
    hcover hdisjoint
  apply Equiv.ext
  intro dart
  apply parts.symm.injective
  simp only [Equiv.permCongr_apply, Equiv.Perm.mul_apply]
  rcases dart with internal | side
  · simp only [parts, orderedCutMatchedSeamData,
      MatchedSeam.Data.alpha_interior,
      retainedDartEquivMatchedParts_symm_interior,
      Equiv.symm_apply_apply]
    change (internalAlpha RS keep internal).1 =
      retainedCappedAlpha RS keep
        (extendBoundaryPerm RS keep seam internal.1)
    rw [extendBoundaryPerm_apply_internal]
    apply Subtype.ext
    exact (retainedCappedAlpha_apply_internal RS keep
      internal.1 internal.2).symm
  · rcases side with left | right
    · simp only [parts, orderedCutMatchedSeamData,
        MatchedSeam.Data.alpha_left,
        retainedDartEquivMatchedParts_symm_left,
        retainedDartEquivMatchedParts_symm_right,
        Equiv.symm_apply_apply]
      change ((orderedCutSeamMatching RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective)
            left).1.1 =
        retainedCappedAlpha RS keep
          (extendBoundaryPerm RS keep seam left.1.1)
      rw [extendBoundaryPerm_apply_boundary]
      rw [show seam left.1 =
          (orderedCutSeamMatching RS keep leftCrossing rightCrossing
            hleftCrosses hrightCrosses hleftInjective hrightInjective
            left).1 from
        orderedBoundarySeamSwap_apply_leftDart RS keep
          leftCrossing rightCrossing hleftCrosses hrightCrosses
          hleftInjective hrightInjective hcover hdisjoint left]
      rw [retainedCappedAlpha_apply_boundary RS keep _
        ((orderedCutSeamMatching RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective
          left).1.2)]
    · simp only [parts, orderedCutMatchedSeamData,
        MatchedSeam.Data.alpha_right,
        retainedDartEquivMatchedParts_symm_right,
        retainedDartEquivMatchedParts_symm_left,
        Equiv.symm_apply_apply]
      change ((orderedCutSeamMatching RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective).symm
            right).1.1 =
        retainedCappedAlpha RS keep
          (extendBoundaryPerm RS keep seam right.1.1)
      rw [extendBoundaryPerm_apply_boundary]
      rw [show seam right.1 =
          ((orderedCutSeamMatching RS keep leftCrossing rightCrossing
            hleftCrosses hrightCrosses hleftInjective hrightInjective).symm
              right).1 from
        orderedBoundarySeamSwap_apply_rightDart RS keep
          leftCrossing rightCrossing hleftCrosses hrightCrosses
          hleftInjective hrightInjective hcover hdisjoint right]
      rw [retainedCappedAlpha_apply_boundary RS keep _
        (((orderedCutSeamMatching RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective).symm
          right).1.2)]

/-- Consequently the entire splice face walk is the retained capped face walk
with the boundary matching inserted, transported to the three-part carrier. -/
theorem orderedCutSplicePhi_eq_rewiredRetainedCappedFacePerm
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCrossing rightCrossing : Fin n → E)
    (hleftCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = leftCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hrightCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = rightCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing ∨
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (houter : keep (RS.vertOf RS.outer)) :
    orderedCutSplicePhi RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter =
      (retainedDartEquivMatchedParts RS keep
        (orderedCut leftCrossing) (orderedCut rightCrossing)
        hcover hdisjoint).permCongr
        (retainedCappedFacePerm RS keep *
          extendBoundaryPerm RS keep
            (orderedBoundarySeamSwap RS keep leftCrossing rightCrossing
              hleftCrosses hrightCrosses hleftInjective hrightInjective
              hcover hdisjoint)) := by
  rw [orderedCutSplicePhi,
    orderedCutSpliceAlpha_eq_rewiredRetainedCappedAlpha RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter]
  apply Equiv.ext
  intro dart
  simp [orderedCutMatchedSeamData, matchedPartsRho,
    retainedCappedFacePerm,
    Equiv.Perm.mul_apply, Equiv.permCongr_apply]

/-- Rewiring the capped retained map composes its computed boundary return
order by the seam matching. -/
theorem nextHitPerm_rewiredRetainedCappedFacePerm
    (RS : RotationSystem V E) (keep : V → Prop)
    (matching : Equiv.Perm (BoundaryDart RS keep)) :
    nextHitPerm
        (retainedCappedFacePerm RS keep *
          extendBoundaryPerm RS keep matching)
        (fun dart => ¬ keep (RS.vertOf (RS.alpha dart.1))) =
      retainedRegionBoundarySuccessor RS keep * matching := by
  classical
  change nextHitPerm
      (retainedCappedFacePerm RS keep *
        Equiv.Perm.ofSubtype matching)
      (fun dart => ¬ keep (RS.vertOf (RS.alpha dart.1))) = _
  exact nextHitPerm_mul_ofSubtype
    (retainedCappedFacePerm RS keep)
    (fun dart => ¬ keep (RS.vertOf (RS.alpha dart.1))) matching

/-- The actual splice face-return successor is computed entirely from the
retained capped boundary order followed by the ordered seam swap. -/
theorem actualOrderedCutFaceReturnSuccessor_eq_retainedBoundarySuccessor
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCrossing rightCrossing : Fin n → E)
    (hleftCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = leftCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hrightCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = rightCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing ∨
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (houter : keep (RS.vertOf RS.outer)) :
    actualOrderedCutFaceReturnSuccessor RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter =
      (orderedRetainedBoundaryPositionEquiv RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint).symm.permCongr
        (retainedRegionBoundarySuccessor RS keep *
          orderedBoundarySeamSwap RS keep leftCrossing rightCrossing
            hleftCrosses hrightCrosses hleftInjective hrightInjective
            hcover hdisjoint) := by
  classical
  let parts := retainedDartEquivMatchedParts RS keep
    (orderedCut leftCrossing) (orderedCut rightCrossing)
    hcover hdisjoint
  let matching := orderedBoundarySeamSwap RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint
  let rewired := retainedCappedFacePerm RS keep *
    extendBoundaryPerm RS keep matching
  let boundaryToSeam := retainedBoundaryEquivSeamDart RS keep
    (orderedCut leftCrossing) (orderedCut rightCrossing)
    hcover hdisjoint
  let positionToBoundary := orderedRetainedBoundaryPositionEquiv RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint
  let positionToSeam := orderedSeamPositionEquiv RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective
  have hphi : orderedCutSplicePhi RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter = parts.permCongr rewired :=
    orderedCutSplicePhi_eq_rewiredRetainedCappedFacePerm RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
  have hreturns : nextHitPerm (parts.permCongr rewired) IsSeamDart =
      boundaryToSeam.permCongr
        (retainedRegionBoundarySuccessor RS keep * matching) := by
    rw [nextHitPerm_permCongr parts rewired
      (fun dart => ¬ keep (RS.vertOf (RS.alpha dart.1))) IsSeamDart
      (retainedBoundary_iff_isSeamDart_parts RS keep
        (orderedCut leftCrossing) (orderedCut rightCrossing)
        hcover hdisjoint)]
    rw [← retainedBoundaryEquivSeamDart_eq_subtypeEquiv_parts RS keep
      (orderedCut leftCrossing) (orderedCut rightCrossing)
      hcover hdisjoint]
    exact congrArg boundaryToSeam.permCongr
      (nextHitPerm_rewiredRetainedCappedFacePerm RS keep matching)
  have henumeration : positionToBoundary.trans boundaryToSeam =
      positionToSeam :=
    orderedRetainedBoundaryPositionEquiv_trans_seam RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint
  rw [actualOrderedCutFaceReturnSuccessor, hphi, hreturns]
  change positionToSeam.symm.permCongr
      (boundaryToSeam.permCongr
        (retainedRegionBoundarySuccessor RS keep * matching)) =
    positionToBoundary.symm.permCongr
      (retainedRegionBoundarySuccessor RS keep * matching)
  rw [← henumeration]
  apply Equiv.ext
  intro position
  simp [Equiv.permCongr_apply]

end

end GoertzelV24RetainedRegionBoundaryOrder

end Mettapedia.GraphTheory.FourColor
