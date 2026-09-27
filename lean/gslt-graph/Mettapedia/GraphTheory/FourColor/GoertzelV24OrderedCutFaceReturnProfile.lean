import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundaryFaceReturnProfile

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrderedCutFaceReturnProfile

open GoertzelV24BoundaryFaceReturnProfile
open GoertzelV24OrderedCutFaceOrbit
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor
open GoertzelV24SeamFaceArc
open GoertzelV24SeamFaceArcPartition

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The next-marked-point map is injective. Two distinct marked roots cannot
have the same next marked endpoint without one occurring strictly inside the
other's canonical return arc. -/
theorem nextHit_injective
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) :
    Function.Injective (nextHit perm hit) := by
  intro first second hnext
  let returnTime := fun root : { point // hit point } =>
    firstPositiveHitTime perm hit root.1 root.2
  have roots_eq_of_le
      (left right : { point // hit point })
      (hle : returnTime left ≤ returnTime right)
      (hnextEq : nextHit perm hit left = nextHit perm hit right) :
      left = right := by
    have hpowers :
        (perm ^ returnTime left) left.1 =
          (perm ^ returnTime right) right.1 :=
      congrArg Subtype.val hnextEq
    have hfactor :
        (perm ^ returnTime right) right.1 =
          (perm ^ returnTime left)
            ((perm ^ (returnTime right - returnTime left)) right.1) := by
      calc
        (perm ^ returnTime right) right.1 =
            (perm ^ (returnTime left +
              (returnTime right - returnTime left))) right.1 := by
          rw [Nat.add_sub_of_le hle]
        _ = (perm ^ returnTime left)
            ((perm ^ (returnTime right - returnTime left)) right.1) := by
          rw [pow_add, Equiv.Perm.mul_apply]
    have hrootPower : left.1 =
        (perm ^ (returnTime right - returnTime left)) right.1 :=
      (perm ^ returnTime left).injective (hpowers.trans hfactor)
    by_cases hzero : returnTime right - returnTime left = 0
    · apply Subtype.ext
      simpa [hzero] using hrootPower
    · have hdiffPos : 0 < returnTime right - returnTime left :=
        Nat.pos_of_ne_zero hzero
      have hleftPos : 0 < returnTime left :=
        firstPositiveHitTime_pos perm hit left.1 left.2
      have hdiffLt : returnTime right - returnTime left < returnTime right := by
        omega
      exact False.elim
        ((not_hit_before_firstPositiveHitTime perm hit right.1 right.2
          hdiffPos hdiffLt) (hrootPower ▸ left.2))
  rcases le_total (returnTime first) (returnTime second) with hle | hge
  · exact roots_eq_of_le first second hle hnext
  · exact (roots_eq_of_le second first hge hnext.symm).symm

/-- The cyclic successor permutation on all marked points. -/
def nextHitPerm
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) :
    Equiv.Perm { point // hit point } :=
  Equiv.ofBijective (nextHit perm hit)
    ⟨nextHit_injective perm hit,
      Finite.surjective_of_injective (nextHit_injective perm hit)⟩

@[simp]
theorem nextHitPerm_apply
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop)
    (root : { point // hit point }) :
    nextHitPerm perm hit root = nextHit perm hit root :=
  rfl

/-- Iterating the marked successor never leaves the ambient permutation
cycle of its starting point. -/
theorem nextHitPerm_pow_sameCycle
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop)
    (root : { point // hit point }) (step : Nat) :
    perm.SameCycle root.1 ((nextHitPerm perm hit ^ step) root).1 := by
  induction step generalizing root with
  | zero =>
      simp only [pow_zero]
      exact Equiv.Perm.SameCycle.refl perm root.1
  | succ step ih =>
      rw [pow_succ, Equiv.Perm.mul_apply]
      exact (nextHit_sameCycle perm hit root).trans
        (ih (nextHitPerm perm hit root))

/-- Any two marked points on one ambient permutation cycle are connected by
iterations of the next-marked-point permutation. -/
theorem exists_nextHitPerm_pow_eq_of_sameCycle
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop)
    (first second : { point // hit point })
    (hcycle : perm.SameCycle first.1 second.1) :
    ∃ step : Nat, (nextHitPerm perm hit ^ step) first = second := by
  rcases hcycle.exists_nat_pow_eq with ⟨distance, hdistance⟩
  have reach : ∀ distance : Nat,
      ∀ first second : { point // hit point },
      (perm ^ distance) first.1 = second.1 →
      ∃ step : Nat, (nextHitPerm perm hit ^ step) first = second := by
    intro distance
    induction distance using Nat.strong_induction_on with
    | h distance ih =>
        intro left right hpower
        by_cases hzero : distance = 0
        · subst distance
          refine ⟨0, ?_⟩
          simp only [pow_zero] at hpower ⊢
          exact Subtype.ext hpower
        · have hdistancePos : 0 < distance := Nat.pos_of_ne_zero hzero
          let returnTime := firstPositiveHitTime perm hit left.1 left.2
          have hrightHit : hit ((perm ^ distance) left.1) := hpower ▸ right.2
          have hreturnLe : returnTime ≤ distance :=
            firstPositiveHitTime_le_of_hit perm hit left.1 left.2
              hdistancePos hrightHit
          by_cases heq : returnTime = distance
          · refine ⟨1, ?_⟩
            apply Subtype.ext
            simpa [nextHitPerm_apply, nextHit, returnTime, heq] using hpower
          · have hreturnLt : returnTime < distance :=
              lt_of_le_of_ne hreturnLe heq
            let following := nextHit perm hit left
            have hremaining :
                (perm ^ (distance - returnTime)) following.1 = right.1 := by
              calc
                (perm ^ (distance - returnTime)) following.1 =
                    (perm ^ (distance - returnTime))
                      ((perm ^ returnTime) left.1) := by
                  rfl
                _ = (perm ^ distance) left.1 := by
                  rw [← Equiv.Perm.mul_apply, ← pow_add,
                    Nat.sub_add_cancel hreturnLe]
                _ = right.1 := hpower
            have hreturnPos : 0 < returnTime :=
              firstPositiveHitTime_pos perm hit left.1 left.2
            obtain ⟨step, hstep⟩ := ih (distance - returnTime)
              (by omega) following right hremaining
            refine ⟨step + 1, ?_⟩
            rw [pow_add, Equiv.Perm.mul_apply, pow_one,
              nextHitPerm_apply, hstep]
  exact reach distance first second hdistance

/-- The cycles of the next-hit permutation are exactly the ambient cycles
restricted to marked points. -/
theorem nextHitPerm_sameCycle_iff
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop)
    (first second : { point // hit point }) :
    (nextHitPerm perm hit).SameCycle first second ↔
      perm.SameCycle first.1 second.1 := by
  constructor
  · intro hcycle
    rcases hcycle.exists_nat_pow_eq with ⟨step, hstep⟩
    exact hstep ▸ nextHitPerm_pow_sameCycle perm hit first step
  · intro hcycle
    rcases exists_nextHitPerm_pow_eq_of_sameCycle
      perm hit first second hcycle with ⟨step, hstep⟩
    exact hstep ▸ (Equiv.Perm.sameCycle_pow_right).2
      (Equiv.Perm.SameCycle.refl (nextHitPerm perm hit) first)

/-- Powers of a transported permutation act by transporting the corresponding
power. -/
theorem permCongr_pow_apply
    {A B : Type*} (equiv : A ≃ B) (perm : Equiv.Perm A)
    (point : A) (step : Nat) :
    ((equiv.permCongr perm) ^ step) (equiv point) =
      equiv ((perm ^ step) point) := by
  induction step generalizing point with
  | zero => simp
  | succ step ih =>
      rw [pow_succ, pow_succ, Equiv.Perm.mul_apply,
        Equiv.Perm.mul_apply, Equiv.permCongr_apply, ih]
      simp

/-- Conjugating a finite permutation along an equivalence transports its cycle
relation exactly. -/
theorem permCongr_sameCycle_iff
    {A B : Type*} [Finite A] [Finite B]
    (equiv : A ≃ B) (perm : Equiv.Perm A)
    (first second : A) :
    (equiv.permCongr perm).SameCycle (equiv first) (equiv second) ↔
      perm.SameCycle first second := by
  constructor
  · intro hcycle
    rcases hcycle.exists_nat_pow_eq with ⟨step, hstep⟩
    have hpowers : (perm ^ step) first = second := by
      apply equiv.injective
      rw [← permCongr_pow_apply equiv perm first step]
      exact hstep
    exact hpowers ▸ (Equiv.Perm.sameCycle_pow_right).2
      (Equiv.Perm.SameCycle.refl perm first)
  · intro hcycle
    rcases hcycle.exists_nat_pow_eq with ⟨step, hstep⟩
    have hpowers : ((equiv.permCongr perm) ^ step) (equiv first) =
        equiv second := by
      rw [permCongr_pow_apply, hstep]
    exact hpowers ▸ (Equiv.Perm.sameCycle_pow_right).2
      (Equiv.Perm.SameCycle.refl (equiv.permCongr perm) (equiv first))

/-- The two oriented seam ports at each ordered cut position. -/
abbrev OrderedSeamPosition (n : Nat) := Fin n ⊕ Fin n

/-- The fixed-width face-return state at an ordered pair of cuts. Each port
stores the cap of its outgoing partial face, while one permutation records
the next port reached by following that partial face. -/
structure OrderedCutFaceReturnProfile (n : Nat) where
  arcCap : OrderedSeamPosition n → Fin 6
  faceSuccessor : Equiv.Perm (OrderedSeamPosition n)
  deriving DecidableEq, Fintype

/-- The completed-face relation is computed from the cycles of the stored
local successor rather than carried as an independent field. -/
def OrderedCutFaceReturnProfile.sameFace
    (profile : OrderedCutFaceReturnProfile n)
    (first second : OrderedSeamPosition n) : Bool :=
  decide (profile.faceSuccessor.SameCycle first second)

@[simp]
theorem OrderedCutFaceReturnProfile.sameFace_eq_true_iff
    (profile : OrderedCutFaceReturnProfile n)
    (first second : OrderedSeamPosition n) :
    profile.sameFace first second = true ↔
      profile.faceSuccessor.SameCycle first second := by
  simp [OrderedCutFaceReturnProfile.sameFace]

private def orderedCutFaceReturnProfileEquiv (n : Nat) :
    OrderedCutFaceReturnProfile n ≃
      (OrderedSeamPosition n → Fin 6) ×
        Equiv.Perm (OrderedSeamPosition n) where
  toFun profile := (profile.arcCap, profile.faceSuccessor)
  invFun data := ⟨data.1, data.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact size of the corrected face-return carrier at cut width `n`. -/
theorem card_orderedCutFaceReturnProfile (n : Nat) :
    Fintype.card (OrderedCutFaceReturnProfile n) =
      6 ^ (2 * n) * (2 * n).factorial := by
  rw [Fintype.card_congr (orderedCutFaceReturnProfileEquiv n),
    Fintype.card_prod, Fintype.card_fun, Fintype.card_perm,
    Fintype.card_sum]
  simp only [Fintype.card_fin]
  congr 2 <;> omega

/-- The cap sum of the completed face containing a named port, computed only
from the finite profile. -/
def OrderedCutFaceReturnProfile.faceCapSum
    (profile : OrderedCutFaceReturnProfile n)
    (root : OrderedSeamPosition n) : Nat :=
  ∑ position : { position : OrderedSeamPosition n //
      profile.sameFace root position = true },
    (profile.arcCap position.1).val

/-- The profile-level minimum-face-size test. -/
def OrderedCutFaceReturnProfile.FaceMeetsFive
    (profile : OrderedCutFaceReturnProfile n)
    (root : OrderedSeamPosition n) : Prop :=
  5 ≤ profile.faceCapSum root

theorem OrderedCutFaceReturnProfile.faceMeetsFive_iff_of_eq
    {left right : OrderedCutFaceReturnProfile n} (hprofiles : left = right)
    (root : OrderedSeamPosition n) :
    left.FaceMeetsFive root ↔ right.FaceMeetsFive root := by
  rw [hprofiles]

/-- Seam tags are exactly the disjoint union of the left and right boundary
interfaces. -/
def seamDartEquiv {I L R : Type*} :
    L ⊕ R ≃ { dart : MatchedSeam.Dart I L R // IsSeamDart dart } where
  toFun
    | Sum.inl left => ⟨Sum.inr (Sum.inl left), trivial⟩
    | Sum.inr right => ⟨Sum.inr (Sum.inr right), trivial⟩
  invFun dart := by
    rcases dart with ⟨dart, hdart⟩
    rcases dart with interior | side
    · exact False.elim hdart
    · exact side
  left_inv side := by rcases side with left | right <;> rfl
  right_inv dart := by
    rcases dart with ⟨dart, hdart⟩
    rcases dart with interior | side
    · exact False.elim hdart
    · rcases side with left | right <;> rfl

/-- Ordered positions enumerate every seam dart of the constructed splice. -/
def orderedSeamPositionEquiv
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
    (hrightInjective : Function.Injective rightCrossing) :
    OrderedSeamPosition n ≃
      { dart : MatchedSeam.Dart (InternalDart RS keep)
          (BoundaryDartOn RS keep (orderedCut leftCrossing))
          (BoundaryDartOn RS keep (orderedCut rightCrossing)) //
        IsSeamDart dart } :=
  (Equiv.sumCongr
    (orderedBoundaryDartEquiv RS keep leftCrossing
      hleftCrosses hleftInjective)
    (orderedBoundaryDartEquiv RS keep rightCrossing
      hrightCrosses hrightInjective)).trans seamDartEquiv

/-- The seam dart named by an oriented ordered position. -/
def orderedSeamRoot
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
    (position : OrderedSeamPosition n) :
    MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep (orderedCut leftCrossing))
      (BoundaryDartOn RS keep (orderedCut rightCrossing)) :=
  (orderedSeamPositionEquiv RS keep leftCrossing rightCrossing
    hleftCrosses hrightCrosses hleftInjective hrightInjective position).1

theorem orderedSeamRoot_isSeam
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
    (position : OrderedSeamPosition n) :
    IsSeamDart (orderedSeamRoot RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective position) :=
  (orderedSeamPositionEquiv RS keep leftCrossing rightCrossing
    hleftCrosses hrightCrosses hleftInjective hrightInjective position).2

@[simp]
theorem orderedSeamRoot_left
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
    (step : Fin n) :
    orderedSeamRoot RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        (Sum.inl step) =
      Sum.inr (Sum.inl
        (orderedBoundaryDart RS keep leftCrossing hleftCrosses step)) :=
  rfl

@[simp]
theorem orderedSeamRoot_right
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
    (step : Fin n) :
    orderedSeamRoot RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        (Sum.inr step) =
      Sum.inr (Sum.inr
        (orderedBoundaryDart RS keep rightCrossing hrightCrosses step)) :=
  rfl

/-- The actual next-port permutation, obtained by transporting the canonical
next seam hit back to the fixed ordered-position carrier. -/
def actualOrderedCutFaceReturnSuccessor
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
    Equiv.Perm (OrderedSeamPosition n) :=
  let seamEquiv := orderedSeamPositionEquiv RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective
  seamEquiv.symm.permCongr
    (nextHitPerm
      (orderedCutSplicePhi RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter)
      IsSeamDart)

/-- The cycles of the local ordered-port successor are exactly the completed
face cycles of the constructed splice. -/
theorem actualOrderedCutFaceReturnSuccessor_sameCycle_iff
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
    (houter : keep (RS.vertOf RS.outer))
    (first second : OrderedSeamPosition n) :
    (actualOrderedCutFaceReturnSuccessor RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter).SameCycle
        first second ↔
      (orderedCutSplicePhi RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter).SameCycle
          (orderedSeamRoot RS keep leftCrossing rightCrossing
            hleftCrosses hrightCrosses hleftInjective hrightInjective first)
          (orderedSeamRoot RS keep leftCrossing rightCrossing
            hleftCrosses hrightCrosses hleftInjective hrightInjective second) := by
  let seamEquiv := orderedSeamPositionEquiv RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective
  let splicePhi := orderedCutSplicePhi RS keep leftCrossing rightCrossing
    hleftCrosses hrightCrosses hleftInjective hrightInjective
    hcover hdisjoint houter
  have htransport := permCongr_sameCycle_iff seamEquiv.symm
    (nextHitPerm splicePhi IsSeamDart)
    (seamEquiv first) (seamEquiv second)
  rw [nextHitPerm_sameCycle_iff] at htransport
  simpa [actualOrderedCutFaceReturnSuccessor, seamEquiv, splicePhi,
    orderedSeamRoot] using htransport

/-- The outgoing segment at a left seam port begins through the matched right
boundary dart at the same ordered position. -/
theorem orderedCutSpliceMatchedBoundary_left
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
    (step : Fin n) :
    orderedCutSpliceMatchedBoundary RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective
        (orderedSeamRoot RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective
          (Sum.inl step))
        (orderedSeamRoot_isSeam RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective
          (Sum.inl step)) =
      (orderedBoundaryDart RS keep rightCrossing
        hrightCrosses step).1 := by
  change (orderedCutSeamMatching RS keep leftCrossing rightCrossing
    hleftCrosses hrightCrosses hleftInjective hrightInjective
    (orderedBoundaryDart RS keep leftCrossing hleftCrosses step)).1 = _
  rw [orderedCutSeamMatching_apply]

/-- The outgoing segment at a right seam port begins through the matched left
boundary dart at the same ordered position. -/
theorem orderedCutSpliceMatchedBoundary_right
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
    (step : Fin n) :
    orderedCutSpliceMatchedBoundary RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective
        (orderedSeamRoot RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective
          (Sum.inr step))
        (orderedSeamRoot_isSeam RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective
          (Sum.inr step)) =
      (orderedBoundaryDart RS keep leftCrossing hleftCrosses step).1 := by
  change ((orderedCutSeamMatching RS keep leftCrossing rightCrossing
    hleftCrosses hrightCrosses hleftInjective hrightInjective).symm
    (orderedBoundaryDart RS keep rightCrossing hrightCrosses step)).1 = _
  rw [orderedCutSeamMatching_symm_apply]

/-- The actual fixed-width profile computed from the rotation system. Its
length fields use old-face return times at the opposite matched ports. -/
def actualOrderedCutFaceReturnProfile
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
    OrderedCutFaceReturnProfile n where
  arcCap
    | Sum.inl step => cappedBoundaryPartialFaceLength RS keep
        (orderedBoundaryDart RS keep rightCrossing hrightCrosses step).1
    | Sum.inr step => cappedBoundaryPartialFaceLength RS keep
        (orderedBoundaryDart RS keep leftCrossing hleftCrosses step).1
  faceSuccessor := actualOrderedCutFaceReturnSuccessor RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter

@[simp]
theorem actualOrderedCutFaceReturnProfile_sameFace_eq_true_iff
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
    (houter : keep (RS.vertOf RS.outer))
    (first second : OrderedSeamPosition n) :
    (actualOrderedCutFaceReturnProfile RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter).sameFace
        first second = true ↔
      (orderedCutSplicePhi RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter).SameCycle
          (orderedSeamRoot RS keep leftCrossing rightCrossing
            hleftCrosses hrightCrosses hleftInjective hrightInjective first)
          (orderedSeamRoot RS keep leftCrossing rightCrossing
            hleftCrosses hrightCrosses hleftInjective hrightInjective second) := by
  change decide ((actualOrderedCutFaceReturnSuccessor RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter).SameCycle
      first second) = true ↔ _
  rw [decide_eq_true_eq]
  exact actualOrderedCutFaceReturnSuccessor_sameCycle_iff RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter first second

/-- Every stored port cap is exactly the canonical seam-return cap in the
constructed face permutation. -/
theorem actualOrderedCutFaceReturnProfile_arcCap_eq_cappedReturnTime
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
    (houter : keep (RS.vertOf RS.outer))
    (position : OrderedSeamPosition n) :
    (actualOrderedCutFaceReturnProfile RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter).arcCap
        position =
      cappedReturnTime
        (orderedCutSplicePhi RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective
          hcover hdisjoint houter)
        IsSeamDart
        ⟨orderedSeamRoot RS keep leftCrossing rightCrossing
            hleftCrosses hrightCrosses hleftInjective hrightInjective
            position,
          orderedSeamRoot_isSeam RS keep leftCrossing rightCrossing
            hleftCrosses hrightCrosses hleftInjective hrightInjective
            position⟩ := by
  rcases position with step | step
  · change cappedBoundaryPartialFaceLength RS keep
        (orderedBoundaryDart RS keep rightCrossing hrightCrosses step).1 = _
    rw [← orderedCutSpliceMatchedBoundary_left RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective step]
    exact cappedMatchedBoundaryPartialFaceLength_eq_cappedSpliceReturnTime
      RS keep leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
      (orderedSeamRoot RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        (Sum.inl step))
      (orderedSeamRoot_isSeam RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        (Sum.inl step))
  · change cappedBoundaryPartialFaceLength RS keep
        (orderedBoundaryDart RS keep leftCrossing hleftCrosses step).1 = _
    rw [← orderedCutSpliceMatchedBoundary_right RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective step]
    exact cappedMatchedBoundaryPartialFaceLength_eq_cappedSpliceReturnTime
      RS keep leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
      (orderedSeamRoot RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        (Sum.inr step))
      (orderedSeamRoot_isSeam RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        (Sum.inr step))

/-- Reindex the seam darts on one completed face by their fixed ordered port
positions. -/
def orderedSeamCyclePositionEquiv
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
    (houter : keep (RS.vertOf RS.outer))
    (rootPosition : OrderedSeamPosition n) :
    { point : MatchedSeam.Dart (InternalDart RS keep)
        (BoundaryDartOn RS keep (orderedCut leftCrossing))
        (BoundaryDartOn RS keep (orderedCut rightCrossing)) //
      IsSeamDart point ∧
        (orderedCutSplicePhi RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective
          hcover hdisjoint houter).SameCycle
            (orderedSeamRoot RS keep leftCrossing rightCrossing
              hleftCrosses hrightCrosses hleftInjective hrightInjective
              rootPosition)
            point } ≃
    { position : OrderedSeamPosition n //
      (actualOrderedCutFaceReturnProfile RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter).sameFace
          rootPosition position = true } := by
  let seamEquiv := orderedSeamPositionEquiv RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective
  let splicePhi := orderedCutSplicePhi RS keep leftCrossing rightCrossing
    hleftCrosses hrightCrosses hleftInjective hrightInjective
    hcover hdisjoint houter
  let root := orderedSeamRoot RS keep leftCrossing rightCrossing
    hleftCrosses hrightCrosses hleftInjective hrightInjective rootPosition
  let profile := actualOrderedCutFaceReturnProfile RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter
  let positionToMarked := seamEquiv.subtypeEquiv
    (p := fun position => profile.sameFace rootPosition position = true)
    (q := fun point => splicePhi.SameCycle root point.1) (by
      intro position
      exact actualOrderedCutFaceReturnProfile_sameFace_eq_true_iff
        RS keep leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        rootPosition position)
  exact (positionToMarked.trans
    (Equiv.subtypeSubtypeEquivSubtypeInter IsSeamDart
      (fun point => splicePhi.SameCycle root point))).symm

@[simp]
theorem orderedSeamCyclePositionEquiv_symm_val
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
    (houter : keep (RS.vertOf RS.outer))
    (rootPosition : OrderedSeamPosition n)
    (position : { position : OrderedSeamPosition n //
      (actualOrderedCutFaceReturnProfile RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter).sameFace
          rootPosition position = true }) :
    ((orderedSeamCyclePositionEquiv RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
      rootPosition).symm position).1 =
      orderedSeamRoot RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        position.1 := by
  rfl

/-- The cap sum read from the fixed ordered-port profile is exactly the
canonical cap sum over the seam darts of the selected completed face. -/
theorem sum_actualOrderedCutFaceReturnProfile_arcCaps_eq_sum_cappedReturnTimes
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
    (houter : keep (RS.vertOf RS.outer))
    (rootPosition : OrderedSeamPosition n) :
    let splicePhi := orderedCutSplicePhi RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
    let root := orderedSeamRoot RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective rootPosition
    let profile := actualOrderedCutFaceReturnProfile RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
    (∑ position : { position : OrderedSeamPosition n //
        profile.sameFace rootPosition position = true },
      (profile.arcCap position.1).val) =
      ∑ marked : { point // IsSeamDart point ∧
          splicePhi.SameCycle root point },
        (cappedReturnTime splicePhi IsSeamDart
          (⟨marked.1, marked.2.1⟩ : { point // IsSeamDart point })).val := by
  classical
  dsimp only
  let cycleEquiv := orderedSeamCyclePositionEquiv RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter rootPosition
  refine Fintype.sum_equiv cycleEquiv.symm _ _ ?_
  intro position
  have hcap := actualOrderedCutFaceReturnProfile_arcCap_eq_cappedReturnTime
    RS keep leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter position.1
  simpa [cycleEquiv] using
    congrArg Fin.val hcap

/-- The fixed ordered-port profile decides the minimum-face-size test exactly
for every seam-touching face of the constructed rotation system. -/
theorem orderedCutRotationSystem_five_le_seam_faceOrbit_iff_profile
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
    (houter : keep (RS.vertOf RS.outer))
    (hseamEndpoints : ∀ step,
      RS.vertOf
          (orderedBoundaryDart RS keep leftCrossing
            hleftCrosses step).1.1.1 ≠
        RS.vertOf
          (orderedBoundaryDart RS keep rightCrossing
            hrightCrosses step).1.1.1)
    (rootPosition : OrderedSeamPosition n) :
    let profile := actualOrderedCutFaceReturnProfile RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
    5 ≤ ((orderedCutRotationSystem RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints).faceOrbit
      (orderedSeamRoot RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        rootPosition)).card ↔
      profile.FaceMeetsFive rootPosition := by
  unfold OrderedCutFaceReturnProfile.FaceMeetsFive
  unfold OrderedCutFaceReturnProfile.faceCapSum
  have hface :=
    orderedCutRotationSystem_five_le_seam_faceOrbit_iff_sum_capped
    RS keep leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter
    hseamEndpoints
    (orderedSeamRoot RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      rootPosition)
    (orderedSeamRoot_isSeam RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      rootPosition)
  have hsum :=
    sum_actualOrderedCutFaceReturnProfile_arcCaps_eq_sum_cappedReturnTimes
    RS keep leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter rootPosition
  exact hface.trans (by rw [← hsum])

end

end GoertzelV24OrderedCutFaceReturnProfile

end Mettapedia.GraphTheory.FourColor
