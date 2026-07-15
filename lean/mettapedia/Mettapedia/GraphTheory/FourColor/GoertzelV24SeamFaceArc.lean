import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedCutFaceOrbit

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SeamFaceArc

open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- A finite permutation always returns a marked root to the marked set in a
positive number of steps. -/
theorem exists_positive_pow_hit
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) (root : A)
    (hroot : hit root) :
    ∃ step : Nat, 0 < step ∧ hit ((perm ^ step) root) := by
  refine ⟨orderOf perm, orderOf_pos perm, ?_⟩
  rw [pow_orderOf_eq_one]
  exact hroot

/-- The least positive time at which the orbit of `root` next meets `hit`.
This is computed from the finite permutation rather than stored as arc data. -/
def firstPositiveHitTime
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) (root : A)
    (hroot : hit root) : Nat := by
  classical
  exact Nat.find (exists_positive_pow_hit perm hit root hroot)

theorem firstPositiveHitTime_pos
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) (root : A)
    (hroot : hit root) :
    0 < firstPositiveHitTime perm hit root hroot := by
  classical
  exact (Nat.find_spec
    (exists_positive_pow_hit perm hit root hroot)).1

theorem firstPositiveHitTime_hits
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) (root : A)
    (hroot : hit root) :
    hit ((perm ^ firstPositiveHitTime perm hit root hroot) root) := by
  classical
  exact (Nat.find_spec
    (exists_positive_pow_hit perm hit root hroot)).2

theorem firstPositiveHitTime_le_of_hit
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) (root : A)
    (hroot : hit root) {step : Nat}
    (hstepPos : 0 < step) (hstepHit : hit ((perm ^ step) root)) :
    firstPositiveHitTime perm hit root hroot ≤ step := by
  classical
  unfold firstPositiveHitTime
  exact Nat.find_min' (exists_positive_pow_hit perm hit root hroot)
    ⟨hstepPos, hstepHit⟩

/-- No strict positive prefix of the canonical return arc meets the marked
set. This is the minimality fact that makes the arc canonical. -/
theorem not_hit_before_firstPositiveHitTime
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) (root : A)
    (hroot : hit root) {step : Nat}
    (hstepPos : 0 < step)
    (hstepLt : step < firstPositiveHitTime perm hit root hroot) :
    ¬ hit ((perm ^ step) root) := by
  classical
  intro hhit
  have hminimal : firstPositiveHitTime perm hit root hroot ≤ step := by
    unfold firstPositiveHitTime
    exact Nat.find_min'
      (exists_positive_pow_hit perm hit root hroot) ⟨hstepPos, hhit⟩
  omega

/-- The orbit powers strictly before the first return are pairwise distinct.
Otherwise their difference would give an earlier positive return to `root`,
which itself belongs to the marked set. -/
theorem pow_injective_before_firstPositiveHitTime
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) (root : A)
    (hroot : hit root) :
    Function.Injective (fun step : Fin
      (firstPositiveHitTime perm hit root hroot) =>
        (perm ^ step.val) root) := by
  let returnTime := firstPositiveHitTime perm hit root hroot
  have noCollision : ∀ {first second : Fin returnTime},
      first.val < second.val →
      (perm ^ first.val) root ≠ (perm ^ second.val) root := by
    intro first second hlt heq
    have hle : first.val ≤ second.val := Nat.le_of_lt hlt
    have hfactor :
        (perm ^ second.val) root =
          (perm ^ first.val) ((perm ^ (second.val - first.val)) root) := by
      calc
        (perm ^ second.val) root =
            (perm ^ (first.val + (second.val - first.val))) root := by
          rw [Nat.add_sub_of_le hle]
        _ = (perm ^ first.val)
            ((perm ^ (second.val - first.val)) root) := by
          rw [pow_add, Equiv.Perm.mul_apply]
    have hreturn : root = (perm ^ (second.val - first.val)) root :=
      (perm ^ first.val).injective (heq.trans hfactor)
    have hdiffPos : 0 < second.val - first.val := by omega
    have hdiffLt : second.val - first.val < returnTime := by
      have := second.isLt
      omega
    exact (not_hit_before_firstPositiveHitTime perm hit root hroot
      hdiffPos hdiffLt) (hreturn ▸ hroot)
  intro first second heq
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (noCollision hlt) heq
  · exact (noCollision hgt) heq.symm

/-- The actual dart set of the canonical half-open return arc. -/
def firstHitArcDarts
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) (root : A)
    (hroot : hit root) : Finset A :=
  Finset.univ.image fun step : Fin
    (firstPositiveHitTime perm hit root hroot) =>
      (perm ^ step.val) root

/-- The canonical arc contains exactly its computed return-time number of
distinct darts. -/
theorem card_firstHitArcDarts
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) (root : A)
    (hroot : hit root) :
    (firstHitArcDarts perm hit root hroot).card =
      firstPositiveHitTime perm hit root hroot := by
  rw [firstHitArcDarts, Finset.card_image_of_injective _
    (pow_injective_before_firstPositiveHitTime perm hit root hroot)]
  simp

/-- Every dart of the canonical return arc lies in the complete permutation
cycle of its root. -/
theorem firstHitArcDarts_subset_sameCycle
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) (root : A)
    (hroot : hit root) :
    firstHitArcDarts perm hit root hroot ⊆
      Finset.univ.filter fun point => perm.SameCycle root point := by
  intro point hpoint
  rcases Finset.mem_image.1 hpoint with ⟨step, _, rfl⟩
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
    (Equiv.Perm.sameCycle_pow_right).2
      (Equiv.Perm.SameCycle.refl perm root)⟩

/-- Consequently, the computed seam-arc length never exceeds the complete
face-cycle length. -/
theorem firstPositiveHitTime_le_sameCycle_card
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) (root : A)
    (hroot : hit root) :
    firstPositiveHitTime perm hit root hroot ≤
      (Finset.univ.filter fun point => perm.SameCycle root point).card := by
  rw [← card_firstHitArcDarts perm hit root hroot]
  exact Finset.card_le_card
    (firstHitArcDarts_subset_sameCycle perm hit root hroot)

/-- The endpoint of the canonical return arc as a point of the marked set. -/
def nextHit
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop)
    (root : { point // hit point }) : { point // hit point } :=
  ⟨(perm ^ firstPositiveHitTime perm hit root.1 root.2) root.1,
    firstPositiveHitTime_hits perm hit root.1 root.2⟩

/-- The next marked endpoint stays in the same complete permutation cycle. -/
theorem nextHit_sameCycle
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop)
    (root : { point // hit point }) :
    perm.SameCycle root.1 (nextHit perm hit root).1 := by
  exact (Equiv.Perm.sameCycle_pow_right).2
    (Equiv.Perm.SameCycle.refl perm root.1)

/-- The computed seam predicate on a matched-splice carrier. -/
def IsSeamDart {I L R : Type*} : MatchedSeam.Dart I L R → Prop
  | Sum.inl _ => False
  | Sum.inr _ => True

@[simp]
theorem isSeamDart_interior_iff {I L R : Type*} (dart : I) :
    IsSeamDart (Sum.inl dart : MatchedSeam.Dart I L R) ↔ False :=
  Iff.rfl

@[simp]
theorem isSeamDart_left {I L R : Type*} (dart : L) :
    IsSeamDart (Sum.inr (Sum.inl dart) : MatchedSeam.Dart I L R) :=
  trivial

@[simp]
theorem isSeamDart_right {I L R : Type*} (dart : R) :
    IsSeamDart (Sum.inr (Sum.inr dart) : MatchedSeam.Dart I L R) :=
  trivial

/-- A matched-splice dart outside the computed seam is an explicitly tagged
intact dart. -/
theorem exists_interior_of_not_isSeamDart
    {I L R : Type*} (point : MatchedSeam.Dart I L R)
    (hpoint : ¬ IsSeamDart point) :
    ∃ dart : I, point = Sum.inl dart := by
  rcases point with dart | side
  · exact ⟨dart, rfl⟩
  · exact False.elim (hpoint trivial)

/-- Every strict intermediate point of the canonical seam-to-seam arc is an
actual intact dart of the ordered splice. -/
theorem orderedCutSplicePhi_between_seams_is_interior
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
    (root : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep (orderedCut leftCrossing))
      (BoundaryDartOn RS keep (orderedCut rightCrossing)))
    (hroot : IsSeamDart root) {step : Nat}
    (hstepPos : 0 < step)
    (hstepLt : step < firstPositiveHitTime
      (orderedCutSplicePhi RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter)
      IsSeamDart root hroot) :
    ∃ dart : InternalDart RS keep,
      (orderedCutSplicePhi RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter ^ step) root = Sum.inl dart := by
  apply exists_interior_of_not_isSeamDart
  exact not_hit_before_firstPositiveHitTime
    (orderedCutSplicePhi RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter)
    IsSeamDart root hroot hstepPos hstepLt

/-- Along every strict intermediate point of a canonical seam arc, the new
face successor is exactly the old ambient face successor after forgetting the
splice tags. -/
theorem orderedCutSplicePhi_underlying_step_between_seams
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
    (root : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep (orderedCut leftCrossing))
      (BoundaryDartOn RS keep (orderedCut rightCrossing)))
    (hroot : IsSeamDart root) {step : Nat}
    (hstepPos : 0 < step)
    (hstepLt : step < firstPositiveHitTime
      (orderedCutSplicePhi RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter)
      IsSeamDart root hroot) :
    let splicePhi := orderedCutSplicePhi RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
    let forget := matchedPartUnderlyingDart RS keep
      (orderedCut leftCrossing) (orderedCut rightCrossing)
    forget (splicePhi ((splicePhi ^ step) root)) =
      RS.phi (forget ((splicePhi ^ step) root)) := by
  dsimp only
  rcases orderedCutSplicePhi_between_seams_is_interior RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter
    root hroot hstepPos hstepLt with ⟨dart, hdart⟩
  rw [hdart]
  exact orderedCutSplicePhi_interior_underlying RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter dart

end

end GoertzelV24SeamFaceArc

end Mettapedia.GraphTheory.FourColor
