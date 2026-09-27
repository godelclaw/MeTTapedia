import Mettapedia.GraphTheory.FourColor.GoertzelV24SeamFaceArc
import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorSpliceObservables

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SeamFaceArcPartition

open GoertzelV24SeamFaceArc
open GoertzelV24CorridorSpliceObservables
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

noncomputable instance hitPointFintype
    {A : Type*} [Fintype A] (hit : A → Prop) :
    Fintype { point // hit point } :=
  Fintype.ofFinite { point // hit point }

/-- Positions in every canonical return arc, indexed by their marked initial
point. -/
abbrev AllFirstHitArcPositions
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) :=
  Σ root : { point // hit point },
    Fin (firstPositiveHitTime perm hit root.1 root.2)

/-- Forget an arc index and return its actual permutation-orbit point. -/
def allFirstHitArcPoint
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) :
    AllFirstHitArcPositions perm hit → A
  | ⟨root, step⟩ => (perm ^ step.val) root.1

/-- Canonical return arcs based at distinct marked points are disjoint. If two
arc positions coincided, cancelling the shorter common prefix would either
identify the roots or exhibit a forbidden earlier marked point. -/
theorem allFirstHitArcPoint_injective
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) :
    Function.Injective (allFirstHitArcPoint perm hit) := by
  rintro ⟨firstRoot, firstStep⟩ ⟨secondRoot, secondStep⟩ heq
  have rootsEqOfLe (hle : firstStep.val ≤ secondStep.val) :
      firstRoot = secondRoot := by
    have hfactor :
        (perm ^ secondStep.val) secondRoot.1 =
          (perm ^ firstStep.val)
            ((perm ^ (secondStep.val - firstStep.val)) secondRoot.1) := by
      calc
        (perm ^ secondStep.val) secondRoot.1 =
            (perm ^ (firstStep.val +
              (secondStep.val - firstStep.val))) secondRoot.1 := by
          rw [Nat.add_sub_of_le hle]
        _ = (perm ^ firstStep.val)
            ((perm ^ (secondStep.val - firstStep.val)) secondRoot.1) := by
          rw [pow_add, Equiv.Perm.mul_apply]
    have hrootPower : firstRoot.1 =
        (perm ^ (secondStep.val - firstStep.val)) secondRoot.1 :=
      (perm ^ firstStep.val).injective (heq.trans hfactor)
    by_cases hsteps : firstStep.val = secondStep.val
    · apply Subtype.ext
      have hzero : secondStep.val - firstStep.val = 0 := by omega
      simpa [hzero] using hrootPower
    · have hdiffPos : 0 < secondStep.val - firstStep.val := by omega
      have hdiffLt : secondStep.val - firstStep.val <
          firstPositiveHitTime perm hit secondRoot.1 secondRoot.2 := by
        have := secondStep.isLt
        omega
      exact False.elim
        ((not_hit_before_firstPositiveHitTime perm hit secondRoot.1
          secondRoot.2 hdiffPos hdiffLt) (hrootPower ▸ firstRoot.2))
  have hroots : firstRoot = secondRoot := by
    rcases le_total firstStep.val secondStep.val with hle | hge
    · exact rootsEqOfLe hle
    · exact (by
        have reverseEq :
            allFirstHitArcPoint perm hit ⟨secondRoot, secondStep⟩ =
              allFirstHitArcPoint perm hit ⟨firstRoot, firstStep⟩ := heq.symm
        have reverseRootsEqOfLe : secondRoot = firstRoot := by
          have hfactor :
              (perm ^ firstStep.val) firstRoot.1 =
                (perm ^ secondStep.val)
                  ((perm ^ (firstStep.val - secondStep.val)) firstRoot.1) := by
            calc
              (perm ^ firstStep.val) firstRoot.1 =
                  (perm ^ (secondStep.val +
                    (firstStep.val - secondStep.val))) firstRoot.1 := by
                rw [Nat.add_sub_of_le hge]
              _ = (perm ^ secondStep.val)
                  ((perm ^ (firstStep.val - secondStep.val)) firstRoot.1) := by
                rw [pow_add, Equiv.Perm.mul_apply]
          have hrootPower : secondRoot.1 =
              (perm ^ (firstStep.val - secondStep.val)) firstRoot.1 :=
            (perm ^ secondStep.val).injective (reverseEq.trans hfactor)
          by_cases hsteps : secondStep.val = firstStep.val
          · apply Subtype.ext
            have hzero : firstStep.val - secondStep.val = 0 := by omega
            simpa [hzero] using hrootPower
          · have hdiffPos : 0 < firstStep.val - secondStep.val := by omega
            have hdiffLt : firstStep.val - secondStep.val <
                firstPositiveHitTime perm hit firstRoot.1 firstRoot.2 := by
              have := firstStep.isLt
              omega
            exact False.elim
              ((not_hit_before_firstPositiveHitTime perm hit firstRoot.1
                firstRoot.2 hdiffPos hdiffLt)
                (hrootPower ▸ secondRoot.2))
        exact reverseRootsEqOfLe.symm)
  subst secondRoot
  have hsteps : firstStep = secondStep :=
    pow_injective_before_firstPositiveHitTime perm hit firstRoot.1
      firstRoot.2 heq
  subst secondStep
  rfl

/-- The union of all canonical marked-to-marked arcs. -/
def allFirstHitArcDarts
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) : Finset A :=
  Finset.univ.image (allFirstHitArcPoint perm hit)

/-- Because the canonical arcs are pairwise disjoint and internally simple,
their union cardinality is the sum of their computed return times. -/
theorem card_allFirstHitArcDarts
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) :
    (allFirstHitArcDarts perm hit).card =
      ∑ root : { point // hit point },
        firstPositiveHitTime perm hit root.1 root.2 := by
  rw [allFirstHitArcDarts,
    Finset.card_image_of_injective _
      (allFirstHitArcPoint_injective perm hit)]
  rw [Finset.card_univ]
  change Fintype.card
      (Σ root : { point // hit point },
        Fin (firstPositiveHitTime perm hit root.1 root.2)) = _
  rw [Fintype.card_sigma]
  simp

/-- Every point covered by a canonical arc belongs to the permutation cycle
of its marked root. -/
theorem mem_allFirstHitArcDarts_sameCycle
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) {point : A}
    (hpoint : point ∈ allFirstHitArcDarts perm hit) :
    ∃ root : { marked // hit marked },
      perm.SameCycle root.1 point := by
  rw [allFirstHitArcDarts] at hpoint
  rcases Finset.mem_image.1 hpoint with ⟨position, _, hposition⟩
  refine ⟨position.1, ?_⟩
  rw [← hposition]
  exact (Equiv.Perm.sameCycle_pow_right).2
    (Equiv.Perm.SameCycle.refl perm position.1.1)

/-- A point whose permutation cycle contains a marked point reaches a marked
point after finitely many backward steps. -/
theorem exists_backward_pow_hit_of_cycle_meets
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) (point : A)
    (hmeets : ∃ root, hit root ∧ perm.SameCycle root point) :
    ∃ step : Nat, hit (((perm⁻¹) ^ step) point) := by
  rcases hmeets with ⟨root, hroot, hcycle⟩
  have hbackwardCycle : (perm⁻¹).SameCycle point root := by
    rw [Equiv.Perm.sameCycle_inv]
    exact hcycle.symm
  rcases hbackwardCycle.exists_nat_pow_eq with ⟨step, hstep⟩
  exact ⟨step, hstep ▸ hroot⟩

/-- The nearest marked point encountered while traversing backward from a
point on a marked cycle. -/
def firstBackwardHitTime
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) (point : A)
    (hmeets : ∃ root, hit root ∧ perm.SameCycle root point) : Nat := by
  classical
  exact Nat.find (exists_backward_pow_hit_of_cycle_meets
    perm hit point hmeets)

theorem firstBackwardHitTime_hits
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) (point : A)
    (hmeets : ∃ root, hit root ∧ perm.SameCycle root point) :
    hit (((perm⁻¹) ^ firstBackwardHitTime perm hit point hmeets) point) := by
  classical
  exact Nat.find_spec
    (exists_backward_pow_hit_of_cycle_meets perm hit point hmeets)

theorem not_hit_before_firstBackwardHitTime
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) (point : A)
    (hmeets : ∃ root, hit root ∧ perm.SameCycle root point)
    {step : Nat}
    (hstepLt : step < firstBackwardHitTime perm hit point hmeets) :
    ¬ hit (((perm⁻¹) ^ step) point) := by
  classical
  intro hhit
  have hminimal : firstBackwardHitTime perm hit point hmeets ≤ step := by
    unfold firstBackwardHitTime
    exact Nat.find_min'
      (exists_backward_pow_hit_of_cycle_meets perm hit point hmeets) hhit
  omega

/-- The actual marked predecessor selected by the backward search. -/
def previousHit
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) (point : A)
    (hmeets : ∃ root, hit root ∧ perm.SameCycle root point) :
    { root // hit root } :=
  ⟨((perm⁻¹) ^ firstBackwardHitTime perm hit point hmeets) point,
    firstBackwardHitTime_hits perm hit point hmeets⟩

theorem pow_apply_symm_pow_apply
    {A : Type*} (perm : Equiv.Perm A) (step : Nat) (point : A) :
    (perm ^ step) (((perm⁻¹) ^ step) point) = point := by
  rw [inv_pow]
  exact (perm ^ step).apply_symm_apply point

theorem symm_pow_apply_pow_apply
    {A : Type*} (perm : Equiv.Perm A) (step : Nat) (point : A) :
    ((perm⁻¹) ^ step) ((perm ^ step) point) = point := by
  rw [inv_pow]
  exact (perm ^ step).symm_apply_apply point

theorem point_eq_pow_previousHit
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) (point : A)
    (hmeets : ∃ root, hit root ∧ perm.SameCycle root point) :
    (perm ^ firstBackwardHitTime perm hit point hmeets)
      (previousHit perm hit point hmeets).1 = point :=
  pow_apply_symm_pow_apply perm
    (firstBackwardHitTime perm hit point hmeets) point

/-- The backward distance to the previous marked point is strictly shorter
than that point's next positive return time. -/
theorem firstBackwardHitTime_lt_next_return
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) (point : A)
    (hmeets : ∃ root, hit root ∧ perm.SameCycle root point) :
    firstBackwardHitTime perm hit point hmeets <
      firstPositiveHitTime perm hit
        (previousHit perm hit point hmeets).1
        (previousHit perm hit point hmeets).2 := by
  let backwardTime := firstBackwardHitTime perm hit point hmeets
  let previous := previousHit perm hit point hmeets
  let returnTime := firstPositiveHitTime perm hit previous.1 previous.2
  by_contra hnot
  have hreturnLe : returnTime ≤ backwardTime := Nat.le_of_not_gt hnot
  have hreturnPos : 0 < returnTime :=
    firstPositiveHitTime_pos perm hit previous.1 previous.2
  have hreturnHit : hit ((perm ^ returnTime) previous.1) :=
    firstPositiveHitTime_hits perm hit previous.1 previous.2
  let remaining := backwardTime - returnTime
  have hremainingLt : remaining < backwardTime := by
    dsimp only [remaining]
    omega
  have hpointFactor : point =
      (perm ^ remaining) ((perm ^ returnTime) previous.1) := by
    have hpointEq : (perm ^ backwardTime) previous.1 = point := by
      simpa only [backwardTime, previous] using
        point_eq_pow_previousHit perm hit point hmeets
    calc
      point = (perm ^ backwardTime) previous.1 := hpointEq.symm
      _ = (perm ^ (remaining + returnTime)) previous.1 := by
        rw [Nat.sub_add_cancel hreturnLe]
      _ = (perm ^ remaining) ((perm ^ returnTime) previous.1) := by
        rw [pow_add, Equiv.Perm.mul_apply]
  have hbackwardPoint :
      ((perm⁻¹) ^ remaining) point =
        (perm ^ returnTime) previous.1 := by
    calc
      ((perm⁻¹) ^ remaining) point =
          ((perm⁻¹) ^ remaining)
            ((perm ^ remaining) ((perm ^ returnTime) previous.1)) := by
        rw [hpointFactor]
      _ = (perm ^ returnTime) previous.1 :=
        symm_pow_apply_pow_apply perm remaining _
  exact (not_hit_before_firstBackwardHitTime perm hit point hmeets
    hremainingLt) (hbackwardPoint ▸ hreturnHit)

/-- The canonical return arcs cover every point on every permutation cycle
that meets the marked set. -/
theorem mem_allFirstHitArcDarts_of_cycle_meets
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) (point : A)
    (hmeets : ∃ root, hit root ∧ perm.SameCycle root point) :
    point ∈ allFirstHitArcDarts perm hit := by
  rw [allFirstHitArcDarts]
  let previous := previousHit perm hit point hmeets
  let step : Fin (firstPositiveHitTime perm hit previous.1 previous.2) :=
    ⟨firstBackwardHitTime perm hit point hmeets,
      firstBackwardHitTime_lt_next_return perm hit point hmeets⟩
  refine Finset.mem_image.2
    ⟨⟨previous, step⟩, Finset.mem_univ _, ?_⟩
  exact point_eq_pow_previousHit perm hit point hmeets

/-- Exact characterization of the canonical arc union. -/
theorem mem_allFirstHitArcDarts_iff_cycle_meets
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) (point : A) :
    point ∈ allFirstHitArcDarts perm hit ↔
      ∃ root, hit root ∧ perm.SameCycle root point := by
  constructor
  · intro hpoint
    rcases mem_allFirstHitArcDarts_sameCycle perm hit hpoint with
      ⟨root, hcycle⟩
    exact ⟨root.1, root.2, hcycle⟩
  · exact mem_allFirstHitArcDarts_of_cycle_meets perm hit point

/-- On a cycle containing a marked root, the complete cycle length is exactly
the sum of the canonical return-arc lengths based at all marked points of that
cycle. This is the structural face-length formula needed by the splice. -/
theorem card_sameCycle_eq_sum_firstPositiveHitTime
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) (root : A)
    (hroot : hit root) :
    (Finset.univ.filter fun point => perm.SameCycle root point).card =
      ∑ marked : { point // hit point ∧ perm.SameCycle root point },
        firstPositiveHitTime perm
          (fun point => hit point ∧ perm.SameCycle root point)
          marked.1 marked.2 := by
  let faceHit := fun point => hit point ∧ perm.SameCycle root point
  have hcarrier : allFirstHitArcDarts perm faceHit =
      Finset.univ.filter fun point => perm.SameCycle root point := by
    ext point
    rw [mem_allFirstHitArcDarts_iff_cycle_meets]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨marked, ⟨_, hrootMarked⟩, hmarkedPoint⟩
      exact hrootMarked.trans hmarkedPoint
    · intro hrootPoint
      exact ⟨root,
        ⟨hroot, Equiv.Perm.SameCycle.refl perm root⟩,
        hrootPoint⟩
  rw [← hcarrier, card_allFirstHitArcDarts]

/-- Two marked predicates that agree on every forward power of a root have
the same least positive return time. -/
theorem firstPositiveHitTime_eq_of_iff_pow_hit
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (leftHit rightHit : A → Prop) (root : A)
    (hleftRoot : leftHit root) (hrightRoot : rightHit root)
    (hiff : ∀ step, leftHit ((perm ^ step) root) ↔
      rightHit ((perm ^ step) root)) :
    firstPositiveHitTime perm leftHit root hleftRoot =
      firstPositiveHitTime perm rightHit root hrightRoot := by
  classical
  have hrightLe : firstPositiveHitTime perm rightHit root hrightRoot ≤
      firstPositiveHitTime perm leftHit root hleftRoot := by
    unfold firstPositiveHitTime
    apply Nat.find_min'
    exact ⟨firstPositiveHitTime_pos perm leftHit root hleftRoot,
      (hiff _).1
        (firstPositiveHitTime_hits perm leftHit root hleftRoot)⟩
  have hleftLe : firstPositiveHitTime perm leftHit root hleftRoot ≤
      firstPositiveHitTime perm rightHit root hrightRoot := by
    unfold firstPositiveHitTime
    apply Nat.find_min'
    exact ⟨firstPositiveHitTime_pos perm rightHit root hrightRoot,
      (hiff _).2
        (firstPositiveHitTime_hits perm rightHit root hrightRoot)⟩
  omega

/-- Restricting the seam predicate to one known face cycle does not change
the computed return time of a seam dart on that face. -/
theorem firstPositiveHitTime_faceHit_eq
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) (root : A)
    (marked : { point // hit point ∧ perm.SameCycle root point }) :
    firstPositiveHitTime perm
        (fun point => hit point ∧ perm.SameCycle root point)
        marked.1 marked.2 =
      firstPositiveHitTime perm hit marked.1 marked.2.1 := by
  apply firstPositiveHitTime_eq_of_iff_pow_hit perm
  intro step
  constructor
  · exact fun hpoint => hpoint.1
  · intro hpoint
    refine ⟨hpoint, marked.2.2.trans ?_⟩
    exact (Equiv.Perm.sameCycle_pow_right).2
      (Equiv.Perm.SameCycle.refl perm marked.1)

/-- Equivalent face-length formula using only the globally computed marked
return time at each marked dart. This is the form used by the finite profile. -/
theorem card_sameCycle_eq_sum_returnTimes
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) (root : A)
    (hroot : hit root) :
    (Finset.univ.filter fun point => perm.SameCycle root point).card =
      ∑ marked : { point // hit point ∧ perm.SameCycle root point },
        firstPositiveHitTime perm hit marked.1 marked.2.1 := by
  rw [card_sameCycle_eq_sum_firstPositiveHitTime perm hit root hroot]
  apply Finset.sum_congr rfl
  intro marked _
  exact firstPositiveHitTime_faceHit_eq perm hit root marked

/-- The return-arc length saturated at five, represented in `Fin 6`. -/
def cappedReturnTime
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop)
    (marked : { point // hit point }) : Fin 6 :=
  ⟨min (firstPositiveHitTime perm hit marked.1 marked.2) 5, by omega⟩

@[simp]
theorem cappedReturnTime_val
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop)
    (marked : { point // hit point }) :
    (cappedReturnTime perm hit marked).val =
      min (firstPositiveHitTime perm hit marked.1 marked.2) 5 :=
  rfl

/-- On a marked face cycle, the sum of cap-at-five return-arc observations
decides exactly whether the complete face length is at least five. -/
theorem five_le_sameCycle_card_iff_sum_cappedReturnTimes
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) (root : A)
    (hroot : hit root) :
    5 ≤ (Finset.univ.filter fun point =>
        perm.SameCycle root point).card ↔
      5 ≤ ∑ marked : { point //
          hit point ∧ perm.SameCycle root point },
        (cappedReturnTime perm hit
          (⟨marked.1, marked.2.1⟩ : { point // hit point })).val := by
  rw [card_sameCycle_eq_sum_returnTimes perm hit root hroot]
  let markedPoints := { point // hit point ∧ perm.SameCycle root point }
  let returnTime : markedPoints → Nat := fun marked =>
    firstPositiveHitTime perm hit marked.1 marked.2.1
  let cappedTime : markedPoints → Nat := fun marked =>
    (cappedReturnTime perm hit
      (⟨marked.1, marked.2.1⟩ : { point // hit point })).val
  have hthreshold := threshold_le_sum_add_iff_of_pointwise_min_eq
    (Finset.univ : Finset markedPoints) returnTime cappedTime 0 5 (by
      intro marked _
      dsimp only [returnTime, cappedTime, cappedReturnTime]
      omega)
  simpa only [Finset.sum_const_zero, Nat.add_zero,
    returnTime, cappedTime] using hthreshold

/-- For a seam-touching face of the actual ordered-cut rotation system, its
`faceOrbit` cardinality is exactly the sum of the canonical seam-to-seam arc
lengths based at every seam dart on that face. -/
theorem orderedCutRotationSystem_seam_faceOrbit_card_eq_sum_arcLengths
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
    (root : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep (orderedCut leftCrossing))
      (BoundaryDartOn RS keep (orderedCut rightCrossing)))
    (hroot : IsSeamDart root) :
    let splicePhi := orderedCutSplicePhi RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
    ((orderedCutRotationSystem RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter hseamEndpoints).faceOrbit root).card =
      ∑ marked : { point //
          IsSeamDart point ∧ splicePhi.SameCycle root point },
        firstPositiveHitTime splicePhi IsSeamDart
          marked.1 marked.2.1 := by
  dsimp only
  change (Finset.univ.filter fun point =>
    (orderedCutSplicePhi RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter).SameCycle root point).card = _
  exact card_sameCycle_eq_sum_returnTimes
    (orderedCutSplicePhi RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter)
    IsSeamDart root hroot

/-- The cap-at-five observations of canonical seam arcs decide exactly the
minimum-face-size test on every seam-touching face of the constructed
rotation system. -/
theorem orderedCutRotationSystem_five_le_seam_faceOrbit_iff_sum_capped
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
    (root : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep (orderedCut leftCrossing))
      (BoundaryDartOn RS keep (orderedCut rightCrossing)))
    (hroot : IsSeamDart root) :
    let splicePhi := orderedCutSplicePhi RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
    5 ≤ ((orderedCutRotationSystem RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter hseamEndpoints).faceOrbit root).card ↔
      5 ≤ ∑ marked : { point //
          IsSeamDart point ∧ splicePhi.SameCycle root point },
        (cappedReturnTime splicePhi IsSeamDart
          (⟨marked.1, marked.2.1⟩ : { point // IsSeamDart point })).val := by
  dsimp only
  change 5 ≤ (Finset.univ.filter fun point =>
    (orderedCutSplicePhi RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter).SameCycle root point).card ↔ _
  exact five_le_sameCycle_card_iff_sum_cappedReturnTimes
    (orderedCutSplicePhi RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter)
    IsSeamDart root hroot

end

end GoertzelV24SeamFaceArcPartition

end Mettapedia.GraphTheory.FourColor
