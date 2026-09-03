import Mettapedia.GraphTheory.FourColor.FiveEdgeCutPentagonCapStructure
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedSpliceFaceCount

/-!
# Face count of the pentagon-capped shore

Faces are counted through the first return of the capped face permutation
to the old retained darts.  Internal darts return in one step; a boundary
dart passes through an incoming cycle dart and the next spoke, returning
in three steps to the next boundary position — so against the facial
first-return order the five sector faces close one per position.  The
five outgoing cycle darts form one face cycle of their own, the inner
pentagon, which never meets a retained dart.  The complete count is
therefore six new faces plus the untouched ambient faces.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24CurvatureScope
open GoertzelV24FaceOrbitPartitionBridge
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RetainedSpliceFaceCount
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24SeamFaceArc

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

namespace FiveEdgeCutPentagonCapData

noncomputable section

variable {RS : RotationSystem V E} (data : FiveEdgeCutPentagonCapData RS)

/-! ## The transported edge flip and face permutation -/

/-- The cap edge flip transported to the reassociated carrier. -/
def capTargetAlpha :
    Equiv.Perm (RetainedDart RS data.keep ⊕ ((Fin 5 × Bool) ⊕ Fin 5)) :=
  data.capDartEquiv.permCongr data.capRotationSystem.alpha

/-- The cap face permutation transported to the reassociated carrier. -/
def capTargetPhi :
    Equiv.Perm (RetainedDart RS data.keep ⊕ ((Fin 5 × Bool) ⊕ Fin 5)) :=
  data.capDartEquiv.permCongr data.capRotationSystem.phi

@[simp]
theorem capTargetAlpha_internal (dart : InternalDart RS data.keep) :
    data.capTargetAlpha (Sum.inl dart.1) =
      Sum.inl (internalAlpha RS data.keep dart).1 := by
  change data.capDartEquiv
      (data.capRewiredDartSystem.alpha
        (data.capDartOfRetained dart.1)) = _
  rw [data.capDartOfRetained_internal,
    data.capRewiredDartSystem_alpha_internal]
  rfl

@[simp]
theorem capTargetAlpha_boundary (position : Fin 5) :
    data.capTargetAlpha
        (Sum.inl (data.crossingBoundaryDartEquiv position).1) =
      Sum.inr (Sum.inr position) := by
  change data.capDartEquiv
      (data.capRewiredDartSystem.alpha
        (data.capDartOfRetained
          (data.crossingBoundaryDartEquiv position).1)) = _
  rw [data.capDartOfRetained_boundary,
    data.capRewiredDartSystem_alpha_boundary]
  rfl

@[simp]
theorem capTargetAlpha_cycle (dart : Fin 5 × Bool) :
    data.capTargetAlpha (Sum.inr (Sum.inl dart)) =
      Sum.inr (Sum.inl (pentagonCyclePairing dart)) := by
  change data.capDartEquiv
      (data.capRewiredDartSystem.alpha (Sum.inl (Sum.inr dart))) = _
  rw [data.capRewiredDartSystem_alpha_cycle]
  rfl

@[simp]
theorem capTargetAlpha_spoke (j : Fin 5) :
    data.capTargetAlpha (Sum.inr (Sum.inr j)) =
      Sum.inl (data.crossingBoundaryDartEquiv j).1 := by
  change data.capDartEquiv
      (data.capRewiredDartSystem.alpha (Sum.inr (Sum.inr j))) = _
  rw [data.capRewiredDartSystem_alpha_spoke,
    data.capDartEquiv_boundary]

theorem capTargetPhi_apply
    (dart : RetainedDart RS data.keep ⊕ ((Fin 5 × Bool) ⊕ Fin 5)) :
    data.capTargetPhi dart =
      data.capTargetRho (data.capTargetAlpha dart) := by
  unfold capTargetPhi capTargetAlpha
  simp only [Equiv.permCongr_apply, RotationSystem.phi]
  change data.capDartEquiv
      (data.capRho (data.capRewiredDartSystem.alpha
        (data.capDartEquiv.symm dart))) =
    data.capTargetRho
      (data.capDartEquiv (data.capRewiredDartSystem.alpha
        (data.capDartEquiv.symm dart)))
  rw [data.capDartEquiv_capRho]

@[simp]
theorem capTargetPhi_internal (dart : InternalDart RS data.keep) :
    data.capTargetPhi (Sum.inl dart.1) =
      Sum.inl (retainedRho RS data.keep
        (internalAlpha RS data.keep dart).1) := by
  rw [data.capTargetPhi_apply, data.capTargetAlpha_internal]
  rfl

@[simp]
theorem capTargetPhi_boundary (position : Fin 5) :
    data.capTargetPhi
        (Sum.inl (data.crossingBoundaryDartEquiv position).1) =
      Sum.inr (Sum.inl (position, true)) := by
  rw [data.capTargetPhi_apply, data.capTargetAlpha_boundary]
  rfl

@[simp]
theorem capTargetPhi_cycleTrue (j : Fin 5) :
    data.capTargetPhi (Sum.inr (Sum.inl (j, true))) =
      Sum.inr (Sum.inr (j + 1)) := by
  rw [data.capTargetPhi_apply, data.capTargetAlpha_cycle]
  rfl

@[simp]
theorem capTargetPhi_cycleFalse (j : Fin 5) :
    data.capTargetPhi (Sum.inr (Sum.inl (j, false))) =
      Sum.inr (Sum.inl (j - 1, false)) := by
  rw [data.capTargetPhi_apply, data.capTargetAlpha_cycle]
  rfl

@[simp]
theorem capTargetPhi_spoke (j : Fin 5) :
    data.capTargetPhi (Sum.inr (Sum.inr j)) =
      Sum.inl (retainedRho RS data.keep
        (data.crossingBoundaryDartEquiv j).1) := by
  rw [data.capTargetPhi_apply, data.capTargetAlpha_spoke]
  rfl

/-! ## First return to the old retained darts -/

/-- Predicate selecting the transported old retained darts. -/
def IsTargetRetained :
    RetainedDart RS data.keep ⊕ ((Fin 5 × Bool) ⊕ Fin 5) → Prop
  | Sum.inl _ => True
  | Sum.inr _ => False

instance isTargetRetainedDecidablePred :
    DecidablePred data.IsTargetRetained
  | Sum.inl _ => isTrue trivial
  | Sum.inr _ => isFalse id

/-- The marked old-dart subtype is canonically the retained-dart carrier. -/
def targetRetainedEquiv :
    {point // data.IsTargetRetained point} ≃ RetainedDart RS data.keep where
  toFun point := by
    rcases point with ⟨retained | pentagon, hpoint⟩
    · exact retained
    · exact False.elim hpoint
  invFun retained := ⟨Sum.inl retained, trivial⟩
  left_inv point := by
    rcases point with ⟨retained | pentagon, hpoint⟩
    · rfl
    · exact False.elim hpoint
  right_inv _ := rfl

@[simp]
theorem targetRetainedEquiv_symm_val
    (dart : RetainedDart RS data.keep) :
    (data.targetRetainedEquiv.symm dart).1 = Sum.inl dart :=
  rfl

/-- First return of cap faces to the old retained dart carrier. -/
def capTargetReturn : Equiv.Perm (RetainedDart RS data.keep) :=
  data.targetRetainedEquiv.permCongr
    (nextHitPerm data.capTargetPhi data.IsTargetRetained)

theorem firstPositiveHitTime_capTargetPhi_internal
    (dart : InternalDart RS data.keep) :
    firstPositiveHitTime data.capTargetPhi data.IsTargetRetained
      (Sum.inl dart.1) trivial = 1 := by
  have hle : firstPositiveHitTime data.capTargetPhi
      data.IsTargetRetained (Sum.inl dart.1) trivial ≤ 1 := by
    apply firstPositiveHitTime_le_of_hit
    · omega
    · simp [data.capTargetPhi_internal, IsTargetRetained]
  have hpos := firstPositiveHitTime_pos data.capTargetPhi
    data.IsTargetRetained (Sum.inl dart.1) trivial
  omega

theorem firstPositiveHitTime_capTargetPhi_boundary (position : Fin 5) :
    firstPositiveHitTime data.capTargetPhi data.IsTargetRetained
      (Sum.inl (data.crossingBoundaryDartEquiv position).1) trivial = 3 := by
  have hthree :
      (data.capTargetPhi ^ (3 : ℕ))
          (Sum.inl (data.crossingBoundaryDartEquiv position).1) =
        Sum.inl (retainedRho RS data.keep
          (data.crossingBoundaryDartEquiv (position + 1)).1) := by
    have h3 : (3 : ℕ) = 2 + 1 := rfl
    rw [h3, pow_succ, Equiv.Perm.mul_apply, pow_succ, Equiv.Perm.mul_apply,
      pow_one]
    rw [data.capTargetPhi_boundary, data.capTargetPhi_cycleTrue,
      data.capTargetPhi_spoke]
  have hle : firstPositiveHitTime data.capTargetPhi
      data.IsTargetRetained
      (Sum.inl (data.crossingBoundaryDartEquiv position).1) trivial ≤ 3 := by
    apply firstPositiveHitTime_le_of_hit
    · omega
    · rw [hthree]
      trivial
  have hpos := firstPositiveHitTime_pos data.capTargetPhi
    data.IsTargetRetained
    (Sum.inl (data.crossingBoundaryDartEquiv position).1) trivial
  have hneOne : firstPositiveHitTime data.capTargetPhi
      data.IsTargetRetained
      (Sum.inl (data.crossingBoundaryDartEquiv position).1) trivial ≠ 1 := by
    intro hone
    have hhit := firstPositiveHitTime_hits data.capTargetPhi
      data.IsTargetRetained
      (Sum.inl (data.crossingBoundaryDartEquiv position).1) trivial
    rw [hone] at hhit
    simp [data.capTargetPhi_boundary, IsTargetRetained] at hhit
  have hneTwo : firstPositiveHitTime data.capTargetPhi
      data.IsTargetRetained
      (Sum.inl (data.crossingBoundaryDartEquiv position).1) trivial ≠ 2 := by
    intro htwo
    have hhit := firstPositiveHitTime_hits data.capTargetPhi
      data.IsTargetRetained
      (Sum.inl (data.crossingBoundaryDartEquiv position).1) trivial
    rw [htwo] at hhit
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, Equiv.Perm.mul_apply,
      pow_one, data.capTargetPhi_boundary,
      data.capTargetPhi_cycleTrue] at hhit
    simp [IsTargetRetained] at hhit
  omega

/-! ## The boundary action of the return -/

/-- Each sector closes onto the next boundary position. -/
def pentBoundaryCycle : Equiv.Perm (BoundaryDart RS data.keep) :=
  data.crossingBoundaryDartEquiv.permCongr (finRotate 5)

@[simp]
theorem pentBoundaryCycle_apply (position : Fin 5) :
    data.pentBoundaryCycle (data.crossingBoundaryDartEquiv position) =
      data.crossingBoundaryDartEquiv (position + 1) := by
  unfold pentBoundaryCycle
  simp [Equiv.permCongr_apply, finRotate_succ_apply]

/-- Eliminating the pentagon darts turns the cap face permutation into the
retained capped face permutation followed by the sector shift. -/
theorem capTargetReturn_eq :
    data.capTargetReturn =
      retainedCappedFacePerm RS data.keep *
        extendBoundaryPerm RS data.keep data.pentBoundaryCycle := by
  apply Equiv.ext
  intro dart
  by_cases hopposite : data.keep (RS.vertOf (RS.alpha dart.1))
  · let internal : InternalDart RS data.keep := ⟨dart, hopposite⟩
    unfold capTargetReturn
    simp only [Equiv.permCongr_apply]
    apply data.targetRetainedEquiv.symm.injective
    simp only [Equiv.symm_apply_apply]
    apply Subtype.ext
    rw [nextHitPerm_apply]
    change
      (data.capTargetPhi ^ firstPositiveHitTime data.capTargetPhi
        data.IsTargetRetained (Sum.inl dart) trivial) (Sum.inl dart) = _
    rw [data.firstPositiveHitTime_capTargetPhi_internal internal]
    rw [pow_one, data.capTargetPhi_internal internal]
    simp only [retainedCappedFacePerm, Equiv.Perm.mul_apply,
      data.targetRetainedEquiv_symm_val, Sum.inl.injEq]
    rw [extendBoundaryPerm_apply_internal RS data.keep
      data.pentBoundaryCycle internal]
    apply congrArg (retainedRho RS data.keep)
    apply Subtype.ext
    rw [internalAlpha_val]
    exact (retainedCappedAlpha_apply_internal RS data.keep dart hopposite).symm
  · rcases data.crossingBoundaryDartEquiv.surjective ⟨dart, hopposite⟩ with
      ⟨position, hposition⟩
    obtain rfl : dart = (data.crossingBoundaryDartEquiv position).1 := by
      rw [hposition]
    unfold capTargetReturn
    simp only [Equiv.permCongr_apply]
    apply data.targetRetainedEquiv.symm.injective
    simp only [Equiv.symm_apply_apply]
    apply Subtype.ext
    rw [nextHitPerm_apply]
    change
      (data.capTargetPhi ^ firstPositiveHitTime data.capTargetPhi
        data.IsTargetRetained
        (Sum.inl (data.crossingBoundaryDartEquiv position).1) trivial)
          (Sum.inl (data.crossingBoundaryDartEquiv position).1) = _
    rw [data.firstPositiveHitTime_capTargetPhi_boundary position]
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, Equiv.Perm.mul_apply,
      pow_succ, Equiv.Perm.mul_apply, pow_one,
      data.capTargetPhi_boundary, data.capTargetPhi_cycleTrue,
      data.capTargetPhi_spoke]
    simp only [retainedCappedFacePerm, Equiv.Perm.mul_apply,
      data.targetRetainedEquiv_symm_val, Sum.inl.injEq]
    rw [extendBoundaryPerm_apply_boundary RS data.keep
      data.pentBoundaryCycle (data.crossingBoundaryDartEquiv position),
      data.pentBoundaryCycle_apply]
    apply congrArg (retainedRho RS data.keep)
    rw [retainedCappedAlpha_apply_boundary RS data.keep
      (data.crossingBoundaryDartEquiv (position + 1)).1
      (data.crossingBoundaryDartEquiv (position + 1)).2]


/-! ## The face count under the facial boundary order -/

/-- Against the facial first-return order, every sector closes in place. -/
theorem nextHitPerm_capTargetReturn_eq_one
    (hsucc : retainedRegionBoundarySuccessor RS data.keep =
      data.crossingBoundaryDartEquiv.permCongr (finRotate 5)⁻¹) :
    nextHitPerm data.capTargetReturn
        (fun dart : RetainedDart RS data.keep =>
          ¬ data.keep (RS.vertOf (RS.alpha dart.1))) = 1 := by
  rw [data.capTargetReturn_eq,
    nextHitPerm_rewiredRetainedCappedFacePerm, hsucc]
  apply Equiv.ext
  intro dart
  simp only [pentBoundaryCycle, Equiv.Perm.mul_apply,
    Equiv.permCongr_apply, Equiv.symm_apply_apply,
    Equiv.Perm.one_apply]
  rw [show ((finRotate 5)⁻¹ : Equiv.Perm (Fin 5)) = (finRotate 5).symm
    from rfl, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  rfl

/-- Exactly five sector faces meet the boundary. -/
theorem card_capTargetReturn_hitOrbit_eq_five
    (hsucc : retainedRegionBoundarySuccessor RS data.keep =
      data.crossingBoundaryDartEquiv.permCongr (finRotate 5)⁻¹) :
    Fintype.card
      (HitOrbit data.capTargetReturn
        (fun dart : RetainedDart RS data.keep =>
          ¬ data.keep (RS.vertOf (RS.alpha dart.1)))) = 5 := by
  rw [card_hitOrbit_eq_nextHit_partition_card,
    data.nextHitPerm_capTargetReturn_eq_one hsucc]
  simp only [Equiv.Perm.parts_partition, Equiv.Perm.cycleType_one,
    zero_add, Equiv.Perm.support_one, Finset.card_empty, Nat.sub_zero,
    Multiset.card_replicate]
  let boundaryEquiv :
      { dart : RetainedDart RS data.keep //
        ¬ data.keep (RS.vertOf (RS.alpha dart.1)) } ≃ Fin 5 :=
    data.crossingBoundaryDartEquiv.symm
  exact Fintype.card_congr boundaryEquiv

/-! ## The inner pentagon face -/

/-- The five outgoing cycle darts. -/
def IsInnerCycleDart :
    RetainedDart RS data.keep ⊕ ((Fin 5 × Bool) ⊕ Fin 5) → Prop :=
  fun point => ∃ j : Fin 5, point = Sum.inr (Sum.inl (j, false))

theorem isInnerCycleDart_phi
    {point : RetainedDart RS data.keep ⊕ ((Fin 5 × Bool) ⊕ Fin 5)}
    (hinner : data.IsInnerCycleDart point) :
    data.IsInnerCycleDart (data.capTargetPhi point) := by
  rcases hinner with ⟨j, rfl⟩
  rw [data.capTargetPhi_cycleFalse]
  exact ⟨j - 1, rfl⟩

theorem isInnerCycleDart_phi_symm
    {point : RetainedDart RS data.keep ⊕ ((Fin 5 × Bool) ⊕ Fin 5)}
    (hinner : data.IsInnerCycleDart point) :
    data.IsInnerCycleDart (data.capTargetPhi⁻¹ point) := by
  rcases hinner with ⟨j, rfl⟩
  refine ⟨j + 1, ?_⟩
  have hforward := data.capTargetPhi_cycleFalse (j + 1)
  rw [add_sub_cancel_right] at hforward
  rw [← hforward, show (data.capTargetPhi⁻¹ : Equiv.Perm _) =
    data.capTargetPhi.symm from rfl, Equiv.symm_apply_apply]

theorem isInnerCycleDart_zpow
    (power : ℤ)
    {point : RetainedDart RS data.keep ⊕ ((Fin 5 × Bool) ⊕ Fin 5)}
    (hinner : data.IsInnerCycleDart point) :
    data.IsInnerCycleDart ((data.capTargetPhi ^ power) point) := by
  induction power using Int.induction_on generalizing point with
  | zero => simpa using hinner
  | succ n ih =>
      rw [zpow_add, zpow_one, Equiv.Perm.mul_apply]
      exact ih (data.isInnerCycleDart_phi hinner)
  | pred n ih =>
      rw [sub_eq_add_neg, zpow_add, zpow_neg_one, Equiv.Perm.mul_apply]
      exact ih (data.isInnerCycleDart_phi_symm hinner)

theorem isInnerCycleDart_of_sameCycle
    {left right : RetainedDart RS data.keep ⊕ ((Fin 5 × Bool) ⊕ Fin 5)}
    (hcycle : data.capTargetPhi.SameCycle left right)
    (hinner : data.IsInnerCycleDart left) :
    data.IsInnerCycleDart right := by
  rcases hcycle with ⟨power, hpower⟩
  rw [← hpower]
  exact data.isInnerCycleDart_zpow power hinner

/-- All outgoing cycle darts lie on one face cycle. -/
theorem innerCycleDart_sameCycle_zero (j : Fin 5) :
    data.capTargetPhi.SameCycle
      (Sum.inr (Sum.inl (j, false))) (Sum.inr (Sum.inl (0, false))) := by
  have hstep : ∀ point, data.capTargetPhi.SameCycle point
      (data.capTargetPhi point) :=
    fun point => Mettapedia.GraphTheory.EquivPermSameCycle.step_right
      data.capTargetPhi point
  have hone : ∀ k : Fin 5, data.capTargetPhi.SameCycle
      (Sum.inr (Sum.inl (k, false))) (Sum.inr (Sum.inl (k - 1, false))) := by
    intro k
    have := hstep (Sum.inr (Sum.inl (k, false)))
    rwa [data.capTargetPhi_cycleFalse] at this
  fin_cases j
  · exact Equiv.Perm.SameCycle.refl _ _
  · simpa using hone 1
  · exact ((hone 2).trans (by simpa using hone 1))
  · exact ((hone 3).trans ((hone 2).trans (by simpa using hone 1)))
  · exact ((hone 4).trans ((hone 3).trans ((hone 2).trans
      (by simpa using hone 1))))

/-- Every non-inner point reaches a retained dart along its face cycle. -/
theorem exists_retained_sameCycle_of_not_inner
    (point : RetainedDart RS data.keep ⊕ ((Fin 5 × Bool) ⊕ Fin 5))
    (hnotInner : ¬ data.IsInnerCycleDart point) :
    ∃ dart : RetainedDart RS data.keep,
      data.capTargetPhi.SameCycle point (Sum.inl dart) := by
  have hstep : ∀ x, data.capTargetPhi.SameCycle x (data.capTargetPhi x) :=
    fun x => Mettapedia.GraphTheory.EquivPermSameCycle.step_right
      data.capTargetPhi x
  rcases point with retained | (⟨j, b⟩ | j)
  · exact ⟨retained, Equiv.Perm.SameCycle.refl _ _⟩
  · cases b
    · exact absurd ⟨j, rfl⟩ hnotInner
    · refine ⟨retainedRho RS data.keep
        (data.crossingBoundaryDartEquiv (j + 1)).1, ?_⟩
      have hfirst := hstep (Sum.inr (Sum.inl (j, true)))
      rw [data.capTargetPhi_cycleTrue] at hfirst
      have hsecond := hstep (Sum.inr (Sum.inr (j + 1)))
      rw [data.capTargetPhi_spoke] at hsecond
      exact hfirst.trans hsecond
  · refine ⟨retainedRho RS data.keep
      (data.crossingBoundaryDartEquiv j).1, ?_⟩
    have := hstep (Sum.inr (Sum.inr j))
    rwa [data.capTargetPhi_spoke] at this

/-- The inner pentagon is the unique face cycle avoiding all retained
darts. -/
theorem card_capTargetPhi_nonHitOrbit_eq_one :
    Fintype.card
      (NonHitOrbit data.capTargetPhi data.IsTargetRetained) = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨Quotient.mk _ (Sum.inr (Sum.inl ((0 : Fin 5), false))), ?_⟩, ?_⟩
  · rintro ⟨point, hhit, hquot⟩
    have hcycle : data.capTargetPhi.SameCycle point
        (Sum.inr (Sum.inl ((0 : Fin 5), false))) :=
      Quotient.exact hquot
    have hinner := data.isInnerCycleDart_of_sameCycle hcycle.symm
      ⟨0, rfl⟩
    rcases hinner with ⟨j, rfl⟩
    exact hhit
  · rintro ⟨orbit, hnothit⟩
    apply Subtype.ext
    obtain ⟨point, hpoint⟩ := Quotient.exists_rep orbit
    by_cases hinner : data.IsInnerCycleDart point
    · rcases hinner with ⟨j, rfl⟩
      calc
        orbit = Quotient.mk _ (Sum.inr (Sum.inl (j, false))) :=
          hpoint.symm
        _ = Quotient.mk _ (Sum.inr (Sum.inl ((0 : Fin 5), false))) :=
          Quotient.sound (data.innerCycleDart_sameCycle_zero j)
    · exfalso
      rcases data.exists_retained_sameCycle_of_not_inner point hinner with
        ⟨dart, hdart⟩
      apply hnothit
      exact ⟨Sum.inl dart, trivial,
        (Quotient.sound hdart.symm).trans hpoint⟩

/-! ## The complete count -/

theorem card_capTargetPhi_partition_eq_capTargetReturn_partition_add_one :
    data.capTargetPhi.partition.parts.card =
      data.capTargetReturn.partition.parts.card + 1 := by
  calc
    data.capTargetPhi.partition.parts.card =
        Fintype.card
          (Quotient (Equiv.Perm.SameCycle.setoid data.capTargetPhi)) :=
      (card_permOrbit_eq_card_partition_parts data.capTargetPhi).symm
    _ = Fintype.card
          (HitOrbit data.capTargetPhi data.IsTargetRetained) +
        Fintype.card
          (NonHitOrbit data.capTargetPhi data.IsTargetRetained) :=
      card_permOrbit_eq_hit_add_nonHit data.capTargetPhi
        data.IsTargetRetained
    _ = (nextHitPerm data.capTargetPhi
          data.IsTargetRetained).partition.parts.card + 1 := by
      rw [card_hitOrbit_eq_nextHit_partition_card,
        data.card_capTargetPhi_nonHitOrbit_eq_one]
    _ = data.capTargetReturn.partition.parts.card + 1 := by
      congr 1
      symm
      exact card_permCongr_partition_parts data.targetRetainedEquiv
        (nextHitPerm data.capTargetPhi data.IsTargetRetained)

theorem card_cap_faceCycleLengths_eq_capTargetReturn_partition_add_one :
    (faceCycleLengths data.capRotationSystem).card =
      data.capTargetReturn.partition.parts.card + 1 := by
  change data.capRotationSystem.phi.partition.parts.card = _
  calc
    data.capRotationSystem.phi.partition.parts.card =
        data.capTargetPhi.partition.parts.card :=
      (card_permCongr_partition_parts data.capDartEquiv
        data.capRotationSystem.phi).symm
    _ = data.capTargetReturn.partition.parts.card + 1 :=
      data.card_capTargetPhi_partition_eq_capTargetReturn_partition_add_one

/-- The complete pentagon face count: five sectors, the inner pentagon,
and the faces never meeting an exposed retained dart. -/
theorem card_cap_faceCycleLengths_eq_six_add_nonHit
    (hsucc : retainedRegionBoundarySuccessor RS data.keep =
      data.crossingBoundaryDartEquiv.permCongr (finRotate 5)⁻¹) :
    (faceCycleLengths data.capRotationSystem).card =
      6 + Fintype.card
        (NonHitOrbit data.capTargetReturn
          (fun dart : RetainedDart RS data.keep =>
            ¬ data.keep (RS.vertOf (RS.alpha dart.1)))) := by
  calc
    (faceCycleLengths data.capRotationSystem).card =
        data.capTargetReturn.partition.parts.card + 1 :=
      data.card_cap_faceCycleLengths_eq_capTargetReturn_partition_add_one
    _ = (Fintype.card
          (HitOrbit data.capTargetReturn
            (fun dart : RetainedDart RS data.keep =>
              ¬ data.keep (RS.vertOf (RS.alpha dart.1)))) +
        Fintype.card
          (NonHitOrbit data.capTargetReturn
            (fun dart : RetainedDart RS data.keep =>
              ¬ data.keep (RS.vertOf (RS.alpha dart.1))))) + 1 := by
      rw [← card_permOrbit_eq_hit_add_nonHit data.capTargetReturn _,
        card_permOrbit_eq_card_partition_parts data.capTargetReturn]
    _ = 6 + Fintype.card
          (NonHitOrbit data.capTargetReturn
            (fun dart : RetainedDart RS data.keep =>
              ¬ data.keep (RS.vertOf (RS.alpha dart.1)))) := by
      rw [data.card_capTargetReturn_hitOrbit_eq_five hsucc]
      omega

end

end FiveEdgeCutPentagonCapData

end Mettapedia.GraphTheory.FourColor
