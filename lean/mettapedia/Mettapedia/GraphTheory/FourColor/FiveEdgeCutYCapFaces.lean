import Mettapedia.GraphTheory.FourColor.FiveEdgeCutYCapStructure
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedSpliceFaceCount

/-!
# Face count of the Y-capped shore

Faces of the Y-capped shore are counted through the first return of its
face permutation to the old retained darts.  Internal darts return in one
step; a seam dart's edge flip lands directly on its partner, also
returning in one step; a star dart bounces off the new vertex and returns
in two.  The boundary action of the return permutation is therefore the
seam swap on the seam pair and the rotated spoke cycle on the star triple.

When the five cut positions are enumerated against the facial first-return
order, the induced permutation of the five boundary positions is the
transposition `(1 4)`: four orbits.  The Y-cap closes the disc with
exactly four new faces — the seam lens, two star sectors, and one long
face touching the two free arcs.
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

namespace FiveEdgeCutYCapData

noncomputable section

variable {RS : RotationSystem V E} (data : FiveEdgeCutYCapData RS)

/-! ## The transported edge flip and face permutation -/

/-- The cap edge flip transported to the old-retained-darts plus spoke
carrier. -/
def capTargetAlpha : Equiv.Perm (RetainedDart RS data.keep ⊕ Fin 3) :=
  data.capDartEquiv.permCongr data.capRotationSystem.alpha

/-- The cap face permutation transported to the old-retained-darts plus
spoke carrier. -/
def capTargetPhi : Equiv.Perm (RetainedDart RS data.keep ⊕ Fin 3) :=
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
theorem capTargetAlpha_seam (part : Bool) :
    data.capTargetAlpha (Sum.inl (data.seamDart part).1) =
      Sum.inl (data.seamDart (seamPairSwap part)).1 := by
  change data.capDartEquiv
      (data.capRewiredDartSystem.alpha
        (data.capDartOfRetained (data.seamDart part).1)) = _
  rw [data.capDartOfRetained_seam,
    data.capRewiredDartSystem_alpha_seam,
    data.capDartEquiv_seam]

@[simp]
theorem capTargetAlpha_star (spoke : Fin 3) :
    data.capTargetAlpha (Sum.inl (data.starDart spoke).1) =
      Sum.inr spoke := by
  change data.capDartEquiv
      (data.capRewiredDartSystem.alpha
        (data.capDartOfRetained (data.starDart spoke).1)) = _
  rw [data.capDartOfRetained_star,
    data.capRewiredDartSystem_alpha_star]
  rfl

@[simp]
theorem capTargetAlpha_cap (spoke : Fin 3) :
    data.capTargetAlpha (Sum.inr spoke) =
      Sum.inl (data.starDart spoke).1 := by
  change data.capDartEquiv
      (data.capRewiredDartSystem.alpha (Sum.inr (Sum.inr spoke))) = _
  rw [data.capRewiredDartSystem_alpha_cap,
    data.capDartEquiv_star]

/-- On the transported carrier, a cap face step is target rotation after
target edge flip. -/
theorem capTargetPhi_apply
    (dart : RetainedDart RS data.keep ⊕ Fin 3) :
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
theorem capTargetPhi_seam (part : Bool) :
    data.capTargetPhi (Sum.inl (data.seamDart part).1) =
      Sum.inl (retainedRho RS data.keep
        (data.seamDart (seamPairSwap part)).1) := by
  rw [data.capTargetPhi_apply, data.capTargetAlpha_seam]
  rfl

@[simp]
theorem capTargetPhi_star (spoke : Fin 3) :
    data.capTargetPhi (Sum.inl (data.starDart spoke).1) =
      Sum.inr (finRotate 3 spoke) := by
  rw [data.capTargetPhi_apply, data.capTargetAlpha_star]
  rfl

@[simp]
theorem capTargetPhi_cap (spoke : Fin 3) :
    data.capTargetPhi (Sum.inr spoke) =
      Sum.inl (retainedRho RS data.keep (data.starDart spoke).1) := by
  rw [data.capTargetPhi_apply, data.capTargetAlpha_cap]
  rfl

/-! ## First return to the old retained darts -/

/-- Predicate selecting the transported old retained darts. -/
def IsTargetRetained : RetainedDart RS data.keep ⊕ Fin 3 → Prop
  | Sum.inl _ => True
  | Sum.inr _ => False

instance isTargetRetainedDecidablePred : DecidablePred data.IsTargetRetained
  | Sum.inl _ => isTrue trivial
  | Sum.inr _ => isFalse id

/-- The marked old-dart subtype is canonically the retained-dart carrier. -/
def targetRetainedEquiv :
    {point // data.IsTargetRetained point} ≃ RetainedDart RS data.keep where
  toFun point := by
    rcases point with ⟨retained | cap, hpoint⟩
    · exact retained
    · exact False.elim hpoint
  invFun retained := ⟨Sum.inl retained, trivial⟩
  left_inv point := by
    rcases point with ⟨retained | cap, hpoint⟩
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

theorem firstPositiveHitTime_capTargetPhi_seam (part : Bool) :
    firstPositiveHitTime data.capTargetPhi data.IsTargetRetained
      (Sum.inl (data.seamDart part).1) trivial = 1 := by
  have hle : firstPositiveHitTime data.capTargetPhi
      data.IsTargetRetained (Sum.inl (data.seamDart part).1) trivial ≤ 1 := by
    apply firstPositiveHitTime_le_of_hit
    · omega
    · simp [data.capTargetPhi_seam, IsTargetRetained]
  have hpos := firstPositiveHitTime_pos data.capTargetPhi
    data.IsTargetRetained (Sum.inl (data.seamDart part).1) trivial
  omega

theorem firstPositiveHitTime_capTargetPhi_star (spoke : Fin 3) :
    firstPositiveHitTime data.capTargetPhi data.IsTargetRetained
      (Sum.inl (data.starDart spoke).1) trivial = 2 := by
  have hle : firstPositiveHitTime data.capTargetPhi
      data.IsTargetRetained (Sum.inl (data.starDart spoke).1) trivial ≤ 2 := by
    apply firstPositiveHitTime_le_of_hit
    · omega
    · simp [pow_two, Equiv.Perm.mul_apply,
        data.capTargetPhi_star, data.capTargetPhi_cap,
        IsTargetRetained]
  have hpos := firstPositiveHitTime_pos data.capTargetPhi
    data.IsTargetRetained (Sum.inl (data.starDart spoke).1) trivial
  have hneOne : firstPositiveHitTime data.capTargetPhi
      data.IsTargetRetained (Sum.inl (data.starDart spoke).1) trivial ≠ 1 := by
    intro hone
    have hhit := firstPositiveHitTime_hits data.capTargetPhi
      data.IsTargetRetained (Sum.inl (data.starDart spoke).1) trivial
    rw [hone] at hhit
    simp [data.capTargetPhi_star, IsTargetRetained] at hhit
  omega

/-! ## The boundary action of the return -/

/-- The seam swap on the seam pair together with the rotated spoke cycle on
the star triple, as a permutation of all boundary darts. -/
def yBoundaryCycle : Equiv.Perm (BoundaryDart RS data.keep) :=
  data.boundarySplitEquiv.symm.permCongr
    (Equiv.sumCongr seamPairSwap (finRotate 3))

@[simp]
theorem boundarySplitEquiv_seamDart (part : Bool) :
    data.boundarySplitEquiv (data.seamDart part) = Sum.inl part := by
  simp [boundarySplitEquiv, seamDart]

@[simp]
theorem boundarySplitEquiv_starDart (spoke : Fin 3) :
    data.boundarySplitEquiv (data.starDart spoke) = Sum.inr spoke := by
  simp [boundarySplitEquiv, starDart]

@[simp]
theorem yBoundaryCycle_seamDart (part : Bool) :
    data.yBoundaryCycle (data.seamDart part) =
      data.seamDart (seamPairSwap part) := by
  unfold yBoundaryCycle
  simp only [Equiv.permCongr_apply, Equiv.symm_symm,
    data.boundarySplitEquiv_seamDart, Equiv.sumCongr_apply, Sum.map_inl]
  apply data.boundarySplitEquiv.injective
  simp

@[simp]
theorem yBoundaryCycle_starDart (spoke : Fin 3) :
    data.yBoundaryCycle (data.starDart spoke) =
      data.starDart (finRotate 3 spoke) := by
  unfold yBoundaryCycle
  simp only [Equiv.permCongr_apply, Equiv.symm_symm,
    data.boundarySplitEquiv_starDart, Equiv.sumCongr_apply, Sum.map_inr]
  apply data.boundarySplitEquiv.injective
  simp

/-- Boundary darts are seam or star darts. -/
theorem boundaryDart_eq_seam_or_star (dart : BoundaryDart RS data.keep) :
    (∃ part, dart = data.seamDart part) ∨
      ∃ spoke, dart = data.starDart spoke := by
  rcases hsplit : data.boundarySplitEquiv dart with part | spoke
  · left
    refine ⟨part, ?_⟩
    apply data.boundarySplitEquiv.injective
    rw [hsplit, data.boundarySplitEquiv_seamDart]
  · right
    refine ⟨spoke, ?_⟩
    apply data.boundarySplitEquiv.injective
    rw [hsplit, data.boundarySplitEquiv_starDart]

/-- Eliminating the spoke darts turns the cap face permutation into the
retained capped face permutation followed by the Y boundary action. -/
theorem capTargetReturn_eq :
    data.capTargetReturn =
      retainedCappedFacePerm RS data.keep *
        extendBoundaryPerm RS data.keep data.yBoundaryCycle := by
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
      data.yBoundaryCycle internal]
    apply congrArg (retainedRho RS data.keep)
    apply Subtype.ext
    rw [internalAlpha_val]
    exact (retainedCappedAlpha_apply_internal RS data.keep dart hopposite).symm
  · rcases data.boundaryDart_eq_seam_or_star ⟨dart, hopposite⟩ with
      ⟨part, hpart⟩ | ⟨spoke, hspoke⟩
    · obtain rfl : dart = (data.seamDart part).1 :=
        congrArg Subtype.val hpart
      unfold capTargetReturn
      simp only [Equiv.permCongr_apply]
      apply data.targetRetainedEquiv.symm.injective
      simp only [Equiv.symm_apply_apply]
      apply Subtype.ext
      rw [nextHitPerm_apply]
      change
        (data.capTargetPhi ^ firstPositiveHitTime data.capTargetPhi
          data.IsTargetRetained (Sum.inl (data.seamDart part).1) trivial)
            (Sum.inl (data.seamDart part).1) = _
      rw [data.firstPositiveHitTime_capTargetPhi_seam part]
      rw [pow_one, data.capTargetPhi_seam part]
      simp only [retainedCappedFacePerm, Equiv.Perm.mul_apply,
        data.targetRetainedEquiv_symm_val, Sum.inl.injEq]
      rw [extendBoundaryPerm_apply_boundary RS data.keep
        data.yBoundaryCycle (data.seamDart part),
        data.yBoundaryCycle_seamDart]
      apply congrArg (retainedRho RS data.keep)
      rw [retainedCappedAlpha_apply_boundary RS data.keep
        (data.seamDart (seamPairSwap part)).1
        (data.seamDart (seamPairSwap part)).2]
    · obtain rfl : dart = (data.starDart spoke).1 :=
        congrArg Subtype.val hspoke
      unfold capTargetReturn
      simp only [Equiv.permCongr_apply]
      apply data.targetRetainedEquiv.symm.injective
      simp only [Equiv.symm_apply_apply]
      apply Subtype.ext
      rw [nextHitPerm_apply]
      change
        (data.capTargetPhi ^ firstPositiveHitTime data.capTargetPhi
          data.IsTargetRetained (Sum.inl (data.starDart spoke).1) trivial)
            (Sum.inl (data.starDart spoke).1) = _
      rw [data.firstPositiveHitTime_capTargetPhi_star spoke]
      rw [pow_two, Equiv.Perm.mul_apply,
        data.capTargetPhi_star spoke, data.capTargetPhi_cap]
      simp only [retainedCappedFacePerm, Equiv.Perm.mul_apply,
        data.targetRetainedEquiv_symm_val, Sum.inl.injEq]
      rw [extendBoundaryPerm_apply_boundary RS data.keep
        data.yBoundaryCycle (data.starDart spoke),
        data.yBoundaryCycle_starDart]
      apply congrArg (retainedRho RS data.keep)
      rw [retainedCappedAlpha_apply_boundary RS data.keep
        (data.starDart (finRotate 3 spoke)).1
        (data.starDart (finRotate 3 spoke)).2]

/-! ## Every face meets the old carrier -/

theorem exists_capTargetRetained_sameCycle
    (point : RetainedDart RS data.keep ⊕ Fin 3) :
    ∃ dart : RetainedDart RS data.keep,
      data.capTargetPhi.SameCycle point (Sum.inl dart) := by
  rcases point with dart | spoke
  · exact ⟨dart, Equiv.Perm.SameCycle.refl data.capTargetPhi _⟩
  · refine ⟨retainedRho RS data.keep (data.starDart spoke).1, ?_⟩
    simpa only [data.capTargetPhi_cap] using
      Mettapedia.GraphTheory.EquivPermSameCycle.step_right
        data.capTargetPhi (Sum.inr spoke)

theorem capTargetNonHitOrbit_isEmpty
    (orbit : NonHitOrbit data.capTargetPhi data.IsTargetRetained) : False := by
  rcases data.exists_capTargetRetained_sameCycle orbit.1.out with
    ⟨dart, hdart⟩
  exact (nonHitOrbit_not_hit_of_sameCycle data.capTargetPhi
    data.IsTargetRetained orbit (Sum.inl dart) hdart) trivial

theorem card_capTargetNonHitOrbit_eq_zero :
    Fintype.card
      (NonHitOrbit data.capTargetPhi data.IsTargetRetained) = 0 := by
  rw [Fintype.card_eq_zero_iff]
  exact ⟨fun orbit => False.elim (data.capTargetNonHitOrbit_isEmpty orbit)⟩

theorem card_capTargetPhi_partition_eq_capTargetReturn_partition :
    data.capTargetPhi.partition.parts.card =
      data.capTargetReturn.partition.parts.card := by
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
          data.IsTargetRetained).partition.parts.card := by
      rw [card_hitOrbit_eq_nextHit_partition_card,
        data.card_capTargetNonHitOrbit_eq_zero, Nat.add_zero]
    _ = data.capTargetReturn.partition.parts.card := by
      symm
      exact card_permCongr_partition_parts data.targetRetainedEquiv
        (nextHitPerm data.capTargetPhi data.IsTargetRetained)

theorem card_cap_faceCycleLengths_eq_capTargetReturn_partition :
    (faceCycleLengths data.capRotationSystem).card =
      data.capTargetReturn.partition.parts.card := by
  change data.capRotationSystem.phi.partition.parts.card = _
  calc
    data.capRotationSystem.phi.partition.parts.card =
        data.capTargetPhi.partition.parts.card :=
      (card_permCongr_partition_parts data.capDartEquiv
        data.capRotationSystem.phi).symm
    _ = data.capTargetReturn.partition.parts.card :=
      data.card_capTargetPhi_partition_eq_capTargetReturn_partition


/-! ## The face count under the facial boundary order -/

/-- The five-position composite of the inverse facial rotation with the Y
boundary action is the transposition of positions `1` and `4`. -/
theorem inverse_rotation_mul_yPosition_eq_swap :
    (finRotate 5)⁻¹ *
        positionSplit.symm.permCongr
          (Equiv.sumCongr seamPairSwap (finRotate 3)) =
      Equiv.swap (1 : Fin 5) 4 := by
  apply Equiv.ext
  decide

/-- The Y boundary action in the crossing coordinates. -/
theorem yBoundaryCycle_eq_permCongr :
    data.yBoundaryCycle =
      data.crossingBoundaryDartEquiv.permCongr
        (positionSplit.symm.permCongr
          (Equiv.sumCongr seamPairSwap (finRotate 3))) := by
  apply Equiv.ext
  intro dart
  simp [yBoundaryCycle, boundarySplitEquiv, Equiv.permCongr_apply]

/-- Against the facial first-return order, the boundary action of the
return composes with the successor to the position transposition. -/
theorem successor_mul_yBoundaryCycle
    (hsucc : retainedRegionBoundarySuccessor RS data.keep =
      data.crossingBoundaryDartEquiv.permCongr (finRotate 5)⁻¹) :
    retainedRegionBoundarySuccessor RS data.keep * data.yBoundaryCycle =
      data.crossingBoundaryDartEquiv.permCongr
        (Equiv.swap (1 : Fin 5) 4) := by
  rw [hsucc, data.yBoundaryCycle_eq_permCongr]
  apply Equiv.ext
  intro dart
  have hpoint := DFunLike.congr_fun inverse_rotation_mul_yPosition_eq_swap
    (data.crossingBoundaryDartEquiv.symm dart)
  simp only [Equiv.Perm.mul_apply, Equiv.permCongr_apply,
    Equiv.symm_apply_apply] at hpoint ⊢
  exact congrArg data.crossingBoundaryDartEquiv hpoint

/-- First return of the capped face walk to the exposed boundary darts, in
crossing coordinates. -/
theorem nextHitPerm_capTargetReturn_eq
    (hsucc : retainedRegionBoundarySuccessor RS data.keep =
      data.crossingBoundaryDartEquiv.permCongr (finRotate 5)⁻¹) :
    nextHitPerm data.capTargetReturn
        (fun dart : RetainedDart RS data.keep =>
          ¬ data.keep (RS.vertOf (RS.alpha dart.1))) =
      data.crossingBoundaryDartEquiv.permCongr
        (Equiv.swap (1 : Fin 5) 4) := by
  rw [data.capTargetReturn_eq,
    nextHitPerm_rewiredRetainedCappedFacePerm,
    data.successor_mul_yBoundaryCycle hsucc]

private theorem parts_card_eq_of_instances {T : Type*}
    (instF1 instF2 : Fintype T) (instD1 instD2 : DecidableEq T)
    (σ : Equiv.Perm T) :
    (@Equiv.Perm.partition T instF1 instD1 σ).parts.card =
      (@Equiv.Perm.partition T instF2 instD2 σ).parts.card := by
  obtain rfl : instF1 = instF2 := Subsingleton.elim _ _
  obtain rfl : instD1 = instD2 := Subsingleton.elim _ _
  rfl

/-- Exactly four capped face cycles meet the boundary: the seam lens, two
star sectors, and the long face through the two free arcs. -/
theorem card_capTargetReturn_hitOrbit_eq_four
    (hsucc : retainedRegionBoundarySuccessor RS data.keep =
      data.crossingBoundaryDartEquiv.permCongr (finRotate 5)⁻¹) :
    Fintype.card
      (HitOrbit data.capTargetReturn
        (fun dart : RetainedDart RS data.keep =>
          ¬ data.keep (RS.vertOf (RS.alpha dart.1)))) = 4 := by
  rw [card_hitOrbit_eq_nextHit_partition_card,
    data.nextHitPerm_capTargetReturn_eq hsucc]
  have hne : (1 : Fin 5) ≠ 4 := by decide
  have hswap : (Equiv.swap (1 : Fin 5) 4).partition.parts.card = 4 := by
    rw [Equiv.Perm.parts_partition,
      (Equiv.Perm.isCycle_swap hne).cycleType,
      Equiv.Perm.support_swap hne]
    simp [Finset.card_pair hne]
  have hgen : ∀ {T : Type _} [Fintype T] [DecidableEq T] (e : Fin 5 ≃ T),
      ((e.permCongr (Equiv.swap (1 : Fin 5) 4)).partition).parts.card = 4 :=
    fun e => (card_permCongr_partition_parts e (Equiv.swap 1 4)).trans hswap
  exact (parts_card_eq_of_instances _ _ _ _ _).trans
    (hgen data.crossingBoundaryDartEquiv)

/-- The complete Y-cap face count: four boundary-closing faces plus the
faces which never meet an exposed retained dart. -/
theorem card_cap_faceCycleLengths_eq_four_add_nonHit
    (hsucc : retainedRegionBoundarySuccessor RS data.keep =
      data.crossingBoundaryDartEquiv.permCongr (finRotate 5)⁻¹) :
    (faceCycleLengths data.capRotationSystem).card =
      4 + Fintype.card
        (NonHitOrbit data.capTargetReturn
          (fun dart : RetainedDart RS data.keep =>
            ¬ data.keep (RS.vertOf (RS.alpha dart.1)))) := by
  calc
    (faceCycleLengths data.capRotationSystem).card =
        data.capTargetReturn.partition.parts.card :=
      data.card_cap_faceCycleLengths_eq_capTargetReturn_partition
    _ = Fintype.card
        (Quotient (Equiv.Perm.SameCycle.setoid data.capTargetReturn)) :=
      (card_permOrbit_eq_card_partition_parts data.capTargetReturn).symm
    _ = Fintype.card
          (HitOrbit data.capTargetReturn
            (fun dart : RetainedDart RS data.keep =>
              ¬ data.keep (RS.vertOf (RS.alpha dart.1)))) +
        Fintype.card
          (NonHitOrbit data.capTargetReturn
            (fun dart : RetainedDart RS data.keep =>
              ¬ data.keep (RS.vertOf (RS.alpha dart.1)))) :=
      card_permOrbit_eq_hit_add_nonHit data.capTargetReturn _
    _ = 4 + Fintype.card
          (NonHitOrbit data.capTargetReturn
            (fun dart : RetainedDart RS data.keep =>
              ¬ data.keep (RS.vertOf (RS.alpha dart.1)))) := by
      rw [data.card_capTargetReturn_hitOrbit_eq_four hsucc]

end

end FiveEdgeCutYCapData

end Mettapedia.GraphTheory.FourColor
