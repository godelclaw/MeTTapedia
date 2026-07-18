import Mettapedia.GraphTheory.FourColor.GoertzelV24ThreeEdgeCutCapOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedSpliceFaceCount

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

namespace RotationSystem

namespace ThreeEdgeCutSideData

noncomputable section

variable {RS : RotationSystem V E} (data : ThreeEdgeCutSideData RS)

/-- The cap edge flip transported to the old-retained-darts plus cap-darts
carrier. -/
def capTargetAlpha : Equiv.Perm (RetainedDart RS data.keep ⊕ Fin 3) :=
  data.capDartEquiv.permCongr data.capRotationSystem.alpha

/-- The cap face permutation transported to the old-retained-darts plus
cap-darts carrier. -/
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
theorem capTargetAlpha_boundary (dart : BoundaryDart RS data.keep) :
    data.capTargetAlpha (Sum.inl dart.1) =
      Sum.inr (data.crossingBoundaryDartEquiv.symm dart) := by
  change data.capDartEquiv
      (data.capRewiredDartSystem.alpha
        (data.capDartOfRetained dart.1)) = _
  rw [data.capDartOfRetained_boundary,
    data.capRewiredDartSystem_alpha_boundary]
  simp

@[simp]
theorem capTargetAlpha_cap (step : Fin 3) :
    data.capTargetAlpha (Sum.inr step) =
      Sum.inl (data.crossingBoundaryDartEquiv step).1 := by
  change data.capDartEquiv
      (data.capRewiredDartSystem.alpha (data.capDart step)) = _
  rw [data.capRewiredDartSystem_alpha_cap]
  rfl

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
theorem capTargetPhi_boundary (dart : BoundaryDart RS data.keep) :
    data.capTargetPhi (Sum.inl dart.1) =
      Sum.inr (finRotate 3
        (data.crossingBoundaryDartEquiv.symm dart)) := by
  rw [data.capTargetPhi_apply, data.capTargetAlpha_boundary]
  rfl

@[simp]
theorem capTargetPhi_cap (step : Fin 3) :
    data.capTargetPhi (Sum.inr step) =
      Sum.inl (retainedRho RS data.keep
        (data.crossingBoundaryDartEquiv step).1) := by
  rw [data.capTargetPhi_apply, data.capTargetAlpha_cap]
  rfl

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

/-- An internal retained dart returns to the retained carrier after one cap
face step. -/
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

/-- A boundary retained dart visits one cap dart and returns to the retained
carrier after the second cap face step. -/
theorem firstPositiveHitTime_capTargetPhi_boundary
    (dart : BoundaryDart RS data.keep) :
    firstPositiveHitTime data.capTargetPhi data.IsTargetRetained
      (Sum.inl dart.1) trivial = 2 := by
  have hle : firstPositiveHitTime data.capTargetPhi
      data.IsTargetRetained (Sum.inl dart.1) trivial ≤ 2 := by
    apply firstPositiveHitTime_le_of_hit
    · omega
    · simp [pow_two, Equiv.Perm.mul_apply,
        data.capTargetPhi_boundary, data.capTargetPhi_cap,
        IsTargetRetained]
  have hpos := firstPositiveHitTime_pos data.capTargetPhi
    data.IsTargetRetained (Sum.inl dart.1) trivial
  have hneOne : firstPositiveHitTime data.capTargetPhi
      data.IsTargetRetained (Sum.inl dart.1) trivial ≠ 1 := by
    intro hone
    have hhit := firstPositiveHitTime_hits data.capTargetPhi
      data.IsTargetRetained (Sum.inl dart.1) trivial
    rw [hone] at hhit
    simp [data.capTargetPhi_boundary, IsTargetRetained] at hhit
  omega

/-- Eliminating the inserted cap darts turns the cap face permutation into
the retained capped face permutation followed by its boundary cycle. -/
theorem capTargetReturn_eq :
    data.capTargetReturn =
      retainedCappedFacePerm RS data.keep *
        extendBoundaryPerm RS data.keep data.capBoundaryCycle := by
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
      data.capBoundaryCycle internal]
    apply congrArg (retainedRho RS data.keep)
    apply Subtype.ext
    rw [internalAlpha_val]
    exact (retainedCappedAlpha_apply_internal RS data.keep dart hopposite).symm
  · let boundary : BoundaryDart RS data.keep := ⟨dart, hopposite⟩
    unfold capTargetReturn
    simp only [Equiv.permCongr_apply]
    apply data.targetRetainedEquiv.symm.injective
    simp only [Equiv.symm_apply_apply]
    apply Subtype.ext
    rw [nextHitPerm_apply]
    change
      (data.capTargetPhi ^ firstPositiveHitTime data.capTargetPhi
        data.IsTargetRetained (Sum.inl dart) trivial) (Sum.inl dart) = _
    rw [data.firstPositiveHitTime_capTargetPhi_boundary boundary]
    rw [pow_two, Equiv.Perm.mul_apply,
      data.capTargetPhi_boundary boundary, data.capTargetPhi_cap]
    simp only [retainedCappedFacePerm, Equiv.Perm.mul_apply,
      data.targetRetainedEquiv_symm_val, Sum.inl.injEq]
    rw [extendBoundaryPerm_apply_boundary RS data.keep
      data.capBoundaryCycle boundary]
    apply congrArg (retainedRho RS data.keep)
    rw [retainedCappedAlpha_apply_boundary RS data.keep
      (data.capBoundaryCycle boundary).1
      (data.capBoundaryCycle boundary).2]
    rfl

/-- Every transported cap-face cycle contains an old retained dart.  A cap
dart returns to the retained carrier in one face step. -/
theorem exists_capTargetRetained_sameCycle
    (point : RetainedDart RS data.keep ⊕ Fin 3) :
    ∃ dart : RetainedDart RS data.keep,
      data.capTargetPhi.SameCycle point (Sum.inl dart) := by
  rcases point with dart | step
  · exact ⟨dart, Equiv.Perm.SameCycle.refl data.capTargetPhi _⟩
  · refine ⟨retainedRho RS data.keep
      (data.crossingBoundaryDartEquiv step).1, ?_⟩
    simpa only [data.capTargetPhi_cap] using
      Mettapedia.GraphTheory.EquivPermSameCycle.step_right
        data.capTargetPhi (Sum.inr step)

/-- Consequently there is no transported cap-face cycle disjoint from the
old retained dart carrier. -/
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

/-- The cap-face cycle count is exactly the cycle count of its first return
on the old retained darts. -/
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

/-- Transporting the cap dart carrier does not alter the face count. -/
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

/-- With the cap spokes in planar boundary order, first return to the three
exposed retained darts is the identity: each of the three boundary arcs is
closed separately by the cap vertex. -/
theorem planarOrdered_capTargetReturn_nextBoundary_eq_one
    (htwoSided : OrbitFacesTwoSided RS) :
    nextHitPerm (data.planarOrdered htwoSided).capTargetReturn
        (fun dart : RetainedDart RS
            (data.planarOrdered htwoSided).keep =>
          ¬ (data.planarOrdered htwoSided).keep
            (RS.vertOf (RS.alpha dart.1))) = 1 := by
  rw [(data.planarOrdered htwoSided).capTargetReturn_eq]
  rw [nextHitPerm_rewiredRetainedCappedFacePerm]
  have hboundary : (data.planarOrdered htwoSided).capBoundaryCycle =
      (retainedRegionBoundarySuccessor RS
        (data.planarOrdered htwoSided).keep)⁻¹ := by
    convert data.planarOrdered_capBoundaryCycle htwoSided using 1
    rfl
  rw [hboundary]
  simp
  rfl

/-- Thus exactly three cap-face cycles meet the boundary. -/
theorem card_planarOrdered_capTargetReturn_hitOrbit_eq_three
    (htwoSided : OrbitFacesTwoSided RS) :
    Fintype.card
      (HitOrbit (data.planarOrdered htwoSided).capTargetReturn
        (fun dart : RetainedDart RS
            (data.planarOrdered htwoSided).keep =>
          ¬ (data.planarOrdered htwoSided).keep
            (RS.vertOf (RS.alpha dart.1)))) = 3 := by
  rw [card_hitOrbit_eq_nextHit_partition_card,
    data.planarOrdered_capTargetReturn_nextBoundary_eq_one htwoSided]
  change (1 : Equiv.Perm (BoundaryDart RS
    (data.planarOrdered htwoSided).keep)).partition.parts.card = 3
  simp only [Equiv.Perm.parts_partition, Equiv.Perm.cycleType_one,
    zero_add, Equiv.Perm.support_one, Finset.card_empty, Nat.sub_zero,
    Multiset.card_replicate]
  simpa using Fintype.card_congr
    (data.planarOrdered htwoSided).crossingBoundaryDartEquiv.symm

/-- The complete planar cap-face count is three boundary-closing cycles plus
the cycles which never meet an exposed retained dart. -/
theorem card_planarOrdered_cap_faceCycleLengths_eq_three_add_nonHit
    (htwoSided : OrbitFacesTwoSided RS) :
    (faceCycleLengths
        (data.planarOrdered htwoSided).capRotationSystem).card =
      3 + Fintype.card
        (NonHitOrbit (data.planarOrdered htwoSided).capTargetReturn
          (fun dart : RetainedDart RS
              (data.planarOrdered htwoSided).keep =>
            ¬ (data.planarOrdered htwoSided).keep
              (RS.vertOf (RS.alpha dart.1)))) := by
  calc
    (faceCycleLengths
        (data.planarOrdered htwoSided).capRotationSystem).card =
        (data.planarOrdered htwoSided).capTargetReturn.partition.parts.card :=
      (data.planarOrdered htwoSided).card_cap_faceCycleLengths_eq_capTargetReturn_partition
    _ = Fintype.card
        (Quotient (Equiv.Perm.SameCycle.setoid
          (data.planarOrdered htwoSided).capTargetReturn)) :=
      (card_permOrbit_eq_card_partition_parts
        (data.planarOrdered htwoSided).capTargetReturn).symm
    _ = Fintype.card
          (HitOrbit (data.planarOrdered htwoSided).capTargetReturn
            (fun dart : RetainedDart RS
                (data.planarOrdered htwoSided).keep =>
              ¬ (data.planarOrdered htwoSided).keep
                (RS.vertOf (RS.alpha dart.1)))) +
        Fintype.card
          (NonHitOrbit (data.planarOrdered htwoSided).capTargetReturn
            (fun dart : RetainedDart RS
                (data.planarOrdered htwoSided).keep =>
              ¬ (data.planarOrdered htwoSided).keep
                (RS.vertOf (RS.alpha dart.1)))) :=
      card_permOrbit_eq_hit_add_nonHit
        (data.planarOrdered htwoSided).capTargetReturn _
    _ = 3 + Fintype.card
          (NonHitOrbit (data.planarOrdered htwoSided).capTargetReturn
            (fun dart : RetainedDart RS
                (data.planarOrdered htwoSided).keep =>
              ¬ (data.planarOrdered htwoSided).keep
                (RS.vertOf (RS.alpha dart.1)))) := by
      rw [data.card_planarOrdered_capTargetReturn_hitOrbit_eq_three
        htwoSided]

end


end ThreeEdgeCutSideData

end RotationSystem

end Mettapedia.GraphTheory.FourColor
