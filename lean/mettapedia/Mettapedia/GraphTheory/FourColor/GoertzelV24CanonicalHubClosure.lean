import Mettapedia.GraphTheory.FourColor.GoertzelV24VertexSideOpenTangle
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedSpliceFaceCount
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedSpliceAmbientFaceCount

/-!
# Canonical hub closure of a literal vertex shore

For a literal vertex shore, the first-return permutation on the exposed
boundary darts records the partial facial arcs inside the shore.  Closing the
shore with the inverse first-return order closes each such arc separately.

This file proves that statement on the actual `hubPhi` carrier used by the
seam-sphericity theorem.  The result is purely permutation-theoretic: it proves
that distinct hub darts lie on distinct face cycles.  It deliberately does not
claim that the inverse first-return permutation is a single vertex rotation;
that cyclicity is a separate geometric property of a noose boundary.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CanonicalHubClosure

open Equiv Equiv.Perm
open GoertzelV24FaceOrbitPartitionBridge
open GoertzelV24FaceDualConnectedness
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24OrderedCutFaceOrbit
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24PermutationOrbitSurgery
open GoertzelV24PlanarBondBoundaryOrder
open GoertzelV24PlanarBondSpliceEuler
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RetainedSpliceAmbientFaceCount
open GoertzelV24RetainedSpliceEdgeCount
open GoertzelV24RetainedSpliceFaceCount
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24SeamExchange
open GoertzelV24SeamFaceArc
open GoertzelV24VertexSideOpenTangle
open GoertzelV24CompositeSphericity
open GoertzelV24CompositeStructuralData
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24TwoEdgeCutMinimality

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- Transport the hub-closure carrier so the real summand is the old retained
dart carrier rather than its internal/boundary partition. -/
def hubTargetEquiv (RS : RotationSystem V E) (keep : V → Prop) :
    ((InternalDart RS keep ⊕ BoundaryDart RS keep) ⊕
        BoundaryDart RS keep) ≃
      (RetainedDart RS keep ⊕ BoundaryDart RS keep) :=
  Equiv.sumCongr (retainedDartEquivInternalSumBoundary RS keep).symm
    (Equiv.refl _)

/-- The hub face permutation transported to retained darts plus hub darts. -/
def hubTargetPhi
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (ρ : Equiv.Perm (BoundaryDart RS keep)) :
    Equiv.Perm (RetainedDart RS keep ⊕ BoundaryDart RS keep) :=
  (hubTargetEquiv RS keep).permCongr
    (hubPhi (ofVertexSide RS keep outer) ρ)

@[simp]
theorem hubTargetPhi_internal
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (ρ : Equiv.Perm (BoundaryDart RS keep))
    (dart : InternalDart RS keep) :
    hubTargetPhi RS keep outer ρ (Sum.inl dart.1) =
      Sum.inl (retainedRho RS keep
        (internalAlpha RS keep dart).1) := by
  unfold hubTargetPhi
  rw [Equiv.permCongr_apply]
  have hpartition :
      retainedDartEquivInternalSumBoundary RS keep dart.1 =
        Sum.inl dart := by
    simp [retainedDartEquivInternalSumBoundary, dart.2]
  rw [show (hubTargetEquiv RS keep).symm (Sum.inl dart.1) =
      Sum.inl (Sum.inl dart) by
    change Sum.inl (retainedDartEquivInternalSumBoundary RS keep dart.1) = _
    rw [hpartition]]
  simp only [hubPhi, Equiv.Perm.mul_apply, hubAlpha_apply, hubAlphaFun]
  change Sum.inl
      ((retainedDartEquivInternalSumBoundary RS keep).symm
        ((ofVertexSide RS keep outer).rho
          (Sum.inl (internalAlpha RS keep dart)))) = _
  rw [ofVertexSide_rho_underlying]
  rfl

@[simp]
theorem hubTargetPhi_boundary
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (ρ : Equiv.Perm (BoundaryDart RS keep))
    (dart : BoundaryDart RS keep) :
    hubTargetPhi RS keep outer ρ (Sum.inl dart.1) =
      Sum.inr (ρ dart) := by
  unfold hubTargetPhi
  rw [Equiv.permCongr_apply]
  have hpartition :
      retainedDartEquivInternalSumBoundary RS keep dart.1 =
        Sum.inr dart := by
    simp [retainedDartEquivInternalSumBoundary, dart.2]
  rw [show (hubTargetEquiv RS keep).symm (Sum.inl dart.1) =
      Sum.inl (Sum.inr dart) by
    change Sum.inl (retainedDartEquivInternalSumBoundary RS keep dart.1) = _
    rw [hpartition]]
  rfl

@[simp]
theorem hubTargetPhi_hub
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (ρ : Equiv.Perm (BoundaryDart RS keep))
    (dart : BoundaryDart RS keep) :
    hubTargetPhi RS keep outer ρ (Sum.inr dart) =
      Sum.inl (retainedRho RS keep dart.1) := by
  change Sum.inl
      ((retainedDartEquivInternalSumBoundary RS keep).symm
        ((ofVertexSide RS keep outer).rho (Sum.inr dart))) = _
  rw [ofVertexSide_rho_underlying]
  rfl

/-- Predicate selecting the transported old retained darts. -/
def IsTargetRetained
    (RS : RotationSystem V E) (keep : V → Prop) :
    RetainedDart RS keep ⊕ BoundaryDart RS keep → Prop
  | Sum.inl _ => True
  | Sum.inr _ => False

instance isTargetRetainedDecidablePred
    (RS : RotationSystem V E) (keep : V → Prop) :
    DecidablePred (IsTargetRetained RS keep)
  | Sum.inl _ => isTrue trivial
  | Sum.inr _ => isFalse id

/-- The marked real-dart subtype is canonically the retained-dart carrier. -/
def targetRetainedEquiv
    (RS : RotationSystem V E) (keep : V → Prop) :
    {point // IsTargetRetained RS keep point} ≃ RetainedDart RS keep where
  toFun point := by
    rcases point with ⟨retained | hub, hpoint⟩
    · exact retained
    · exact False.elim hpoint
  invFun retained := ⟨Sum.inl retained, trivial⟩
  left_inv point := by
    rcases point with ⟨retained | hub, hpoint⟩
    · rfl
    · exact False.elim hpoint
  right_inv _ := rfl

@[simp]
theorem targetRetainedEquiv_symm_val
    (RS : RotationSystem V E) (keep : V → Prop)
    (dart : RetainedDart RS keep) :
    ((targetRetainedEquiv RS keep).symm dart).1 = Sum.inl dart :=
  rfl

/-- First return of hub faces to the real retained-dart carrier. -/
def hubTargetReturn
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (ρ : Equiv.Perm (BoundaryDart RS keep)) :
    Equiv.Perm (RetainedDart RS keep) :=
  (targetRetainedEquiv RS keep).permCongr
    (nextHitPerm (hubTargetPhi RS keep outer ρ)
      (IsTargetRetained RS keep))

theorem firstPositiveHitTime_hubTargetPhi_internal
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (ρ : Equiv.Perm (BoundaryDart RS keep))
    (dart : InternalDart RS keep) :
    firstPositiveHitTime (hubTargetPhi RS keep outer ρ)
      (IsTargetRetained RS keep) (Sum.inl dart.1) trivial = 1 := by
  have hle : firstPositiveHitTime (hubTargetPhi RS keep outer ρ)
      (IsTargetRetained RS keep) (Sum.inl dart.1) trivial ≤ 1 := by
    apply firstPositiveHitTime_le_of_hit
    · omega
    · simp [IsTargetRetained]
  have hpos := firstPositiveHitTime_pos (hubTargetPhi RS keep outer ρ)
    (IsTargetRetained RS keep) (Sum.inl dart.1) trivial
  omega

theorem firstPositiveHitTime_hubTargetPhi_boundary
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (ρ : Equiv.Perm (BoundaryDart RS keep))
    (dart : BoundaryDart RS keep) :
    firstPositiveHitTime (hubTargetPhi RS keep outer ρ)
      (IsTargetRetained RS keep) (Sum.inl dart.1) trivial = 2 := by
  have hle : firstPositiveHitTime (hubTargetPhi RS keep outer ρ)
      (IsTargetRetained RS keep) (Sum.inl dart.1) trivial ≤ 2 := by
    apply firstPositiveHitTime_le_of_hit
    · omega
    · simp [pow_two, Equiv.Perm.mul_apply, IsTargetRetained]
  have hpos := firstPositiveHitTime_pos (hubTargetPhi RS keep outer ρ)
    (IsTargetRetained RS keep) (Sum.inl dart.1) trivial
  have hneOne : firstPositiveHitTime (hubTargetPhi RS keep outer ρ)
      (IsTargetRetained RS keep) (Sum.inl dart.1) trivial ≠ 1 := by
    intro hone
    have hhit := firstPositiveHitTime_hits (hubTargetPhi RS keep outer ρ)
      (IsTargetRetained RS keep) (Sum.inl dart.1) trivial
    rw [hone] at hhit
    simp [IsTargetRetained] at hhit
  omega

/-- Eliminating the hub darts inserts the hub rotation at boundary points of
the capped retained face walk. -/
theorem hubTargetReturn_eq
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (ρ : Equiv.Perm (BoundaryDart RS keep)) :
    hubTargetReturn RS keep outer ρ =
      retainedCappedFacePerm RS keep *
        extendBoundaryPerm RS keep ρ := by
  apply Equiv.ext
  intro dart
  by_cases hopposite : keep (RS.vertOf (RS.alpha dart.1))
  · let internal : InternalDart RS keep := ⟨dart, hopposite⟩
    unfold hubTargetReturn
    simp only [Equiv.permCongr_apply]
    apply (targetRetainedEquiv RS keep).symm.injective
    simp only [Equiv.symm_apply_apply]
    apply Subtype.ext
    rw [nextHitPerm_apply]
    change
      ((hubTargetPhi RS keep outer ρ) ^
        firstPositiveHitTime (hubTargetPhi RS keep outer ρ)
          (IsTargetRetained RS keep) (Sum.inl dart) trivial)
        (Sum.inl dart) = _
    rw [firstPositiveHitTime_hubTargetPhi_internal RS keep outer ρ internal]
    rw [pow_one]
    change hubTargetPhi RS keep outer ρ (Sum.inl internal.1) = _
    rw [hubTargetPhi_internal]
    simp only [retainedCappedFacePerm, Equiv.Perm.mul_apply,
      targetRetainedEquiv_symm_val, Sum.inl.injEq]
    rw [extendBoundaryPerm_apply_internal RS keep ρ internal]
    apply congrArg (retainedRho RS keep)
    apply Subtype.ext
    rw [internalAlpha_val]
    exact (retainedCappedAlpha_apply_internal RS keep dart hopposite).symm
  · let boundary : BoundaryDart RS keep := ⟨dart, hopposite⟩
    unfold hubTargetReturn
    simp only [Equiv.permCongr_apply]
    apply (targetRetainedEquiv RS keep).symm.injective
    simp only [Equiv.symm_apply_apply]
    apply Subtype.ext
    rw [nextHitPerm_apply]
    change
      ((hubTargetPhi RS keep outer ρ) ^
        firstPositiveHitTime (hubTargetPhi RS keep outer ρ)
          (IsTargetRetained RS keep) (Sum.inl dart) trivial)
        (Sum.inl dart) = _
    rw [firstPositiveHitTime_hubTargetPhi_boundary RS keep outer ρ boundary]
    rw [pow_two, Equiv.Perm.mul_apply]
    change hubTargetPhi RS keep outer ρ
      (hubTargetPhi RS keep outer ρ (Sum.inl boundary.1)) = _
    rw [hubTargetPhi_boundary, hubTargetPhi_hub]
    simp only [retainedCappedFacePerm, Equiv.Perm.mul_apply,
      targetRetainedEquiv_symm_val, Sum.inl.injEq]
    rw [extendBoundaryPerm_apply_boundary RS keep ρ boundary]
    apply congrArg (retainedRho RS keep)
    rw [retainedCappedAlpha_apply_boundary RS keep
      (ρ boundary).1 (ρ boundary).2]

/-- On boundary darts, the canonical hub return is the identity. -/
theorem nextHitPerm_hubTargetReturn_canonical_eq_one
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep) :
    nextHitPerm
        (hubTargetReturn RS keep outer (canonicalHubRotation RS keep))
        (fun dart : RetainedDart RS keep =>
          ¬ keep (RS.vertOf (RS.alpha dart.1))) = 1 := by
  rw [hubTargetReturn_eq]
  rw [nextHitPerm_rewiredRetainedCappedFacePerm]
  simp [canonicalHubRotation]
  rfl

/-- Closing a literal shore by the inverse of its boundary first-return order
puts every hub dart on a different face.  This is the exact
`HubFacesDistinct` premise of the seam face-count theorem. -/
theorem hubFacesDistinct_canonical
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep) :
    HubFacesDistinct (ofVertexSide RS keep outer)
      (canonicalHubRotation RS keep) := by
  intro first second hcycle
  let ρ := canonicalHubRotation RS keep
  let firstPrev : BoundaryDart RS keep := ρ.symm first
  let secondPrev : BoundaryDart RS keep := ρ.symm second
  have htarget :
      (hubTargetPhi RS keep outer ρ).SameCycle
        (Sum.inr first) (Sum.inr second) := by
    exact (permCongr_sameCycle_iff (hubTargetEquiv RS keep)
      (hubPhi (ofVertexSide RS keep outer) ρ)
      (Sum.inr first) (Sum.inr second)).2 hcycle
  have hfirstStep :
      (hubTargetPhi RS keep outer ρ).SameCycle
        (Sum.inl firstPrev.1) (Sum.inr first) := by
    have hstep := Mettapedia.GraphTheory.EquivPermSameCycle.step_right
      (hubTargetPhi RS keep outer ρ) (Sum.inl firstPrev.1)
    simpa [firstPrev] using hstep
  have hsecondStep :
      (hubTargetPhi RS keep outer ρ).SameCycle
        (Sum.inl secondPrev.1) (Sum.inr second) := by
    have hstep := Mettapedia.GraphTheory.EquivPermSameCycle.step_right
      (hubTargetPhi RS keep outer ρ) (Sum.inl secondPrev.1)
    simpa [secondPrev] using hstep
  have hreal :
      (hubTargetPhi RS keep outer ρ).SameCycle
        (Sum.inl firstPrev.1) (Sum.inl secondPrev.1) :=
    hfirstStep.trans (htarget.trans hsecondStep.symm)
  let firstReal :
      {point // IsTargetRetained RS keep point} :=
    ⟨Sum.inl firstPrev.1, trivial⟩
  let secondReal :
      {point // IsTargetRetained RS keep point} :=
    ⟨Sum.inl secondPrev.1, trivial⟩
  have hnextReal :
      (nextHitPerm (hubTargetPhi RS keep outer ρ)
        (IsTargetRetained RS keep)).SameCycle firstReal secondReal :=
    (nextHitPerm_sameCycle_iff
      (hubTargetPhi RS keep outer ρ) (IsTargetRetained RS keep)
      firstReal secondReal).2 hreal
  have hreturn :
      (hubTargetReturn RS keep outer ρ).SameCycle
        firstPrev.1 secondPrev.1 := by
    exact (permCongr_sameCycle_iff (targetRetainedEquiv RS keep)
      (nextHitPerm (hubTargetPhi RS keep outer ρ)
        (IsTargetRetained RS keep)) firstReal secondReal).2 hnextReal
  let firstBoundary :
      {dart : RetainedDart RS keep //
        ¬ keep (RS.vertOf (RS.alpha dart.1))} :=
    ⟨firstPrev.1, firstPrev.2⟩
  let secondBoundary :
      {dart : RetainedDart RS keep //
        ¬ keep (RS.vertOf (RS.alpha dart.1))} :=
    ⟨secondPrev.1, secondPrev.2⟩
  have hboundary :
      (nextHitPerm
        (hubTargetReturn RS keep outer ρ)
        (fun dart : RetainedDart RS keep =>
          ¬ keep (RS.vertOf (RS.alpha dart.1)))).SameCycle
          firstBoundary secondBoundary :=
    (nextHitPerm_sameCycle_iff
      (hubTargetReturn RS keep outer ρ)
      (fun dart : RetainedDart RS keep =>
        ¬ keep (RS.vertOf (RS.alpha dart.1)))
      firstBoundary secondBoundary).2 hreturn
  have hboundaryEq : firstBoundary = secondBoundary := by
    rw [show ρ = canonicalHubRotation RS keep by rfl,
      nextHitPerm_hubTargetReturn_canonical_eq_one] at hboundary
    simpa using hboundary
  have hprev : firstPrev = secondPrev := by
    apply Subtype.ext
    exact congrArg (fun point => point.1) hboundaryEq
  exact ρ.symm.injective hprev

/-! ## Exact canonical-hub face count -/

/-- Every hub-closure face contains a real retained dart. -/
theorem exists_targetRetained_sameCycle
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (ρ : Equiv.Perm (BoundaryDart RS keep))
    (point : RetainedDart RS keep ⊕ BoundaryDart RS keep) :
    ∃ dart : RetainedDart RS keep,
      (hubTargetPhi RS keep outer ρ).SameCycle point (Sum.inl dart) := by
  rcases point with dart | hub
  · exact ⟨dart, Equiv.Perm.SameCycle.refl _ _⟩
  · refine ⟨retainedRho RS keep hub.1, ?_⟩
    simpa only [hubTargetPhi_hub] using
      Mettapedia.GraphTheory.EquivPermSameCycle.step_right
        (hubTargetPhi RS keep outer ρ) (Sum.inr hub)

/-- Therefore no face cycle of the transported hub closure avoids the real
retained-dart carrier. -/
theorem targetNonHitOrbit_isEmpty
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (ρ : Equiv.Perm (BoundaryDart RS keep))
    (orbit : NonHitOrbit (hubTargetPhi RS keep outer ρ)
      (IsTargetRetained RS keep)) : False := by
  rcases exists_targetRetained_sameCycle RS keep outer ρ orbit.1.out with
    ⟨dart, hdart⟩
  exact (nonHitOrbit_not_hit_of_sameCycle
    (hubTargetPhi RS keep outer ρ) (IsTargetRetained RS keep)
    orbit (Sum.inl dart) hdart) trivial

theorem card_targetNonHitOrbit_eq_zero
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (ρ : Equiv.Perm (BoundaryDart RS keep)) :
    Fintype.card (NonHitOrbit (hubTargetPhi RS keep outer ρ)
      (IsTargetRetained RS keep)) = 0 := by
  rw [Fintype.card_eq_zero_iff]
  exact ⟨fun orbit => False.elim
    (targetNonHitOrbit_isEmpty RS keep outer ρ orbit)⟩

/-- Eliminating the inserted hub darts preserves the number of face cycles. -/
theorem card_hubTargetPhi_partition_eq_hubTargetReturn_partition
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (ρ : Equiv.Perm (BoundaryDart RS keep)) :
    (hubTargetPhi RS keep outer ρ).partition.parts.card =
      (hubTargetReturn RS keep outer ρ).partition.parts.card := by
  calc
    (hubTargetPhi RS keep outer ρ).partition.parts.card =
        Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid
          (hubTargetPhi RS keep outer ρ))) :=
      (card_permOrbit_eq_card_partition_parts _).symm
    _ = Fintype.card
          (HitOrbit (hubTargetPhi RS keep outer ρ)
            (IsTargetRetained RS keep)) +
        Fintype.card
          (NonHitOrbit (hubTargetPhi RS keep outer ρ)
            (IsTargetRetained RS keep)) :=
      card_permOrbit_eq_hit_add_nonHit _ _
    _ = (nextHitPerm (hubTargetPhi RS keep outer ρ)
          (IsTargetRetained RS keep)).partition.parts.card := by
      rw [card_hitOrbit_eq_nextHit_partition_card,
        card_targetNonHitOrbit_eq_zero, Nat.add_zero]
    _ = (hubTargetReturn RS keep outer ρ).partition.parts.card := by
      symm
      exact card_permCongr_partition_parts (targetRetainedEquiv RS keep)
        (nextHitPerm (hubTargetPhi RS keep outer ρ)
          (IsTargetRetained RS keep))

/-- The boundary-marked subtype of retained darts is just the displayed
boundary-dart type. -/
def retainedBoundaryEquiv
    (RS : RotationSystem V E) (keep : V → Prop) :
    {dart : RetainedDart RS keep //
      ¬ keep (RS.vertOf (RS.alpha dart.1))} ≃ BoundaryDart RS keep where
  toFun dart := ⟨dart.1, dart.2⟩
  invFun dart := ⟨dart.1, dart.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The canonical hub has exactly one boundary-meeting face per boundary
dart. -/
theorem card_hubTargetReturn_hitOrbit_eq_boundary
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep) :
    Fintype.card
      (HitOrbit
        (hubTargetReturn RS keep outer (canonicalHubRotation RS keep))
        (fun dart : RetainedDart RS keep =>
          ¬ keep (RS.vertOf (RS.alpha dart.1)))) =
      Fintype.card (BoundaryDart RS keep) := by
  rw [card_hitOrbit_eq_nextHit_partition_card,
    nextHitPerm_hubTargetReturn_canonical_eq_one]
  simp only [Equiv.Perm.parts_partition, Equiv.Perm.cycleType_one,
    zero_add, Equiv.Perm.support_one, Finset.card_empty, Nat.sub_zero,
    Multiset.card_replicate]
  exact Fintype.card_congr (retainedBoundaryEquiv RS keep)

/-- Boundary-avoiding canonical-hub return cycles. -/
abbrev CanonicalNonBoundaryOrbit
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep) :=
  NonHitOrbit
    (hubTargetReturn RS keep outer (canonicalHubRotation RS keep))
    (fun dart : RetainedDart RS keep =>
      ¬ keep (RS.vertOf (RS.alpha dart.1)))

/-- The complete canonical hub-face count is one boundary face per port plus
the cycles which never reach an exposed retained dart. -/
theorem card_canonicalHub_face_eq_boundary_add_nonHit
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep) :
    (hubPhi (ofVertexSide RS keep outer)
        (canonicalHubRotation RS keep)).partition.parts.card =
      Fintype.card (BoundaryDart RS keep) +
        Fintype.card (CanonicalNonBoundaryOrbit RS keep outer) := by
  calc
    (hubPhi (ofVertexSide RS keep outer)
        (canonicalHubRotation RS keep)).partition.parts.card =
        (hubTargetPhi RS keep outer
          (canonicalHubRotation RS keep)).partition.parts.card :=
      (card_permCongr_partition_parts (hubTargetEquiv RS keep)
        (hubPhi (ofVertexSide RS keep outer)
          (canonicalHubRotation RS keep))).symm
    _ = (hubTargetReturn RS keep outer
          (canonicalHubRotation RS keep)).partition.parts.card :=
      card_hubTargetPhi_partition_eq_hubTargetReturn_partition
        RS keep outer _
    _ = Fintype.card
          (Quotient (Equiv.Perm.SameCycle.setoid
            (hubTargetReturn RS keep outer
              (canonicalHubRotation RS keep)))) :=
      (card_permOrbit_eq_card_partition_parts _).symm
    _ = Fintype.card
          (HitOrbit
            (hubTargetReturn RS keep outer (canonicalHubRotation RS keep))
            (fun dart : RetainedDart RS keep =>
              ¬ keep (RS.vertOf (RS.alpha dart.1)))) +
        Fintype.card (CanonicalNonBoundaryOrbit RS keep outer) :=
      card_permOrbit_eq_hit_add_nonHit _ _
    _ = Fintype.card (BoundaryDart RS keep) +
        Fintype.card (CanonicalNonBoundaryOrbit RS keep outer) := by
      rw [card_hubTargetReturn_hitOrbit_eq_boundary]

/-- Away from the boundary, a canonical-hub return step is exactly the old
ambient face step after forgetting the retainedness proof. -/
theorem hubTargetReturn_internal_val
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (dart : InternalDart RS keep) :
    (hubTargetReturn RS keep outer (canonicalHubRotation RS keep)
      dart.1).1 = RS.phi dart.1.1 := by
  rw [hubTargetReturn_eq]
  simp only [Equiv.Perm.mul_apply,
    extendBoundaryPerm_apply_internal RS keep
      (canonicalHubRotation RS keep) dart,
    retainedCappedFacePerm,
    retainedCappedAlpha_apply_internal RS keep dart.1 dart.2,
    retainedRho_val]
  rfl

/-- Every point on a boundary-avoiding canonical-hub face is an internal old
dart. -/
theorem canonicalNonBoundaryOrbit_all_internal
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (orbit : CanonicalNonBoundaryOrbit RS keep outer)
    (point : {point //
      (hubTargetReturn RS keep outer (canonicalHubRotation RS keep)).SameCycle
        orbit.1.out point}) :
    ∃ dart : InternalDart RS keep, point.1 = dart.1 := by
  have hnotBoundary := nonHitOrbit_not_hit_of_sameCycle
    (hubTargetReturn RS keep outer (canonicalHubRotation RS keep))
    (fun dart : RetainedDart RS keep =>
      ¬ keep (RS.vertOf (RS.alpha dart.1)))
    orbit point.1 point.2
  have hopposite : keep (RS.vertOf (RS.alpha point.1.1)) := by
    simpa using hnotBoundary
  exact ⟨⟨point.1, hopposite⟩, rfl⟩

/-- Forgetting retainedness commutes with face steps along a
boundary-avoiding canonical-hub cycle. -/
theorem canonicalNonBoundaryOrbit_forget_commutes
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (orbit : CanonicalNonBoundaryOrbit RS keep outer)
    (point : RetainedDart RS keep)
    (hpoint :
      (hubTargetReturn RS keep outer (canonicalHubRotation RS keep)).SameCycle
        orbit.1.out point) :
    (hubTargetReturn RS keep outer (canonicalHubRotation RS keep) point).1 =
      RS.phi point.1 := by
  rcases canonicalNonBoundaryOrbit_all_internal RS keep outer orbit
      ⟨point, hpoint⟩ with ⟨dart, rfl⟩
  exact hubTargetReturn_internal_val RS keep outer dart

/-- Forgetting retainedness maps one complete boundary-avoiding canonical
hub face onto its ambient facial cycle. -/
def canonicalNonBoundaryCycleForget
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (orbit : CanonicalNonBoundaryOrbit RS keep outer) :
    {point //
      (hubTargetReturn RS keep outer (canonicalHubRotation RS keep)).SameCycle
        orbit.1.out point} →
      {dart // RS.phi.SameCycle orbit.1.out.1 dart} :=
  fun point => ⟨point.1.1, by
    rcases point.2.exists_nat_pow_eq with ⟨power, hpower⟩
    have htransport := map_pow_of_map_apply_on_cycle
      (hubTargetReturn RS keep outer (canonicalHubRotation RS keep)) RS.phi
      (fun dart : RetainedDart RS keep => dart.1)
      orbit.1.out
      (canonicalNonBoundaryOrbit_forget_commutes RS keep outer orbit) power
    rw [hpower] at htransport
    rw [htransport]
    exact (Equiv.Perm.sameCycle_pow_right).2
      (Equiv.Perm.SameCycle.refl RS.phi orbit.1.out.1)⟩

theorem canonicalNonBoundaryCycleForget_bijective
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (orbit : CanonicalNonBoundaryOrbit RS keep outer) :
    Function.Bijective
      (canonicalNonBoundaryCycleForget RS keep outer orbit) := by
  let cycleForget := canonicalNonBoundaryCycleForget RS keep outer orbit
  have hinjective : Function.Injective cycleForget := by
    intro first second heq
    apply Subtype.ext
    apply Subtype.ext
    simpa only [cycleForget, canonicalNonBoundaryCycleForget] using
      congrArg Subtype.val heq
  apply (Fintype.bijective_iff_injective_and_card cycleForget).2
  refine ⟨hinjective, ?_⟩
  have hcard := card_sameCycle_eq_of_injective_map_apply
    (hubTargetReturn RS keep outer (canonicalHubRotation RS keep)) RS.phi
    (fun dart : RetainedDart RS keep => dart.1)
    Subtype.val_injective orbit.1.out
    (canonicalNonBoundaryOrbit_forget_commutes RS keep outer orbit)
  simpa only [cycleForget, Fintype.card_subtype] using hcard

/-- The ambient face containing a boundary-avoiding canonical-hub cycle
never visits a deleted vertex. -/
theorem canonicalNonBoundaryOrbit_ambient_avoids_deleted
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (orbit : CanonicalNonBoundaryOrbit RS keep outer) :
    ¬ ∃ point : RS.D, ¬ keep (RS.vertOf point) ∧
      Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) point =
        Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi)
          orbit.1.out.1 := by
  rintro ⟨point, hdeleted, hpoint⟩
  have hcycle : RS.phi.SameCycle orbit.1.out.1 point :=
    Quotient.exact hpoint.symm
  let target : {dart // RS.phi.SameCycle orbit.1.out.1 dart} :=
    ⟨point, hcycle⟩
  rcases (canonicalNonBoundaryCycleForget_bijective
      RS keep outer orbit).2 target with ⟨source, hsource⟩
  apply hdeleted
  have hunderlying : source.1.1 = point := congrArg Subtype.val hsource
  rw [← hunderlying]
  exact source.1.2

/-- Send a boundary-avoiding canonical-hub face to its unchanged ambient
face. -/
def canonicalNonBoundaryOrbitToAmbient
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep) :
    CanonicalNonBoundaryOrbit RS keep outer →
      AmbientRetainedFaceOrbit RS keep :=
  fun orbit =>
    ⟨Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) orbit.1.out.1,
      canonicalNonBoundaryOrbit_ambient_avoids_deleted
        RS keep outer orbit⟩

theorem canonicalNonBoundaryOrbitToAmbient_injective
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep) :
    Function.Injective
      (canonicalNonBoundaryOrbitToAmbient RS keep outer) := by
  intro left right heq
  apply Subtype.ext
  have hambientQuotient :
      Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) left.1.out.1 =
        Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi)
          right.1.out.1 := congrArg Subtype.val heq
  have hambientCycle : RS.phi.SameCycle left.1.out.1 right.1.out.1 :=
    Quotient.exact hambientQuotient
  let target : {dart // RS.phi.SameCycle left.1.out.1 dart} :=
    ⟨right.1.out.1, hambientCycle⟩
  rcases (canonicalNonBoundaryCycleForget_bijective
      RS keep outer left).2 target with ⟨source, hsource⟩
  have hunderlying : source.1.1 = right.1.out.1 := by
    simpa only [canonicalNonBoundaryCycleForget, target] using
      congrArg Subtype.val hsource
  have hsourceEq : source.1 = right.1.out := Subtype.ext hunderlying
  have hcapCycle :
      (hubTargetReturn RS keep outer (canonicalHubRotation RS keep)).SameCycle
        left.1.out right.1.out := by
    simpa only [hsourceEq] using source.2
  exact (Quotient.out_eq left.1).symm.trans
    ((Quotient.sound hcapCycle).trans (Quotient.out_eq right.1))

/-- One canonical-hub return step from an internal dart on an untouched
ambient face remains internal and follows that same ambient face. -/
theorem ambientRetainedFaceOrbit_canonicalReturn_step
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (orbit : AmbientRetainedFaceOrbit RS keep)
    (point : RetainedDart RS keep)
    (hpointNonBoundary :
      ¬ (¬ keep (RS.vertOf (RS.alpha point.1))))
    (hpointCycle : RS.phi.SameCycle orbit.1.out point.1) :
    ¬ (¬ keep (RS.vertOf (RS.alpha (hubTargetReturn RS keep outer
        (canonicalHubRotation RS keep) point).1))) ∧
      RS.phi.SameCycle orbit.1.out
        (hubTargetReturn RS keep outer (canonicalHubRotation RS keep)
          point).1 := by
  have hopposite : keep (RS.vertOf (RS.alpha point.1)) := by
    simpa using hpointNonBoundary
  let internal : InternalDart RS keep := ⟨point, hopposite⟩
  have hstep :
      (hubTargetReturn RS keep outer (canonicalHubRotation RS keep)
        point).1 = RS.phi point.1 := by
    simpa only [internal] using
      hubTargetReturn_internal_val RS keep outer internal
  have hnextCycle : RS.phi.SameCycle orbit.1.out
      (hubTargetReturn RS keep outer (canonicalHubRotation RS keep)
        point).1 := by
    rw [hstep]
    exact hpointCycle.trans
      (Mettapedia.GraphTheory.EquivPermSameCycle.step_right RS.phi point.1)
  have hfollowingCycle : RS.phi.SameCycle orbit.1.out
      (RS.phi (hubTargetReturn RS keep outer
        (canonicalHubRotation RS keep) point).1) :=
    hnextCycle.trans
      (Mettapedia.GraphTheory.EquivPermSameCycle.step_right RS.phi _)
  have hfollowingKeep := ambientRetainedFaceOrbit_keep RS keep orbit
    (RS.phi (hubTargetReturn RS keep outer
      (canonicalHubRotation RS keep) point).1) hfollowingCycle
  refine ⟨?_, hnextCycle⟩
  intro hboundary
  apply hboundary
  rw [← RS.vert_phi_eq_vert_alpha]
  exact hfollowingKeep

/-- Every iterate from a chosen dart of an untouched ambient face remains
off the boundary and continues around the original ambient face. -/
theorem ambientRetainedFaceOrbit_canonicalReturn_pow
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (orbit : AmbientRetainedFaceOrbit RS keep) (power : Nat) :
    let root : RetainedDart RS keep :=
      (ambientRetainedFaceOrbitInternalDart RS keep orbit).1
    ¬ (¬ keep (RS.vertOf (RS.alpha
        ((hubTargetReturn RS keep outer (canonicalHubRotation RS keep) ^
          power) root).1))) ∧
      RS.phi.SameCycle orbit.1.out
        ((hubTargetReturn RS keep outer (canonicalHubRotation RS keep) ^
          power) root).1 := by
  let root : RetainedDart RS keep :=
    (ambientRetainedFaceOrbitInternalDart RS keep orbit).1
  change ¬ (¬ keep (RS.vertOf (RS.alpha
      ((hubTargetReturn RS keep outer (canonicalHubRotation RS keep) ^
        power) root).1))) ∧
    RS.phi.SameCycle orbit.1.out
      ((hubTargetReturn RS keep outer (canonicalHubRotation RS keep) ^
        power) root).1
  induction power with
  | zero =>
      refine ⟨by
        simpa [root] using
          (ambientRetainedFaceOrbitInternalDart RS keep orbit).2, ?_⟩
      change RS.phi.SameCycle orbit.1.out orbit.1.out
      exact Equiv.Perm.SameCycle.refl RS.phi orbit.1.out
  | succ power ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact ambientRetainedFaceOrbit_canonicalReturn_step
        RS keep outer orbit _ ih.1 ih.2

/-- Construct the boundary-avoiding canonical-hub face represented by an
untouched ambient face. -/
def ambientRetainedFaceOrbitToCanonicalNonBoundary
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (orbit : AmbientRetainedFaceOrbit RS keep) :
    CanonicalNonBoundaryOrbit RS keep outer :=
  let root : RetainedDart RS keep :=
    (ambientRetainedFaceOrbitInternalDart RS keep orbit).1
  ⟨Quotient.mk (Equiv.Perm.SameCycle.setoid
      (hubTargetReturn RS keep outer (canonicalHubRotation RS keep))) root, by
    rintro ⟨point, hboundary, hpoint⟩
    have hcycle :
        (hubTargetReturn RS keep outer
          (canonicalHubRotation RS keep)).SameCycle root point :=
      (Quotient.exact hpoint).symm
    rcases hcycle.exists_nat_pow_eq with ⟨power, hpower⟩
    have hnonBoundary :=
      (ambientRetainedFaceOrbit_canonicalReturn_pow
        RS keep outer orbit power).1
    exact hnonBoundary (hpower.symm ▸ hboundary)⟩

theorem canonicalNonBoundaryOrbitToAmbient_surjective
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep) :
    Function.Surjective
      (canonicalNonBoundaryOrbitToAmbient RS keep outer) := by
  intro orbit
  let source := ambientRetainedFaceOrbitToCanonicalNonBoundary
    RS keep outer orbit
  refine ⟨source, ?_⟩
  apply Subtype.ext
  let root : RetainedDart RS keep :=
    (ambientRetainedFaceOrbitInternalDart RS keep orbit).1
  have hsourceCycle :
      (hubTargetReturn RS keep outer
        (canonicalHubRotation RS keep)).SameCycle source.1.out root := by
    have hquot :
        Quotient.mk (Equiv.Perm.SameCycle.setoid
          (hubTargetReturn RS keep outer (canonicalHubRotation RS keep)))
            source.1.out =
          Quotient.mk (Equiv.Perm.SameCycle.setoid
            (hubTargetReturn RS keep outer (canonicalHubRotation RS keep)))
            root := calc
      Quotient.mk (Equiv.Perm.SameCycle.setoid
          (hubTargetReturn RS keep outer (canonicalHubRotation RS keep)))
          source.1.out = source.1 := Quotient.out_eq source.1
      _ = Quotient.mk (Equiv.Perm.SameCycle.setoid
          (hubTargetReturn RS keep outer (canonicalHubRotation RS keep)))
          root := by rfl
    exact Quotient.exact hquot
  let sourcePoint : {point //
      (hubTargetReturn RS keep outer
        (canonicalHubRotation RS keep)).SameCycle source.1.out point} :=
    ⟨root, hsourceCycle⟩
  have hambientCycle :=
    (canonicalNonBoundaryCycleForget RS keep outer source sourcePoint).2
  change RS.phi.SameCycle source.1.out.1 sourcePoint.1.1 at hambientCycle
  have hrootUnderlying : sourcePoint.1.1 = orbit.1.out := by rfl
  have hambientOut : RS.phi.SameCycle source.1.out.1 orbit.1.out := by
    rw [hrootUnderlying] at hambientCycle
    exact hambientCycle
  change Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi)
      source.1.out.1 = orbit.1
  exact (Quotient.sound hambientOut).trans (Quotient.out_eq orbit.1)

/-- Boundary-avoiding canonical-hub faces are canonically the untouched
ambient faces. -/
def canonicalNonBoundaryOrbitEquivAmbientRetainedFaceOrbit
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep) :
    CanonicalNonBoundaryOrbit RS keep outer ≃
      AmbientRetainedFaceOrbit RS keep :=
  Equiv.ofBijective (canonicalNonBoundaryOrbitToAmbient RS keep outer)
    ⟨canonicalNonBoundaryOrbitToAmbient_injective RS keep outer,
      canonicalNonBoundaryOrbitToAmbient_surjective RS keep outer⟩

theorem card_canonicalNonBoundaryOrbit_eq_ambientRetainedFaceOrbit
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep) :
    Fintype.card (CanonicalNonBoundaryOrbit RS keep outer) =
      Fintype.card (AmbientRetainedFaceOrbit RS keep) :=
  Fintype.card_congr
    (canonicalNonBoundaryOrbitEquivAmbientRetainedFaceOrbit
      RS keep outer)

/-- A canonical hub closure has exactly the untouched ambient faces plus one
separately closed face for every boundary dart. -/
theorem card_canonicalHub_face_eq_boundary_add_ambient
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep) :
    (hubPhi (ofVertexSide RS keep outer)
        (canonicalHubRotation RS keep)).partition.parts.card =
      Fintype.card (BoundaryDart RS keep) +
        Fintype.card (AmbientRetainedFaceOrbit RS keep) := by
  rw [card_canonicalHub_face_eq_boundary_add_nonHit,
    card_canonicalNonBoundaryOrbit_eq_ambientRetainedFaceOrbit]

/-! ## Edge count and spherical cap arithmetic -/

/-- Map an intact retained dart to its ambient retained internal edge. -/
def internalDartToInternalEdge
    (RS : RotationSystem V E) (keep : V → Prop)
    (dart : InternalDart RS keep) : RetainedInternalEdge RS keep :=
  ⟨RS.edgeOf dart.1.1, ⟨dart, rfl⟩⟩

/-- A fiber of the intact-dart-to-edge map is the old two-dart edge fiber. -/
def internalDartFiberEquivDartsOn
    (RS : RotationSystem V E) (keep : V → Prop)
    (edge : RetainedInternalEdge RS keep) :
    {dart : InternalDart RS keep //
      internalDartToInternalEdge RS keep dart = edge} ≃
      ↑(RS.dartsOn edge.1) := by
  let toDartsOn :
      {dart : InternalDart RS keep //
        internalDartToInternalEdge RS keep dart = edge} →
        ↑(RS.dartsOn edge.1) :=
    fun dart => ⟨dart.1.1.1, by
      apply RS.mem_dartsOn.mpr
      exact congrArg Subtype.val dart.2⟩
  apply Equiv.ofBijective toDartsOn
  constructor
  · intro left right heq
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    simpa only [toDartsOn] using congrArg Subtype.val heq
  · intro dart
    rcases edge.2 with ⟨root, hroot⟩
    rcases RS.edge_fiber_two_cases hroot
        (RS.mem_dartsOn.mp dart.2) with hsame | hopposite
    · let source : {dart : InternalDart RS keep //
          internalDartToInternalEdge RS keep dart = edge} :=
        ⟨root, by
          apply Subtype.ext
          exact hroot⟩
      refine ⟨source, ?_⟩
      apply Subtype.ext
      exact hsame.symm
    · let opposite := internalAlpha RS keep root
      let source : {dart : InternalDart RS keep //
          internalDartToInternalEdge RS keep dart = edge} :=
        ⟨opposite, by
          apply Subtype.ext
          change RS.edgeOf opposite.1.1 = edge.1
          rw [internalAlpha_val, RS.edge_alpha, hroot]⟩
      refine ⟨source, ?_⟩
      apply Subtype.ext
      change opposite.1.1 = dart.1
      rw [internalAlpha_val]
      exact hopposite.symm

theorem card_internalDartFiber_eq_two
    (RS : RotationSystem V E) (keep : V → Prop)
    (edge : RetainedInternalEdge RS keep) :
    Fintype.card {dart : InternalDart RS keep //
      internalDartToInternalEdge RS keep dart = edge} = 2 := by
  calc
    Fintype.card {dart : InternalDart RS keep //
        internalDartToInternalEdge RS keep dart = edge} =
        Fintype.card ↑(RS.dartsOn edge.1) :=
      Fintype.card_congr (internalDartFiberEquivDartsOn RS keep edge)
    _ = (RS.dartsOn edge.1).card := Fintype.card_coe _
    _ = 2 := RS.dartsOn_card_two edge.1

/-- Every retained internal edge contributes its two old darts. -/
theorem card_internalDart_eq_twice_internalEdge
    (RS : RotationSystem V E) (keep : V → Prop) :
    Fintype.card (InternalDart RS keep) =
      2 * Fintype.card (RetainedInternalEdge RS keep) := by
  calc
    Fintype.card (InternalDart RS keep) =
        Fintype.card (Σ edge : RetainedInternalEdge RS keep,
          {dart : InternalDart RS keep //
            internalDartToInternalEdge RS keep dart = edge}) :=
      Fintype.card_congr
        (Equiv.sigmaFiberEquiv
          (internalDartToInternalEdge RS keep)).symm
    _ = ∑ edge : RetainedInternalEdge RS keep,
          Fintype.card {dart : InternalDart RS keep //
            internalDartToInternalEdge RS keep dart = edge} :=
      Fintype.card_sigma
    _ = 2 * Fintype.card (RetainedInternalEdge RS keep) := by
      simp_rw [card_internalDartFiber_eq_two]
      simp [mul_comm]

/-- The pairing orbits of a hub closure are its retained internal edges plus
one spoke for every boundary dart. -/
theorem orbitCount_hubAlpha_ofVertexSide
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep) :
    orbitCount (hubAlpha (ofVertexSide RS keep outer)) =
      Fintype.card (RetainedInternalEdge RS keep) +
        Fintype.card (BoundaryDart RS keep) := by
  have hhub := GoertzelV24CompositeSphericity.two_mul_orbitCount_hubAlpha
    (ofVertexSide RS keep outer)
  have hinternal := card_internalDart_eq_twice_internalEdge RS keep
  omega

/-- Exact side rank is the only Euler input needed once the canonical hub
order has been chosen. -/
theorem closedSideSpherical_canonical_of_faceRank
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (hfaceRank :
      Fintype.card (AmbientRetainedFaceOrbit RS keep) +
          Fintype.card (RetainedVertex keep) =
        Fintype.card (RetainedInternalEdge RS keep) + 1) :
    ClosedSideSpherical (ofVertexSide RS keep outer)
      (canonicalHubRotation RS keep) := by
  have hfacesPartition :=
    card_canonicalHub_face_eq_boundary_add_ambient RS keep outer
  have hfaces :
      orbitCount (hubPhi (ofVertexSide RS keep outer)
        (canonicalHubRotation RS keep)) =
        Fintype.card (BoundaryDart RS keep) +
          Fintype.card (AmbientRetainedFaceOrbit RS keep) := by
    calc
      orbitCount (hubPhi (ofVertexSide RS keep outer)
          (canonicalHubRotation RS keep)) =
          (hubPhi (ofVertexSide RS keep outer)
            (canonicalHubRotation RS keep)).partition.parts.card :=
        card_permOrbit_eq_card_partition_parts _
      _ = _ := hfacesPartition
  have hedges := orbitCount_hubAlpha_ofVertexSide RS keep outer
  unfold ClosedSideSpherical
  change Fintype.card (RetainedVertex keep) + 1 + _ = _
  omega

section GraphBacked

variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- For a connected graph-backed spherical bond, the exact side-rank theorem
discharges the canonical hub closure's Euler equality. -/
theorem closedSideSpherical_canonical_of_planarBond
    (rotation : SimpleGraphDartRotation.Data G)
    (deleted : Finset V)
    (outer : RetainedDart rotation.toRotationSystem
      (deletedRegionKeep deleted))
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hretainedConnected :
      (G.induce {vertex | deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex |
        ¬ deletedRegionKeep deleted vertex}).Connected) :
    ClosedSideSpherical
      (ofVertexSide rotation.toRotationSystem
        (deletedRegionKeep deleted) outer)
      (canonicalHubRotation rotation.toRotationSystem
        (deletedRegionKeep deleted)) := by
  have hranks := planarBond_exact_sideRanks_and_transitionCount
    rotation deleted hsphere htwoSided hconnected hrotation
      hretainedConnected hdeletedConnected
  have hrank := hranks.1
  have hambient := card_ambientRetainedFaceOrbit_eq_allOnSide
    rotation.toRotationSystem (deletedRegionKeep deleted)
  have hvertices :
      sideVertexCount (deletedRegionKeep deleted) =
        Fintype.card (RetainedVertex (deletedRegionKeep deleted)) :=
    sideVertexCount_eq_card_sideVertex _
  have hedges := card_retainedInternalEdge_eq_allOnSide rotation
    (deletedRegionKeep deleted)
  apply closedSideSpherical_canonical_of_faceRank
  omega

end GraphBacked

/-! ## Canonical two-shore splice -/

/-- Two literal connected shores with opposite first-return orders and exact
side ranks feed the complete structural seam theorem with no remaining cap
algebra hypotheses.  Geometry is isolated in the opposite-order and side-rank
premises. -/
def bridgelessSphericalCubicMapData_ofVertexSides_canonical
    (RS : RotationSystem V E) (keepL keepR : V → Prop)
    (outerL : RetainedDart RS keepL) (outerR : RetainedDart RS keepR)
    (matching : BoundaryDart RS keepL ≃ BoundaryDart RS keepR)
    (hconnectedL :
      ((rotationPrimalGraph RS).induce {vertex | keepL vertex}).Connected)
    (hconnectedR :
      ((rotationPrimalGraph RS).induce {vertex | keepR vertex}).Connected)
    (hbridgeless : (toMultigraph RS).Bridgeless)
    (p₀ q₀ : BoundaryDart RS keepL) (hpq : p₀ ≠ q₀)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (hopposite : ∀ b : BoundaryDart RS keepL,
      retainedRegionBoundarySuccessor RS keepR
          (matching (retainedRegionBoundarySuccessor RS keepL b)) =
        matching b)
    (hfaceRankL :
      Fintype.card (AmbientRetainedFaceOrbit RS keepL) +
          Fintype.card (RetainedVertex keepL) =
        Fintype.card (RetainedInternalEdge RS keepL) + 1)
    (hfaceRankR :
      Fintype.card (AmbientRetainedFaceOrbit RS keepR) +
          Fintype.card (RetainedVertex keepR) =
        Fintype.card (RetainedInternalEdge RS keepR) + 1) :
    BridgelessSphericalCubicMapData
      ((ofVertexSide RS keepL outerL).composeRotationSystem
        (ofVertexSide RS keepR outerR) matching) :=
  bridgelessSphericalCubicMapData_ofVertexSides
    RS keepL keepR outerL outerR matching
    (canonicalHubRotation RS keepL)
    (canonicalHubRotation RS keepR)
    hconnectedL hconnectedR hbridgeless p₀ q₀ hpq hcubic hrotation
    (hubFacesDistinct_canonical RS keepL outerL)
    (hubFacesDistinct_canonical RS keepR outerR)
    (orientationReversing_canonicalHubRotation_of_opposite
      RS keepL keepR matching hopposite)
    (closedSideSpherical_canonical_of_faceRank
      RS keepL outerL hfaceRankL)
    (closedSideSpherical_canonical_of_faceRank
      RS keepR outerR hfaceRankR)

end

end GoertzelV24CanonicalHubClosure

end Mettapedia.GraphTheory.FourColor
