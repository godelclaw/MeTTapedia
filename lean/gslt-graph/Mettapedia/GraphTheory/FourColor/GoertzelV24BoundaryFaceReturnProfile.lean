import Mettapedia.GraphTheory.FourColor.GoertzelV24SeamArcAmbientFace

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24BoundaryFaceReturnProfile

open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor
open GoertzelV24SeamArcAmbientFace
open GoertzelV24SeamFaceArc
open GoertzelV24SeamFaceArcPartition

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The first positive old-face return to the deleted side, starting from the
deleted-side dart opposite a retained boundary port. -/
def boundaryDeletedSideReturnTime
    (RS : RotationSystem V E) (keep : V → Prop)
    (boundary : BoundaryDart RS keep) : Nat :=
  firstPositiveHitTime RS.phi
    (fun dart => ¬ keep (RS.vertOf dart))
    (RS.alpha boundary.1.1) boundary.2

/-- The half-open partial face length contributed by one retained side. The
subtraction removes the next boundary endpoint, which belongs to the following
arc after splicing. -/
def boundaryPartialFaceLength
    (RS : RotationSystem V E) (keep : V → Prop)
    (boundary : BoundaryDart RS keep) : Nat :=
  boundaryDeletedSideReturnTime RS keep boundary - 1

/-- The corrected cap-at-five partial face observation. -/
def cappedBoundaryPartialFaceLength
    (RS : RotationSystem V E) (keep : V → Prop)
    (boundary : BoundaryDart RS keep) : Fin 6 :=
  ⟨min (boundaryPartialFaceLength RS keep boundary) 5, by omega⟩

@[simp]
theorem cappedBoundaryPartialFaceLength_val
    (RS : RotationSystem V E) (keep : V → Prop)
    (boundary : BoundaryDart RS keep) :
    (cappedBoundaryPartialFaceLength RS keep boundary).val =
      min (boundaryDeletedSideReturnTime RS keep boundary - 1) 5 :=
  rfl

/-- The old boundary dart reached by crossing a new seam dart. -/
def orderedCutSpliceMatchedBoundary
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
    (root : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep (orderedCut leftCrossing))
      (BoundaryDartOn RS keep (orderedCut rightCrossing)))
    (hroot : IsSeamDart root) : BoundaryDart RS keep :=
  match root with
  | Sum.inl _ => False.elim hroot
  | Sum.inr (Sum.inl left) =>
      (orderedCutSeamMatching RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective left).1
  | Sum.inr (Sum.inr right) =>
      ((orderedCutSeamMatching RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective
        hrightInjective).symm right).1

/-- The ambient root computed from the splice involution is exactly the old
opposite of the extracted matched boundary dart. -/
theorem orderedCutSpliceAmbientFaceRoot_eq_alpha_matchedBoundary
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
    (hroot : IsSeamDart root) :
    orderedCutSpliceAmbientFaceRoot RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter root =
      RS.alpha (orderedCutSpliceMatchedBoundary RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective root hroot).1.1 := by
  rcases root with dart | side
  · exact False.elim hroot
  · rcases side with dart | dart <;> rfl

/-- The old deleted-side return time of the ambient face selected by a seam
root. -/
def orderedCutSpliceAmbientDeletedSideReturnTime
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
    (hroot : IsSeamDart root) : Nat :=
  firstPositiveHitTime RS.phi
    (fun dart => ¬ keep (RS.vertOf dart))
    (orderedCutSpliceAmbientFaceRoot RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter root)
    (not_keep_orderedCutSpliceAmbientFaceRoot RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter root hroot)

/-- The old deleted-side return occurs exactly one step after the new
seam-to-seam return. This is the endpoint-count correction linking a
single-cut partial length to the actual spliced face arc. -/
theorem ambientDeletedSideReturnTime_eq_spliceReturnTime_add_one
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
    (hroot : IsSeamDart root) :
    orderedCutSpliceAmbientDeletedSideReturnTime RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter root hroot =
      firstPositiveHitTime
        (orderedCutSplicePhi RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective
          hcover hdisjoint houter)
        IsSeamDart root hroot + 1 := by
  classical
  let splicePhi := orderedCutSplicePhi RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter
  let spliceReturnTime := firstPositiveHitTime
    splicePhi IsSeamDart root hroot
  let ambientRoot := orderedCutSpliceAmbientFaceRoot RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter root
  let deletedSide := fun dart => ¬ keep (RS.vertOf dart)
  have hambientRoot : deletedSide ambientRoot :=
    not_keep_orderedCutSpliceAmbientFaceRoot RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter root hroot
  let ambientReturnTime := firstPositiveHitTime
    RS.phi deletedSide ambientRoot hambientRoot
  have hambientReturnPos : 0 < ambientReturnTime :=
    firstPositiveHitTime_pos RS.phi deletedSide ambientRoot hambientRoot
  have hambientReturnDeleted : deletedSide
      ((RS.phi ^ ambientReturnTime) ambientRoot) :=
    firstPositiveHitTime_hits RS.phi deletedSide ambientRoot hambientRoot
  have hspliceLtAmbient : spliceReturnTime < ambientReturnTime := by
    by_contra hnot
    have hambientLe : ambientReturnTime ≤ spliceReturnTime :=
      Nat.le_of_not_gt hnot
    have hkept := keep_ambient_phi_pow_through_return RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
      root hroot hambientReturnPos hambientLe
    exact hambientReturnDeleted hkept
  have hambientLeSucc : ambientReturnTime ≤ spliceReturnTime + 1 := by
    apply firstPositiveHitTime_le_of_hit
    · omega
    · exact not_keep_ambient_phi_pow_after_return RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter root hroot
  change ambientReturnTime = spliceReturnTime + 1
  omega

/-- Therefore the corrected old partial length is exactly the new canonical
seam-arc length. -/
theorem ambientPartialFaceLength_eq_spliceReturnTime
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
    (hroot : IsSeamDart root) :
    orderedCutSpliceAmbientDeletedSideReturnTime RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter root hroot - 1 =
      firstPositiveHitTime
        (orderedCutSplicePhi RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective
          hcover hdisjoint houter)
        IsSeamDart root hroot := by
  rw [ambientDeletedSideReturnTime_eq_spliceReturnTime_add_one RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter root hroot]
  omega

/-- The corrected cap computed at the matched old boundary port is exactly
the canonical return-arc cap used by the new face-orbit theorem. -/
theorem cappedMatchedBoundaryPartialFaceLength_eq_cappedSpliceReturnTime
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
    (hroot : IsSeamDart root) :
    cappedBoundaryPartialFaceLength RS keep
        (orderedCutSpliceMatchedBoundary RS keep
          leftCrossing rightCrossing hleftCrosses hrightCrosses
          hleftInjective hrightInjective root hroot) =
      cappedReturnTime
        (orderedCutSplicePhi RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective
          hcover hdisjoint houter)
        IsSeamDart ⟨root, hroot⟩ := by
  apply Fin.ext
  change min
      (boundaryDeletedSideReturnTime RS keep
        (orderedCutSpliceMatchedBoundary RS keep
          leftCrossing rightCrossing hleftCrosses hrightCrosses
          hleftInjective hrightInjective root hroot) - 1) 5 =
    min (firstPositiveHitTime
      (orderedCutSplicePhi RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter)
      IsSeamDart root hroot) 5
  have hreturns : boundaryDeletedSideReturnTime RS keep
      (orderedCutSpliceMatchedBoundary RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective root hroot) =
      orderedCutSpliceAmbientDeletedSideReturnTime RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter root hroot := by
    rcases root with dart | side
    · exact False.elim hroot
    · rcases side with dart | dart <;> rfl
  rw [hreturns, ambientPartialFaceLength_eq_spliceReturnTime RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter root hroot]

end

end GoertzelV24BoundaryFaceReturnProfile

end Mettapedia.GraphTheory.FourColor
