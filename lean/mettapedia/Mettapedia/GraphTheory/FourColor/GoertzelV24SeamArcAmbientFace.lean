import Mettapedia.GraphTheory.FourColor.GoertzelV24SeamFaceArcPartition

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SeamArcAmbientFace

open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor
open GoertzelV24SeamFaceArc

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Forgetting any matched-part tag always produces a dart based at a
retained vertex. -/
theorem keep_matchedPartUnderlyingDart
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCut rightCut : Finset E)
    (point : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep leftCut)
      (BoundaryDartOn RS keep rightCut)) :
    keep (RS.vertOf
      (matchedPartUnderlyingDart RS keep leftCut rightCut point)) := by
  rcases point with dart | side
  · exact dart.1.2
  · rcases side with dart | dart
    · exact dart.1.1.2
    · exact dart.1.1.2

/-- At a seam dart, the next old face step leaves the retained vertex set. -/
theorem not_keep_phi_matchedPartUnderlyingDart_of_isSeam
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCut rightCut : Finset E)
    (point : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep leftCut)
      (BoundaryDartOn RS keep rightCut))
    (hpoint : IsSeamDart point) :
    ¬ keep (RS.vertOf (RS.phi
      (matchedPartUnderlyingDart RS keep leftCut rightCut point))) := by
  rw [RS.vert_phi_eq_vert_alpha]
  rcases point with dart | side
  · exact False.elim hpoint
  · rcases side with dart | dart
    · exact dart.1.2
    · exact dart.1.2

/-- The old ambient-face dart immediately before a new seam arc enters the
retained region. It is computed by crossing the new seam and then taking the
old opposite dart at the matched port. -/
def orderedCutSpliceAmbientFaceRoot
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
      (BoundaryDartOn RS keep (orderedCut rightCrossing))) : RS.D :=
  RS.alpha
    (matchedPartUnderlyingDart RS keep (orderedCut leftCrossing)
      (orderedCut rightCrossing)
      ((orderedCutMatchedSeamData RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter).alpha root))

/-- At a seam dart, the computed ambient predecessor is based on the deleted
side of the matched crossing edge. -/
theorem not_keep_orderedCutSpliceAmbientFaceRoot
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
    ¬ keep (RS.vertOf (orderedCutSpliceAmbientFaceRoot RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter root)) := by
  rcases root with dart | side
  · exact False.elim hroot
  · rcases side with dart | dart
    · change ¬ keep (RS.vertOf (RS.alpha
        ((orderedCutSeamMatching RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective
          dart).1.1.1)))
      exact (orderedCutSeamMatching RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective dart).1.2
    · change ¬ keep (RS.vertOf (RS.alpha
        (((orderedCutSeamMatching RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective).symm
          dart).1.1.1)))
      exact ((orderedCutSeamMatching RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective
        hrightInjective).symm dart).1.2

/-- The first new face step at any splice dart is the first old ambient face
step from the computed ambient root after forgetting the splice tags. -/
theorem orderedCutSplicePhi_first_underlying_eq_ambient_phi
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
      (BoundaryDartOn RS keep (orderedCut rightCrossing))) :
    matchedPartUnderlyingDart RS keep (orderedCut leftCrossing)
        (orderedCut rightCrossing)
        (orderedCutSplicePhi RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective
          hcover hdisjoint houter root) =
      RS.phi (orderedCutSpliceAmbientFaceRoot RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter root) := by
  change matchedPartUnderlyingDart RS keep (orderedCut leftCrossing)
      (orderedCut rightCrossing)
      (matchedPartsRho RS keep (orderedCut leftCrossing)
        (orderedCut rightCrossing) hcover hdisjoint
        ((orderedCutMatchedSeamData RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective
          hcover hdisjoint houter).alpha root)) =
    RS.rho (RS.alpha (RS.alpha
      (matchedPartUnderlyingDart RS keep (orderedCut leftCrossing)
        (orderedCut rightCrossing)
        ((orderedCutMatchedSeamData RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective
          hcover hdisjoint houter).alpha root))))
  rw [matchedPartUnderlyingDart_rho, RS.alpha_involutive]

/-- Through the complete canonical seam arc, every positive new face power
is the corresponding power of one actual old ambient face after forgetting
the splice tags. -/
theorem orderedCutSplicePhi_pow_underlying_eq_ambient_phi_pow
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
    (hstepLe : step ≤ firstPositiveHitTime
      (orderedCutSplicePhi RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter)
      IsSeamDart root hroot) :
    matchedPartUnderlyingDart RS keep (orderedCut leftCrossing)
        (orderedCut rightCrossing)
        ((orderedCutSplicePhi RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective
          hcover hdisjoint houter ^ step) root) =
      (RS.phi ^ step)
        (orderedCutSpliceAmbientFaceRoot RS keep
          leftCrossing rightCrossing hleftCrosses hrightCrosses
          hleftInjective hrightInjective hcover hdisjoint houter root) := by
  induction step with
  | zero => omega
  | succ previous ih =>
      by_cases hpreviousZero : previous = 0
      · subst previous
        simpa using orderedCutSplicePhi_first_underlying_eq_ambient_phi
          RS keep leftCrossing rightCrossing hleftCrosses hrightCrosses
          hleftInjective hrightInjective hcover hdisjoint houter root
      · have hpreviousPos : 0 < previous := Nat.pos_of_ne_zero hpreviousZero
        have hpreviousLt : previous < firstPositiveHitTime
            (orderedCutSplicePhi RS keep leftCrossing rightCrossing
              hleftCrosses hrightCrosses hleftInjective hrightInjective
              hcover hdisjoint houter)
            IsSeamDart root hroot := by
          omega
        rw [pow_succ', Equiv.Perm.mul_apply,
          pow_succ', Equiv.Perm.mul_apply]
        rw [orderedCutSplicePhi_underlying_step_between_seams RS keep
          leftCrossing rightCrossing hleftCrosses hrightCrosses
          hleftInjective hrightInjective hcover hdisjoint houter
          root hroot hpreviousPos hpreviousLt]
        rw [ih hpreviousPos (Nat.le_of_lt hpreviousLt)]

/-- Every positive old face power through the seam-return endpoint is based
at a retained vertex. Combined with the deleted-side root theorem, the
ambient powers form a boundary-to-boundary retained face segment. -/
theorem keep_ambient_phi_pow_through_return
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
    (hstepLe : step ≤ firstPositiveHitTime
      (orderedCutSplicePhi RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter)
      IsSeamDart root hroot) :
    keep (RS.vertOf ((RS.phi ^ step)
      (orderedCutSpliceAmbientFaceRoot RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter root))) := by
  rw [← orderedCutSplicePhi_pow_underlying_eq_ambient_phi_pow RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter
    root hroot hstepPos hstepLe]
  exact keep_matchedPartUnderlyingDart RS keep
    (orderedCut leftCrossing) (orderedCut rightCrossing) _

/-- The old face power immediately after the canonical return endpoint is
again based on the deleted side. Hence the positive powers through the return
are the maximal retained interval of this ambient face occurrence. -/
theorem not_keep_ambient_phi_pow_after_return
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
    let returnTime := firstPositiveHitTime
      (orderedCutSplicePhi RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter)
      IsSeamDart root hroot
    ¬ keep (RS.vertOf ((RS.phi ^ (returnTime + 1))
      (orderedCutSpliceAmbientFaceRoot RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter root))) := by
  dsimp only
  let splicePhi := orderedCutSplicePhi RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter
  let returnTime := firstPositiveHitTime splicePhi IsSeamDart root hroot
  have hreturnPos : 0 < returnTime :=
    firstPositiveHitTime_pos splicePhi IsSeamDart root hroot
  have htransport :=
    orderedCutSplicePhi_pow_underlying_eq_ambient_phi_pow RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
      root hroot hreturnPos (Nat.le_refl returnTime)
  have hreturnSeam : IsSeamDart ((splicePhi ^ returnTime) root) :=
    firstPositiveHitTime_hits splicePhi IsSeamDart root hroot
  rw [pow_succ', Equiv.Perm.mul_apply, ← htransport]
  exact not_keep_phi_matchedPartUnderlyingDart_of_isSeam RS keep
    (orderedCut leftCrossing) (orderedCut rightCrossing)
    ((splicePhi ^ returnTime) root) hreturnSeam

end

end GoertzelV24SeamArcAmbientFace

end Mettapedia.GraphTheory.FourColor
