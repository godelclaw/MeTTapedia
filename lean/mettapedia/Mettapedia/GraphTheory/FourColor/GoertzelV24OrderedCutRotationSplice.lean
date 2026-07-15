import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationCutDartDecomposition

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrderedCutRotationSplice

open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Classify an exposed dart into the left or right cut. -/
def boundaryDartToCutSum
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCut rightCut : Finset E)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ leftCut ∨ RS.edgeOf dart.1.1 ∈ rightCut)
    (dart : BoundaryDart RS keep) :
      BoundaryDartOn RS keep leftCut ⊕
        BoundaryDartOn RS keep rightCut :=
  if hleft : RS.edgeOf dart.1.1 ∈ leftCut then
    Sum.inl ⟨dart, hleft⟩
  else
    Sum.inr ⟨dart, (hcover dart).resolve_left hleft⟩

/-- Forget which of the two cuts contains an exposed dart. -/
def cutSumUnderlyingBoundary
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCut rightCut : Finset E) :
    BoundaryDartOn RS keep leftCut ⊕ BoundaryDartOn RS keep rightCut →
      BoundaryDart RS keep
  | Sum.inl left => left.1
  | Sum.inr right => right.1

@[simp]
theorem cutSumUnderlyingBoundary_toCutSum
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCut rightCut : Finset E)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ leftCut ∨ RS.edgeOf dart.1.1 ∈ rightCut)
    (dart : BoundaryDart RS keep) :
    cutSumUnderlyingBoundary RS keep leftCut rightCut
      (boundaryDartToCutSum RS keep leftCut rightCut hcover dart) = dart := by
  classical
  by_cases hleft : RS.edgeOf dart.1.1 ∈ leftCut
  · simp [boundaryDartToCutSum, cutSumUnderlyingBoundary, hleft]
  · simp [boundaryDartToCutSum, cutSumUnderlyingBoundary, hleft]

@[simp]
theorem boundaryDartToCutSum_underlyingBoundary
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCut rightCut : Finset E)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ leftCut ∨ RS.edgeOf dart.1.1 ∈ rightCut)
    (hdisjoint : Disjoint leftCut rightCut)
    (side : BoundaryDartOn RS keep leftCut ⊕
      BoundaryDartOn RS keep rightCut) :
    boundaryDartToCutSum RS keep leftCut rightCut hcover
      (cutSumUnderlyingBoundary RS keep leftCut rightCut side) = side := by
  classical
  rcases side with left | right
  · by_cases hleft : RS.edgeOf left.1.1.1 ∈ leftCut
    · simp [boundaryDartToCutSum, cutSumUnderlyingBoundary, hleft]
    · exact False.elim (hleft left.2)
  · have hnotLeft : RS.edgeOf right.1.1.1 ∉ leftCut := by
      intro hleft
      exact Finset.disjoint_left.1 hdisjoint hleft right.2
    simp [boundaryDartToCutSum, cutSumUnderlyingBoundary, hnotLeft]

/-- Exposed darts split between two disjoint cuts that cover the entire
boundary of the retained region. -/
def boundaryDartEquivCutSum
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCut rightCut : Finset E)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ leftCut ∨ RS.edgeOf dart.1.1 ∈ rightCut)
    (hdisjoint : Disjoint leftCut rightCut) :
    BoundaryDart RS keep ≃
      BoundaryDartOn RS keep leftCut ⊕
        BoundaryDartOn RS keep rightCut where
  toFun := boundaryDartToCutSum RS keep leftCut rightCut hcover
  invFun := cutSumUnderlyingBoundary RS keep leftCut rightCut
  left_inv := cutSumUnderlyingBoundary_toCutSum RS keep leftCut rightCut hcover
  right_inv := boundaryDartToCutSum_underlyingBoundary RS keep leftCut
    rightCut hcover hdisjoint

/-- The retained darts split into intact darts and the two ordered cut
interfaces, provided every exposed dart lies on exactly one of the cuts. -/
def retainedDartEquivMatchedParts
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCut rightCut : Finset E)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ leftCut ∨ RS.edgeOf dart.1.1 ∈ rightCut)
    (hdisjoint : Disjoint leftCut rightCut) :
    RetainedDart RS keep ≃
      MatchedSeam.Dart (InternalDart RS keep)
        (BoundaryDartOn RS keep leftCut)
        (BoundaryDartOn RS keep rightCut) :=
  (retainedDartEquivInternalSumBoundary RS keep).trans
    (Equiv.sumCongr (Equiv.refl (InternalDart RS keep))
      (boundaryDartEquivCutSum RS keep leftCut rightCut hcover hdisjoint))

/-- Recover the original retained dart from one of the three matched parts. -/
def matchedPartUnderlyingDart
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCut rightCut : Finset E) :
    MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep leftCut)
      (BoundaryDartOn RS keep rightCut) → RS.D
  | Sum.inl internal => internal.1.1
  | Sum.inr (Sum.inl left) => left.1.1.1
  | Sum.inr (Sum.inr right) => right.1.1.1

/-- The explicit underlying-dart projection agrees with the inverse of the
three-part decomposition. -/
theorem matchedPartUnderlyingDart_eq_equiv_symm_val
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCut rightCut : Finset E)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ leftCut ∨ RS.edgeOf dart.1.1 ∈ rightCut)
    (hdisjoint : Disjoint leftCut rightCut)
    (dart : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep leftCut)
      (BoundaryDartOn RS keep rightCut)) :
    matchedPartUnderlyingDart RS keep leftCut rightCut dart =
      ((retainedDartEquivMatchedParts RS keep leftCut rightCut
        hcover hdisjoint).symm dart).1 := by
  rcases dart with internal | side
  · rfl
  · rcases side with left | right <;> rfl

/-- Forgetting the three-part tag is injective because the tags are the
partition induced by the retained-dart equivalence. -/
theorem matchedPartUnderlyingDart_injective
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCut rightCut : Finset E)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ leftCut ∨ RS.edgeOf dart.1.1 ∈ rightCut)
    (hdisjoint : Disjoint leftCut rightCut) :
    Function.Injective
      (matchedPartUnderlyingDart RS keep leftCut rightCut) := by
  intro left right hdarts
  let parts := retainedDartEquivMatchedParts RS keep leftCut rightCut
    hcover hdisjoint
  apply parts.symm.injective
  apply Subtype.ext
  rw [← matchedPartUnderlyingDart_eq_equiv_symm_val RS keep leftCut
    rightCut hcover hdisjoint left]
  rw [← matchedPartUnderlyingDart_eq_equiv_symm_val RS keep leftCut
    rightCut hcover hdisjoint right]
  exact hdarts

/-- The decomposition equivalence does not alter the underlying dart. -/
theorem matchedPartUnderlyingDart_equiv
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCut rightCut : Finset E)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ leftCut ∨ RS.edgeOf dart.1.1 ∈ rightCut)
    (hdisjoint : Disjoint leftCut rightCut)
    (dart : RetainedDart RS keep) :
    matchedPartUnderlyingDart RS keep leftCut rightCut
        (retainedDartEquivMatchedParts RS keep leftCut rightCut
          hcover hdisjoint dart) = dart.1 := by
  let parts := retainedDartEquivMatchedParts RS keep leftCut rightCut
    hcover hdisjoint
  have hinverse := congrArg Subtype.val (parts.left_inv dart)
  change (parts.symm (parts dart)).1 = dart.1 at hinverse
  rw [matchedPartUnderlyingDart_eq_equiv_symm_val RS keep leftCut rightCut
    hcover hdisjoint]
  exact hinverse

/-- Match the two exposed cut interfaces by their common ordered position. -/
def orderedCutSeamMatching
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
    BoundaryDartOn RS keep (orderedCut leftCrossing) ≃
      BoundaryDartOn RS keep (orderedCut rightCrossing) :=
  (orderedBoundaryDartEquiv RS keep leftCrossing hleftCrosses
    hleftInjective).symm.trans
      (orderedBoundaryDartEquiv RS keep rightCrossing hrightCrosses
        hrightInjective)

/-- The seam matching pairs exactly equal ordered positions. -/
theorem orderedCutSeamMatching_apply
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
    orderedCutSeamMatching RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        (orderedBoundaryDart RS keep leftCrossing hleftCrosses step) =
      orderedBoundaryDart RS keep rightCrossing hrightCrosses step := by
  let leftEquiv := orderedBoundaryDartEquiv RS keep leftCrossing
    hleftCrosses hleftInjective
  let rightEquiv := orderedBoundaryDartEquiv RS keep rightCrossing
    hrightCrosses hrightInjective
  change rightEquiv (leftEquiv.symm (leftEquiv step)) = rightEquiv step
  rw [leftEquiv.symm_apply_apply]

/-- The inverse seam matching also preserves the ordered position. -/
theorem orderedCutSeamMatching_symm_apply
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
    (orderedCutSeamMatching RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective).symm
        (orderedBoundaryDart RS keep rightCrossing hrightCrosses step) =
      orderedBoundaryDart RS keep leftCrossing hleftCrosses step := by
  apply (orderedCutSeamMatching RS keep leftCrossing rightCrossing
    hleftCrosses hrightCrosses hleftInjective hrightInjective).injective
  rw [Equiv.apply_symm_apply, orderedCutSeamMatching_apply]

/-- Transport the retained vertex rotation to the three-part seam carrier. -/
def matchedPartsRho
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCut rightCut : Finset E)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ leftCut ∨ RS.edgeOf dart.1.1 ∈ rightCut)
    (hdisjoint : Disjoint leftCut rightCut) :
    Equiv.Perm
      (MatchedSeam.Dart (InternalDart RS keep)
        (BoundaryDartOn RS keep leftCut)
        (BoundaryDartOn RS keep rightCut)) :=
  let parts := retainedDartEquivMatchedParts RS keep leftCut rightCut
    hcover hdisjoint
  (parts.symm.trans (retainedRho RS keep)).trans parts

@[simp]
theorem matchedPartsRho_apply
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCut rightCut : Finset E)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ leftCut ∨ RS.edgeOf dart.1.1 ∈ rightCut)
    (hdisjoint : Disjoint leftCut rightCut)
    (dart : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep leftCut)
      (BoundaryDartOn RS keep rightCut)) :
    matchedPartsRho RS keep leftCut rightCut hcover hdisjoint dart =
      retainedDartEquivMatchedParts RS keep leftCut rightCut hcover hdisjoint
        (retainedRho RS keep
          ((retainedDartEquivMatchedParts RS keep leftCut rightCut
            hcover hdisjoint).symm dart)) :=
  rfl

/-- Transporting the rotation exactly retains the old rotation on underlying
darts. -/
theorem matchedPartUnderlyingDart_rho
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCut rightCut : Finset E)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ leftCut ∨ RS.edgeOf dart.1.1 ∈ rightCut)
    (hdisjoint : Disjoint leftCut rightCut)
    (dart : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep leftCut)
      (BoundaryDartOn RS keep rightCut)) :
    matchedPartUnderlyingDart RS keep leftCut rightCut
        (matchedPartsRho RS keep leftCut rightCut hcover hdisjoint dart) =
      RS.rho (matchedPartUnderlyingDart RS keep leftCut rightCut dart) := by
  let parts := retainedDartEquivMatchedParts RS keep leftCut rightCut
    hcover hdisjoint
  have hforward := matchedPartUnderlyingDart_equiv RS keep leftCut rightCut
    hcover hdisjoint (retainedRho RS keep (parts.symm dart))
  have hbackward :
      matchedPartUnderlyingDart RS keep leftCut rightCut dart =
        (parts.symm dart).1 := by
    simpa [parts] using matchedPartUnderlyingDart_equiv RS keep
      leftCut rightCut hcover hdisjoint (parts.symm dart)
  rw [matchedPartsRho_apply, hforward, hbackward, retainedRho_val]

/-- Consequently, transporting the rotation preserves the base vertex. -/
theorem matchedPartUnderlyingDart_rho_vertex
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCut rightCut : Finset E)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ leftCut ∨ RS.edgeOf dart.1.1 ∈ rightCut)
    (hdisjoint : Disjoint leftCut rightCut)
    (dart : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep leftCut)
      (BoundaryDartOn RS keep rightCut)) :
    RS.vertOf (matchedPartUnderlyingDart RS keep leftCut rightCut
        (matchedPartsRho RS keep leftCut rightCut hcover hdisjoint dart)) =
      RS.vertOf (matchedPartUnderlyingDart RS keep leftCut rightCut dart) := by
  rw [matchedPartUnderlyingDart_rho RS keep leftCut rightCut
    hcover hdisjoint, RS.vert_rho]

/-- The matched-seam data computed from two complete ordered cuts. -/
def orderedCutMatchedSeamData
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
    MatchedSeam.Data V (InternalDart RS keep)
      (BoundaryDartOn RS keep (orderedCut leftCrossing))
      (BoundaryDartOn RS keep (orderedCut rightCrossing)) where
  interiorVert := fun dart => RS.vertOf dart.1.1
  leftVert := fun dart => RS.vertOf dart.1.1.1
  rightVert := fun dart => RS.vertOf dart.1.1.1
  interiorAlpha := internalAlpha RS keep
  matching := orderedCutSeamMatching RS keep leftCrossing rightCrossing
    hleftCrosses hrightCrosses hleftInjective hrightInjective
  rho := matchedPartsRho RS keep (orderedCut leftCrossing)
    (orderedCut rightCrossing) hcover hdisjoint
  outer := retainedDartEquivMatchedParts RS keep
    (orderedCut leftCrossing) (orderedCut rightCrossing) hcover hdisjoint
    ⟨RS.outer, houter⟩

/-- The data's vertex projection is exactly the original vertex of the
underlying retained dart. -/
theorem orderedCutMatchedSeamData_vertOf
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
    (dart : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep (orderedCut leftCrossing))
      (BoundaryDartOn RS keep (orderedCut rightCrossing))) :
    (orderedCutMatchedSeamData RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter).vertOf dart =
      RS.vertOf (matchedPartUnderlyingDart RS keep
        (orderedCut leftCrossing) (orderedCut rightCrossing) dart) := by
  rcases dart with interior | side
  · rfl
  · rcases side with left | right <;> rfl

/-- The face-successor permutation before assigning names to the new edges. -/
def orderedCutSplicePhi
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
    Equiv.Perm
      (MatchedSeam.Dart (InternalDart RS keep)
        (BoundaryDartOn RS keep (orderedCut leftCrossing))
        (BoundaryDartOn RS keep (orderedCut rightCrossing))) :=
  let data := orderedCutMatchedSeamData RS keep leftCrossing rightCrossing
    hleftCrosses hrightCrosses hleftInjective hrightInjective
    hcover hdisjoint houter
  data.rho * data.alpha

/-- On an intact dart, the spliced face successor is exactly the old face
successor after forgetting the decomposition. -/
theorem orderedCutSplicePhi_interior_underlying
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
    (dart : InternalDart RS keep) :
    matchedPartUnderlyingDart RS keep (orderedCut leftCrossing)
        (orderedCut rightCrossing)
        (orderedCutSplicePhi RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective
          hcover hdisjoint houter (Sum.inl dart)) =
      RS.phi dart.1.1 := by
  change matchedPartUnderlyingDart RS keep (orderedCut leftCrossing)
      (orderedCut rightCrossing)
      (matchedPartsRho RS keep (orderedCut leftCrossing)
        (orderedCut rightCrossing) hcover hdisjoint
        (Sum.inl (internalAlpha RS keep dart))) =
    RS.rho (RS.alpha dart.1.1)
  rw [matchedPartUnderlyingDart_rho]
  rfl

/-- At a left cut position, the spliced face successor crosses to the matching
right cut position and then follows the old right-end vertex rotation. -/
theorem orderedCutSplicePhi_left_underlying
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
    (houter : keep (RS.vertOf RS.outer)) (step : Fin n) :
    matchedPartUnderlyingDart RS keep (orderedCut leftCrossing)
        (orderedCut rightCrossing)
        (orderedCutSplicePhi RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective
          hcover hdisjoint houter
          (Sum.inr (Sum.inl
            (orderedBoundaryDart RS keep leftCrossing hleftCrosses step)))) =
      RS.rho
        (orderedBoundaryDart RS keep rightCrossing hrightCrosses step).1.1.1 := by
  change matchedPartUnderlyingDart RS keep (orderedCut leftCrossing)
      (orderedCut rightCrossing)
      (matchedPartsRho RS keep (orderedCut leftCrossing)
        (orderedCut rightCrossing) hcover hdisjoint
        (Sum.inr (Sum.inr
          ((orderedCutSeamMatching RS keep leftCrossing rightCrossing
            hleftCrosses hrightCrosses hleftInjective hrightInjective)
              (orderedBoundaryDart RS keep leftCrossing hleftCrosses step))))) = _
  rw [matchedPartUnderlyingDart_rho, orderedCutSeamMatching_apply]
  rfl

/-- The reverse seam direction obeys the symmetric transition law. -/
theorem orderedCutSplicePhi_right_underlying
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
    (houter : keep (RS.vertOf RS.outer)) (step : Fin n) :
    matchedPartUnderlyingDart RS keep (orderedCut leftCrossing)
        (orderedCut rightCrossing)
        (orderedCutSplicePhi RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective
          hcover hdisjoint houter
          (Sum.inr (Sum.inr
            (orderedBoundaryDart RS keep rightCrossing hrightCrosses step)))) =
      RS.rho
        (orderedBoundaryDart RS keep leftCrossing hleftCrosses step).1.1.1 := by
  change matchedPartUnderlyingDart RS keep (orderedCut leftCrossing)
      (orderedCut rightCrossing)
      (matchedPartsRho RS keep (orderedCut leftCrossing)
        (orderedCut rightCrossing) hcover hdisjoint
        (Sum.inr (Sum.inl
          ((orderedCutSeamMatching RS keep leftCrossing rightCrossing
            hleftCrosses hrightCrosses hleftInjective hrightInjective).symm
              (orderedBoundaryDart RS keep rightCrossing hrightCrosses step))))) = _
  rw [matchedPartUnderlyingDart_rho, orderedCutSeamMatching_symm_apply]
  rfl

/-- Rewire two complete ordered cuts after deleting the vertices between
them. Coverage says these are all exposed half-edges; endpoint separation
rules out a newly created loop. The output's edges and two-dart fibers are
computed by `RewiredDartSystem`, rather than supplied as hypotheses. -/
def orderedCutRewiredDartSystem
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
          (orderedBoundaryDart RS keep leftCrossing hleftCrosses step).1.1.1 ≠
        RS.vertOf
          (orderedBoundaryDart RS keep rightCrossing hrightCrosses step).1.1.1) :
    RewiredDartSystem V
      (MatchedSeam.Dart (InternalDart RS keep)
        (BoundaryDartOn RS keep (orderedCut leftCrossing))
        (BoundaryDartOn RS keep (orderedCut rightCrossing))) := by
  let data := orderedCutMatchedSeamData RS keep leftCrossing rightCrossing
    hleftCrosses hrightCrosses hleftInjective hrightInjective
    hcover hdisjoint houter
  apply data.toRewiredDartSystem
  · exact internalAlpha_involutive RS keep
  · exact internalAlpha_fixfree RS keep
  · intro dart
    rw [orderedCutMatchedSeamData_vertOf RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter]
    rw [orderedCutMatchedSeamData_vertOf RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter]
    exact matchedPartUnderlyingDart_rho_vertex RS keep
      (orderedCut leftCrossing) (orderedCut rightCrossing)
      hcover hdisjoint dart
  · intro interior
    exact RS.no_self_loops interior.1.1
  · intro left
    rcases orderedBoundaryDart_surjective RS keep leftCrossing hleftCrosses
      left with ⟨step, hstep⟩
    rw [← hstep]
    change
      RS.vertOf
          (orderedBoundaryDart RS keep leftCrossing hleftCrosses step).1.1.1 ≠
        RS.vertOf
          ((orderedCutSeamMatching RS keep leftCrossing rightCrossing
            hleftCrosses hrightCrosses hleftInjective hrightInjective)
              (orderedBoundaryDart RS keep leftCrossing hleftCrosses step)).1.1.1
    rw [orderedCutSeamMatching_apply]
    exact hseamEndpoints step

/-- The shortened rotation system produced by an ordered transversal splice.
This theorem constructs only the combinatorial embedding data; preservation of
spherical planarity and face-size bounds is a property of this concrete output
to be proved from the two transversal face orders. -/
def orderedCutRotationSystem
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
          (orderedBoundaryDart RS keep leftCrossing hleftCrosses step).1.1.1 ≠
        RS.vertOf
          (orderedBoundaryDart RS keep rightCrossing hrightCrosses step).1.1.1) :
    RotationSystem V
      (orderedCutRewiredDartSystem RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter hseamEndpoints).Edge :=
  (orderedCutRewiredDartSystem RS keep leftCrossing rightCrossing
    hleftCrosses hrightCrosses hleftInjective hrightInjective
    hcover hdisjoint houter hseamEndpoints).toRotationSystem

end

end GoertzelV24OrderedCutRotationSplice

end Mettapedia.GraphTheory.FourColor
