import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedCutMinimumFaceSplice

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RetainedVertexRotationSplice

open GoertzelV24OrderedCutRotationSplice
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24OrderedCutMinimumFaceSplice
open GoertzelV24OrderedCutOldFaceReturn
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor
open GoertzelV24SeamArcAmbientFace

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The actual vertex carrier after a region is removed. Using this subtype
prevents deleted ambient vertices from surviving as degree-zero vertices in
the shortened rotation system. -/
abbrev RetainedVertex (keep : V → Prop) := { vertex : V // keep vertex }

noncomputable instance retainedVertexFintype (keep : V → Prop) :
    Fintype (RetainedVertex keep) :=
  Fintype.ofInjective (fun vertex : RetainedVertex keep => vertex.1)
    Subtype.val_injective

instance retainedVertexDecidableEq (keep : V → Prop) :
    DecidableEq (RetainedVertex keep) :=
  Classical.decEq _

/-- Removing at least one ambient vertex makes the retained carrier strictly
smaller, as required by a vertex-minimal shortening argument. -/
theorem card_retainedVertex_lt (keep : V → Prop)
    (removed : V) (hremoved : ¬ keep removed) :
    Fintype.card (RetainedVertex keep) < Fintype.card V := by
  exact Fintype.card_subtype_lt hremoved

/-- The retained vertex supporting a decomposed splice dart. -/
def matchedPartRetainedVertex
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCut rightCut : Finset E)
    (dart : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep leftCut)
      (BoundaryDartOn RS keep rightCut)) : RetainedVertex keep :=
  ⟨RS.vertOf (matchedPartUnderlyingDart RS keep leftCut rightCut dart),
    keep_matchedPartUnderlyingDart RS keep leftCut rightCut dart⟩

@[simp]
theorem matchedPartRetainedVertex_val
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCut rightCut : Finset E)
    (dart : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep leftCut)
      (BoundaryDartOn RS keep rightCut)) :
    (matchedPartRetainedVertex RS keep leftCut rightCut dart).1 =
      RS.vertOf (matchedPartUnderlyingDart RS keep leftCut rightCut dart) :=
  rfl

/-- The ordered splice with its vertex map restricted to vertices that still
support darts. Its edge involution and face permutation are the concrete
ones already constructed by the ordered-cut splice. -/
def orderedCutRetainedVertexRewiredDartSystem
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
            hrightCrosses step).1.1.1) :
    RewiredDartSystem (RetainedVertex keep)
      (MatchedSeam.Dart (InternalDart RS keep)
        (BoundaryDartOn RS keep (orderedCut leftCrossing))
        (BoundaryDartOn RS keep (orderedCut rightCrossing))) :=
  let base := orderedCutRewiredDartSystem RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter hseamEndpoints
  have hbaseVert : ∀ dart, base.vertOf dart =
      (matchedPartRetainedVertex RS keep
        (orderedCut leftCrossing) (orderedCut rightCrossing) dart).1 := by
    intro dart
    simpa [base, orderedCutRewiredDartSystem,
      MatchedSeam.Data.toRewiredDartSystem] using
      orderedCutMatchedSeamData_vertOf RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter dart
  { vertOf := matchedPartRetainedVertex RS keep
      (orderedCut leftCrossing) (orderedCut rightCrossing)
    alpha := base.alpha
    rho := base.rho
    alpha_involutive := base.alpha_involutive
    alpha_fixfree := base.alpha_fixfree
    vert_rho := by
      intro dart
      apply Subtype.ext
      exact matchedPartUnderlyingDart_rho_vertex RS keep
        (orderedCut leftCrossing) (orderedCut rightCrossing)
        hcover hdisjoint dart
    outer := base.outer
    no_self_loops := by
      intro dart
      intro heq
      apply base.no_self_loops dart
      rw [hbaseVert dart, hbaseVert (base.alpha dart)]
      exact congrArg Subtype.val heq }

/-- The shortened rotation system on the honest retained-vertex carrier. -/
def orderedCutRetainedVertexRotationSystem
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
            hrightCrosses step).1.1.1) :
    RotationSystem (RetainedVertex keep)
      (orderedCutRetainedVertexRewiredDartSystem RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints).Edge :=
  (orderedCutRetainedVertexRewiredDartSystem RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter
    hseamEndpoints).toRotationSystem

/-- Darts based at a retained vertex are in bijection with all old darts
based at its ambient vertex. -/
def retainedVertexDartsEquiv
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
    (vertex : RetainedVertex keep) :
    { dart : (orderedCutRetainedVertexRotationSystem RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints).D //
      (orderedCutRetainedVertexRotationSystem RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints).vertOf dart = vertex } ≃
      { dart : RS.D // RS.vertOf dart = vertex.1 } := by
  let parts := retainedDartEquivMatchedParts RS keep
    (orderedCut leftCrossing) (orderedCut rightCrossing) hcover hdisjoint
  let newRS := orderedCutRetainedVertexRotationSystem RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter hseamEndpoints
  refine
    { toFun := fun dart =>
        ⟨matchedPartUnderlyingDart RS keep
            (orderedCut leftCrossing) (orderedCut rightCrossing) dart.1,
          congrArg Subtype.val dart.2⟩
      invFun := fun dart =>
        let retained : RetainedDart RS keep :=
          ⟨dart.1, dart.2.symm ▸ vertex.2⟩
        ⟨parts retained, by
          change matchedPartRetainedVertex RS keep
            (orderedCut leftCrossing) (orderedCut rightCrossing)
              (parts retained) = vertex
          apply Subtype.ext
          change RS.vertOf (matchedPartUnderlyingDart RS keep
            (orderedCut leftCrossing) (orderedCut rightCrossing)
              (parts retained)) = vertex.1
          rw [matchedPartUnderlyingDart_equiv RS keep
            (orderedCut leftCrossing) (orderedCut rightCrossing)
            hcover hdisjoint retained]
          exact dart.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro dart
    apply Subtype.ext
    apply matchedPartUnderlyingDart_injective RS keep
      (orderedCut leftCrossing) (orderedCut rightCrossing) hcover hdisjoint
    rw [matchedPartUnderlyingDart_equiv RS keep
      (orderedCut leftCrossing) (orderedCut rightCrossing) hcover hdisjoint]
  · intro dart
    apply Subtype.ext
    let retained : RetainedDart RS keep :=
      ⟨dart.1, dart.2.symm ▸ vertex.2⟩
    change matchedPartUnderlyingDart RS keep
      (orderedCut leftCrossing) (orderedCut rightCrossing)
        (parts retained) = dart.1
    rw [matchedPartUnderlyingDart_equiv RS keep
      (orderedCut leftCrossing) (orderedCut rightCrossing) hcover hdisjoint]

/-- Reindexing to retained vertices preserves each local dart count. -/
theorem orderedCutRetainedVertexRotationSystem_dartsAt_card
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
    (vertex : RetainedVertex keep) :
    ((orderedCutRetainedVertexRotationSystem RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
      hseamEndpoints).dartsAt vertex).card =
      (RS.dartsAt vertex.1).card := by
  classical
  unfold RotationSystem.dartsAt
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr
    (retainedVertexDartsEquiv RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter hseamEndpoints vertex)

/-- Cubicity survives ordered deletion and rewiring once the output uses the
honest retained-vertex carrier. -/
theorem orderedCutRetainedVertexRotationSystem_isCubic
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
    (hcubic : RS.IsCubic) :
    (orderedCutRetainedVertexRotationSystem RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
      hseamEndpoints).IsCubic := by
  intro vertex
  rw [orderedCutRetainedVertexRotationSystem_dartsAt_card RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter
    hseamEndpoints vertex]
  exact hcubic vertex.1

/-- Vertex reindexing changes neither the face permutation nor any face
orbit; it only removes unused ambient vertices from the vertex carrier. -/
theorem orderedCutRetainedVertexRotationSystem_faceOrbit_eq
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
      (BoundaryDartOn RS keep (orderedCut rightCrossing))) :
    (orderedCutRetainedVertexRotationSystem RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints).faceOrbit root =
      (orderedCutRotationSystem RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints).faceOrbit root := by
  rfl

/-- The global minimum-face splice theorem therefore holds on the honest
retained-vertex output as well as on the dart-equivalent ambient carrier. -/
theorem five_le_all_retainedVertexRotationSystem_faceOrbits_of_oldProfile
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
    (hminimum : ∀ dart : RS.D, 5 ≤ (RS.faceOrbit dart).card)
    (hprofile : ∀ position : OrderedSeamPosition n,
      OrderedCutFaceReturnProfile.FaceMeetsFive
        (oldRotationOrderedCutFaceReturnProfile RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter) position)
    (root : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep (orderedCut leftCrossing))
      (BoundaryDartOn RS keep (orderedCut rightCrossing))) :
    5 ≤ ((orderedCutRetainedVertexRotationSystem RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
      hseamEndpoints).faceOrbit root).card := by
  rw [orderedCutRetainedVertexRotationSystem_faceOrbit_eq RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter
    hseamEndpoints root]
  exact five_le_all_orderedCutRotationSystem_faceOrbits_of_oldProfile
    RS keep leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter
    hseamEndpoints hminimum hprofile root

end

end GoertzelV24RetainedVertexRotationSplice

end Mettapedia.GraphTheory.FourColor
