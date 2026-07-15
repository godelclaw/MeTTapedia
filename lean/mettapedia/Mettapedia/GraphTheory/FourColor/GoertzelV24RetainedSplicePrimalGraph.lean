import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedVertexRotationSplice
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceDualConnectedness

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RetainedSplicePrimalGraph

open GoertzelV24FaceDualConnectedness
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The retained endpoint of one position on an ordered cut. -/
def orderedBoundaryRetainedVertex
    (RS : RotationSystem V E) (keep : V -> Prop)
    (crossing : Fin n -> E)
    (hcrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = crossing step /\
      keep (RS.vertOf dart) /\
      Not (keep (RS.vertOf (RS.alpha dart))))
    (step : Fin n) : RetainedVertex keep :=
  let dart := orderedBoundaryDart RS keep crossing hcrosses step
  ⟨RS.vertOf dart.1.1.1, dart.1.1.2⟩

@[simp]
theorem orderedBoundaryRetainedVertex_val
    (RS : RotationSystem V E) (keep : V -> Prop)
    (crossing : Fin n -> E)
    (hcrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = crossing step /\
      keep (RS.vertOf dart) /\
      Not (keep (RS.vertOf (RS.alpha dart))))
    (step : Fin n) :
    (orderedBoundaryRetainedVertex RS keep crossing hcrosses step).1 =
      RS.vertOf
        (orderedBoundaryDart RS keep crossing hcrosses step).1.1.1 :=
  rfl

/-- The old primal graph induced on the vertices left after deletion. -/
abbrev retainedAmbientPrimalGraph
    (RS : RotationSystem V E) (keep : V -> Prop) :
    SimpleGraph (RetainedVertex keep) :=
  (rotationPrimalGraph RS).induce {vertex | keep vertex}

/-- The new seam edges computed from the two ordered endpoint lists. -/
def orderedCutSeamPrimalGraph
    (RS : RotationSystem V E) (keep : V -> Prop)
    (leftCrossing rightCrossing : Fin n -> E)
    (hleftCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = leftCrossing step /\
      keep (RS.vertOf dart) /\
      Not (keep (RS.vertOf (RS.alpha dart))))
    (hrightCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = rightCrossing step /\
      keep (RS.vertOf dart) /\
      Not (keep (RS.vertOf (RS.alpha dart))))
    (hseamEndpoints : forall step,
      RS.vertOf
          (orderedBoundaryDart RS keep leftCrossing
            hleftCrosses step).1.1.1 ≠
        RS.vertOf
          (orderedBoundaryDart RS keep rightCrossing
            hrightCrosses step).1.1.1) :
    SimpleGraph (RetainedVertex keep) where
  Adj left right := exists step : Fin n,
    (left = orderedBoundaryRetainedVertex RS keep leftCrossing
        hleftCrosses step /\
      right = orderedBoundaryRetainedVertex RS keep rightCrossing
        hrightCrosses step) \/
    (left = orderedBoundaryRetainedVertex RS keep rightCrossing
        hrightCrosses step /\
      right = orderedBoundaryRetainedVertex RS keep leftCrossing
        hleftCrosses step)
  symm := ⟨by
    rintro left right ⟨step, hforward | hbackward⟩
    · exact ⟨step, Or.inr ⟨hforward.2, hforward.1⟩⟩
    · exact ⟨step, Or.inl ⟨hbackward.2, hbackward.1⟩⟩⟩
  loopless := ⟨by
    rintro vertex ⟨step, hforward | hbackward⟩
    · apply hseamEndpoints step
      exact congrArg Subtype.val (hforward.1.symm.trans hforward.2)
    · apply hseamEndpoints step
      exact congrArg Subtype.val (hbackward.2.symm.trans hbackward.1)⟩

/-- The full primal graph predicted before gluing: retained old edges plus
the explicitly paired seam endpoints. -/
def orderedCutComputedPrimalGraph
    (RS : RotationSystem V E) (keep : V -> Prop)
    (leftCrossing rightCrossing : Fin n -> E)
    (hleftCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = leftCrossing step /\
      keep (RS.vertOf dart) /\
      Not (keep (RS.vertOf (RS.alpha dart))))
    (hrightCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = rightCrossing step /\
      keep (RS.vertOf dart) /\
      Not (keep (RS.vertOf (RS.alpha dart))))
    (hseamEndpoints : forall step,
      RS.vertOf
          (orderedBoundaryDart RS keep leftCrossing
            hleftCrosses step).1.1.1 ≠
        RS.vertOf
          (orderedBoundaryDart RS keep rightCrossing
            hrightCrosses step).1.1.1) :
    SimpleGraph (RetainedVertex keep) :=
  retainedAmbientPrimalGraph RS keep ⊔
    orderedCutSeamPrimalGraph RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hseamEndpoints

@[simp]
theorem orderedCutRetainedVertexRotationSystem_vertOf_val
    (RS : RotationSystem V E) (keep : V -> Prop)
    (leftCrossing rightCrossing : Fin n -> E)
    (hleftCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = leftCrossing step /\ keep (RS.vertOf dart) /\
        Not (keep (RS.vertOf (RS.alpha dart))))
    (hrightCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = rightCrossing step /\ keep (RS.vertOf dart) /\
        Not (keep (RS.vertOf (RS.alpha dart))))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : forall dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing \/
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing) (orderedCut rightCrossing))
    (houter : keep (RS.vertOf RS.outer))
    (hseamEndpoints : forall step,
      RS.vertOf (orderedBoundaryDart RS keep leftCrossing
          hleftCrosses step).1.1.1 ≠
        RS.vertOf (orderedBoundaryDart RS keep rightCrossing
          hrightCrosses step).1.1.1)
    (dart : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep (orderedCut leftCrossing))
      (BoundaryDartOn RS keep (orderedCut rightCrossing))) :
    ((orderedCutRetainedVertexRotationSystem RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints).vertOf dart).1 =
      RS.vertOf (matchedPartUnderlyingDart RS keep
        (orderedCut leftCrossing) (orderedCut rightCrossing) dart) :=
  rfl

@[simp]
theorem orderedCutRetainedVertexRotationSystem_alpha_interior
    (RS : RotationSystem V E) (keep : V -> Prop)
    (leftCrossing rightCrossing : Fin n -> E)
    (hleftCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = leftCrossing step /\ keep (RS.vertOf dart) /\
        Not (keep (RS.vertOf (RS.alpha dart))))
    (hrightCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = rightCrossing step /\ keep (RS.vertOf dart) /\
        Not (keep (RS.vertOf (RS.alpha dart))))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : forall dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing \/
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing) (orderedCut rightCrossing))
    (houter : keep (RS.vertOf RS.outer))
    (hseamEndpoints : forall step,
      RS.vertOf (orderedBoundaryDart RS keep leftCrossing
          hleftCrosses step).1.1.1 ≠
        RS.vertOf (orderedBoundaryDart RS keep rightCrossing
          hrightCrosses step).1.1.1)
    (dart : InternalDart RS keep) :
    (orderedCutRetainedVertexRotationSystem RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints).alpha (Sum.inl dart) =
      Sum.inl (internalAlpha RS keep dart) :=
  rfl

@[simp]
theorem orderedCutRetainedVertexRotationSystem_alpha_left
    (RS : RotationSystem V E) (keep : V -> Prop)
    (leftCrossing rightCrossing : Fin n -> E)
    (hleftCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = leftCrossing step /\ keep (RS.vertOf dart) /\
        Not (keep (RS.vertOf (RS.alpha dart))))
    (hrightCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = rightCrossing step /\ keep (RS.vertOf dart) /\
        Not (keep (RS.vertOf (RS.alpha dart))))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : forall dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing \/
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing) (orderedCut rightCrossing))
    (houter : keep (RS.vertOf RS.outer))
    (hseamEndpoints : forall step,
      RS.vertOf (orderedBoundaryDart RS keep leftCrossing
          hleftCrosses step).1.1.1 ≠
        RS.vertOf (orderedBoundaryDart RS keep rightCrossing
          hrightCrosses step).1.1.1)
    (dart : BoundaryDartOn RS keep (orderedCut leftCrossing)) :
    (orderedCutRetainedVertexRotationSystem RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints).alpha (Sum.inr (Sum.inl dart)) =
      Sum.inr (Sum.inr
        (orderedCutSeamMatching RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective dart)) :=
  rfl

@[simp]
theorem orderedCutRetainedVertexRotationSystem_alpha_right
    (RS : RotationSystem V E) (keep : V -> Prop)
    (leftCrossing rightCrossing : Fin n -> E)
    (hleftCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = leftCrossing step /\ keep (RS.vertOf dart) /\
        Not (keep (RS.vertOf (RS.alpha dart))))
    (hrightCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = rightCrossing step /\ keep (RS.vertOf dart) /\
        Not (keep (RS.vertOf (RS.alpha dart))))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : forall dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing \/
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing) (orderedCut rightCrossing))
    (houter : keep (RS.vertOf RS.outer))
    (hseamEndpoints : forall step,
      RS.vertOf (orderedBoundaryDart RS keep leftCrossing
          hleftCrosses step).1.1.1 ≠
        RS.vertOf (orderedBoundaryDart RS keep rightCrossing
          hrightCrosses step).1.1.1)
    (dart : BoundaryDartOn RS keep (orderedCut rightCrossing)) :
    (orderedCutRetainedVertexRotationSystem RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints).alpha (Sum.inr (Sum.inr dart)) =
      Sum.inr (Sum.inl
        ((orderedCutSeamMatching RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective).symm dart)) :=
  rfl

/-- The primal graph of the concrete retained-vertex splice is exactly the
graph computed before gluing from retained old edges and ordered seam pairs. -/
theorem rotationPrimalGraph_orderedCutRetainedVertexRotationSystem_eq
    (RS : RotationSystem V E) (keep : V -> Prop)
    (leftCrossing rightCrossing : Fin n -> E)
    (hleftCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = leftCrossing step /\
      keep (RS.vertOf dart) /\
      Not (keep (RS.vertOf (RS.alpha dart))))
    (hrightCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = rightCrossing step /\
      keep (RS.vertOf dart) /\
      Not (keep (RS.vertOf (RS.alpha dart))))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : forall dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing \/
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (houter : keep (RS.vertOf RS.outer))
    (hseamEndpoints : forall step,
      RS.vertOf
          (orderedBoundaryDart RS keep leftCrossing
            hleftCrosses step).1.1.1 ≠
        RS.vertOf
          (orderedBoundaryDart RS keep rightCrossing
            hrightCrosses step).1.1.1) :
    rotationPrimalGraph
        (orderedCutRetainedVertexRotationSystem RS keep
          leftCrossing rightCrossing hleftCrosses hrightCrosses
          hleftInjective hrightInjective hcover hdisjoint houter
          hseamEndpoints) =
      orderedCutComputedPrimalGraph RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hseamEndpoints := by
  ext left right
  simp only [rotationPrimalGraph_adj_iff, orderedCutComputedPrimalGraph,
    SimpleGraph.sup_adj, SimpleGraph.induce_adj]
  constructor
  · rintro ⟨dart, hleft, hright⟩
    rcases dart with interior | side
    · left
      refine ⟨interior.1.1, ?_, ?_⟩
      · simpa [matchedPartUnderlyingDart] using
          congrArg Subtype.val hleft
      · rw [orderedCutRetainedVertexRotationSystem_alpha_interior] at hright
        simpa [matchedPartUnderlyingDart, internalAlpha] using
          congrArg Subtype.val hright
    · rcases side with leftDart | rightDart
      · right
        rcases orderedBoundaryDart_surjective RS keep leftCrossing
          hleftCrosses leftDart with ⟨step, rfl⟩
        refine ⟨step, Or.inl ⟨?_, ?_⟩⟩
        · apply Subtype.ext
          simpa [matchedPartUnderlyingDart] using
            congrArg Subtype.val hleft.symm
        · rw [orderedCutRetainedVertexRotationSystem_alpha_left,
            orderedCutSeamMatching_apply] at hright
          apply Subtype.ext
          simpa [matchedPartUnderlyingDart] using
            congrArg Subtype.val hright.symm
      · right
        rcases orderedBoundaryDart_surjective RS keep rightCrossing
          hrightCrosses rightDart with ⟨step, rfl⟩
        refine ⟨step, Or.inr ⟨?_, ?_⟩⟩
        · apply Subtype.ext
          simpa [matchedPartUnderlyingDart] using
            congrArg Subtype.val hleft.symm
        · rw [orderedCutRetainedVertexRotationSystem_alpha_right,
            orderedCutSeamMatching_symm_apply] at hright
          apply Subtype.ext
          simpa [matchedPartUnderlyingDart] using
            congrArg Subtype.val hright.symm
  · rintro (hold | hseam)
    · rcases hold with ⟨dart, hleft, hright⟩
      let interior : InternalDart RS keep :=
        ⟨⟨dart, by simpa [hleft] using left.2⟩,
          by simpa [hright] using right.2⟩
      refine ⟨Sum.inl interior, ?_, ?_⟩
      · apply Subtype.ext
        simpa [matchedPartUnderlyingDart] using hleft
      · apply Subtype.ext
        rw [orderedCutRetainedVertexRotationSystem_alpha_interior]
        simpa [interior, matchedPartUnderlyingDart, internalAlpha] using hright
    · rcases hseam with ⟨step, hforward | hbackward⟩
      · refine ⟨Sum.inr (Sum.inl
          (orderedBoundaryDart RS keep leftCrossing
            hleftCrosses step)), ?_, ?_⟩
        · apply Subtype.ext
          simpa [matchedPartUnderlyingDart] using
            congrArg Subtype.val hforward.1.symm
        · rw [orderedCutRetainedVertexRotationSystem_alpha_left,
            orderedCutSeamMatching_apply]
          apply Subtype.ext
          simpa [matchedPartUnderlyingDart] using
            congrArg Subtype.val hforward.2.symm
      · refine ⟨Sum.inr (Sum.inr
          (orderedBoundaryDart RS keep rightCrossing
            hrightCrosses step)), ?_, ?_⟩
        · apply Subtype.ext
          simpa [matchedPartUnderlyingDart] using
            congrArg Subtype.val hbackward.1.symm
        · rw [orderedCutRetainedVertexRotationSystem_alpha_right,
            orderedCutSeamMatching_symm_apply]
          apply Subtype.ext
          simpa [matchedPartUnderlyingDart] using
            congrArg Subtype.val hbackward.2.symm

/-- Connectedness of the shortened graph is therefore exactly the finite,
pre-gluing connectivity test on retained old edges plus seam endpoint pairs. -/
theorem rotationPrimalGraph_orderedCutRetainedVertexRotationSystem_connected_iff
    (RS : RotationSystem V E) (keep : V -> Prop)
    (leftCrossing rightCrossing : Fin n -> E)
    (hleftCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = leftCrossing step /\
      keep (RS.vertOf dart) /\
      Not (keep (RS.vertOf (RS.alpha dart))))
    (hrightCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = rightCrossing step /\
      keep (RS.vertOf dart) /\
      Not (keep (RS.vertOf (RS.alpha dart))))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : forall dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing \/
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (houter : keep (RS.vertOf RS.outer))
    (hseamEndpoints : forall step,
      RS.vertOf
          (orderedBoundaryDart RS keep leftCrossing
            hleftCrosses step).1.1.1 ≠
        RS.vertOf
          (orderedBoundaryDart RS keep rightCrossing
            hrightCrosses step).1.1.1) :
    (rotationPrimalGraph
      (orderedCutRetainedVertexRotationSystem RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints)).Connected ↔
      (orderedCutComputedPrimalGraph RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hseamEndpoints).Connected := by
  rw [rotationPrimalGraph_orderedCutRetainedVertexRotationSystem_eq]

/-- In particular, a connected retained ambient subgraph remains connected
after the seam edges are added. -/
theorem rotationPrimalGraph_orderedCutRetainedVertexRotationSystem_connected_of_retained
    (RS : RotationSystem V E) (keep : V -> Prop)
    (leftCrossing rightCrossing : Fin n -> E)
    (hleftCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = leftCrossing step /\
      keep (RS.vertOf dart) /\
      Not (keep (RS.vertOf (RS.alpha dart))))
    (hrightCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = rightCrossing step /\
      keep (RS.vertOf dart) /\
      Not (keep (RS.vertOf (RS.alpha dart))))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : forall dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing \/
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (houter : keep (RS.vertOf RS.outer))
    (hseamEndpoints : forall step,
      RS.vertOf
          (orderedBoundaryDart RS keep leftCrossing
            hleftCrosses step).1.1.1 ≠
        RS.vertOf
          (orderedBoundaryDart RS keep rightCrossing
            hrightCrosses step).1.1.1)
    (hconnected : (retainedAmbientPrimalGraph RS keep).Connected) :
    (rotationPrimalGraph
      (orderedCutRetainedVertexRotationSystem RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints)).Connected := by
  rw [rotationPrimalGraph_orderedCutRetainedVertexRotationSystem_eq]
  exact hconnected.mono le_sup_left

end

end GoertzelV24RetainedSplicePrimalGraph

end Mettapedia.GraphTheory.FourColor
