import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedSplicePrimalGraph

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RetainedSpliceEdgeDecomposition

open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RetainedSplicePrimalGraph
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Endpoint pair of an old edge whose two darts both survive deletion. -/
def retainedInternalEndpointPair
    (RS : RotationSystem V E) (keep : V -> Prop)
    (dart : InternalDart RS keep) : Finset (RetainedVertex keep) :=
  {⟨RS.vertOf dart.1.1, dart.1.2⟩,
    ⟨RS.vertOf (RS.alpha dart.1.1), dart.2⟩}

/-- Forgetting retained-vertex proofs recovers the ambient edge endpoint set. -/
theorem image_val_retainedInternalEndpointPair
    (RS : RotationSystem V E) (keep : V -> Prop)
    (dart : InternalDart RS keep) :
    (retainedInternalEndpointPair RS keep dart).image Subtype.val =
      RS.endpoints (RS.edgeOf dart.1.1) := by
  have hmem : dart.1.1 ∈ RS.dartsOn (RS.edgeOf dart.1.1) :=
    RS.mem_dartsOn.2 rfl
  rw [RS.endpoints_eq_pair_of_mem hmem]
  simp [retainedInternalEndpointPair]

/-- Endpoint pair of the new seam edge at an ordered cut position. -/
def orderedCutSeamEndpointPair
    (RS : RotationSystem V E) (keep : V -> Prop)
    (leftCrossing rightCrossing : Fin n -> E)
    (hleftCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = leftCrossing step /\ keep (RS.vertOf dart) /\
        Not (keep (RS.vertOf (RS.alpha dart))))
    (hrightCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = rightCrossing step /\ keep (RS.vertOf dart) /\
        Not (keep (RS.vertOf (RS.alpha dart))))
    (step : Fin n) : Finset (RetainedVertex keep) :=
  {orderedBoundaryRetainedVertex RS keep leftCrossing hleftCrosses step,
    orderedBoundaryRetainedVertex RS keep rightCrossing hrightCrosses step}

/-- The exact finite endpoint condition required to avoid new parallel edges:
different seam positions have different pairs, and no seam pair duplicates an
old retained edge pair. -/
def OrderedCutEndpointSimple
    (RS : RotationSystem V E) (keep : V -> Prop)
    (leftCrossing rightCrossing : Fin n -> E)
    (hleftCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = leftCrossing step /\ keep (RS.vertOf dart) /\
        Not (keep (RS.vertOf (RS.alpha dart))))
    (hrightCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = rightCrossing step /\ keep (RS.vertOf dart) /\
        Not (keep (RS.vertOf (RS.alpha dart)))) : Prop :=
  Function.Injective
      (orderedCutSeamEndpointPair RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses) /\
    forall step (dart : InternalDart RS keep),
      orderedCutSeamEndpointPair RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses step ≠
        retainedInternalEndpointPair RS keep dart

/-- Output edge represented by an old retained internal dart. -/
def retainedInternalSpliceEdge
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
    (orderedCutRetainedVertexRewiredDartSystem RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
      hseamEndpoints).Edge :=
  (orderedCutRetainedVertexRotationSystem RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter
    hseamEndpoints).edgeOf (Sum.inl dart)

/-- Output edge at one ordered seam position. -/
def orderedCutSeamSpliceEdge
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
    (step : Fin n) :
    (orderedCutRetainedVertexRewiredDartSystem RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
      hseamEndpoints).Edge :=
  (orderedCutRetainedVertexRotationSystem RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter
    hseamEndpoints).edgeOf
      (Sum.inr (Sum.inl
        (orderedBoundaryDart RS keep leftCrossing hleftCrosses step)))

/-- Two retained internal representatives name the same output edge exactly
when their underlying old darts name the same ambient edge. -/
theorem retainedInternalSpliceEdge_eq_iff
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
    (left right : InternalDart RS keep) :
    retainedInternalSpliceEdge RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter hseamEndpoints left =
      retainedInternalSpliceEdge RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter hseamEndpoints right ↔
      RS.edgeOf left.1.1 = RS.edgeOf right.1.1 := by
  let data := orderedCutRetainedVertexRewiredDartSystem RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter hseamEndpoints
  change data.edgeOf (Sum.inl left) = data.edgeOf (Sum.inl right) ↔ _
  rw [data.edgeOf_eq_edgeOf_iff]
  constructor
  · rintro (hsame | hopposite)
    · exact congrArg (fun dart : InternalDart RS keep => RS.edgeOf dart.1.1)
        (Sum.inl.inj hsame)
    · have hinterior : left = internalAlpha RS keep right := by
        have hs :
            (Sum.inl left : MatchedSeam.Dart (InternalDart RS keep)
              (BoundaryDartOn RS keep (orderedCut leftCrossing))
              (BoundaryDartOn RS keep (orderedCut rightCrossing))) =
              Sum.inl (internalAlpha RS keep right) := by
          simpa [data, orderedCutRetainedVertexRewiredDartSystem,
            orderedCutRewiredDartSystem,
            MatchedSeam.Data.toRewiredDartSystem,
            orderedCutMatchedSeamData] using hopposite
        exact Sum.inl.inj hs
      rw [hinterior, internalAlpha_val, RS.edge_alpha]
  · intro hold
    have hcases := RS.edge_fiber_two_cases
      (e := RS.edgeOf right.1.1) (d := right.1.1) (y := left.1.1)
      rfl hold
    rcases hcases with hsame | hopposite
    · exact Or.inl (congrArg Sum.inl (Subtype.ext (Subtype.ext hsame)))
    · apply Or.inr
      have hinterior : left = internalAlpha RS keep right := by
        apply Subtype.ext
        apply Subtype.ext
        exact hopposite
      have hs :
          (Sum.inl left : MatchedSeam.Dart (InternalDart RS keep)
            (BoundaryDartOn RS keep (orderedCut leftCrossing))
            (BoundaryDartOn RS keep (orderedCut rightCrossing))) =
            Sum.inl (internalAlpha RS keep right) :=
        congrArg (fun dart : InternalDart RS keep =>
          (Sum.inl dart : MatchedSeam.Dart (InternalDart RS keep)
            (BoundaryDartOn RS keep (orderedCut leftCrossing))
            (BoundaryDartOn RS keep (orderedCut rightCrossing)))) hinterior
      simpa [data, orderedCutRetainedVertexRewiredDartSystem,
        orderedCutRewiredDartSystem,
        MatchedSeam.Data.toRewiredDartSystem,
        orderedCutMatchedSeamData] using hs

/-- Ordered positions give pairwise distinct seam edges. -/
theorem orderedCutSeamSpliceEdge_injective
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
          hrightCrosses step).1.1.1) :
    Function.Injective
      (orderedCutSeamSpliceEdge RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter hseamEndpoints) := by
  intro left right hedges
  let data := orderedCutRetainedVertexRewiredDartSystem RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter hseamEndpoints
  change data.edgeOf
      (Sum.inr (Sum.inl
        (orderedBoundaryDart RS keep leftCrossing hleftCrosses left))) =
    data.edgeOf
      (Sum.inr (Sum.inl
        (orderedBoundaryDart RS keep leftCrossing hleftCrosses right))) at hedges
  rw [data.edgeOf_eq_edgeOf_iff] at hedges
  rcases hedges with hsame | hopposite
  · apply orderedBoundaryDart_injective RS keep leftCrossing
      hleftCrosses hleftInjective
    exact Sum.inl.inj (Sum.inr.inj hsame)
  · exfalso
    simpa [data, orderedCutRetainedVertexRewiredDartSystem,
      orderedCutRewiredDartSystem,
      MatchedSeam.Data.toRewiredDartSystem,
      orderedCutMatchedSeamData] using hopposite

/-- No retained internal edge can be one of the newly paired seam edges. -/
theorem retainedInternalSpliceEdge_ne_orderedCutSeamSpliceEdge
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
    (dart : InternalDart RS keep) (step : Fin n) :
    retainedInternalSpliceEdge RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter hseamEndpoints dart ≠
      orderedCutSeamSpliceEdge RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter hseamEndpoints step := by
  let data := orderedCutRetainedVertexRewiredDartSystem RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter hseamEndpoints
  intro hedges
  change data.edgeOf (Sum.inl dart) =
    data.edgeOf (Sum.inr (Sum.inl
      (orderedBoundaryDart RS keep leftCrossing hleftCrosses step))) at hedges
  have hcases := (data.edgeOf_eq_edgeOf_iff _ _).1 hedges
  simpa [data, orderedCutRetainedVertexRewiredDartSystem,
    orderedCutRewiredDartSystem,
    MatchedSeam.Data.toRewiredDartSystem,
    orderedCutMatchedSeamData] using hcases

/-- Every output edge is represented either by an old retained internal dart
or by exactly one of the ordered seam positions. -/
theorem retainedSpliceEdge_internal_or_seam
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
    (edge : (orderedCutRetainedVertexRewiredDartSystem RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
      hseamEndpoints).Edge) :
    (exists dart : InternalDart RS keep,
      edge = retainedInternalSpliceEdge RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter hseamEndpoints dart) \/
    (exists step : Fin n,
      edge = orderedCutSeamSpliceEdge RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter hseamEndpoints step) := by
  let data := orderedCutRetainedVertexRewiredDartSystem RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter hseamEndpoints
  rcases edge.property with ⟨dart, hdart⟩
  have hedge : edge = data.edgeOf dart := Subtype.ext hdart
  rw [hedge]
  rcases dart with interior | side
  · exact Or.inl ⟨interior, rfl⟩
  · rcases side with leftDart | rightDart
    · rcases orderedBoundaryDart_surjective RS keep leftCrossing
        hleftCrosses leftDart with ⟨step, rfl⟩
      exact Or.inr ⟨step, rfl⟩
    · rcases orderedBoundaryDart_surjective RS keep rightCrossing
        hrightCrosses rightDart with ⟨step, rfl⟩
      apply Or.inr
      refine ⟨step, ?_⟩
      change data.edgeOf
          (Sum.inr (Sum.inr
            (orderedBoundaryDart RS keep rightCrossing
              hrightCrosses step))) =
        data.edgeOf
          (Sum.inr (Sum.inl
            (orderedBoundaryDart RS keep leftCrossing
              hleftCrosses step)))
      apply (data.edgeOf_eq_edgeOf_iff _ _).2
      apply Or.inr
      simpa [data, orderedCutRetainedVertexRewiredDartSystem,
        orderedCutRewiredDartSystem,
        MatchedSeam.Data.toRewiredDartSystem,
        orderedCutMatchedSeamData,
        orderedCutSeamMatching_apply]

/-- Endpoint set of an internal output edge is the retained form of its old
ambient endpoint set. -/
theorem endpoints_retainedInternalSpliceEdge
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
      hseamEndpoints).endpoints
        (retainedInternalSpliceEdge RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective
          hcover hdisjoint houter hseamEndpoints dart) =
      retainedInternalEndpointPair RS keep dart := by
  let newRS := orderedCutRetainedVertexRotationSystem RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter hseamEndpoints
  have hmem : (Sum.inl dart : newRS.D) ∈
      newRS.dartsOn (newRS.edgeOf (Sum.inl dart)) :=
    newRS.mem_dartsOn.2 rfl
  change newRS.endpoints (newRS.edgeOf (Sum.inl dart)) = _
  rw [newRS.endpoints_eq_pair_of_mem hmem]
  have hbase : newRS.vertOf (Sum.inl dart) =
      (⟨RS.vertOf dart.1.1, dart.1.2⟩ : RetainedVertex keep) := by
    apply Subtype.ext
    rfl
  have hopposite : newRS.vertOf (newRS.alpha (Sum.inl dart)) =
      (⟨RS.vertOf (RS.alpha dart.1.1), dart.2⟩ : RetainedVertex keep) := by
    rw [orderedCutRetainedVertexRotationSystem_alpha_interior]
    apply Subtype.ext
    rfl
  rw [hbase, hopposite]
  rfl

/-- Endpoint set of a seam edge is exactly its pre-gluing ordered endpoint
pair. -/
theorem endpoints_orderedCutSeamSpliceEdge
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
    (step : Fin n) :
    (orderedCutRetainedVertexRotationSystem RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
      hseamEndpoints).endpoints
        (orderedCutSeamSpliceEdge RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective
          hcover hdisjoint houter hseamEndpoints step) =
      orderedCutSeamEndpointPair RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses step := by
  let newRS := orderedCutRetainedVertexRotationSystem RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter hseamEndpoints
  let leftDart := orderedBoundaryDart RS keep leftCrossing hleftCrosses step
  have hmem : (Sum.inr (Sum.inl leftDart) : newRS.D) ∈
      newRS.dartsOn (newRS.edgeOf (Sum.inr (Sum.inl leftDart))) :=
    newRS.mem_dartsOn.2 rfl
  change newRS.endpoints (newRS.edgeOf (Sum.inr (Sum.inl leftDart))) = _
  rw [newRS.endpoints_eq_pair_of_mem hmem]
  have hbase : newRS.vertOf (Sum.inr (Sum.inl leftDart)) =
      orderedBoundaryRetainedVertex RS keep leftCrossing
        hleftCrosses step := by
    apply Subtype.ext
    rfl
  have hopposite :
      newRS.vertOf (newRS.alpha (Sum.inr (Sum.inl leftDart))) =
        orderedBoundaryRetainedVertex RS keep rightCrossing
          hrightCrosses step := by
    rw [orderedCutRetainedVertexRotationSystem_alpha_left,
      orderedCutSeamMatching_apply]
    apply Subtype.ext
    rfl
  rw [hbase, hopposite]
  rfl

/-- Ambient endpoint injectivity plus the computed seam endpoint test imply
endpoint injectivity for every edge of the shortened rotation system. -/
theorem orderedCutRetainedVertexRotationSystem_endpoints_injective
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
    (hambient : Function.Injective RS.endpoints)
    (hsimple : OrderedCutEndpointSimple RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses) :
    Function.Injective
      (orderedCutRetainedVertexRotationSystem RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints).endpoints := by
  intro leftEdge rightEdge hends
  rcases retainedSpliceEdge_internal_or_seam RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
      hseamEndpoints leftEdge with
    ⟨leftDart, rfl⟩ | ⟨leftStep, rfl⟩
  · rcases retainedSpliceEdge_internal_or_seam RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints rightEdge with
      ⟨rightDart, rfl⟩ | ⟨rightStep, rfl⟩
    · rw [endpoints_retainedInternalSpliceEdge,
        endpoints_retainedInternalSpliceEdge] at hends
      apply (retainedInternalSpliceEdge_eq_iff RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints leftDart rightDart).2
      apply hambient
      rw [← image_val_retainedInternalEndpointPair RS keep leftDart,
        ← image_val_retainedInternalEndpointPair RS keep rightDart]
      exact congrArg (Finset.image Subtype.val) hends
    · rw [endpoints_retainedInternalSpliceEdge,
        endpoints_orderedCutSeamSpliceEdge] at hends
      exact False.elim (hsimple.2 rightStep leftDart hends.symm)
  · rcases retainedSpliceEdge_internal_or_seam RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints rightEdge with
      ⟨rightDart, rfl⟩ | ⟨rightStep, rfl⟩
    · rw [endpoints_orderedCutSeamSpliceEdge,
        endpoints_retainedInternalSpliceEdge] at hends
      exact False.elim (hsimple.2 leftStep rightDart hends)
    · rw [endpoints_orderedCutSeamSpliceEdge,
        endpoints_orderedCutSeamSpliceEdge] at hends
      exact congrArg
        (orderedCutSeamSpliceEdge RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective
          hcover hdisjoint houter hseamEndpoints) (hsimple.1 hends)

/-- For an ambient simple graph, the finite seam endpoint predicate is not
merely sufficient: it is equivalent to simplicity of the splice output. -/
theorem orderedCutRetainedVertexRotationSystem_endpoints_injective_iff
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
    (hambient : Function.Injective RS.endpoints) :
    Function.Injective
        (orderedCutRetainedVertexRotationSystem RS keep
          leftCrossing rightCrossing hleftCrosses hrightCrosses
          hleftInjective hrightInjective hcover hdisjoint houter
          hseamEndpoints).endpoints ↔
      OrderedCutEndpointSimple RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses := by
  constructor
  · intro houtput
    constructor
    · intro left right hpairs
      apply orderedCutSeamSpliceEdge_injective RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints
      apply houtput
      rw [endpoints_orderedCutSeamSpliceEdge,
        endpoints_orderedCutSeamSpliceEdge]
      exact hpairs
    · intro step dart hpairs
      have hedges :
          orderedCutSeamSpliceEdge RS keep leftCrossing rightCrossing
              hleftCrosses hrightCrosses hleftInjective hrightInjective
              hcover hdisjoint houter hseamEndpoints step =
            retainedInternalSpliceEdge RS keep leftCrossing rightCrossing
              hleftCrosses hrightCrosses hleftInjective hrightInjective
              hcover hdisjoint houter hseamEndpoints dart := by
        apply houtput
        rw [endpoints_orderedCutSeamSpliceEdge,
          endpoints_retainedInternalSpliceEdge]
        exact hpairs
      exact (retainedInternalSpliceEdge_ne_orderedCutSeamSpliceEdge RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints dart step) hedges.symm
  · exact orderedCutRetainedVertexRotationSystem_endpoints_injective RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
      hseamEndpoints hambient

/-- The endpoint test supplies the exact no-parallel-edges field required by
`RotationSystem.PlanarGeometry`; it is not assumed on the splice output. -/
theorem orderedCutRetainedVertexRotationSystem_no_parallel_edges
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
    (hambient : Function.Injective RS.endpoints)
    (hsimple : OrderedCutEndpointSimple RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses) :
    let data := orderedCutRetainedVertexRewiredDartSystem RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
      hseamEndpoints
    let newRS := orderedCutRetainedVertexRotationSystem RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
      hseamEndpoints
    forall {edge edge' : data.Edge} {dart dart' : newRS.D},
      newRS.edgeOf dart = edge ->
      newRS.edgeOf dart' = edge' ->
      edge ≠ edge' ->
      ({newRS.vertOf dart, newRS.vertOf (newRS.alpha dart)} :
          Finset (RetainedVertex keep)) ≠
        {newRS.vertOf dart', newRS.vertOf (newRS.alpha dart')} := by
  dsimp only
  let newRS := orderedCutRetainedVertexRotationSystem RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter hseamEndpoints
  intro edge edge' dart dart' hdart hdart' hne hpairs
  apply hne
  apply orderedCutRetainedVertexRotationSystem_endpoints_injective RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter
    hseamEndpoints hambient hsimple
  have hmem : dart ∈ newRS.dartsOn edge := newRS.mem_dartsOn.2 hdart
  have hmem' : dart' ∈ newRS.dartsOn edge' := newRS.mem_dartsOn.2 hdart'
  rw [newRS.endpoints_eq_pair_of_mem hmem,
    newRS.endpoints_eq_pair_of_mem hmem']
  exact hpairs

end

end GoertzelV24RetainedSpliceEdgeDecomposition

end Mettapedia.GraphTheory.FourColor
