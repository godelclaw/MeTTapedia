import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedSpliceEdgeDecomposition

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RetainedSpliceEdgeCount

open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RetainedSpliceEdgeDecomposition
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Ambient edges whose complete two-dart fiber survives the deletion. -/
def RetainedInternalEdge
    (RS : RotationSystem V E) (keep : V -> Prop) :=
  {edge : E // exists dart : InternalDart RS keep,
    RS.edgeOf dart.1.1 = edge}

noncomputable instance retainedInternalEdgeFintype
    (RS : RotationSystem V E) (keep : V -> Prop) :
    Fintype (RetainedInternalEdge RS keep) :=
  Fintype.ofInjective (fun edge : RetainedInternalEdge RS keep => edge.1)
    Subtype.val_injective

instance retainedInternalEdgeDecidableEq
    (RS : RotationSystem V E) (keep : V -> Prop) :
    DecidableEq (RetainedInternalEdge RS keep) :=
  Classical.decEq _

/-- A chosen old dart representative of a retained internal edge. -/
def retainedInternalEdgeDart
    (RS : RotationSystem V E) (keep : V -> Prop)
    (edge : RetainedInternalEdge RS keep) : InternalDart RS keep :=
  Classical.choose edge.2

@[simp]
theorem retainedInternalEdgeDart_edgeOf
    (RS : RotationSystem V E) (keep : V -> Prop)
    (edge : RetainedInternalEdge RS keep) :
    RS.edgeOf (retainedInternalEdgeDart RS keep edge).1.1 = edge.1 :=
  Classical.choose_spec edge.2

/-- Map the disjoint pre-gluing edge sources to output edges. -/
def retainedSpliceEdgeOfSource
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
    RetainedInternalEdge RS keep ⊕ Fin n ->
      (orderedCutRetainedVertexRewiredDartSystem RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints).Edge
  | Sum.inl edge => retainedInternalSpliceEdge RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
      hseamEndpoints (retainedInternalEdgeDart RS keep edge)
  | Sum.inr step => orderedCutSeamSpliceEdge RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
      hseamEndpoints step

theorem retainedSpliceEdgeOfSource_injective
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
      (retainedSpliceEdgeOfSource RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter hseamEndpoints) := by
  intro left right hedges
  rcases left with leftEdge | leftStep
  · rcases right with rightEdge | rightStep
    · apply congrArg Sum.inl
      apply Subtype.ext
      have hold := (retainedInternalSpliceEdge_eq_iff RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints (retainedInternalEdgeDart RS keep leftEdge)
        (retainedInternalEdgeDart RS keep rightEdge)).1 hedges
      simpa using hold
    · exact False.elim
        ((retainedInternalSpliceEdge_ne_orderedCutSeamSpliceEdge RS keep
          leftCrossing rightCrossing hleftCrosses hrightCrosses
          hleftInjective hrightInjective hcover hdisjoint houter
          hseamEndpoints (retainedInternalEdgeDart RS keep leftEdge)
          rightStep) hedges)
  · rcases right with rightEdge | rightStep
    · exact False.elim
        ((retainedInternalSpliceEdge_ne_orderedCutSeamSpliceEdge RS keep
          leftCrossing rightCrossing hleftCrosses hrightCrosses
          hleftInjective hrightInjective hcover hdisjoint houter
          hseamEndpoints (retainedInternalEdgeDart RS keep rightEdge)
          leftStep) hedges.symm)
    · apply congrArg Sum.inr
      exact orderedCutSeamSpliceEdge_injective RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints hedges

theorem retainedSpliceEdgeOfSource_surjective
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
    Function.Surjective
      (retainedSpliceEdgeOfSource RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter hseamEndpoints) := by
  intro edge
  rcases retainedSpliceEdge_internal_or_seam RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
      hseamEndpoints edge with hInternal | hSeam
  · rcases hInternal with ⟨dart, hedge⟩
    let source : RetainedInternalEdge RS keep :=
      ⟨RS.edgeOf dart.1.1, ⟨dart, rfl⟩⟩
    refine ⟨Sum.inl source, ?_⟩
    change retainedInternalSpliceEdge RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints (retainedInternalEdgeDart RS keep source) = edge
    rw [hedge]
    apply (retainedInternalSpliceEdge_eq_iff RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
      hseamEndpoints (retainedInternalEdgeDart RS keep source) dart).2
    exact retainedInternalEdgeDart_edgeOf RS keep source
  · rcases hSeam with ⟨step, hedge⟩
    exact ⟨Sum.inr step, hedge.symm⟩

/-- Canonical classification of every output edge by its pre-gluing source. -/
def retainedSpliceEdgeSourceEquiv
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
    RetainedInternalEdge RS keep ⊕ Fin n ≃
      (orderedCutRetainedVertexRewiredDartSystem RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints).Edge :=
  Equiv.ofBijective
    (retainedSpliceEdgeOfSource RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter hseamEndpoints)
    ⟨retainedSpliceEdgeOfSource_injective RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints,
      retainedSpliceEdgeOfSource_surjective RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints⟩

/-- Exact edge-count term for Euler arithmetic after an ordered deletion and
splice. -/
theorem card_orderedCutRetainedVertexRotationSystem_edges
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
    Fintype.card
        (orderedCutRetainedVertexRewiredDartSystem RS keep
          leftCrossing rightCrossing hleftCrosses hrightCrosses
          hleftInjective hrightInjective hcover hdisjoint houter
          hseamEndpoints).Edge =
      Fintype.card (RetainedInternalEdge RS keep) + n := by
  calc
    Fintype.card
        (orderedCutRetainedVertexRewiredDartSystem RS keep
          leftCrossing rightCrossing hleftCrosses hrightCrosses
          hleftInjective hrightInjective hcover hdisjoint houter
          hseamEndpoints).Edge =
        Fintype.card (RetainedInternalEdge RS keep ⊕ Fin n) :=
      Fintype.card_congr
        (retainedSpliceEdgeSourceEquiv RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective
          hcover hdisjoint houter hseamEndpoints).symm
    _ = Fintype.card (RetainedInternalEdge RS keep) + Fintype.card (Fin n) :=
      Fintype.card_sum
    _ = Fintype.card (RetainedInternalEdge RS keep) + n := by simp

end

end GoertzelV24RetainedSpliceEdgeCount

end Mettapedia.GraphTheory.FourColor
