import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedCutRotationSplice
import Mettapedia.GraphTheory.FourColor.GoertzelV24RewiredTaitColoring

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrderedCutTaitSplice

open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Color each retained or exposed dart by its old edge. Equal cut colors will
make this invariant under the newly rewired edge flip. -/
def orderedCutDartColor
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCrossing rightCrossing : Fin n → E)
    (C : E → Color) :
    MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep (orderedCut leftCrossing))
      (BoundaryDartOn RS keep (orderedCut rightCrossing)) → Color :=
  fun dart => C (RS.edgeOf (matchedPartUnderlyingDart RS keep
    (orderedCut leftCrossing) (orderedCut rightCrossing) dart))

/-- Matching the cut color words is exactly what is needed for the old dart
color to be invariant under the new seam involution. -/
theorem orderedCutDartColor_alpha
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
    (C : E → Color)
    (hcutColors : ∀ step, C (leftCrossing step) = C (rightCrossing step))
    (dart : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep (orderedCut leftCrossing))
      (BoundaryDartOn RS keep (orderedCut rightCrossing))) :
    orderedCutDartColor RS keep leftCrossing rightCrossing C
        ((orderedCutMatchedSeamData RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective
          hcover hdisjoint houter).alpha dart) =
      orderedCutDartColor RS keep leftCrossing rightCrossing C dart := by
  rcases dart with interior | side
  · change C (RS.edgeOf (RS.alpha interior.1.1)) =
      C (RS.edgeOf interior.1.1)
    rw [RS.edge_alpha]
  · rcases side with left | right
    · rcases orderedBoundaryDart_surjective RS keep leftCrossing
        hleftCrosses left with ⟨step, hstep⟩
      rw [← hstep]
      change C (RS.edgeOf
          ((orderedCutSeamMatching RS keep leftCrossing rightCrossing
            hleftCrosses hrightCrosses hleftInjective hrightInjective)
              (orderedBoundaryDart RS keep leftCrossing
                hleftCrosses step)).1.1.1) =
        C (RS.edgeOf (orderedBoundaryDart RS keep leftCrossing
          hleftCrosses step).1.1.1)
      rw [orderedCutSeamMatching_apply, orderedBoundaryDart_edgeOf,
        orderedBoundaryDart_edgeOf]
      exact (hcutColors step).symm
    · rcases orderedBoundaryDart_surjective RS keep rightCrossing
        hrightCrosses right with ⟨step, hstep⟩
      rw [← hstep]
      change C (RS.edgeOf
          ((orderedCutSeamMatching RS keep leftCrossing rightCrossing
            hleftCrosses hrightCrosses hleftInjective hrightInjective).symm
              (orderedBoundaryDart RS keep rightCrossing
                hrightCrosses step)).1.1.1) =
        C (RS.edgeOf (orderedBoundaryDart RS keep rightCrossing
          hrightCrosses step).1.1.1)
      rw [orderedCutSeamMatching_symm_apply, orderedBoundaryDart_edgeOf,
        orderedBoundaryDart_edgeOf]
      exact hcutColors step

/-- Properness of the old coloring transfers locally to the retained dart
carrier. The proof derives distinct old edges from distinct retained darts at
the same original vertex. -/
theorem orderedCutDartColor_proper
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
    (C : RS.EdgeColoring Color)
    {left right : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep (orderedCut leftCrossing))
      (BoundaryDartOn RS keep (orderedCut rightCrossing))}
    (hvertex :
      (orderedCutMatchedSeamData RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter).vertOf left =
      (orderedCutMatchedSeamData RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter).vertOf right)
    (hne : left ≠ right) :
    orderedCutDartColor RS keep leftCrossing rightCrossing C left ≠
      orderedCutDartColor RS keep leftCrossing rightCrossing C right := by
  let leftDart := matchedPartUnderlyingDart RS keep
    (orderedCut leftCrossing) (orderedCut rightCrossing) left
  let rightDart := matchedPartUnderlyingDart RS keep
    (orderedCut leftCrossing) (orderedCut rightCrossing) right
  have hdartNe : leftDart ≠ rightDart :=
    (matchedPartUnderlyingDart_injective RS keep
      (orderedCut leftCrossing) (orderedCut rightCrossing)
      hcover hdisjoint).ne hne
  have hvertex' : RS.vertOf leftDart = RS.vertOf rightDart := by
    rw [← orderedCutMatchedSeamData_vertOf RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter]
    rw [← orderedCutMatchedSeamData_vertOf RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter]
    exact hvertex
  have hedgeNe : RS.edgeOf leftDart ≠ RS.edgeOf rightDart := by
    intro hedges
    apply hdartNe
    apply RS.edgeOf_injOn_dartsAt (RS.vertOf leftDart)
    · simp [RotationSystem.dartsAt]
    · simp [RotationSystem.dartsAt, hvertex'.symm]
    · exact hedges
  apply C.valid
  apply RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges hedgeNe
  · exact (RS.mem_incidentEdges_iff).2 ⟨leftDart, rfl, rfl⟩
  · exact (RS.mem_incidentEdges_iff).2 ⟨rightDart, rfl, hvertex'.symm⟩

/-- The old Tait coloring therefore descends to a proper coloring of the
shortened rotation system's computed edge orbits. -/
def orderedCutSplicedColoring
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
          (orderedBoundaryDart RS keep rightCrossing hrightCrosses step).1.1.1)
    (C : RS.EdgeColoring Color)
    (hcutColors : ∀ step, C (leftCrossing step) = C (rightCrossing step)) :
    (orderedCutRotationSystem RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter hseamEndpoints).EdgeColoring Color := by
  let rewired := orderedCutRewiredDartSystem RS keep leftCrossing rightCrossing
    hleftCrosses hrightCrosses hleftInjective hrightInjective
    hcover hdisjoint houter hseamEndpoints
  apply rewired.descendedColoring
    (orderedCutDartColor RS keep leftCrossing rightCrossing C)
  · exact orderedCutDartColor_alpha RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter C hcutColors
  · intro left right hvertex hne
    exact orderedCutDartColor_proper RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter C hvertex hne

/-- Nonzero old edge colors remain nonzero after descent, so an equal-color
ordered splice carries an actual Tait coloring. -/
theorem orderedCutSplicedColoring_isTait
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
          (orderedBoundaryDart RS keep rightCrossing hrightCrosses step).1.1.1)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (hcutColors : ∀ step, C (leftCrossing step) = C (rightCrossing step)) :
    (orderedCutRotationSystem RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter hseamEndpoints).IsTaitEdgeColoring
        (orderedCutSplicedColoring RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective
          hcover hdisjoint houter hseamEndpoints C hcutColors) := by
  let rewired := orderedCutRewiredDartSystem RS keep leftCrossing rightCrossing
    hleftCrosses hrightCrosses hleftInjective hrightInjective
    hcover hdisjoint houter hseamEndpoints
  apply rewired.descendedColoring_isTait
    (orderedCutDartColor RS keep leftCrossing rightCrossing C)
  · exact orderedCutDartColor_alpha RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter C hcutColors
  · intro left right hvertex hne
    exact orderedCutDartColor_proper RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter C hvertex hne
  · intro dart
    exact hC (RS.edgeOf (matchedPartUnderlyingDart RS keep
      (orderedCut leftCrossing) (orderedCut rightCrossing) dart))

end

end GoertzelV24OrderedCutTaitSplice

end Mettapedia.GraphTheory.FourColor
