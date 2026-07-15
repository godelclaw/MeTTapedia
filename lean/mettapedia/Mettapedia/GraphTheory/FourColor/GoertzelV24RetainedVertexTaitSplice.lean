import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedCutTaitSplice
import Mettapedia.GraphTheory.FourColor.GoertzelV24PlanarBondSpliceEuler

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RetainedVertexTaitSplice

open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24OrderedCutTaitSplice
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The equal-color ordered splice descends directly to the corrected
retained-vertex rotation system. This is the same edge coloring as the
ambient-carrier construction, but its vertex carrier contains no deleted
isolated vertices. -/
def orderedCutRetainedVertexSplicedColoring
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
    (C : RS.EdgeColoring Color)
    (hcutColors : ∀ step,
      C (leftCrossing step) = C (rightCrossing step)) :
    (orderedCutRetainedVertexRotationSystem RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
      hseamEndpoints).EdgeColoring Color := by
  let rewired := orderedCutRetainedVertexRewiredDartSystem RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter hseamEndpoints
  apply rewired.descendedColoring
    (orderedCutDartColor RS keep leftCrossing rightCrossing C)
  · exact orderedCutDartColor_alpha RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter C hcutColors
  · intro left right hvertex hne
    have hvertexUnderlying :
        RS.vertOf (matchedPartUnderlyingDart RS keep
            (orderedCut leftCrossing) (orderedCut rightCrossing) left) =
          RS.vertOf (matchedPartUnderlyingDart RS keep
            (orderedCut leftCrossing) (orderedCut rightCrossing) right) := by
      change matchedPartRetainedVertex RS keep
          (orderedCut leftCrossing) (orderedCut rightCrossing) left =
        matchedPartRetainedVertex RS keep
          (orderedCut leftCrossing) (orderedCut rightCrossing) right at hvertex
      exact congrArg Subtype.val hvertex
    apply orderedCutDartColor_proper RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter C
    · rw [orderedCutMatchedSeamData_vertOf,
        orderedCutMatchedSeamData_vertOf]
      exact hvertexUnderlying
    · exact hne

/-- A Tait coloring with equal colors on the matched interfaces remains a
Tait coloring on the corrected retained-vertex splice. -/
theorem orderedCutRetainedVertexSplicedColoring_isTait
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
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (hcutColors : ∀ step,
      C (leftCrossing step) = C (rightCrossing step)) :
    (orderedCutRetainedVertexRotationSystem RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
      hseamEndpoints).IsTaitEdgeColoring
        (orderedCutRetainedVertexSplicedColoring RS keep
          leftCrossing rightCrossing hleftCrosses hrightCrosses
          hleftInjective hrightInjective hcover hdisjoint houter
          hseamEndpoints C hcutColors) := by
  let rewired := orderedCutRetainedVertexRewiredDartSystem RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter hseamEndpoints
  apply rewired.descendedColoring_isTait
    (orderedCutDartColor RS keep leftCrossing rightCrossing C)
  · exact orderedCutDartColor_alpha RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter C hcutColors
  · intro left right hvertex hne
    have hvertexUnderlying :
        RS.vertOf (matchedPartUnderlyingDart RS keep
            (orderedCut leftCrossing) (orderedCut rightCrossing) left) =
          RS.vertOf (matchedPartUnderlyingDart RS keep
            (orderedCut leftCrossing) (orderedCut rightCrossing) right) := by
      change matchedPartRetainedVertex RS keep
          (orderedCut leftCrossing) (orderedCut rightCrossing) left =
        matchedPartRetainedVertex RS keep
          (orderedCut leftCrossing) (orderedCut rightCrossing) right at hvertex
      exact congrArg Subtype.val hvertex
    apply orderedCutDartColor_proper RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter C
    · rw [orderedCutMatchedSeamData_vertOf,
        orderedCutMatchedSeamData_vertOf]
      exact hvertexUnderlying
    · exact hne
  · intro dart
    exact hC (RS.edgeOf (matchedPartUnderlyingDart RS keep
      (orderedCut leftCrossing) (orderedCut rightCrossing) dart))

/-- Equality of graph-derived corridor profiles supplies the interface color
matching needed by the corrected retained-vertex splice. -/
theorem orderedCutRetainedVertexSplicedColoring_isTait_of_profiles_eq
    (RS : RotationSystem V E) (keep : V → Prop)
    {terminalCount faceFragmentCount : Nat}
    (left right : GraphCorridorCutData RS n terminalCount faceFragmentCount)
    (hleftCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = left.crossingEdge step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hrightCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = right.crossingEdge step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hleftInjective : Function.Injective left.crossingEdge)
    (hrightInjective : Function.Injective right.crossingEdge)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut left.crossingEdge ∨
        RS.edgeOf dart.1.1 ∈ orderedCut right.crossingEdge)
    (hdisjoint : Disjoint (orderedCut left.crossingEdge)
      (orderedCut right.crossingEdge))
    (houter : keep (RS.vertOf RS.outer))
    (hseamEndpoints : ∀ step,
      RS.vertOf
          (orderedBoundaryDart RS keep left.crossingEdge
            hleftCrosses step).1.1.1 ≠
        RS.vertOf
          (orderedBoundaryDart RS keep right.crossingEdge
            hrightCrosses step).1.1.1)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (hprofiles : left.profile C hC = right.profile C hC) :
    (orderedCutRetainedVertexRotationSystem RS keep
      left.crossingEdge right.crossingEdge hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
      hseamEndpoints).IsTaitEdgeColoring
        (orderedCutRetainedVertexSplicedColoring RS keep
          left.crossingEdge right.crossingEdge hleftCrosses hrightCrosses
          hleftInjective hrightInjective hcover hdisjoint houter
          hseamEndpoints C
          (crossingEdge_color_eq_of_profiles_eq left right C C hC hC
            hprofiles)) :=
  orderedCutRetainedVertexSplicedColoring_isTait RS keep
    left.crossingEdge right.crossingEdge hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter hseamEndpoints
    C hC (crossingEdge_color_eq_of_profiles_eq left right C C hC hC
      hprofiles)

end

end GoertzelV24RetainedVertexTaitSplice

end Mettapedia.GraphTheory.FourColor
