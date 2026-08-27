import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitExecutableSignature
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitPlaneHistogram

/-!
# Transparent plane-histogram tests for the eight-field orbit chart

These formulas evaluate the independently defined plane-multiplicity
invariant and tensor sign directly on the checked fixed-width chart.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceOrbitHistogramExecutable

open SU2LatticeFDCensusNoGo
open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open HypercubicRawFDCharacterCensus
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16TraceOrbitChartCore
open HypercubicDimension16TraceOrbitChart
open HypercubicDimension16TraceOrbitExecutableSignature
open HypercubicDimension16TraceOrbitPlaneHistogram

/-- Plane multiplicity after one literal hypercubic action, evaluated on a
fixed-width entry. -/
@[reducible] def encodedPlaneMultiplicityAt (code : Array Nat)
    (h : Hypercubic4) (plane : OrientedPlane) : Nat :=
  ∑ field : Fin 8,
    if planeAction h (encodedPlane code field) = plane then 1 else 0

/-- The six plane multiplicities of one chart representative after an
action. -/
@[reducible] def directRepresentativePlaneHistogramAt
    (index : PositiveRepresentativeIndex) (h : Hypercubic4) :
    OrientedPlane → Nat :=
  encodedPlaneMultiplicityAt (positiveRepresentativeCode index) h

theorem encodedPlaneMultiplicityAt_eq_decoded
    (index : PositiveRepresentativeIndex) (h : Hypercubic4)
    (plane : OrientedPlane) :
    encodedPlaneMultiplicityAt (positiveRepresentativeCode index) h plane =
      labeledPlaneMultiplicity
        ((decodedPositiveRepresentative index).hypercubicAct h) plane := by
  rfl

theorem directRepresentativePlaneHistogramAt_eq
    (index : PositiveRepresentativeIndex) (h : Hypercubic4) :
    directRepresentativePlaneHistogramAt index h =
      fieldEightOrbitPlaneHistogram
        ((positiveRepresentativeTarget index).hypercubicAct h) := by
  funext plane
  unfold directRepresentativePlaneHistogramAt positiveRepresentativeTarget
  rw [FieldRelabelOrbitCarrier.hypercubicAct_mk,
    fieldEightOrbitPlaneHistogram_mk]
  exact encodedPlaneMultiplicityAt_eq_decoded index h plane

/-- Reflections do not alter the transported plane histogram. -/
theorem directRepresentativePlaneHistogramAt_reflection_blind
    (index : PositiveRepresentativeIndex) (permutation : Fin 24)
    (reflection : Fin 16) :
    directRepresentativePlaneHistogramAt index
        (decodedHypercubicCharacterElement permutation reflection) =
      directRepresentativePlaneHistogramAt index
        (decodedHypercubicCharacterElement permutation 0) := by
  rfl

/-- On a two-form component, the unsigned reordering sign and the coordinate
reflection sign factor exactly. -/
theorem planeTensorSign_decodedHypercubic_split :
    ∀ permutation : Fin 24, ∀ reflection : Fin 16,
      ∀ plane : OrientedPlane,
        planeTensorSign
            (decodedHypercubicCharacterElement permutation reflection) plane =
          planeTensorSign
              (decodedHypercubicCharacterElement permutation 0) plane *
            planeTensorSign
              (decodedHypercubicCharacterElement 0 reflection) plane := by
  decide

/-- The full tensor sign factors into its unsigned-permutation part and its
pure-reflection part. -/
theorem directRepresentativeTensorSign_character_split
    (index : PositiveRepresentativeIndex) (permutation : Fin 24)
    (reflection : Fin 16) :
    directRepresentativeTensorSign index
        (decodedHypercubicCharacterElement permutation reflection) =
      directRepresentativeTensorSign index
          (decodedHypercubicCharacterElement permutation 0) *
      directRepresentativeTensorSign index
          (decodedHypercubicCharacterElement 0 reflection) := by
  unfold directRepresentativeTensorSign
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro field _
  rw [← Int.cast_mul, planeTensorSign_decodedHypercubic_split]

end HypercubicDimension16TraceOrbitHistogramExecutable
end YangMills
end QuantumTheory
end Mettapedia
