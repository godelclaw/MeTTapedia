import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartCertificate
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignCertificate

/-!
# Kernel-checked stabilizer signs for the eight-field orbit chart

Every actual carrier stabilizer preserves the six standard plane
multiplicities.  Bounded kernel replays test this deliberately coarser
necessary condition against the transparent `24 x 16` enumeration of the
literal hypercubic group and certify tensor sign `+1`.  No completeness claim
for the plane histogram is used.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceOrbitChartSignCertificate

open V14HypercubicFDCensus
open HypercubicRawFDCharacterCensus
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16TraceOrbitChartCore
open HypercubicDimension16TraceOrbitChart
open HypercubicDimension16TraceOrbitExecutableSignature
open HypercubicDimension16TraceOrbitPlaneHistogram
open HypercubicDimension16TraceOrbitHistogramExecutable
open HypercubicDimension16TraceOrbitHistogramSignCertificate

theorem directRepresentativeTensorSign_eq
    (index : PositiveRepresentativeIndex) (h : Hypercubic4) :
    directRepresentativeTensorSign index h =
      (positiveRepresentativeTarget index).tensorSign h := by
  rw [← executableRepresentativeTensorSign_eq]
  unfold directRepresentativeTensorSign executableRepresentativeTensorSign
  unfold LabeledLocalWordSector.tensorSign LocalFieldLetter.tensorSign
  apply Finset.prod_congr rfl
  intro field _
  simp [decodedPositiveRepresentative]

/-- Every standard plane-histogram stabilizer in the decoded chart has
positive tensor sign. -/
theorem allHistogramStabilizersPositive
    (index : PositiveRepresentativeIndex) (h : Hypercubic4)
    (hhistogram :
      fieldEightOrbitPlaneHistogram
          ((positiveRepresentativeTarget index).hypercubicAct h) =
        fieldEightOrbitPlaneHistogram
          (positiveRepresentativeTarget index)) :
    (positiveRepresentativeTarget index).tensorSign h = 1 := by
  let code : Fin 24 × Fin 16 := hypercubicCharacterCodeEquiv.symm h
  have hdecode :
      decodedHypercubicCharacterElement code.1 code.2 = h := by
    change hypercubicCharacterCodeEquiv code = h
    exact hypercubicCharacterCodeEquiv.apply_symm_apply h
  have hdirect :
      directRepresentativePlaneHistogramAt index
          (decodedHypercubicCharacterElement code.1 code.2) =
        directRepresentativePlaneHistogramAt index 1 := by
    rw [hdecode, directRepresentativePlaneHistogramAt_eq,
      directRepresentativePlaneHistogramAt_eq]
    rw [FieldRelabelOrbitCarrier.hypercubicAct_one]
    exact hhistogram
  have hfinite :=
    representative_histogram_stabilizers_positive index code hdirect
  rw [hdecode, directRepresentativeTensorSign_eq] at hfinite
  exact hfinite

/-- Every actual stabilizer of a decoded representative has tensor sign
`+1`. -/
theorem positiveRepresentativeTarget_stabilizer_sign
    (index : PositiveRepresentativeIndex) (h : Hypercubic4)
    (hfixed : (positiveRepresentativeTarget index).hypercubicAct h =
      positiveRepresentativeTarget index) :
    (positiveRepresentativeTarget index).tensorSign h = 1 := by
  apply allHistogramStabilizersPositive index h
  rw [hfixed]

end HypercubicDimension16TraceOrbitChartSignCertificate
end YangMills
end QuantumTheory
end Mettapedia
