import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateCore

/-!
# Local execution probe for OUR corrected trace-rank replay

These are bounded kernel checks of selected decoded replay rows.  They make no
rank, conditioning, or complete-census assertion.
-/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceRankCertificate

open HypercubicDimension16TraceRankCertificateData

set_option maxRecDepth 1000000

theorem correctedReplayRow_zero : replaySelectedRow 0 = true := by
  unfold replaySelectedRow
  unfold selectedIntegerRow? selectedIntegerRowsPayload0
  unfold normalizedRationalBasisRow? normalizedRationalBasisPayload0
  unfold rationalReplayStepRow? rationalReplayStepsPayload0
  unfold pivotColumn? pivotColumnsPayload0
  unfold columnOwner? columnOwnerPayload0
  decide +kernel

theorem correctedReplayRange_zero : rationalReplayRangeCheck 0 1 = true := by
  simp [rationalReplayRangeCheck, correctedReplayRow_zero]

theorem correctedReplayRow_final : replaySelectedRow 11555 = true := by
  unfold replaySelectedRow
  unfold selectedIntegerRow? selectedIntegerRowsPayload11
  unfold normalizedRationalBasisRow? normalizedRationalBasisPayload11
  unfold rationalReplayStepRow? rationalReplayStepsPayload11
  unfold pivotColumn? pivotColumnsPayload11
  unfold columnOwner? columnOwnerPayload11
  decide +kernel

theorem correctedReplayRange_final : rationalReplayRangeCheck 11555 1 = true := by
  simp [rationalReplayRangeCheck, correctedReplayRow_final]

#print axioms correctedReplayRow_zero
#print axioms correctedReplayRange_zero
#print axioms correctedReplayRow_final
#print axioms correctedReplayRange_final

end HypercubicDimension16TraceRankCertificate
end YangMills
end QuantumTheory
end Mettapedia
