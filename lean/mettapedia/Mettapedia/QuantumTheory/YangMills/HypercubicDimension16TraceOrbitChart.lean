import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidity

/-!
# A checked labeled chart for the positive signed eight-field orbits

The generated payload contains a forward trace permutation, its independently
stored inverse, and eight oriented-plane colors.  A single finite theorem
checks the width, ranges, and both inverse laws for all 11,654 entries before
they are decoded into the standard labeled local-word carrier.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceOrbitChart

open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16TraceOrbitSignature
open HypercubicDimension16TraceOrbitChartCore
open HypercubicDimension16TraceOrbitChartValidity

/-- Decoding lands in the standard derivative-free labeled carrier. -/
def decodedPositiveRepresentative (index : PositiveRepresentativeIndex) :
    FieldEightLabeledSector :=
  let code := positiveRepresentativeCode index
  let valid := positiveRepresentativeCodes_valid index
  { trace :=
      { toFun := encodedTraceForward code
        invFun := encodedTraceBackward code
        left_inv := valid.2.2.2.2.1
        right_inv := valid.2.2.2.2.2 }
    decoration :=
      ⟨fun field =>
        { plane := encodedPlane code field
          derivativeCount := 0
          derivativeAxis := Fin.elim0 }, by simp⟩ }

/-- The decoded representative in the genuine field-relabel orbit carrier. -/
def positiveRepresentativeTarget (index : PositiveRepresentativeIndex) :
    FieldEightOrbitCarrier :=
  Quotient.mk _ (decodedPositiveRepresentative index)

@[simp] theorem positiveRepresentativeTarget_signature
    (index : PositiveRepresentativeIndex) :
    fieldEightOrbitSignature (positiveRepresentativeTarget index) =
      labeledTraceSignature (decodedPositiveRepresentative index) :=
  rfl

end HypercubicDimension16TraceOrbitChart
end YangMills
end QuantumTheory
end Mettapedia
