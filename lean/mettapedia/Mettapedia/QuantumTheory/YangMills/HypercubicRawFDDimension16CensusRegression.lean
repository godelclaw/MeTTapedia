import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDDimension16Census

/-! Regression and axiom audit for the unpadded raw character census. -/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicRawFDDimension16CensusRegression

open V14HypercubicFDCensus
open HypercubicRawFDCharacterCensus
open HypercubicRawFDDimension16Census

example : dimension16LayoutMultiplicity = 5361612271200 :=
  dimension16LayoutMultiplicity_exact

example : Module.finrank ℚ
    (axisTensorInvariantSubmodule ContractionParity.scalar 16) =
      22379179 :=
  scalar_rank16_tensorMultiplicity

example : Module.finrank ℚ
    (axisTensorInvariantSubmodule ContractionParity.pseudoscalar 16) =
      22368256 :=
  pseudoscalar_rank16_tensorMultiplicity

example : Module.finrank ℚ
    (dimension16RawInvariantSubmodule ContractionParity.scalar) =
      119988480745781344800 :=
  scalar_dimension16_rawInvariantCount

example : Module.finrank ℚ
    (dimension16RawInvariantSubmodule ContractionParity.pseudoscalar) =
      119929915854943027200 :=
  pseudoscalar_dimension16_rawInvariantCount

example : Module.finrank ℚ
    (exactDimension16UnpaddedInvariantSubmodule
      ContractionParity.scalar) =
      119988480745781344800 :=
  scalar_dimension16_exactUnpaddedInvariantCount

example : Module.finrank ℚ
    (exactDimension16UnpaddedInvariantSubmodule
      ContractionParity.pseudoscalar) =
      119929915854943027200 :=
  pseudoscalar_dimension16_exactUnpaddedInvariantCount

example : Fintype.card Dimension16RawAxisCarrier =
    23027949358636282675200 :=
  dimension16_rawCarrierCount

example : Fintype.card ExactDimension16UnpaddedRawFDMonomial =
    23027949358636282675200 :=
  exactDimension16_unpaddedRawCarrierCount

#print axioms decodedHypercubicCharacterElement_bijective
#print axioms finrank_axisTensorInvariantSubmodule
#print axioms finrank_axisTensorInvariantSubmodule_certificate
#print axioms dimension16LayoutMultiplicity_exact
#print axioms finrank_dimension16RawInvariantSubmodule
#print axioms scalar_dimension16_rawInvariantCount
#print axioms pseudoscalar_dimension16_rawInvariantCount
#print axioms dimension16_rawCarrierCount
#print axioms exactDimension16UnpaddedCarrierEquiv
#print axioms exactDimension16UnpaddedCarrierEquiv_act
#print axioms exactDimension16UnpaddedCarrierEquiv_tensorSign
#print axioms exactDimension16_unpaddedRawCarrierCount
#print axioms exactDimension16UnpaddedInvariantEquiv
#print axioms scalar_dimension16_exactUnpaddedInvariantCount
#print axioms pseudoscalar_dimension16_exactUnpaddedInvariantCount

end HypercubicRawFDDimension16CensusRegression
end YangMills
end QuantumTheory
end Mettapedia
