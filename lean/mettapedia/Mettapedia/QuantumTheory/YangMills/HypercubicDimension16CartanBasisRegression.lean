import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanBasis

/-! Regression and axiom audit for the dimension-sixteen Cartan census. -/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CartanBasisRegression

open HypercubicDimension16CartanCensus

example : Fintype.card OcticMonomial = 1287 :=
  card_octicMonomial

example (monomial : OcticMonomial) :
    (∃ coordinate : Fin 17,
      InSignedOcticOrbit (octicRepresentative coordinate) monomial) ∨
      HasNegativeOcticStabilizer monomial :=
  octic_signedOrbit_classification monomial

example : octicConditioningConstant = 1 := rfl

example :
    HasOcticCoordinateSupBound octicUnitCoordinate 1 ∧
      |octicSynthesis octicUnitCoordinate (octicRepresentative 0)| = 1 :=
  octicConditioningConstant_sharp

#print axioms octic_signedOrbit_classification
#print axioms octic_representative_stabilizer_positive
#print axioms octic_hypercubic_reconstruction
#print axioms octic_conditioning_matrix_identity
#print axioms octicSynthesis_coefficientSup_le
#print axioms octicDual_coefficientSup_le
#print axioms dimension16CartanCensus_packet

end HypercubicDimension16CartanBasisRegression
end YangMills
end QuantumTheory
end Mettapedia
