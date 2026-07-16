import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16BoundarySymanzik

/-! Regression and axiom audit for the MOVE 8B boundary/Symanzik packet. -/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16BoundarySymanzikRegression

open HypercubicDimension16CartanCensus
open HypercubicWilsonSymanzikRestoration
open HypercubicDimension16BoundarySymanzik

example (a : ℝ) :
    actualWilsonDimension16SymanzikCoordinate a 0 =
      -(a ^ 12) / 20160 := by
  rw [actualWilsonDimension16SymanzikCoordinate_eq]
  simp

example : Module.finrank ℝ HonestOcticBoundaryH0 = 17 :=
  honestOcticBoundaryH0_finrank

example : honestDimension16ExtractionConstant = 1 :=
  honestDimension16ExtractionConstant_eq_one

example : honestDimension16RecursionBudget = (5544 : ℝ) / 5 :=
  honestDimension16RecursionBudget_eq

example :
    HasTwoSourceBootstrapSlack honestDimension16RecursionBudget 2 15 ∧
      ∀ depth : ℕ, depth ≤ 14 →
        ¬HasTwoSourceBootstrapSlack
          honestDimension16RecursionBudget 2 depth :=
  leastDepth_honestDimension16_packet

#print axioms normalizedSU2CartanWilsonDensity_eighthJet
#print axioms actualWilsonDimension16SymanzikCoordinate_eq
#print axioms normalizedSU2CartanWilsonDensity_rotation_error
#print axioms honestOcticBoundaryH0_finrank
#print axioms globalRecombine_actualWilsonOcticBulkCoordinates
#print axioms globalRecombine_actualWilsonOctic_add_sharedBoundary
#print axioms honestOcticSynthesisReal_coefficientSup_le
#print axioms honestOcticDualReal_coefficientSup_le
#print axioms actualFactors_le_honestDimension16RecursionBudget
#print axioms leastDepth_honestDimension16_packet
#print axioms move8B_boundarySymanzik_packet

end HypercubicDimension16BoundarySymanzikRegression
end YangMills
end QuantumTheory
end Mettapedia
