import Mettapedia.ProbabilityTheory.ImpreciseProbability.IntervalError
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction

/-!
# Deduction readouts and information radii

The four formula inputs are `P(B|A)`, `P(C|B)`, `P(B)`, `P(C)`.
They need not describe a coherent joint law. Antecedent mass and dependence
information are separate data; their use as error certificates requires proofs.
-/

namespace Mettapedia.PLN.Comparisons.DeductionStability

/-- Four probability readouts; compatibility with a joint law is additional. -/
structure PremiseValues where
  ab : Set.Icc (0 : ℝ) 1
  bc : Set.Icc (0 : ℝ) 1
  b : Set.Icc (0 : ℝ) 1
  c : Set.Icc (0 : ℝ) 1

/-- Evaluate the existing nonlinear deduction formula. -/
noncomputable def estimate (input : PremiseValues) : ℝ :=
  Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation.plnDeductionStrength
    input.ab input.bc input.b input.c

/-- Ordinary conditional-information radius; information uses natural logarithms. -/
noncomputable def informationRadius (antecedentMass information : ℝ) : ℝ :=
  Real.sqrt (information / (2 * antecedentMass))

/-- Complementary mass sharpens the radius when both endpoint marginals agree. -/
noncomputable def balancedRadius (antecedentMass information : ℝ) : ℝ :=
  Real.sqrt ((1 - antecedentMass) * information / (2 * antecedentMass))

/-- The sharp five-readout interval, evaluated at a proposed estimate. -/
noncomputable def credalRadius (antecedentMass : ℝ) (input : PremiseValues) (value : ℝ) : ℝ :=
  Mettapedia.ProbabilityTheory.ImpreciseProbability.IntervalError.intervalErrorRadius
    (Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.deductionCredalStrengthLower
      antecedentMass input.b input.c input.ab input.bc)
    (Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.deductionCredalStrengthUpper
      antecedentMass input.b input.c input.ab input.bc) value

end Mettapedia.PLN.Comparisons.DeductionStability
