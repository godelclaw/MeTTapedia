import Mettapedia.Analysis.RootPartitionEnergy

/-! Regressions distinguishing fourth-power from squared root normalization. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RootPartitionEnergyTests

open scoped BigOperators
open RootPartitionEnergy GaussianPartitionEnergy FiniteExponentialWeights

example : (∑ i : Fin 4, rootAmplitude (fun _ ↦ (0 : ℝ)) 1 2 0 i ^ 4) = 16 := by
  rw [sum_rootAmplitude_fourth]
  norm_num

/-- Four equal root amplitudes have squared sum two, but fourth-power sum one. -/
example : (∑ i : Fin 4, rootAmplitude (fun _ ↦ (0 : ℝ)) 1 1 0 i ^ 2) = 2 ∧
    (∑ i : Fin 4, rootAmplitude (fun _ ↦ (0 : ℝ)) 1 1 0 i ^ 4) = 1 := by
  constructor
  · have hs : Real.sqrt 4 = 2 :=
      (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
    simp only [rootAmplitude_sq]
    norm_num [gaussianAmplitude, score, amplitude, partition, hs]
  · simpa using sum_rootAmplitude_fourth (fun _ : Fin 4 ↦ (0 : ℝ)) 1 1 0

end Mettapedia.Analysis.RootPartitionEnergyTests

#print axioms Mettapedia.Analysis.RootPartitionEnergy.sum_weighted_deriv_sq_le
#print axioms Mettapedia.Analysis.RootPartitionEnergy.rootAmplitude_sq
#print axioms Mettapedia.Analysis.RootPartitionEnergy.sum_rootAmplitude_fourth
#print axioms Mettapedia.Analysis.RootPartitionEnergy.differentiableAt_rootAmplitude
#print axioms Mettapedia.Analysis.RootPartitionEnergy.sum_deriv_rootAmplitude_sq_sq_le
#print axioms Mettapedia.Analysis.RootPartitionEnergy.sum_weighted_rootVorticity_deriv_sq_le
