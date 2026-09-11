import Mettapedia.Analysis.DyadicLowPass
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicPartition
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPressureTraceSymbol

/-!
# Matched dyadic indices with one fixed physical output scale

Increasing the input scale by `2^j` and starting the output-band index at
`j` leaves the physical output filter unchanged. The kernel mass retains
`4^(-j)` decay, and its first moment has the same decay relative to the
base input scale. The output filter is built into the kernel symbol.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputSymbol

open PeriodicFourierTriad FourierPressureCommutator FourierPressureTraceSymbol
open PressureLowOutputSymbol (pairEquiv)
open PressureLowOutputCutoff (ratio)
open PressureLowOutputDyadicBudget PressureDyadicPhysicalKernel PressureDyadicPartition
open Mettapedia.Analysis.DyadicAnnulus Mettapedia.Analysis.DyadicLowPass

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def inputScale (N : ℝ) (j : ℕ) : ℝ := N * (2 : ℝ) ^ j

theorem inputScale_pos (N : ℝ) (hN : 0 < N) (j : ℕ) : 0 < inputScale N j := by
  unfold inputScale
  positivity

def outputMultiplier (N : ℝ) (q : Wavevector) : ℝ := multiplier ((256 / N : ℝ) • realFrequency q)

theorem outputMultiplier_nonneg (N : ℝ) (q : Wavevector) : 0 ≤ outputMultiplier N q :=
  multiplier_nonneg _

theorem outputMultiplier_le_one (N : ℝ) (q : Wavevector) : outputMultiplier N q ≤ 1 :=
  multiplier_le_one _

theorem outputMultiplier_eq_one (N : ℝ) (hN : 0 < N) (q : Wavevector)
    (hq : ‖realFrequency q‖ ≤ N / 256) : outputMultiplier N q = 1 := by
  apply multiplier_eq_one_of_norm_le
  rw [norm_smul, Real.norm_of_nonneg (div_nonneg (by norm_num) hN.le)]
  calc
    _ ≤ (256 / N) * (N / 256) := mul_le_mul_of_nonneg_left hq (by positivity)
    _ = 1 := by field_simp

theorem outputMultiplier_eq_zero (N : ℝ) (hN : 0 < N) (q : Wavevector)
    (hq : N / 64 ≤ ‖realFrequency q‖) : outputMultiplier N q = 0 := by
  apply multiplier_eq_zero_of_le_norm
  rw [norm_smul, Real.norm_of_nonneg (div_nonneg (by norm_num) hN.le)]
  calc
    (4 : ℝ) = (256 / N) * (N / 64) := by field_simp; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left hq (by positivity)

theorem physicalCutoff_matched (N : ℝ) (j m : ℕ) (k p : Wavevector) :
    physicalCutoff (dyadicParameter (j + m))
      ((inputScale N j)⁻¹ • pairEquiv.symm (realFrequency k, realFrequency p)) =
      normalizedCutoff ((inputScale N j)⁻¹ • realFrequency k) *
        normalizedCutoff ((2 : ℝ) ^ m • ((256 / N : ℝ) • realFrequency (k + p))) := by
  rw [physicalCutoff_dyadicParameter]
  simp only [map_smul, pairEquiv.apply_symm_apply, Prod.smul_fst, Prod.smul_snd,
    ← smul_add, realFrequency_add, smul_smul]
  congr 2
  unfold inputScale
  rw [pow_add]
  field_simp

theorem ratio_matched (j m : ℕ) :
    ratio (dyadicParameter (j + m)) = (1 / 256 : ℝ) * (1 / 2) ^ j * (1 / 2) ^ m := by
  rw [ratio_dyadicParameter, pow_add]
  ring

theorem ratio_sq_matched (j m : ℕ) :
    (ratio (dyadicParameter (j + m))) ^ 2 =
      (1 / 65536 : ℝ) * (1 / 4) ^ j * (1 / 4) ^ m := by
  rw [ratio_matched]
  simp only [mul_pow]
  rw [pow_right_comm (1 / 2 : ℝ) j 2, pow_right_comm (1 / 2 : ℝ) m 2]
  norm_num

theorem ratio_div_inputScale (N : ℝ) (j m : ℕ) :
    ratio (dyadicParameter (j + m)) / inputScale N j =
      (1 / (256 * N)) * (1 / 4 : ℝ) ^ j * (1 / 2) ^ m := by
  rw [ratio_matched, inputScale]
  simp only [div_pow]
  field_simp
  rw [pow_right_comm (2 : ℝ) j 2]
  norm_num

end Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputSymbol
