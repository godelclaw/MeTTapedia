import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressurePairMisalignment
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPressureTraceSymbol
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSameSectorDissipation

/-!
# Complex pressure pairs at the actual periodic Biot--Savart coefficients

The bilinear trace kernel uses the existing complex curl-inversion symbol.
On real amplitudes it agrees exactly with the real pressure-pair kernel.
The physical unit-torus derivative phases contribute an overall minus sign,
recorded separately from the phase-suppressed kernel used in norm estimates.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ComplexPressurePair

open scoped BigOperators RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeFrequencyProjectorCommutator
open FourierPressureCommutator FourierPressureTraceSymbol PressureTiltSymbol
open PancakeLowPressureBudget PancakeSameSectorDissipation

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)

def realCoefficient (w : R3) : VelocityCoefficient := fun i ↦ (w i : ℂ)

theorem norm_realCoefficient (w : R3) : ‖coefficientVec (realCoefficient w)‖ = ‖w‖ :=
  norm_complexifyVector w

theorem norm_frequencyVec_eq (k : Wavevector) : ‖frequencyVec k‖ = ‖realFrequency k‖ :=
  norm_complexifyVector (realFrequency k)

theorem modeSquare_eq_real (k : Wavevector) : modeSquare k = (‖realFrequency k‖ ^ 2 : ℝ) := by
  rw [modeSquare_eq_norm_sq, norm_frequencyVec_eq]

theorem modeDot_realCoefficient (k : Wavevector) (w : R3) :
    modeDot k (realCoefficient w) = (⟪realFrequency k, w⟫ : ℝ) := by
  simp [modeDot, realCoefficient, realFrequency, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Complex.ofReal_sum, mul_comm]

theorem coefficientCross_realCoefficient (k : Wavevector) (w : R3) :
    coefficientCross (wavevectorCoefficient k) (realCoefficient w) =
      realCoefficient (Mettapedia.Analysis.EuclideanCrossProduct.cross (realFrequency k) w) := by
  ext i
  fin_cases i <;>
    simp [coefficientCross, wavevectorCoefficient, realCoefficient,
      Mettapedia.Analysis.EuclideanCrossProduct.cross, realFrequency, crossProduct]

def tracePair (k p : Wavevector) (w v : VelocityCoefficient) : ℂ :=
  modeDot p (complexBiotSavartAmp k w) * modeDot k (complexBiotSavartAmp p v)

def tiltPair (e : R3) (k p : Wavevector) (w v : VelocityCoefficient) : C3 :=
  tracePair k p w v • complexTiltSymbol e (k + p)

theorem tracePair_real (k p : Wavevector) (w v : R3) :
    tracePair k p (realCoefficient w) (realCoefficient v) =
      (CoherentPressurePair.tracePair (realFrequency k) (realFrequency p) w v : ℝ) := by
  simp only [tracePair, complexBiotSavartAmp, modeDot_smul,
    coefficientCross_realCoefficient, modeDot_realCoefficient, modeSquare_eq_real,
    CoherentPressurePair.tracePair, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_pow]
  ring

theorem tiltPair_real (e : R3) (k p : Wavevector) (w v : R3) :
    tiltPair e k p (realCoefficient w) (realCoefficient v) =
      complexifyVector (CoherentPressurePair.tiltPair e (realFrequency k) (realFrequency p) w v) := by
  rw [tiltPair, tracePair_real]
  ext i
  simp [complexTiltSymbol, realFrequency_add, complexifyVector, coefficientVec,
    CoherentPressurePair.tiltPair]

theorem norm_tiltPair_coherent_le (e : R3) (he : ‖e‖ = 1) (k p : Wavevector) :
    ‖tiltPair e k p (realCoefficient e) (realCoefficient e)‖ ≤
      |⟪realFrequency k, e⟫| / ‖frequencyVec k‖ +
        |⟪realFrequency p, e⟫| / ‖frequencyVec p‖ := by
  rw [tiltPair_real, norm_complexifyVector, norm_frequencyVec_eq, norm_frequencyVec_eq]
  exact CoherentPressurePair.norm_tiltPair_coherent_le e _ _ he

theorem norm_tracePair_le (k p : Wavevector) (w v : VelocityCoefficient) :
    ‖tracePair k p w v‖ ≤ ‖coefficientVec w‖ * ‖coefficientVec v‖ := by
  rw [tracePair, norm_mul]
  calc
    _ ≤ (‖frequencyVec p‖ * ‖coefficientVec (complexBiotSavartAmp k w)‖) *
        (‖frequencyVec k‖ * ‖coefficientVec (complexBiotSavartAmp p v)‖) :=
      mul_le_mul (norm_modeDot_le _ _) (norm_modeDot_le _ _) (norm_nonneg _) (by positivity)
    _ = (‖frequencyVec k‖ * ‖coefficientVec (complexBiotSavartAmp k w)‖) *
        (‖frequencyVec p‖ * ‖coefficientVec (complexBiotSavartAmp p v)‖) := by ring
    _ ≤ _ := mul_le_mul (frequency_mul_norm_biot_le k w) (frequency_mul_norm_biot_le p v)
      (by positivity) (norm_nonneg _)

theorem norm_tiltPair_le (e : R3) (he : ‖e‖ = 1) (k p : Wavevector) (w v : VelocityCoefficient) :
    ‖tiltPair e k p w v‖ ≤ ‖coefficientVec w‖ * ‖coefficientVec v‖ := by
  rw [tiltPair, norm_smul, complexTiltSymbol, norm_complexifyVector]
  simpa only [mul_one] using mul_le_mul (norm_tracePair_le k p w v)
    (norm_tiltSymbol_le_one e (realFrequency (k + p)) he) (norm_nonneg _) (by positivity)

/-- The two curl-inversion phases cancel the two derivatives, including
their sign. No transversality or nonzero-frequency premise is needed. -/
theorem physical_tracePair_eq (k p : Wavevector) (w v : VelocityCoefficient) :
    -unitTorusDerivativePhase ^ 2 *
        (modeDot p (unitTorusBiotSavartAmp k w) * modeDot k (unitTorusBiotSavartAmp p v)) =
      -tracePair k p w v := by
  simp only [unitTorusBiotSavartAmp, modeDot_smul, tracePair]
  field_simp [unitTorusDerivativePhase_ne_zero]

end Mettapedia.FluidDynamics.NavierStokes.ComplexPressurePair
