import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ParallelHeatGeometry

/-!
# A finite, divergence-free snapshot with positive eighth-moment stretching

The velocity is `(-sin y, 0, sin x + sin (x+y))`, with physical angles
`2πx` and `2πy`. This is an instantaneous field, not a claimed solution
with invariant finite support. All spatial quantities are reconstructed
from its actual Fourier coefficients.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PositiveStretchingSnapshot

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory PeriodicFourierTriad PancakeGalerkinKineticEnergy
open PancakeBlockReality PancakePeriodicVorticityEquation
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeIndexedFourierMoments
open PancakeLocalGradientEquation PancakeDyadicDirectionEvolution PancakeFourierMaterialPaths
open PancakeTransverseEnergyFreezing LocalLowDiffusionBudget LocalAlignmentForcing
open LocalVorticityEighthMoment FourierFiniteSupport

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def xMode : Wavevector := ![1, 0, 0]
def yMode : Wavevector := ![0, 1, 0]
def diagonalMode : Wavevector := ![1, 1, 0]

def modes : Finset Wavevector :=
  {xMode, -xMode, yMode, -yMode, diagonalMode, -diagonalMode}

def sineCoeff (q : Wavevector) : Wavevector →₀ ℂ :=
  Finsupp.single q (-Complex.I / 2) + Finsupp.single (-q) (Complex.I / 2)

def coefficients : FourierVelocity := fun q ↦
  ![-sineCoeff yMode q, 0, sineCoeff xMode q + sineCoeff diagonalMode q]

theorem supported (q : Wavevector) (hq : q ∉ modes) : coefficients q = 0 := by
  classical
  simp only [modes, Finset.mem_insert, Finset.mem_singleton, not_or] at hq
  ext i
  fin_cases i <;> simp [coefficients, sineCoeff,
    hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1, hq.2.2.2.2.2]

theorem transverse (q : Wavevector) : modeDot q (coefficients q) = 0 := by
  classical
  by_cases hq : q ∈ modes
  · simp only [modes, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [modeDot, coefficients, sineCoeff, xMode, yMode, diagonalMode,
        Finsupp.single_apply, Fin.sum_univ_three, Matrix.vecCons_inj, Matrix.cons_val_two]
  · simp [supported q hq, modeDot]

theorem sineCoeff_neg (q k : Wavevector) : sineCoeff q (-k) = conj (sineCoeff q k) := by
  classical
  simp only [sineCoeff, Finsupp.add_apply, Finsupp.single_apply, neg_eq_iff_eq_neg, neg_neg]
  split_ifs <;> simp [map_div₀, map_ofNat]
  all_goals ring

theorem reality (q : Wavevector) : coefficients (-q) = coefficientConjugate (coefficients q) := by
  ext i
  fin_cases i <;> simp [coefficients, sineCoeff_neg, coefficientConjugate]

theorem coefficients_zero : coefficients 0 = 0 := by
  apply supported
  norm_num [modes, xMode, yMode, diagonalMode, Matrix.vecCons_inj, funext_iff, Fin.forall_fin_succ]

def cosine (q : Wavevector) (x : T3) : ℝ := (UnitAddTorus.mFourier q x).re

set_option maxHeartbeats 800000 in
theorem coordinateDerivative_eq (i j : Fin 3) (x : T3) :
    (coordinateDerivative (fullFourierField id coefficients) j x i).re =
      (2 * Real.pi) *
        (!![0, -cosine yMode x, 0;
            0, 0, 0;
            cosine xMode x + cosine diagonalMode x, cosine diagonalMode x, 0] i j) := by
  classical
  have hx : (UnitAddTorus.mFourier ![-1, 0, 0] x).re =
      (UnitAddTorus.mFourier ![1, 0, 0] x).re := by
    simpa [xMode] using congrArg Complex.re (UnitAddTorus.mFourier_neg (n := xMode) (x := x))
  have hy : (UnitAddTorus.mFourier ![0, -1, 0] x).re =
      (UnitAddTorus.mFourier ![0, 1, 0] x).re := by
    simpa [yMode] using congrArg Complex.re (UnitAddTorus.mFourier_neg (n := yMode) (x := x))
  have hz : (UnitAddTorus.mFourier ![-1, -1, 0] x).re =
      (UnitAddTorus.mFourier ![1, 1, 0] x).re := by
    simpa [diagonalMode] using congrArg Complex.re
      (UnitAddTorus.mFourier_neg (n := diagonalMode) (x := x))
  rw [coordinateDerivative_eq_sum modes coefficients supported j x]
  fin_cases i <;> fin_cases j <;>
    norm_num [modes, coefficients, sineCoeff, xMode, yMode, diagonalMode,
      Finsupp.single_apply, indexedDerivativeCoeff, unitTorusDerivativePhase,
      UnitAddTorus.mFourier_neg, Complex.mul_re, Complex.mul_im, cosine, Matrix.vecCons_inj,
      Matrix.cons_val_two, hx, hy, hz]
  all_goals ring

theorem vorticity_eq (x : T3) : fullVorticity coefficients x =
    (2 * Real.pi) • WithLp.toLp 2
      ![cosine diagonalMode x, -(cosine xMode x + cosine diagonalMode x), cosine yMode x] := by
  ext i
  fin_cases i <;>
    simp [fullVorticity, spatialCurl, complexRealPartEuclideanCLM_apply,
      complexRealPartEuclidean, coordinateDerivative_eq, Complex.sub_re]
  all_goals ring

theorem strain_vorticity_eq (x : T3) :
    fullStrainOperator coefficients x (fullVorticity coefficients x) =
      (2 * Real.pi) ^ 2 • WithLp.toLp 2
        ![cosine yMode x * (cosine xMode x + cosine diagonalMode x), 0, 0] := by
  rw [vorticity_eq]
  ext i
  rw [fullStrainOperator, realMatrixOperator_apply]
  fin_cases i <;>
    norm_num [PancakeLocalStrainEquation.spatialStrain,
      PancakeFilteredStrainDynamics.symmetrize, spatialVelocityGradient,
      coordinateDerivative_eq, Fin.sum_univ_three, Complex.mul_re,
      Matrix.cons_val_two] <;> ring

theorem stretchingDensity_eq (x : T3) : stretchingDensity coefficients x =
    (2 * Real.pi) ^ 9 *
      ((cosine xMode x + cosine diagonalMode x) ^ 2 +
        cosine diagonalMode x ^ 2 + cosine yMode x ^ 2) ^ 3 *
      (cosine yMode x * (cosine xMode x + cosine diagonalMode x) * cosine diagonalMode x) := by
  rw [stretchingDensity, strain_vorticity_eq, show ‖fullVorticity coefficients x‖ ^ 6 =
      (‖fullVorticity coefficients x‖ ^ 2) ^ 3 by ring,
    EuclideanSpace.real_norm_sq_eq, vorticity_eq]
  norm_num [PiLp.inner_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  ring

end Mettapedia.FluidDynamics.NavierStokes.PositiveStretchingSnapshot
