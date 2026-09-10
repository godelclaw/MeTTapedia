import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPressureEllipticCommutator
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ComplexTransverseMatrix

/-!
# First and second coordinate factors in elliptic localization

Coordinate multipliers use integer frequencies, not physical derivatives:
each physical unit-torus derivative additionally contributes `2π i`.
The exact identities below retain these normalizations and all outputs.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierEllipticProductCoefficients

open scoped BigOperators RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open FourierPressureCommutator FourierPressureTraceSymbol FourierPressureEllipticCommutator
open ComplexTransverseMatrix PancakeAnisotropyDepletion
open Mettapedia.Analysis.FiniteMultiplierLocalization

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def coordinateMultiplier (c : Wavevector → ℂ) (j : Fin 3) (q : Wavevector) : ℂ := (q j : ℂ) * c q

def secondCoordinateMultiplier (c : Wavevector → ℂ) (i j : Fin 3) (q : Wavevector) : ℂ :=
  (q i : ℂ) * (q j : ℂ) * c q

def laplaceMultiplier (c : Wavevector → ℂ) (q : Wavevector) : ℂ :=
  (‖realFrequency q‖ ^ 2 : ℝ) * c q

theorem laplaceMultiplier_eq_sum (c : Wavevector → ℂ) (q : Wavevector) :
    laplaceMultiplier c q = ∑ j : Fin 3, secondCoordinateMultiplier c j j q := by
  simp only [laplaceMultiplier, secondCoordinateMultiplier, EuclideanSpace.norm_sq_eq,
    realFrequency, Real.norm_eq_abs, sq_abs, Complex.ofReal_sum,
    Complex.ofReal_pow, Complex.ofReal_intCast, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

def tensorKernel (p k : Wavevector) (i j : Fin 3) : ℂ :=
  (p i : ℂ) * (k j : ℂ) + (k i : ℂ) * (p j : ℂ) + (p i : ℂ) * (p j : ℂ)

def tensorCoefficient (P K : Finset Wavevector) (c phi : Wavevector → ℂ)
    (q : Wavevector) (i j : Fin 3) : ℂ :=
  ∑ pk ∈ P ×ˢ K with pk.1 + pk.2 = q, c pk.1 * phi pk.2 * tensorKernel pk.1 pk.2 i j

theorem scalarCoefficient_eq_products (P K : Finset Wavevector) (c phi : Wavevector → ℂ)
    (q : Wavevector) :
    ellipticScalarCoefficient P K c phi q =
      2 * (∑ j : Fin 3, scalarConvolution P K (coordinateMultiplier c j) (coordinateMultiplier phi j) q) +
        scalarConvolution P K (laplaceMultiplier c) phi q := by
  have hp (p k : Wavevector) : c p * phi k * (ellipticScalarKernel p k : ℝ) =
      2 * (∑ j : Fin 3, coordinateMultiplier c j p * coordinateMultiplier phi j k) +
        laplaceMultiplier c p * phi k := by
    simp only [ellipticScalarKernel, coordinateMultiplier, laplaceMultiplier,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, realFrequency,
      star_trivial, Fin.sum_univ_three, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_intCast]
    ring
  unfold ellipticScalarCoefficient
  simp_rw [hp]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
  rfl

theorem tensorCoefficient_eq_products (P K : Finset Wavevector) (c phi : Wavevector → ℂ)
    (q : Wavevector) (i j : Fin 3) :
    tensorCoefficient P K c phi q i j =
      scalarConvolution P K (coordinateMultiplier c i) (coordinateMultiplier phi j) q +
        scalarConvolution P K (coordinateMultiplier c j) (coordinateMultiplier phi i) q +
        scalarConvolution P K (secondCoordinateMultiplier c i j) phi q := by
  unfold tensorCoefficient scalarConvolution
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro pk _
  simp only [tensorKernel, coordinateMultiplier, secondCoordinateMultiplier]
  ring

theorem complexifyVector_kernel_eq (e : R3) (p k : Wavevector) :
    complexifyVector (ellipticVectorKernel e p k) = transverse e (matrixAction (tensorKernel p k) e) := by
  ext i
  simp only [ellipticVectorKernel, lineRemainder, complexifyVector, coefficientVec,
    PiLp.toLp_apply, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    realFrequency, matrixAction, transverse, pairing, Fin.sum_univ_three,
    Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_intCast,
    tensorKernel]
  ring

theorem matrixAction_tensorCoefficient (P K : Finset Wavevector) (c phi : Wavevector → ℂ)
    (e : R3) (q : Wavevector) :
    matrixAction (tensorCoefficient P K c phi q) e =
      ∑ pk ∈ P ×ˢ K with pk.1 + pk.2 = q,
        (c pk.1 * phi pk.2) • matrixAction (tensorKernel pk.1 pk.2) e := by
  ext i
  simp only [matrixAction, tensorCoefficient, coefficientVec, PiLp.toLp_apply,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro pk _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem vectorCoefficient_eq_tensor (P K : Finset Wavevector) (c phi : Wavevector → ℂ)
    (e : R3) (q : Wavevector) :
    ellipticVectorCoefficient P K c phi e q = transverse e (matrixAction (tensorCoefficient P K c phi q) e) := by
  rw [matrixAction_tensorCoefficient, transverse_sum]
  unfold ellipticVectorCoefficient
  apply Finset.sum_congr rfl
  intro pk _
  rw [transverse_smul, complexifyVector_kernel_eq]

theorem norm_vectorCoefficient_sq_le_tensor (P K : Finset Wavevector) (c phi : Wavevector → ℂ)
    (e : R3) (he : ‖e‖ = 1) (q : Wavevector) :
    ‖ellipticVectorCoefficient P K c phi e q‖ ^ 2 ≤
      4 * (∑ i : Fin 3, ∑ j : Fin 3, ‖tensorCoefficient P K c phi q i j‖ ^ 2) := by
  rw [vectorCoefficient_eq_tensor]
  have hn := pow_le_pow_left₀ (norm_nonneg _)
    (norm_transverse_le e (matrixAction (tensorCoefficient P K c phi q) e) he) 2
  have hm := norm_matrixAction_sq_le (tensorCoefficient P K c phi q) e he
  nlinarith only [hn, hm]

end Mettapedia.FluidDynamics.NavierStokes.FourierEllipticProductCoefficients
