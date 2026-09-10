import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.BottomSpectralProjectorPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smooth spectral invariants for three-dimensional strain

The cubic is expressed using traces of operator powers. Its coefficients
are smooth even at eigenvalue collisions. The bottom root is simple
whenever the bottom gap is positive, regardless of the top gap.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.StrainSpectralInvariants

open scoped RealInnerProductSpace ContDiff
open PancakeStrainSpectralFrame PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralClusterDichotomy.SymmetricStrain StrainEigenvalueContinuity

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3

def operatorTrace (A : Op) : ℝ := LinearMap.trace ℝ R3 A.toLinearMap

def secondInvariant (A : Op) : ℝ := (operatorTrace A ^ 2 - operatorTrace (A ^ 2)) / 2

def thirdInvariant (A : Op) : ℝ :=
  (operatorTrace A ^ 3 - 3 * operatorTrace A * operatorTrace (A ^ 2) +
    2 * operatorTrace (A ^ 3)) / 6

def characteristicValue (A : Op) (z : ℝ) : ℝ :=
  z ^ 3 - operatorTrace A * z ^ 2 + secondInvariant A * z - thirdInvariant A

theorem trace_pow_eq_sum_orderedEigenvalues (S : SymmetricStrain) (k : ℕ) :
    operatorTrace (S.1 ^ k) =
      topEigenvalue S ^ k + secondEigenvalue S ^ k + thirdEigenvalue S ^ k := by
  have he (i : Fin 3) : (S.1 ^ k) ((orderedEigenframe S.1 S.2).eigenbasis i) =
      (orderedEigenframe S.1 S.2).eigenvalue i ^ k • (orderedEigenframe S.1 S.2).eigenbasis i := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_apply_eq_comp, ih, map_smul,
        (orderedEigenframe S.1 S.2).apply_eigenbasis, smul_smul, pow_succ]
  rw [operatorTrace, LinearMap.trace_eq_sum_inner _ (orderedEigenframe S.1 S.2).eigenbasis]
  simp only [ContinuousLinearMap.coe_coe, he, real_inner_smul_right, real_inner_self_eq_norm_sq,
    (orderedEigenframe S.1 S.2).eigenbasis.norm_eq_one, one_pow, mul_one]
  simp [Fin.sum_univ_succ, topEigenvalue, secondEigenvalue, thirdEigenvalue, add_assoc]

theorem secondInvariant_eq (S : SymmetricStrain) :
    secondInvariant S.1 = topEigenvalue S * secondEigenvalue S +
      topEigenvalue S * thirdEigenvalue S + secondEigenvalue S * thirdEigenvalue S := by
  unfold secondInvariant
  rw [show operatorTrace S.1 = topEigenvalue S + secondEigenvalue S + thirdEigenvalue S from
    trace_eq_sum_orderedEigenvalues S, trace_pow_eq_sum_orderedEigenvalues]
  ring

theorem thirdInvariant_eq (S : SymmetricStrain) :
    thirdInvariant S.1 = topEigenvalue S * secondEigenvalue S * thirdEigenvalue S := by
  unfold thirdInvariant
  rw [show operatorTrace S.1 = topEigenvalue S + secondEigenvalue S + thirdEigenvalue S from
    trace_eq_sum_orderedEigenvalues S, trace_pow_eq_sum_orderedEigenvalues,
    trace_pow_eq_sum_orderedEigenvalues]
  ring

theorem characteristicValue_eq_prod (S : SymmetricStrain) (z : ℝ) :
    characteristicValue S.1 z =
      (z - topEigenvalue S) * (z - secondEigenvalue S) * (z - thirdEigenvalue S) := by
  rw [characteristicValue, secondInvariant_eq, thirdInvariant_eq,
    show operatorTrace S.1 = topEigenvalue S + secondEigenvalue S + thirdEigenvalue S from
      trace_eq_sum_orderedEigenvalues S]
  ring

theorem characteristicValue_bottom_eq_zero (S : SymmetricStrain) :
    characteristicValue S.1 (thirdEigenvalue S) = 0 := by
  rw [characteristicValue_eq_prod, sub_self, mul_zero]

theorem hasDerivAt_characteristicValue (A : Op) (z : ℝ) :
    HasDerivAt (characteristicValue A)
      (3 * z ^ 2 - 2 * operatorTrace A * z + secondInvariant A) z := by
  have h := ((((hasDerivAt_id z).pow 3).sub
    (((hasDerivAt_id z).pow 2).const_mul (operatorTrace A))).add
    ((hasDerivAt_id z).const_mul (secondInvariant A))).sub_const (thirdInvariant A)
  apply h.congr_deriv
  simp only [Nat.cast_ofNat, mul_one, id_eq]
  ring

theorem characteristicValue_bottom_derivative (S : SymmetricStrain) :
    3 * thirdEigenvalue S ^ 2 - 2 * operatorTrace S.1 * thirdEigenvalue S + secondInvariant S.1 =
      spectralWidth S * bottomGap S := by
  rw [secondInvariant_eq, show operatorTrace S.1 = topEigenvalue S + secondEigenvalue S + thirdEigenvalue S from
    trace_eq_sum_orderedEigenvalues S]
  unfold spectralWidth bottomGap
  ring

theorem contDiff_operatorTrace {n : ℕ∞ω} : ContDiff ℝ n operatorTrace := by
  change ContDiff ℝ n (fun A : Op ↦ operatorTrace A)
  simp_rw [operatorTrace, LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  apply ContDiff.sum
  intro i _
  exact contDiff_const.inner ℝ (contDiff_id.clm_apply contDiff_const)

theorem contDiff_secondInvariant {n : ℕ∞ω} : ContDiff ℝ n secondInvariant := by
  unfold secondInvariant
  have h := contDiff_operatorTrace (n := n)
  fun_prop

theorem contDiff_thirdInvariant {n : ℕ∞ω} : ContDiff ℝ n thirdInvariant := by
  unfold thirdInvariant
  have h := contDiff_operatorTrace (n := n)
  fun_prop

theorem contDiff_characteristicValue {n : ℕ∞ω} :
    ContDiff ℝ n (fun p : Op × ℝ ↦ characteristicValue p.1 p.2) := by
  unfold characteristicValue
  have ht := contDiff_operatorTrace (n := n)
  have h2 := contDiff_secondInvariant (n := n)
  have h3 := contDiff_thirdInvariant (n := n)
  fun_prop

end Mettapedia.FluidDynamics.NavierStokes.StrainSpectralInvariants
