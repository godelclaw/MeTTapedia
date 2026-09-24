import Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierTriad
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeConeLatticeCount

/-!
# Coherent/misaligned splitting on the genuine periodic Fourier lattice

The pairwise cone calculation was first proved in an exact rational
three-vector model.  This module connects its coherent direction to the
existing complex Fourier carrier for the unit three-torus.

For every nonzero lattice frequency `k`, let `p(k) = P_k e₀`, using the actual
complex Leray symbol `PeriodicFourierTriad.lerayMode`.  An arbitrary complex
Fourier coefficient `w(k)` has the exact split

`w = (⟪p,w⟫ / ⟪p,p⟫) p + w_mis`.

Inside a square-dyadic pancake cone with `N ≥ 2`, `p` is nonzero, so the
denominator is nonzero.  The remainder is Hermitian-orthogonal to `p`; and if
the original coefficient is divergence-free, both summands remain
divergence-free.  Thus the coherent/misaligned split is now constructed for
arbitrary complex mode amplitudes on `ℤ³`, rather than postulated as an
abstract pair of scalar functionals.

The remaining field-level work is to sum this exact mode split through the
Littlewood--Paley projectors and prove the required uniform multiplier bounds.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakePeriodicCoherentSplit

open scoped BigOperators ComplexConjugate Matrix
open PeriodicFourierTriad
open PancakeConeDirectionDichotomy
open PancakeCoherentPairEstimate
open PancakeCoherentWeightedTransfer
open PancakeConeLatticeCount

/-- Convert the right-associated integer triple used by the pancake count to
the repository's genuine periodic wavevector. -/
def latticeToWavevector (k : Lattice3) : Wavevector :=
  ![k.1, k.2.1, k.2.2]

/-- Convert an exact rational three-vector to a complex Fourier coefficient. -/
def ratVecToCoefficient (v : Vec3) : VelocityCoefficient :=
  ![(v.1 : ℂ), (v.2.1 : ℂ), (v.2.2 : ℂ)]

/-- The fixed in-plane reference direction. -/
def referenceCoefficient : VelocityCoefficient :=
  ![(1 : ℂ), 0, 0]

/-- The actual periodic Leray projection `P_k e₀`. -/
def periodicCoherentMode (k : Wavevector) : VelocityCoefficient :=
  lerayMode k referenceCoefficient

/-- Hermitian squared length of the coherent direction. -/
def coherentDenominator (k : Wavevector) : ℂ :=
  coefficientHermitian (periodicCoherentMode k) (periodicCoherentMode k)

/-- Complex scalar coefficient of the coherent rank-one projection. -/
def coherentScalar (k : Wavevector) (w : VelocityCoefficient) : ℂ :=
  coefficientHermitian (periodicCoherentMode k) w / coherentDenominator k

/-- Coherent part of an arbitrary complex Fourier coefficient. -/
def coherentComponent (k : Wavevector) (w : VelocityCoefficient) :
    VelocityCoefficient :=
  coherentScalar k w • periodicCoherentMode k

/-- Orthogonal misalignment remainder. -/
def misalignmentComponent (k : Wavevector) (w : VelocityCoefficient) :
    VelocityCoefficient :=
  w - coherentComponent k w

theorem modeSquare_latticeToWavevector (k : Lattice3) :
    modeSquare (latticeToWavevector k) = (latticeNormSq k : ℂ) := by
  simp only [modeSquare, latticeToWavevector, latticeNormSq,
    Fin.sum_univ_succ]
  push_cast
  ring

theorem modeSquare_latticeToWavevector_ne_zero {N : ℕ} {k : Lattice3}
    (hk : InSquarePancakeConeBall N k) :
    modeSquare (latticeToWavevector k) ≠ 0 := by
  rw [modeSquare_latticeToWavevector]
  exact_mod_cast (ne_of_gt hk.2.1)

/-- The complex periodic Leray direction is exactly the cast of the rational
coherent direction used in the pairwise estimate. -/
theorem periodicCoherentMode_latticeToWavevector {N : ℕ} {k : Lattice3}
    (hk : InSquarePancakeConeBall N k) :
    periodicCoherentMode (latticeToWavevector k) =
      ratVecToCoefficient (coherentP (toRatVec k)) := by
  have hsq := modeSquare_latticeToWavevector_ne_zero hk
  have hdenC :
      (k.1 : ℂ) ^ 2 + (k.2.1 : ℂ) ^ 2 + (k.2.2 : ℂ) ^ 2 ≠ 0 := by
    have hdenZ : latticeNormSq k ≠ 0 := ne_of_gt hk.2.1
    exact_mod_cast hdenZ
  rw [periodicCoherentMode, lerayMode, dif_neg hsq]
  ext i
  fin_cases i <;>
    simp only [referenceCoefficient, latticeToWavevector, ratVecToCoefficient,
      coherentP, coherentW, toRatVec, modeDot, modeSquare, normSq, dot,
      PancakeConeDirectionDichotomy.smul,
      PancakeConeDirectionDichotomy.add, ex, Fin.sum_univ_three] <;>
    push_cast <;>
    field_simp [hdenC, normSq_toRatVec_ne_zero hk] <;>
    ring

theorem coefficientHermitian_ratVecToCoefficient_self (v : Vec3) :
    coefficientHermitian (ratVecToCoefficient v) (ratVecToCoefficient v) =
      (normSq v : ℂ) := by
  obtain ⟨x, y, z⟩ := v
  simp only [coefficientHermitian, ratVecToCoefficient, normSq, dot,
    Fin.sum_univ_three]
  push_cast
  simp only [map_ratCast]

theorem coherentDenominator_latticeToWavevector {N : ℕ} {k : Lattice3}
    (hk : InSquarePancakeConeBall N k) :
    coherentDenominator (latticeToWavevector k) =
      (normSq (coherentP (toRatVec k)) : ℂ) := by
  unfold coherentDenominator
  rw [periodicCoherentMode_latticeToWavevector hk]
  exact coefficientHermitian_ratVecToCoefficient_self _

/-- On every square-dyadic pancake cone with aperture at most `1/2`, the
coherent rank-one projection has a nonzero denominator. -/
theorem coherentDenominator_ne_zero {N : ℕ} (hN : 2 ≤ N) {k : Lattice3}
    (hk : InSquarePancakeConeBall N k) :
    coherentDenominator (latticeToWavevector k) ≠ 0 := by
  rw [coherentDenominator_latticeToWavevector hk]
  exact_mod_cast ne_of_gt (normSq_coherentP_pos
    (normSq_toRatVec_ne_zero hk) (toRatVec_mem_cone hk)
    (inv_nat_sq_le_quarter hN))

theorem coefficientHermitian_sub_right (u v w : VelocityCoefficient) :
    coefficientHermitian u (v - w) =
      coefficientHermitian u v - coefficientHermitian u w := by
  simp only [coefficientHermitian, Pi.sub_apply, mul_sub,
    Finset.sum_sub_distrib]

theorem coefficientHermitian_smul_right
    (u v : VelocityCoefficient) (c : ℂ) :
    coefficientHermitian u (c • v) = c * coefficientHermitian u v := by
  simp only [coefficientHermitian, Pi.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem modeDot_sub (k : Wavevector) (u v : VelocityCoefficient) :
    modeDot k (u - v) = modeDot k u - modeDot k v := by
  simp only [modeDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem modeDot_smul (k : Wavevector) (c : ℂ)
    (v : VelocityCoefficient) :
    modeDot k (c • v) = c * modeDot k v := by
  simp only [modeDot, Pi.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact modewise coherent/misaligned decomposition. -/
theorem coherentComponent_add_misalignmentComponent
    (k : Wavevector) (w : VelocityCoefficient) :
    coherentComponent k w + misalignmentComponent k w = w := by
  simp only [misalignmentComponent]
  abel

/-- The remainder is Hermitian-orthogonal to the coherent direction whenever
the coherent projection is nondegenerate. -/
theorem coefficientHermitian_periodicCoherentMode_misalignment_eq_zero
    {k : Wavevector} (w : VelocityCoefficient)
    (hden : coherentDenominator k ≠ 0) :
    coefficientHermitian (periodicCoherentMode k)
      (misalignmentComponent k w) = 0 := by
  rw [misalignmentComponent, coefficientHermitian_sub_right,
    coherentComponent, coefficientHermitian_smul_right]
  unfold coherentScalar
  change coefficientHermitian (periodicCoherentMode k) w -
    (coefficientHermitian (periodicCoherentMode k) w / coherentDenominator k) *
      coherentDenominator k = 0
  rw [div_mul_cancel₀ _ hden, sub_self]

/-- The coherent summand is divergence-free at a nonzero lattice mode. -/
theorem modeDot_coherentComponent_eq_zero {k : Wavevector}
    (w : VelocityCoefficient) (hk : modeSquare k ≠ 0) :
    modeDot k (coherentComponent k w) = 0 := by
  rw [coherentComponent, modeDot_smul, periodicCoherentMode,
    modeDot_lerayMode_eq_zero k referenceCoefficient hk, mul_zero]

/-- A divergence-free coefficient has a divergence-free misalignment
remainder. -/
theorem modeDot_misalignmentComponent_eq_zero {k : Wavevector}
    (w : VelocityCoefficient) (hk : modeSquare k ≠ 0)
    (hw : modeDot k w = 0) :
    modeDot k (misalignmentComponent k w) = 0 := by
  rw [misalignmentComponent, modeDot_sub, hw,
    modeDot_coherentComponent_eq_zero w hk, sub_zero]

/-- If a mode was already coherent, the constructed misalignment remainder
vanishes exactly. -/
theorem misalignmentComponent_smul_periodicCoherentMode_eq_zero
    {k : Wavevector} (a : ℂ) (hden : coherentDenominator k ≠ 0) :
    misalignmentComponent k (a • periodicCoherentMode k) = 0 := by
  have hs : coherentScalar k (a • periodicCoherentMode k) = a := by
    rw [coherentScalar, coefficientHermitian_smul_right]
    change a * coherentDenominator k / coherentDenominator k = a
    exact mul_div_cancel_right₀ a hden
  rw [misalignmentComponent, coherentComponent, hs, sub_self]

/-! ## Exact finite Fourier fields -/

/-- Coherent coefficients of an arbitrary periodic Fourier field. -/
def coherentFourierField (omega : FourierVelocity) : FourierVelocity :=
  fun k => coherentComponent k (omega k)

/-- Misalignment coefficients of an arbitrary periodic Fourier field. -/
def misalignmentFourierField (omega : FourierVelocity) : FourierVelocity :=
  fun k => misalignmentComponent k (omega k)

/-- The coefficient-level split is an exact equality of full Fourier fields. -/
theorem coherentFourierField_add_misalignmentFourierField
    (omega : FourierVelocity) :
    coherentFourierField omega + misalignmentFourierField omega = omega := by
  funext k
  exact coherentComponent_add_misalignmentComponent k (omega k)

/-- Exact trigonometric-polynomial reconstruction on the unit three-torus. -/
def finiteFourierReconstruction (s : Finset Wavevector)
    (omega : FourierVelocity) (x : UnitAddTorus (Fin 3)) :
    VelocityCoefficient :=
  ∑ k ∈ s, UnitAddTorus.mFourier k x • omega k

/-- A finite Fourier reconstruction is continuous. -/
theorem continuous_finiteFourierReconstruction (s : Finset Wavevector)
    (omega : FourierVelocity) :
    Continuous (finiteFourierReconstruction s omega) := by
  unfold finiteFourierReconstruction
  fun_prop

/-- Reconstruction commutes exactly with the constructed
coherent/misaligned split. -/
theorem finiteFourierReconstruction_split (s : Finset Wavevector)
    (omega : FourierVelocity) (x : UnitAddTorus (Fin 3)) :
    finiteFourierReconstruction s omega x =
      finiteFourierReconstruction s (coherentFourierField omega) x +
        finiteFourierReconstruction s (misalignmentFourierField omega) x := by
  unfold finiteFourierReconstruction coherentFourierField
    misalignmentFourierField
  simp_rw [← Finset.sum_add_distrib, ← smul_add,
    coherentComponent_add_misalignmentComponent]

/-- Coherent coefficients inherit incompressibility mode by mode. -/
theorem coherentFourierField_divergenceFree
    (omega : FourierVelocity) {k : Wavevector} (hk : modeSquare k ≠ 0) :
    modeDot k (coherentFourierField omega k) = 0 :=
  modeDot_coherentComponent_eq_zero (omega k) hk

/-- Misalignment coefficients inherit incompressibility mode by mode. -/
theorem misalignmentFourierField_divergenceFree
    (omega : FourierVelocity) {k : Wavevector} (hk : modeSquare k ≠ 0)
    (homega : modeDot k (omega k) = 0) :
    modeDot k (misalignmentFourierField omega k) = 0 :=
  modeDot_misalignmentComponent_eq_zero (omega k) hk homega

/-- The norm of a finite trigonometric polynomial is bounded pointwise by
the `ℓ¹` mass of its Fourier coefficients. -/
theorem norm_finiteFourierReconstruction_le (s : Finset Wavevector)
    (omega : FourierVelocity) (x : UnitAddTorus (Fin 3)) :
    ‖finiteFourierReconstruction s omega x‖ ≤ ∑ k ∈ s, ‖omega k‖ := by
  unfold finiteFourierReconstruction
  calc
    ‖∑ k ∈ s, UnitAddTorus.mFourier k x • omega k‖
      ≤ ∑ k ∈ s, ‖UnitAddTorus.mFourier k x • omega k‖ :=
        norm_sum_le _ _
    _ = ∑ k ∈ s, ‖omega k‖ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [norm_smul]
      simp only [UnitAddTorus.mFourier, fourier_apply, ContinuousMap.coe_mk, norm_prod,
        Circle.norm_coe, Finset.prod_const_one, one_mul]

end PancakePeriodicCoherentSplit
end NavierStokes
end FluidDynamics
end Mettapedia
