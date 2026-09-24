import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFourierPressureStrain

/-!
# The exact filtered velocity-gradient equation

Filtering convection creates an explicit interaction coefficient
`chi(k+l) - chi(k) chi(l)`. Its gradient is retained in the material
equation. No filter commutation with a nonlinear product is assumed.
The filter here is static; a time-dependent filter has an additional
time-derivative term and is not covered by these statements.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeFilteredStrainDynamics

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeGalerkinKineticEnergy
open PancakeFourierPressureStrain PancakeFrequencyProjectorCommutator

def filteredVelocity (chi : Wavevector → ℂ) (u : FourierVelocity) : FourierVelocity :=
  fun q ↦ chi q • u q

/-- Divergence of the unresolved velocity-product stress, before its
physical derivative factor. All source pairs remain explicit. -/
def subgridConvection (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (q : Wavevector) : VelocityCoefficient :=
  ∑ k ∈ modes, ∑ l ∈ modes, if k + l = q then
    (chi q - chi k * chi l) • orderedConvection k l u else 0

def subgridGradient (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (q : Wavevector) : MatrixCoefficient :=
  gradientCoeff (fun p ↦ (-unitTorusDerivativePhase) • subgridConvection chi modes u p) q

theorem filteredVelocity_transverse (chi : Wavevector → ℂ) (u : FourierVelocity)
    (q : Wavevector) (hu : modeDot q (u q) = 0) :
    modeDot q (filteredVelocity chi u q) = 0 := by
  simp [filteredVelocity, modeDot_smul, hu]

theorem orderedConvection_filtered (chi : Wavevector → ℂ) (u : FourierVelocity)
    (k l : Wavevector) :
    orderedConvection k l (filteredVelocity chi u) =
      (chi k * chi l) • orderedConvection k l u := by
  simp only [orderedConvection, filteredVelocity, modeDot_smul, smul_smul]
  congr 1
  ring

/-- The precise failure of nonlinear convection to commute with filtering. -/
theorem filtered_convection_eq (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (q : Wavevector) :
    chi q • convectionConvolution modes u q =
      convectionConvolution modes (filteredVelocity chi u) q + subgridConvection chi modes u q := by
  classical
  simp only [convectionConvolution, subgridConvection, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  by_cases hkl : k + l = q
  · simp only [hkl, ite_true, orderedConvection_filtered, ← add_smul]
    congr 1
    ring
  · simp [hkl]

theorem gradientCoeff_filtered (chi : Wavevector → ℂ) (u : FourierVelocity)
    (q : Wavevector) : gradientCoeff (filteredVelocity chi u) q = chi q • gradientCoeff u q := by
  ext i j
  simp [gradientCoeff, filteredVelocity]
  ring

theorem strainCoeff_filtered (chi : Wavevector → ℂ) (u : FourierVelocity) (q : Wavevector) :
    strainCoeff (filteredVelocity chi u) q = chi q • strainCoeff u q := by
  ext i j
  simp only [strainCoeff, gradientCoeff, filteredVelocity, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem viscousGradientCoeff_filtered (chi : Wavevector → ℂ) (u : FourierVelocity)
    (nu : ℝ) (q : Wavevector) :
    viscousGradientCoeff nu (filteredVelocity chi u) q = chi q • viscousGradientCoeff nu u q := by
  rw [viscousGradientCoeff, gradientCoeff_filtered, smul_comm]
  rfl

/-- Filtering the physical velocity RHS yields resolved convection,
filtered physical pressure, viscosity, and the explicit subgrid force. -/
theorem filtered_velocityRHS_eq (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (nu : ℝ) (q : Wavevector)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u k) = 0) :
    chi q • velocityRHS modes u nu q =
      (-unitTorusDerivativePhase) • convectionConvolution modes (filteredVelocity chi u) q -
        chi q • pressureGradientCoeff modes u q +
        unitTorusViscousVorticityCoeff nu (filteredVelocity chi u) q +
        (-unitTorusDerivativePhase) • subgridConvection chi modes u q := by
  rw [velocityRHS_eq_negativeConvection_pressure_viscosity modes u nu hk hu q,
    smul_add, smul_sub, smul_comm (chi q), filtered_convection_eq, smul_add]
  have hv : chi q • unitTorusViscousVorticityCoeff nu u q =
      unitTorusViscousVorticityCoeff nu (filteredVelocity chi u) q := by
    ext i
    simp [unitTorusViscousVorticityCoeff, filteredVelocity]
    ring
  rw [hv]
  abel

/-- The material gradient equation for a static filtered velocity, with
the actual pressure and the nonlinear filter error both retained. -/
theorem gradient_filtered_velocityRHS_material
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (nu : ℝ) (q : Wavevector)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u k) = 0) :
    gradientCoeff (filteredVelocity chi (velocityRHS modes u nu)) q +
        gradientAdvectionCoeff modes (filteredVelocity chi u) q =
      -gradientSquareCoeff modes (filteredVelocity chi u) q -
        chi q • pressureHessianCoeff modes u q +
        viscousGradientCoeff nu (filteredVelocity chi u) q + subgridGradient chi modes u q := by
  have hg : gradientCoeff (filteredVelocity chi (velocityRHS modes u nu)) q =
      gradientCoeff (fun p ↦ (-unitTorusDerivativePhase) •
        convectionConvolution modes (filteredVelocity chi u) p) q -
        chi q • pressureHessianCoeff modes u q +
        viscousGradientCoeff nu (filteredVelocity chi u) q + subgridGradient chi modes u q := by
    ext i j
    simp only [gradientCoeff, filteredVelocity]
    have hv := congrFun (filtered_velocityRHS_eq chi modes u nu q hk hu) i
    have hd := congrArg (fun z : ℂ ↦ unitTorusDerivativePhase * (q j : ℂ) * z) hv
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply,
      pressureGradientCoeff, pressureHessianCoeff, viscousGradientCoeff,
      unitTorusViscousVorticityCoeff, subgridGradient, gradientCoeff,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, mul_add, mul_sub,
      mul_assoc, mul_left_comm, mul_comm, pow_two] using hd
  rw [hg]
  have he := gradient_negativeConvection_add_advection modes (filteredVelocity chi u) q
  calc
    _ = (gradientCoeff (fun p ↦ (-unitTorusDerivativePhase) •
        convectionConvolution modes (filteredVelocity chi u) p) q +
        gradientAdvectionCoeff modes (filteredVelocity chi u) q) -
        chi q • pressureHessianCoeff modes u q +
        viscousGradientCoeff nu (filteredVelocity chi u) q + subgridGradient chi modes u q := by abel
    _ = _ := by rw [he]

/-- Coefficient evolution is derived from the original velocity ODE,
not supplied as a second filtered equation. -/
theorem hasDerivAt_filtered_gradientCoeff
    (chi : Wavevector → ℂ) (u : ℝ → FourierVelocity) (du : FourierVelocity)
    (q : Wavevector) (i j : Fin 3) (t : ℝ)
    (hd : HasDerivAt (fun tau ↦ u tau q i) (du q i) t) :
    HasDerivAt (fun tau ↦ gradientCoeff (filteredVelocity chi (u tau)) q i j)
      (gradientCoeff (filteredVelocity chi du) q i j) t :=
  hasDerivAt_gradientCoeff (fun tau ↦ filteredVelocity chi (u tau))
    (filteredVelocity chi du) q i j t (hd.const_mul (chi q))

/-- The filtered gradient evolution, derived at each retained mode from
the original physical velocity ODE. -/
theorem hasDerivAt_filtered_gradient_of_velocityRHS
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : ℝ → FourierVelocity)
    (nu t : ℝ) (q : Wavevector) (i j : Fin 3)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u t k) = 0)
    (hd : HasDerivAt (fun tau ↦ u tau q i) (velocityRHS modes (u t) nu q i) t) :
    HasDerivAt (fun tau ↦ gradientCoeff (filteredVelocity chi (u tau)) q i j)
      ((-gradientSquareCoeff modes (filteredVelocity chi (u t)) q -
        chi q • pressureHessianCoeff modes (u t) q +
        viscousGradientCoeff nu (filteredVelocity chi (u t)) q +
        subgridGradient chi modes (u t) q -
        gradientAdvectionCoeff modes (filteredVelocity chi (u t)) q) i j) t := by
  apply (hasDerivAt_filtered_gradientCoeff chi u (velocityRHS modes (u t) nu) q i j t hd).congr_deriv
  have h := congrFun (congrFun
    (gradient_filtered_velocityRHS_material chi modes (u t) nu q hk hu) i) j
  exact eq_sub_of_add_eq h

def strainSpinSquareCoeff (modes : Finset Wavevector) (u : FourierVelocity)
    (q : Wavevector) : MatrixCoefficient :=
  ∑ k ∈ modes, ∑ l ∈ modes, if k + l = q then
    strainCoeff u l * strainCoeff u k + spinCoeff u l * spinCoeff u k else 0

theorem symmetric_square_pair (u : FourierVelocity) (k l : Wavevector) :
    (1 / 2 : ℂ) • (gradientCoeff u l * gradientCoeff u k +
      (gradientCoeff u l).transpose * (gradientCoeff u k).transpose) =
        strainCoeff u l * strainCoeff u k + spinCoeff u l * spinCoeff u k := by
  ext i j
  simp only [strainCoeff, spinCoeff, Matrix.mul_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- Symmetrization cancels the strain-spin cross terms after exchanging
the ordered Fourier pair. This is the actual `S² + W²` source term. -/
theorem symmetric_gradientSquareCoeff (modes : Finset Wavevector)
    (u : FourierVelocity) (q : Wavevector) :
    (1 / 2 : ℂ) • (gradientSquareCoeff modes u q +
      (gradientSquareCoeff modes u q).transpose) = strainSpinSquareCoeff modes u q := by
  classical
  have ht : (gradientSquareCoeff modes u q).transpose =
      ∑ k ∈ modes, ∑ l ∈ modes, if k + l = q then
        (gradientCoeff u l).transpose * (gradientCoeff u k).transpose else 0 := by
    simp only [gradientSquareCoeff, Matrix.transpose_sum, apply_ite,
      Matrix.transpose_mul, Matrix.transpose_zero]
    rw [Finset.sum_comm]
    simp only [add_comm]
  rw [ht]
  simp only [gradientSquareCoeff, strainSpinSquareCoeff, ← Finset.sum_add_distrib,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  by_cases hkl : k + l = q
  · simp only [hkl, ite_true]
    exact symmetric_square_pair u k l
  · simp [hkl]

def symmetrize : MatrixCoefficient →ₗ[ℂ] MatrixCoefficient where
  toFun A := (1 / 2 : ℂ) • (A + A.transpose)
  map_add' A B := by ext i j; simp; ring
  map_smul' c A := by ext i j; simp; ring

theorem symmetrize_gradient (u : FourierVelocity) (q : Wavevector) :
    symmetrize (gradientCoeff u q) = strainCoeff u q := rfl

theorem symmetrize_pressureHessian (modes : Finset Wavevector)
    (u : FourierVelocity) (q : Wavevector) :
    symmetrize (pressureHessianCoeff modes u q) = pressureHessianCoeff modes u q := by
  change (1 / 2 : ℂ) • (_ + (pressureHessianCoeff modes u q).transpose) = _
  rw [pressureHessianCoeff_symmetric]
  ext i j
  simp
  ring

def strainAdvectionCoeff (modes : Finset Wavevector) (u : FourierVelocity)
    (q : Wavevector) : MatrixCoefficient := symmetrize (gradientAdvectionCoeff modes u q)

def viscousStrainCoeff (nu : ℝ) (u : FourierVelocity)
    (q : Wavevector) : MatrixCoefficient := symmetrize (viscousGradientCoeff nu u q)

def subgridStrainCoeff (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (q : Wavevector) : MatrixCoefficient :=
  symmetrize (subgridGradient chi modes u q)

/-- The strain equation now has the actual strain/spin squares, physical
pressure, viscosity and subgrid term; these are not abstract forcing inputs. -/
theorem strain_filtered_velocityRHS_material
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (nu : ℝ) (q : Wavevector)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u k) = 0) :
    strainCoeff (filteredVelocity chi (velocityRHS modes u nu)) q +
        strainAdvectionCoeff modes (filteredVelocity chi u) q =
      -strainSpinSquareCoeff modes (filteredVelocity chi u) q -
        chi q • pressureHessianCoeff modes u q +
        viscousStrainCoeff nu (filteredVelocity chi u) q + subgridStrainCoeff chi modes u q := by
  have h := congrArg symmetrize (gradient_filtered_velocityRHS_material chi modes u nu q hk hu)
  simp only [map_add, map_sub, map_neg, map_smul, symmetrize_gradient,
    symmetrize_pressureHessian] at h
  have hs : symmetrize (gradientSquareCoeff modes (filteredVelocity chi u) q) =
      strainSpinSquareCoeff modes (filteredVelocity chi u) q :=
    symmetric_gradientSquareCoeff modes (filteredVelocity chi u) q
  rw [hs] at h
  exact h

theorem hasDerivAt_filtered_strainCoeff
    (chi : Wavevector → ℂ) (u : ℝ → FourierVelocity) (du : FourierVelocity)
    (q : Wavevector) (i j : Fin 3) (t : ℝ)
    (hd : ∀ k : Fin 3, HasDerivAt (fun tau ↦ u tau q k) (du q k) t) :
    HasDerivAt (fun tau ↦ strainCoeff (filteredVelocity chi (u tau)) q i j)
      (strainCoeff (filteredVelocity chi du) q i j) t :=
  ((hasDerivAt_filtered_gradientCoeff chi u du q i j t (hd i)).add
    (hasDerivAt_filtered_gradientCoeff chi u du q j i t (hd j))).const_mul (1 / 2 : ℂ)

theorem hasDerivAt_filtered_strain_of_velocityRHS
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : ℝ → FourierVelocity)
    (nu t : ℝ) (q : Wavevector) (i j : Fin 3)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u t k) = 0)
    (hd : ∀ k : Fin 3,
      HasDerivAt (fun tau ↦ u tau q k) (velocityRHS modes (u t) nu q k) t) :
    HasDerivAt (fun tau ↦ strainCoeff (filteredVelocity chi (u tau)) q i j)
      ((-strainSpinSquareCoeff modes (filteredVelocity chi (u t)) q -
        chi q • pressureHessianCoeff modes (u t) q +
        viscousStrainCoeff nu (filteredVelocity chi (u t)) q +
        subgridStrainCoeff chi modes (u t) q -
        strainAdvectionCoeff modes (filteredVelocity chi (u t)) q) i j) t := by
  apply (hasDerivAt_filtered_strainCoeff chi u (velocityRHS modes (u t) nu) q i j t hd).congr_deriv
  exact eq_sub_of_add_eq (congrFun (congrFun
    (strain_filtered_velocityRHS_material chi modes (u t) nu q hk hu) i) j)

/-- A filter supported on the retained modes supplies an evolution at
every output frequency. No ODE for discarded velocity modes is assumed. -/
theorem hasDerivAt_filtered_strain_of_retained_velocityRHS
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : ℝ → FourierVelocity)
    (nu t : ℝ) (q : Wavevector) (i j : Fin 3)
    (hchi : ∀ p, p ∉ modes → chi p = 0)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u t k) = 0)
    (hd : ∀ p ∈ modes, ∀ k : Fin 3,
      HasDerivAt (fun tau ↦ u tau p k) (velocityRHS modes (u t) nu p k) t) :
    HasDerivAt (fun tau ↦ strainCoeff (filteredVelocity chi (u tau)) q i j)
      ((-strainSpinSquareCoeff modes (filteredVelocity chi (u t)) q -
        chi q • pressureHessianCoeff modes (u t) q +
        viscousStrainCoeff nu (filteredVelocity chi (u t)) q +
        subgridStrainCoeff chi modes (u t) q -
        strainAdvectionCoeff modes (filteredVelocity chi (u t)) q) i j) t := by
  have hdq (k : Fin 3) :
      HasDerivAt (fun tau ↦ filteredVelocity chi (u tau) q k)
        (filteredVelocity chi (velocityRHS modes (u t) nu) q k) t := by
    by_cases hq : q ∈ modes
    · exact (hd q hq k).const_mul (chi q)
    · simp only [filteredVelocity, hchi q hq, zero_smul, Pi.zero_apply]
      exact hasDerivAt_const t 0
  have h := ((hasDerivAt_gradientCoeff (fun tau ↦ filteredVelocity chi (u tau))
    (filteredVelocity chi (velocityRHS modes (u t) nu)) q i j t (hdq i)).add
      (hasDerivAt_gradientCoeff (fun tau ↦ filteredVelocity chi (u tau))
        (filteredVelocity chi (velocityRHS modes (u t) nu)) q j i t (hdq j))).const_mul (1 / 2 : ℂ)
  apply h.congr_deriv
  exact eq_sub_of_add_eq (congrFun (congrFun
    (strain_filtered_velocityRHS_material chi modes (u t) nu q hk hu) i) j)

end Mettapedia.FluidDynamics.NavierStokes.PancakeFilteredStrainDynamics
