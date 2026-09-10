import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.InfiniteFilteredEquation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpatialStrainEvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalMaterialTrajectories

/-!
# Filtered strain along the actual material flow

The filtered velocity is extracted from the constructed infinite solution.
Its strain evolves along the full velocity's material path, not an assumed
closed evolution of a finite truncation. The remainder retains two separate
effects: the all-input, pressure-projected subgrid force, and transport by
the difference between the actual velocity and the resolved velocity.

These identities provide the source terms for a filtered spectral-defect
estimate. They do not bound their scale-critical time integrals.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalFilteredStrain

open scoped BigOperators ComplexConjugate Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFilteredStrainDynamics
open PancakeFourierPressureStrain PancakeFourierMaterialPaths PancakeSpatialStrainEvolution
open PancakeFrequencyProjectorCommutator PancakeGalerkinKineticEnergy
open PancakeLocalInfiniteVelocity PancakeLocalMaterialTrajectories InfiniteFilteredEquation
open PancakeBlockReality
open PancakePeriodicVorticityEquation

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem strainCoeff_add (u v : FourierVelocity) (q : Wavevector) :
    strainCoeff (u + v) q = strainCoeff u q + strainCoeff v q := by
  ext i j
  simp [strainCoeff, gradientCoeff]
  ring

/-- The finite nonlinear algebra for an unfiltered, resolved velocity. -/
theorem strain_velocityRHS_material (modes : Finset Wavevector) (u : FourierVelocity)
    (nu : ℝ) (q : Wavevector) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u k) = 0) :
    strainCoeff (velocityRHS modes u nu) q + strainAdvectionCoeff modes u q =
      -strainSpinSquareCoeff modes u q - pressureHessianCoeff modes u q +
        viscousStrainCoeff nu u q := by
  have h := strain_filtered_velocityRHS_material (fun _ ↦ 1) modes u nu q hk hu
  have hf (v : FourierVelocity) : filteredVelocity (fun _ ↦ 1) v = v := by
    funext k
    exact one_smul ℂ (v k)
  have hz : subgridStrainCoeff (fun _ ↦ 1) modes u q = 0 := by
    ext i j
    simp [subgridStrainCoeff, subgridGradient,
      PancakeFilteredStrainDynamics.subgridConvection, gradientCoeff, symmetrize]
  rw [hf, hf, hz] at h
  simpa only [one_smul, add_zero] using h

/-- Resolved pressure and viscosity, plus the symmetric gradient of the
all-input subgrid force (including its pressure correction). -/
def forcingCoeff (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (nu : ℝ) (q : Wavevector) : MatrixCoefficient :=
  -pressureHessianCoeff modes (filteredVelocity chi u) q +
    viscousStrainCoeff nu (filteredVelocity chi u) q +
    strainCoeff (subgridForce chi u) q

/-- The strain transported by the velocity discarded by the static filter.
The velocity argument is real and may be the actual lifted velocity. -/
def transportCorrectionCoeff (modes : Finset Wavevector) (v : FourierVelocity)
    (V : X3) (x : T3) (q : Wavevector) : MatrixCoefficient :=
  (unitTorusDerivativePhase *
    (realModeDot q (V - fun i ↦ (finiteFourierReconstruction modes v x i).re) : ℂ)) •
      strainCoeff v q

theorem material_advection_add_correction (modes outputs : Finset Wavevector)
    (v : FourierVelocity) (V : X3) (x : T3) (hsub : modes ⊆ outputs)
    (hout : ∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ q, v (-q) = coefficientConjugate (v q))
    (hv : ∀ q, q ∉ modes → strainCoeff v q = 0) :
    matrixReconstruction outputs
      (fun q ↦ (unitTorusDerivativePhase * (realModeDot q V : ℂ)) • strainCoeff v q) x =
      matrixReconstruction outputs (strainAdvectionCoeff modes v) x +
        matrixReconstruction outputs (transportCorrectionCoeff modes v V x) x := by
  have he : (fun q ↦ (unitTorusDerivativePhase * (realModeDot q V : ℂ)) • strainCoeff v q) =
      fun q ↦ (unitTorusDerivativePhase *
        (realModeDot q (fun i ↦ (finiteFourierReconstruction modes v x i).re) : ℂ)) •
          strainCoeff v q + transportCorrectionCoeff modes v V x q := by
    funext q
    have hd : realModeDot q (V - fun i ↦ (finiteFourierReconstruction modes v x i).re) =
        realModeDot q V - realModeDot q (fun i ↦ (finiteFourierReconstruction modes v x i).re) := by
      simp [realModeDot, mul_sub, Finset.sum_sub_distrib]
    simp only [transportCorrectionCoeff, hd, Complex.ofReal_sub, mul_sub, sub_smul]
    abel
  rw [he, matrixReconstruction_add,
    matrixReconstruction_material_advection modes outputs v x hsub hout hs hr hv]

variable {nu T B : ℝ} {u₀ : FourierVelocity}

theorem hasDerivAt_strainCoeff (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ k, ‖chi k‖ ≤ C)
    (modes : Finset Wavevector) (hcut : ∀ k, k ∉ modes → chi k = 0)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (q : Wavevector) (i j : Fin 3) :
    HasDerivAt (fun τ ↦ strainCoeff (filteredVelocity chi (s.coefficients τ)) q i j)
      ((-strainSpinSquareCoeff modes (filteredVelocity chi (s.coefficients t)) q +
        forcingCoeff chi modes (s.coefficients t) nu q -
        strainAdvectionCoeff modes (filteredVelocity chi (s.coefficients t)) q) i j) t := by
  let v := fun τ ↦ filteredVelocity chi (s.coefficients τ)
  let dv := velocityRHS modes (v t) nu + subgridForce chi (s.coefficients t)
  have hd (l : Fin 3) : HasDerivAt (fun τ ↦ v τ q l) (dv q l) t :=
    hasDerivAt_filtered_coefficients_finite s chi C hchi modes hcut hk t ht q l
  have h := ((hasDerivAt_gradientCoeff v dv q i j t (hd i)).add
    (hasDerivAt_gradientCoeff v dv q j i t (hd j))).const_mul (1 / 2 : ℂ)
  change HasDerivAt _ (strainCoeff dv q i j) t at h
  apply h.congr_deriv
  have he := strain_velocityRHS_material modes (v t) nu q hk
    (fun k _ ↦ filteredVelocity_transverse chi _ k (s.transverse t k))
  have hdv : strainCoeff dv q =
      -strainSpinSquareCoeff modes (v t) q + forcingCoeff chi modes (s.coefficients t) nu q -
        strainAdvectionCoeff modes (v t) q := by
    dsimp only [dv]
    rw [strainCoeff_add, eq_sub_of_add_eq he]
    dsimp only [forcingCoeff, v]
    abel
  exact congrFun (congrFun hdv i) j

/-- Actual filtered strain evolution along a trajectory of the full local
solution. The transport difference is derived, not set to zero. -/
theorem hasDerivAt_strain_matrix_material
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ k, ‖chi k‖ ≤ C)
    (modes outputs : Finset Wavevector) (hcut : ∀ k, k ∉ modes → chi k = 0)
    (hchir : ∀ q, chi (-q) = conj (chi q))
    (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (X : ℝ → X3) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hX : HasDerivAt X (liftedVelocity s t (X t)) t) :
    HasDerivAt (fun τ ↦ matrixReconstruction outputs
      (strainCoeff (filteredVelocity chi (s.coefficients τ))) (torusPoint (X τ)))
      (-matrixReconstruction outputs
        (strainSpinSquareCoeff modes (filteredVelocity chi (s.coefficients t))) (torusPoint (X t)) +
        matrixReconstruction outputs (forcingCoeff chi modes (s.coefficients t) nu) (torusPoint (X t)) +
        matrixReconstruction outputs
          (transportCorrectionCoeff modes (filteredVelocity chi (s.coefficients t))
            (liftedVelocity s t (X t)) (torusPoint (X t))) (torusPoint (X t))) t := by
  let v := filteredVelocity chi (s.coefficients t)
  let x := torusPoint (X t)
  let rate : FourierMatrix := fun q ↦ -strainSpinSquareCoeff modes v q +
    forcingCoeff chi modes (s.coefficients t) nu q - strainAdvectionCoeff modes v q
  have h := hasDerivAt_matrixReconstruction_moving outputs
    (fun τ ↦ strainCoeff (filteredVelocity chi (s.coefficients τ))) rate X _ t
    (fun q _ i j ↦ hasDerivAt_strainCoeff s chi C hchi modes hcut hk t ht q i j)
    (hasDerivAt_pi.mp hX)
  apply h.congr_deriv
  rw [matrixReconstruction_add,
    material_advection_add_correction modes outputs v _ x hsub hout hs
      (filteredVelocity_conjugate chi _ hchir (s.reality t))
      (filtered_strain_zero_of_not_mem chi modes _ hcut)]
  dsimp only [rate]
  rw [matrixReconstruction_sub, matrixReconstruction_add, matrixReconstruction_neg]
  abel

/-- The self-adjoint, resolved strain evaluated on the actual material path. -/
def strainAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (X : ℝ → X3) (t : ℝ) :
    PancakeSpectralProjectorRegularity.SymmetricStrain :=
  spatialStrain modes (filteredVelocity chi (s.coefficients t)) (torusPoint (X t))

/-- All terms other than the negative resolved strain square. Pressure,
spin, viscosity, unresolved stress and unresolved transport remain explicit. -/
def remainderAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector) (X : ℝ → X3) (t : ℝ) :
    R3 →L[ℝ] R3 :=
  -(spatialSpin modes (filteredVelocity chi (s.coefficients t)) (torusPoint (X t)) *
    spatialSpin modes (filteredVelocity chi (s.coefficients t)) (torusPoint (X t))) +
    realMatrixOperator (matrixReconstruction outputs (forcingCoeff chi modes (s.coefficients t) nu)
      (torusPoint (X t))) +
    realMatrixOperator (matrixReconstruction outputs
      (transportCorrectionCoeff modes (filteredVelocity chi (s.coefficients t))
        (liftedVelocity s t (X t)) (torusPoint (X t))) (torusPoint (X t)))

/-- The real operator equation needed by the collision-safe spectral-defect
calculus. It follows from the actual infinite solution and material path. -/
theorem hasDerivAt_strainAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ k, ‖chi k‖ ≤ C)
    (modes outputs : Finset Wavevector) (hcut : ∀ k, k ∉ modes → chi k = 0)
    (hchir : ∀ q, chi (-q) = conj (chi q))
    (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (X : ℝ → X3) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hX : HasDerivAt X (liftedVelocity s t (X t)) t) :
    HasDerivAt (fun τ ↦ (strainAlong s chi modes X τ).1)
      (-(strainAlong s chi modes X t).1 * (strainAlong s chi modes X t).1 +
        remainderAlong s chi modes outputs X t) t := by
  have h := hasDerivAt_realMatrixOperator _ _ t
    (hasDerivAt_strain_matrix_material s chi C hchi modes outputs hcut hchir
      hsub hout hs hk X t ht hX)
  have he : (fun τ ↦ realMatrixOperator (matrixReconstruction outputs
      (strainCoeff (filteredVelocity chi (s.coefficients τ))) (torusPoint (X τ)))) =
      fun τ ↦ (strainAlong s chi modes X τ).1 := by
    funext τ
    change realMatrixOperator _ = realMatrixOperator _
    rw [matrixReconstruction_subset modes outputs _ _ hsub
      (filtered_strain_zero_of_not_mem chi modes _ hcut)]
  rw [he] at h
  apply h.congr_deriv
  rw [realMatrixOperator_add, realMatrixOperator_add, realMatrixOperator_neg,
    realMatrixOperator_strainSpinSquare modes outputs _ _ hs
      (filteredVelocity_conjugate chi _ hchir (s.reality t)) hout]
  dsimp only [strainAlong, remainderAlong]
  ext v
  simp only [add_apply, neg_apply, mul_apply_eq_comp]
  abel_nf

end Mettapedia.FluidDynamics.NavierStokes.LocalFilteredStrain
