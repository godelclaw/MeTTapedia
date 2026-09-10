import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalRetainedEnergyBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFiniteLocalizedEvolution

/-!
# Moving localization of the actual retained vorticity

The advection matrix uses the full velocity at every difference frequency
between retained modes. It is skew-adjoint even if the output set itself
is not conjugation symmetric. The actual retained equation keeps both
subgrid curl and the correction from resolved to full advection.

Moving spatial and directional localizers are explicit differentiable
operator paths. The energy identity retains their material rates and the
signed diffusion anticommutator. It neither constructs these localizers
nor assumes estimates for the resulting commutators.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalRetainedLocalizedEnergy

open scoped BigOperators ComplexConjugate RealInnerProductSpace
open Matrix
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicVorticityEquation
open PancakeFrequencyProjectorCommutator PancakeGalerkinKineticEnergy
open PancakeGalerkinVorticityBridge PancakeFiniteLocalizedEvolution
open PancakeLocalizedQuadraticEnergy PancakeLocalInfiniteVelocity
open LocalFilteredVorticity InfiniteFilteredEquation PancakeBlockReality

/-- Compression of positive advection by the full velocity. Only the two
test-field indices are restricted; the velocity source `q-l` is not. -/
def retainedAdvectionMatrix (modes : Finset Wavevector) (u : FourierVelocity) :
    Matrix (modes × Fin 3) (modes × Fin 3) ℂ :=
  fun q l ↦ if q.2 = l.2 then -InfiniteKineticCancellation.transportMatrix u q.1 l.1 else 0

def retainedAdvection (modes : Finset Wavevector) (u : FourierVelocity) :
    FiniteField modes →ₗ[ℂ] FiniteField modes :=
  (retainedAdvectionMatrix modes u).toEuclideanLin

/-- The entries are the Fourier coefficients of `u · ∇` acting on a
retained polynomial, including sources outside the retained set. -/
theorem retainedAdvection_apply (modes : Finset Wavevector) (u : FourierVelocity)
    (v : FiniteField modes) (q : modes) (i : Fin 3) :
    retainedAdvection modes u v (q, i) =
      ∑ l : modes, (unitTorusDerivativePhase * modeDot l (u (q-l))) * v (l, i) := by
  classical
  change (∑ l : modes × Fin 3, retainedAdvectionMatrix modes u (q, i) l * v l) = _
  rw [Fintype.sum_prod_type]
  simp only [retainedAdvectionMatrix, InfiniteKineticCancellation.transportMatrix,
    neg_mul, neg_neg, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem retainedAdvectionMatrix_skew (modes : Finset Wavevector) (u : FourierVelocity)
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) :
    (retainedAdvectionMatrix modes u).conjTranspose = -retainedAdvectionMatrix modes u := by
  ext q l
  change conj (if l.2 = q.2 then -InfiniteKineticCancellation.transportMatrix u l.1 q.1 else 0) =
    -(if q.2 = l.2 then -InfiniteKineticCancellation.transportMatrix u q.1 l.1 else 0)
  by_cases hi : q.2 = l.2
  · rw [if_pos hi, if_pos hi.symm, InfiniteKineticCancellation.transportMatrix_skew u hr hd q.1 l.1]
    simp
  · simp [hi, Ne.symm hi]

theorem retainedAdvection_skew_inner (modes : Finset Wavevector) (u : FourierVelocity)
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) (v w : FiniteField modes) :
    ⟪retainedAdvection modes u v, w⟫ = -⟪v, retainedAdvection modes u w⟫ := by
  have ha : (retainedAdvection modes u).adjoint = -retainedAdvection modes u := by
    rw [retainedAdvection, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      retainedAdvectionMatrix_skew modes u hr hd, map_neg]
  have h := (retainedAdvection modes u).adjoint_inner_right v w
  rw [ha] at h
  simpa only [finiteField_real_inner, LinearMap.neg_apply, inner_neg_right, Complex.neg_re]
    using (congrArg Complex.re h).symm

/-- The two corrections needed when transporting the retained curl by
the full velocity. Neither term is an external body force. -/
def feedbackField (modes : Finset Wavevector) (u : FourierVelocity) : FiniteField modes :=
  restrictCoefficients modes (subgridCurl (sharpFilter modes) u) +
    retainedAdvection modes u (restrictCoefficients modes (fourierCurl u)) -
    advection modes modes (fourierCurl u) (restrictCoefficients modes (fourierCurl u))

variable {nu T B : ℝ} {u₀ : FourierVelocity}

/-- Full advection, resolved stretching, true viscosity and explicit
feedback on the finite test-field space of the actual infinite solution. -/
theorem hasDerivAt_retainedField (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (modes : Finset Wavevector) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    let w := fun τ ↦ restrictCoefficients modes (fourierCurl (s.coefficients τ))
    HasDerivAt w
      (-retainedAdvection modes (s.coefficients t) (w t) +
        (restrictCoefficients modes (finiteUnitTorusStretchingCoeff modes modes
          (fourierCurl (s.coefficients t)) (fourierCurl (s.coefficients t))) +
          feedbackField modes (s.coefficients t)) + nu • laplacian modes (w t)) t := by
  dsimp only
  have h := hasDerivAt_restrictCoefficients modes (fun τ ↦ fourierCurl (s.coefficients τ))
    (finiteUnitTorusVorticityRHS modes modes (fourierCurl (s.coefficients t))
      (fourierCurl (s.coefficients t)) nu + subgridCurl (sharpFilter modes) (s.coefficients t)) t
    (fun q hq i ↦ hasDerivAt_retained_fourierCurl s modes hk t ht q hq i)
  apply h.congr_deriv
  have hadd (a b : FourierVelocity) : restrictCoefficients modes (a + b) =
      restrictCoefficients modes a + restrictCoefficients modes b := rfl
  rw [hadd, vorticityRHS_restrict]
  dsimp only [feedbackField]
  abel

/-- The moving-localized energy equation of the actual local solution.
The localizer and projector are not assumed stationary along the flow;
their full material rates and the unresolved work remain in the formula. -/
theorem hasDerivAt_materialLocalizedEnergy (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (modes : Finset Wavevector) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (C P : ℝ → FiniteField modes →L[ℝ] FiniteField modes)
    (Cdot Pdot : FiniteField modes →L[ℝ] FiniteField modes)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hC : HasDerivAt C Cdot t) (hP : HasDerivAt P Pdot t) (hPs : IsSelfAdjoint (P t)) :
    let w := fun τ ↦ restrictCoefficients modes (fourierCurl (s.coefficients τ))
    let A := sandwich (C t) (P t)
    let B := retainedAdvection modes (s.coefficients t)
    let D := laplacian modes
    let stretch := restrictCoefficients modes (finiteUnitTorusStretchingCoeff modes modes
      (fourierCurl (s.coefficients t)) (fourierCurl (s.coefficients t)))
    HasDerivAt (fun τ ↦ localizedEnergy (sandwich (C τ) (P τ)) (w τ))
      (materialMotionRate (C t) Cdot (P t) Pdot B (w t) +
        2 * ⟪A (w t), stretch⟫ +
        2 * ⟪A (w t), feedbackField modes (s.coefficients t)⟫ +
        nu * ⟪w t, A (D (w t)) + D (A (w t))⟫) t := by
  dsimp only
  have h := hasDerivAt_sandwichEnergy_material C P Cdot Pdot
    (fun τ ↦ restrictCoefficients modes (fourierCurl (s.coefficients τ)))
    (retainedAdvection modes (s.coefficients t)) (laplacian modes)
    (restrictCoefficients modes (finiteUnitTorusStretchingCoeff modes modes
      (fourierCurl (s.coefficients t)) (fourierCurl (s.coefficients t))) +
      feedbackField modes (s.coefficients t)) nu t
    Set.univ (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _) hC hP hPs
    (hasDerivAt_retainedField s modes hk t ht)
    (fun v _ w _ ↦ retainedAdvection_skew_inner modes (s.coefficients t) (s.reality t) (s.transverse t) v w)
    (fun v _ w _ ↦ laplacian_symmetric_inner modes v w)
  convert h using 1
  simp only [inner_add_right]
  ring

/-- The physical diffusion operator remains nonpositive on the whole
retained carrier, whether or not individual localized contributions are. -/
theorem inner_laplacian_nonpos (modes : Finset Wavevector) (w : FiniteField modes) :
    ⟪w, laplacian modes w⟫ ≤ 0 := by
  let v := extendCoefficients modes w
  have hw : restrictCoefficients modes v = w := restrict_extend modes w
  have hd : laplacian modes w =
      restrictCoefficients modes (unitTorusViscousVorticityCoeff 1 v) := by
    ext p
    exact laplacian_apply modes w p.1 p.2
  rw [hd, ← hw, inner_restrictCoefficients]
  apply Finset.sum_nonpos
  intro q _
  rw [PancakeSignedTransportEnergy.viscous_energy_pair]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _))
      (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)))
    (PancakeArbitraryDataBlocks.coefficientEnergy_nonneg _)

/-- The signed diffusion term of the actual localized energy identity. -/
def diffusionWork (modes : Finset Wavevector)
    (A : FiniteField modes →L[ℝ] FiniteField modes) (w : FiniteField modes) : ℝ :=
  ⟪w, A (laplacian modes w) + laplacian modes (A w)⟫

theorem diffusionWork_eq_two_inner (modes : Finset Wavevector)
    (A : FiniteField modes →L[ℝ] FiniteField modes) (hA : IsSelfAdjoint A)
    (w : FiniteField modes) :
    diffusionWork modes A w = 2 * ⟪A w, laplacian modes w⟫ := by
  have ha := hA.isSymmetric w (laplacian modes w)
  change ⟪A w, laplacian modes w⟫ = ⟪w, A (laplacian modes w)⟫ at ha
  have hd := laplacian_symmetric_inner modes w (A w)
  have hc := real_inner_comm (laplacian modes w) (A w)
  rw [diffusionWork, inner_add_right]
  linarith

/-- Joint diffusion over an exact operator partition has no cell-count
loss. No commutation of the individual localizers with the Laplacian is
required; this is a signed sum, not a sum of absolute values. -/
theorem sum_diffusionWork_eq {ι : Type*} (cells : Finset ι) (modes : Finset Wavevector)
    (A : ι → FiniteField modes →L[ℝ] FiniteField modes)
    (hA : ∀ a ∈ cells, IsSelfAdjoint (A a)) (hp : ∑ a ∈ cells, A a = 1)
    (w : FiniteField modes) :
    ∑ a ∈ cells, diffusionWork modes (A a) w = 2 * ⟪w, laplacian modes w⟫ := by
  have he : (∑ a ∈ cells, A a w) = w := by
    simpa only [_root_.sum_apply, one_apply_eq_self] using
      congrArg (fun F : FiniteField modes →L[ℝ] FiniteField modes ↦ F w) hp
  calc
    _ = ∑ a ∈ cells, 2 * ⟪A a w, laplacian modes w⟫ :=
      Finset.sum_congr rfl (fun a ha ↦ diffusionWork_eq_two_inner modes (A a) (hA a ha) w)
    _ = _ := by rw [← Finset.mul_sum, ← sum_inner, he]

theorem sum_diffusionWork_nonpos {ι : Type*} (cells : Finset ι) (modes : Finset Wavevector)
    (A : ι → FiniteField modes →L[ℝ] FiniteField modes)
    (hA : ∀ a ∈ cells, IsSelfAdjoint (A a)) (hp : ∑ a ∈ cells, A a = 1)
    (w : FiniteField modes) :
    ∑ a ∈ cells, diffusionWork modes (A a) w ≤ 0 := by
  rw [sum_diffusionWork_eq cells modes A hA hp]
  exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (inner_laplacian_nonpos modes w)

end Mettapedia.FluidDynamics.NavierStokes.LocalRetainedLocalizedEnergy
