import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeProjectionEnergyCancellation

/-!+# Projection forcing sees only variation of the weight

Every constant real linear operator preserves orthogonality between retained
and discarded Fourier outputs. Subtracting any frozen operator therefore
leaves the integrated signed projection pairing unchanged. The resulting
estimate measures oscillation, not the size of the frozen strain or the
regularizing scalar. No cutoff-uniform bound on the discarded field is
asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeProjectionWeightOscillation

open MeasureTheory
open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeMisalignmentEnergyBridge
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing PancakeBlockReality
open PancakeFiniteFourierOrthogonality PancakeWeightedOperatorTransport
open PancakeProjectionEnergyCancellation PancakeRetainedProjectionDefect
open PancakePhysicalSpectralDefect PancakeGalerkinKineticEnergy PancakeFourierMaterialPaths
open PancakePhysicalWeightedTransport PancakeSignedTransportForcing
open PancakeMaterialDiffusionBudget PancakePeriodicComplexStretch
open PancakeFrequencyProjectorCommutator PancakeSpectralFiniteDifference
open PancakeFilteredStrainDynamics

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "B" => EuclideanSpace.basisFun (Fin 3) ℝ

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integral_constant_operator_disjoint (s t : Finset Wavevector) (a b : FourierVelocity)
    (A : R3 →L[ℝ] R3) (hd : Disjoint s t)
    (hr : ∀ x : T3, ∀ i : Fin 3, (finiteFourierReconstruction s a x i).im = 0) :
    (∫ x : T3, ⟪A (complexRealPartEuclidean (finiteFourierReconstruction s a x)),
      complexRealPartEuclidean (finiteFourierReconstruction t b x)⟫) = 0 := by
  let F := fun i j (x : T3) ↦ (A (B j) i) *
    ((finiteScalarFourierReconstruction s (fun q ↦ a q j) x).re *
      (finiteScalarFourierReconstruction t (fun q ↦ b q i) x).re)
  have hi : ∀ i j, Integrable (F i j) := by
    intro i j
    have hc : Continuous (F i j) :=
      ((Complex.continuous_re.comp (continuous_finiteScalarFourierReconstruction s (fun q ↦ a q j))).mul
        (Complex.continuous_re.comp (continuous_finiteScalarFourierReconstruction t (fun q ↦ b q i)))).const_mul _
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he : ∀ x : T3, ⟪A (complexRealPartEuclidean (finiteFourierReconstruction s a x)),
      complexRealPartEuclidean (finiteFourierReconstruction t b x)⟫ =
        ∑ i : Fin 3, ∑ j : Fin 3, F i j x := by
    intro x
    change (∑ i : Fin 3, (finiteFourierReconstruction t b x i).re *
      A (complexRealPartEuclidean (finiteFourierReconstruction s a x)) i) = _
    apply Finset.sum_congr rfl
    intro i _
    rw [operator_apply_coordinate, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [F, complexRealPartEuclidean]
    simp only [finiteFourierReconstruction_component]
    ring
  simp only [he]
  rw [integral_finsetSum Finset.univ (fun i _ ↦ integrable_finsetSum Finset.univ (fun j _ ↦ hi i j))]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ ↦ hi i j)]
  apply Finset.sum_eq_zero
  intro j _
  dsimp [F]
  rw [integral_const_mul, integral_real_scalar_cross_disjoint s t _ _ hd]
  · simp
  · intro x
    simpa only [finiteFourierReconstruction_component] using hr x j

theorem integral_constant_weight_discarded_zero (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (A : R3 →L[ℝ] R3)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    (∫ x : T3, ⟪A (spatialVorticity modes u x), discardedNonlinearField modes outputs u x⟫) = 0 := by
  apply integral_constant_operator_disjoint modes (outputs \ modes) (fourierCurl u) (nonlinearVorticityCoeff modes u) A
  · exact Finset.disjoint_left.mpr (fun q hq ho ↦ (Finset.mem_sdiff.mp ho).2 hq)
  · intro x i
    exact finiteFourierReconstruction_im_eq_zero_of_neg_closed modes (fourierCurl u) hs
      (fourierCurl_conjugate u hr) x i

theorem integral_weight_discarded_eq_oscillation (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (K : T3 → R3 →L[ℝ] R3) (A : R3 →L[ℝ] R3)
    (hK : Continuous K) (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    (∫ x : T3, ⟪K x (spatialVorticity modes u x), discardedNonlinearField modes outputs u x⟫) =
      ∫ x : T3, ⟪(K x - A) (spatialVorticity modes u x), discardedNonlinearField modes outputs u x⟫ := by
  have hw := continuous_vorticity modes u
  have hd := continuous_discardedNonlinearField modes outputs u
  have hkc : Continuous (fun x : T3 ↦ ⟪K x (spatialVorticity modes u x),
      discardedNonlinearField modes outputs u x⟫) := (hK.clm_apply hw).inner hd
  have hac : Continuous (fun x : T3 ↦ ⟪A (spatialVorticity modes u x),
      discardedNonlinearField modes outputs u x⟫) := (A.continuous.comp hw).inner hd
  simp only [sub_apply, inner_sub_left]
  rw [integral_sub (hkc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hac.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
    integral_constant_weight_discarded_zero modes outputs u A hs hr, sub_zero]

theorem abs_integral_weight_discarded_le_oscillation (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (K : T3 → R3 →L[ℝ] R3) (A : R3 →L[ℝ] R3)
    (epsilon : ℝ) (hK : Continuous K) (hosc : ∀ x, ‖K x - A‖ ≤ epsilon)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    |∫ x : T3, ⟪K x (spatialVorticity modes u x), discardedNonlinearField modes outputs u x⟫| ≤
      epsilon * ∫ x : T3, ‖spatialVorticity modes u x‖ * ‖discardedNonlinearField modes outputs u x‖ := by
  have hw := continuous_vorticity modes u
  have hd := continuous_discardedNonlinearField modes outputs u
  have hc : Continuous (fun x : T3 ↦ ⟪(K x - A) (spatialVorticity modes u x),
      discardedNonlinearField modes outputs u x⟫) := ((hK.sub continuous_const).clm_apply hw).inner hd
  have hb : Continuous (fun x : T3 ↦ epsilon * (‖spatialVorticity modes u x‖ *
      ‖discardedNonlinearField modes outputs u x‖)) := (hw.norm.mul hd.norm).const_mul _
  rw [integral_weight_discarded_eq_oscillation modes outputs u K A hK hs hr,
    ← integral_const_mul]
  apply abs_integral_le_integral_abs.trans
  apply integral_mono (hc.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hb.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  intro x
  calc
    _ ≤ ‖(K x - A) (spatialVorticity modes u x)‖ * ‖discardedNonlinearField modes outputs u x‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (‖K x - A‖ * ‖spatialVorticity modes u x‖) * ‖discardedNonlinearField modes outputs u x‖ :=
      mul_le_mul_of_nonneg_right ((K x - A).le_opNorm _) (norm_nonneg _)
    _ ≤ epsilon * (‖spatialVorticity modes u x‖ * ‖discardedNonlinearField modes outputs u x‖) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (hosc x) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem integral_projection_pairing_eq_frozen_oscillation
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector) (u : FourierVelocity) (delta : ℝ)
    (x₀ : T3) (hsub : modes ⊆ outputs)
    (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u k) = 0)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    (∫ x : T3, gapForcingPairing chi modes u delta (spatialVorticityForcing (fun _ ↦ 1) modes u 0) x) =
      -2 * ∫ x : T3, ⟪(physicalGapWeight chi modes u 0 x - physicalGapWeight chi modes u 0 x₀)
        (spatialVorticity modes u x), discardedNonlinearField modes outputs u x⟫ := by
  rw [integral_projection_pairing_delta_independent chi modes outputs u delta hsub hout hk hu hs hr]
  simp only [gapForcingPairing, forcing_full_eq_negative_discarded modes outputs u _ hsub hout hk hu hs hr,
    inner_neg_right, mul_neg, integral_neg, integral_const_mul]
  rw [integral_weight_discarded_eq_oscillation modes outputs u (physicalGapWeight chi modes u 0)
    (physicalGapWeight chi modes u 0 x₀) (continuous_physicalGapWeight chi modes u 0) hs hr]
  ring

theorem abs_integral_projection_pairing_le_strain_oscillation
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector) (u : FourierVelocity) (delta epsilon : ℝ)
    (x₀ : T3) (hsub : modes ⊆ outputs)
    (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u k) = 0)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q))
    (hosc : ∀ x, ‖(spatialStrain modes (filteredVelocity chi u) x).1 -
      (spatialStrain modes (filteredVelocity chi u) x₀).1‖ ≤ epsilon) :
    |∫ x : T3, gapForcingPairing chi modes u delta (spatialVorticityForcing (fun _ ↦ 1) modes u 0) x| ≤
      4 * epsilon * ∫ x : T3, ‖spatialVorticity modes u x‖ * ‖discardedNonlinearField modes outputs u x‖ := by
  have hg : ∀ x, ‖physicalGapWeight chi modes u 0 x - physicalGapWeight chi modes u 0 x₀‖ ≤ 2 * epsilon := by
    intro x
    exact (regularizedGap_sub_norm (spatialStrain modes (filteredVelocity chi u) x₀)
      (spatialStrain modes (filteredVelocity chi u) x) 0).trans (by linarith [hosc x])
  have hb := abs_integral_weight_discarded_le_oscillation modes outputs u (physicalGapWeight chi modes u 0)
    (physicalGapWeight chi modes u 0 x₀) (2 * epsilon) (continuous_physicalGapWeight chi modes u 0) hg hs hr
  rw [integral_projection_pairing_delta_independent chi modes outputs u delta hsub hout hk hu hs hr]
  simp only [gapForcingPairing, forcing_full_eq_negative_discarded modes outputs u _ hsub hout hk hu hs hr,
    inner_neg_right, mul_neg, integral_neg, integral_const_mul, abs_neg, abs_mul]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

end Mettapedia.FluidDynamics.NavierStokes.PancakeProjectionWeightOscillation
