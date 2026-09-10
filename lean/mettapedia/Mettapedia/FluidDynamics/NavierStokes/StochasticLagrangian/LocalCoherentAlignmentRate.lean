import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAlignmentRegularization
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The actual material rate at exact alignment

Unregularized alignment energy is nonnegative. At a zero its frozen scalar
derivative is zero; the actual local equation identifies this derivative
with the algebraic material rate almost everywhere. This includes multiple
top eigenvalues and exposes a cancellation lost by the coarse collision
envelope. It does not assert that coherence is preserved in time.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalCoherentAlignmentRate

open scoped Topology RealInnerProductSpace ComplexConjugate
open Filter MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeLocalInfiniteVelocity PancakeFourierMaterialPaths PancakeFilteredStrainDynamics
open PancakeSpectralDefectEvolution PancakeRegularizedMaterialRate PancakeMeasurableMaterialRate
open PancakeSpectralFiniteDifference PancakePhysicalLaplacian
open PancakeFrequencyProjectorCommutator LocalLowDiffusionBudget
open LocalAlignmentTransport LocalAlignmentForcing LocalAlignmentRegularization

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem alignmentEnergy_zero_eq_inner_residual (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) :
    alignmentEnergy chi modes u 0 x = ⟪fullVorticity u x, residual chi modes u x⟫ := by
  simp only [alignmentEnergy, regularizedEnergy_eq, zero_mul, add_zero,
    topSpectralDefect, spectralDefect_eq_inner, LocalAlignmentForcing.residual]

theorem alignmentEnergy_zero_nonneg (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : 0 ≤ alignmentEnergy chi modes u 0 x := by
  simpa only [alignmentEnergy, regularizedEnergy_eq, zero_mul, add_zero] using
    topSpectralDefect_nonneg (spatialStrain modes (filteredVelocity chi u) x) (fullVorticity u x)

theorem alignmentEnergy_zero_of_residual_eq_zero (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) (hz : residual chi modes u x = 0) :
    alignmentEnergy chi modes u 0 x = 0 := by
  rw [alignmentEnergy_zero_eq_inner_residual, hz, inner_zero_right]

/-- This statement uses Lean's total scalar derivative. Its identification
with the physical algebraic rate is supplied separately almost everywhere. -/
theorem frozenMaterialRate_eq_zero_of_alignmentEnergy_eq_zero
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : ℝ → FourierVelocity)
    (t : ℝ) (x : T3) (hA : alignmentEnergy chi modes (u t) 0 x = 0) :
    LocalMeanAlignmentBalance.frozenMaterialRate chi modes u 0 t x = 0 := by
  have hs : materialShift (LocalMeanAlignmentBalance.velocity (u t) x) 0 = 0 := by
    ext i
    simp [materialShift, torusPoint]
  apply IsLocalMin.deriv_eq_zero
  change ∀ᶠ h in 𝓝 (0 : ℝ),
    alignmentEnergy chi modes (u (t + 0)) 0
        (x + materialShift (LocalMeanAlignmentBalance.velocity (u t) x) 0) ≤
      alignmentEnergy chi modes (u (t + h)) 0
        (x + materialShift (LocalMeanAlignmentBalance.velocity (u t) x) h)
  apply Eventually.of_forall
  intro h
  simpa only [add_zero, hs, hA] using alignmentEnergy_zero_nonneg chi modes (u (t + h))
    (x + materialShift (LocalMeanAlignmentBalance.velocity (u t) x) h)

theorem materialRate_zero_eq_anisotropies_of_residual_eq_zero
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector) (u : FourierVelocity)
    (nu : ℝ) (x : T3) (hz : residual chi modes u x = 0) :
    materialRate chi modes outputs u 0 nu x =
      remainderAnisotropy (nonviscousRemainder chi modes outputs u x)
        (topVector (spatialStrain modes (filteredVelocity chi u) x)) (fullVorticity u x) +
      nu * remainderAnisotropy (strainLaplacian modes (filteredVelocity chi u) x)
        (topVector (spatialStrain modes (filteredVelocity chi u) x)) (fullVorticity u x) := by
  unfold materialRate
  rw [linearRate_viscous_split]
  dsimp only [LocalAlignmentForcing.residual] at hz
  simp only [linearRate, regularizedGap_apply_eq,
    hz, zero_smul, add_zero, norm_zero, zero_pow (by omega : 2 ≠ 0), neg_zero,
    zero_add, inner_zero_left, mul_zero, zero_mul]

/-- At coherent points the only remaining regularized material rate is
the regularizer times the actual squared-vorticity rate, even at collisions. -/
theorem ae_ae_materialRate_eq_regularizer_of_residual_eq_zero
    {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hB : 0 ≤ B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
    (modes outputs : Finset Wavevector) (hcut : ∀ q, q ∉ modes → chi q = 0)
    (hchir : ∀ q, chi (-q) = conj (chi q))
    (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (delta a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b), ∀ᵐ x : T3,
      residual chi modes (s.coefficients t) x = 0 →
      materialRate chi modes outputs (s.coefficients t) delta nu x =
        delta * vorticityNormRate (s.coefficients t) nu x := by
  filter_upwards [LocalAlignmentEnergyBudget.ae_ae_frozenMaterialRate_eq_materialRate
    s hB g hg hSum hu chi C hchi modes outputs hcut hchir hsub hout hs hk 0 a b hab hI] with t ht
  exact ht.mono (fun x hx hz ↦ by
    have hzero := frozenMaterialRate_eq_zero_of_alignmentEnergy_eq_zero chi modes s.coefficients t x
      (alignmentEnergy_zero_of_residual_eq_zero chi modes (s.coefficients t) x hz)
    rw [materialRate_eq_zero_add, ← hx, hzero, zero_add])

/-- The nonlinear and viscous anisotropies cancel jointly at coherent
points of the actual solution. Neither term is asserted to vanish alone. -/
theorem ae_ae_anisotropy_add_viscous_eq_zero_of_residual_eq_zero
    {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hB : 0 ≤ B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
    (modes outputs : Finset Wavevector) (hcut : ∀ q, q ∉ modes → chi q = 0)
    (hchir : ∀ q, chi (-q) = conj (chi q))
    (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b), ∀ᵐ x : T3,
      residual chi modes (s.coefficients t) x = 0 →
      remainderAnisotropy (nonviscousRemainder chi modes outputs (s.coefficients t) x)
        (topVector (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x))
        (fullVorticity (s.coefficients t) x) +
      nu * remainderAnisotropy (strainLaplacian modes (filteredVelocity chi (s.coefficients t)) x)
        (topVector (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x))
        (fullVorticity (s.coefficients t) x) = 0 := by
  filter_upwards [ae_ae_materialRate_eq_regularizer_of_residual_eq_zero
    s hB g hg hSum hu chi C hchi modes outputs hcut hchir hsub hout hs hk 0 a b hab hI] with t ht
  exact ht.mono (fun x hx hz ↦ by
    simpa only [materialRate_zero_eq_anisotropies_of_residual_eq_zero chi modes outputs _ nu x hz,
      zero_mul] using hx hz)

end Mettapedia.FluidDynamics.NavierStokes.LocalCoherentAlignmentRate
