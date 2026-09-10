import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAlignmentDifferential
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalMeanAlignmentBalance

/-!
# The actual frozen alignment derivative is the algebraic material rate

Use a straight line with the instantaneous full velocity, applying the
pointwise tangency theorem rather than asserting that the line solves
the material ODE. Spectral differentiability is explicit in this module.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalFrozenAlignmentRate

open scoped Topology ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakeFilteredStrainDynamics
open PancakeLocalInfiniteVelocity PancakeLocalMaterialTrajectories PancakeFourierMaterialPaths
open PancakeMeasurableMaterialRate PancakeMaterialChainRule
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing PancakeLocalSpatialVelocity
open PancakeSpectralProjectorRegularity.SymmetricStrain
open LocalAlignmentDifferential LocalAlignmentForcing LocalAlignmentTransport
open LocalMeanAlignmentBalance

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ

def SpectralDifferentiable (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (t : ℝ) (x : T3) : Prop :=
  DifferentiableAt ℝ (fun h ↦ topEigenvalue (spatialStrain modes (filteredVelocity chi (u (t + h)))
    (x + materialShift (velocity (u t) x) h))) 0

theorem frozenMaterialRate_eq_materialRate {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
    (modes outputs : Finset Wavevector) (hcut : ∀ q, q ∉ modes → chi q = 0)
    (hchir : ∀ q, chi (-q) = conj (chi q))
    (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (delta a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (t : ℝ) (ht : t ∈ Set.Ioo a b) (x : T3)
    (hlambda : SpectralDifferentiable chi modes s.coefficients t x) :
    LocalMeanAlignmentBalance.frozenMaterialRate chi modes s.coefficients delta t x =
      materialRate chi modes outputs (s.coefficients t) delta nu x := by
  obtain ⟨r, rfl⟩ := torusPoint_surjective x
  let v := velocity (s.coefficients t) (torusPoint r)
  let X : ℝ → X3 := fun τ i ↦ r i + (τ - t) * v i
  have hXt : X t = r := by funext i; simp only [X, sub_self, zero_mul, add_zero]
  have hX : HasDerivAt X (liftedVelocity s t (X t)) t := by
    rw [hXt]
    apply hasDerivAt_pi.mpr
    intro i
    have h := (((hasDerivAt_id t).sub_const t).mul_const (v i)).const_add (r i)
    simpa only [X, id_eq, one_mul, v, velocity, liftedVelocity, spatialField,
      complexRealPartEuclideanCLM_apply, complexRealPartEuclidean, PiLp.toLp_apply] using h
  have hL : DifferentiableAt ℝ
      (fun τ ↦ topEigenvalue (LocalFilteredStrain.strainAlong s chi modes X τ)) t := by
    have h0 : DifferentiableAt ℝ
        (fun h ↦ topEigenvalue (spatialStrain modes (filteredVelocity chi (s.coefficients (t + h)))
          (torusPoint r + materialShift v h))) (t - t) := by
      simpa only [SpectralDifferentiable, sub_self, v] using hlambda
    have h : DifferentiableAt ℝ
        (fun τ ↦ topEigenvalue (spatialStrain modes (filteredVelocity chi (s.coefficients (t + (τ - t))))
          (torusPoint r + materialShift v (τ - t)))) t :=
      h0.comp t (f := fun τ : ℝ ↦ τ - t) ((hasDerivAt_id t).sub_const t).differentiableAt
    have he (τ : ℝ) : t + (τ - t) = τ := by ring
    simpa only [he, LocalFilteredStrain.strainAlong, X, torusPoint_line] using h
  have h := hasDerivAt_alignmentEnergy_path s g hg hSum hu chi C hchi modes outputs hcut hchir
    hsub hout hs hk delta a b hab hI X t ht hX hL
  have h0 : HasDerivAt (fun τ ↦ alignmentEnergy chi modes (s.coefficients τ) delta (torusPoint (X τ)))
      (materialRate chi modes outputs (s.coefficients t) delta nu (torusPoint r)) (t + 0) := by
    simpa only [add_zero, hXt] using h
  have h' := h0.comp 0 (h := fun h : ℝ ↦ t + h) ((hasDerivAt_id (0 : ℝ)).const_add t)
  simpa only [LocalMeanAlignmentBalance.frozenMaterialRate, scalarMaterialRate, Function.comp_def,
    id_eq, add_zero, mul_one, X, add_sub_cancel_left, torusPoint_line, v] using h'.deriv

end Mettapedia.FluidDynamics.NavierStokes.LocalFrozenAlignmentRate
