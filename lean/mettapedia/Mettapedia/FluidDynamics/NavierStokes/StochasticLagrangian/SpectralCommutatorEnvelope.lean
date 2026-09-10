import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralSourceCommutator
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralDiffusionWeightLimit

/-!
# A continuous source envelope separating tilt from transverse energy

Commuting sources have no linear-in-misalignment channel. For general
sources that channel is charged to the strain commutator. The minimum
with the earlier envelope ensures the refinement never increases the cost.
The positive part extends the definition harmlessly to nonpositive
auxiliary parameters; it is inactive for every positive parameter.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SpectralCommutatorEnvelope

open scoped RealInnerProductSpace
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralFiniteDifference PancakeSpectralDefectEvolution PancakeAnisotropyDepletion
open SpectralSourceCommutator SpectralDiffusionWeight StrainEigenvalueContinuity

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def tiltBound (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (epsilon : ℝ) : ℝ :=
  (‖commutator S R‖ + epsilon * ‖R‖) / (topGap S + epsilon)

def refinedBound (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) (epsilon : ℝ) : ℝ :=
  2 * ‖R‖ * weight S w epsilon +
    2 * tiltBound S R epsilon * ‖w‖ * Real.sqrt (weight S w epsilon)

def envelope (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) (epsilon : ℝ) : ℝ :=
  min (SpectralAnisotropyEnvelope.envelope S R w epsilon) (max (refinedBound S R w epsilon) 0)

theorem tiltBound_nonneg (S : SymmetricStrain) (R : R3 →L[ℝ] R3)
    (epsilon : ℝ) (heps : 0 < epsilon) : 0 ≤ tiltBound S R epsilon :=
  div_nonneg (add_nonneg (norm_nonneg _) (mul_nonneg heps.le (norm_nonneg R)))
    (add_nonneg (topGap_nonneg S) heps.le)

theorem refinedBound_nonneg (S : SymmetricStrain) (R : R3 →L[ℝ] R3)
    (w : R3) (epsilon : ℝ) (heps : 0 < epsilon) : 0 ≤ refinedBound S R w epsilon := by
  have hw := weight_nonneg S w epsilon heps
  have ht := tiltBound_nonneg S R epsilon heps
  unfold refinedBound
  positivity

theorem envelope_nonneg (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) (epsilon : ℝ) :
    0 ≤ envelope S R w epsilon :=
  le_min (SpectralAnisotropyEnvelope.envelope_nonneg S R w epsilon) (le_max_right _ _)

theorem envelope_le_previous (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) (epsilon : ℝ) :
    envelope S R w epsilon ≤ SpectralAnisotropyEnvelope.envelope S R w epsilon := min_le_left _ _

theorem envelope_le_coarse (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) (epsilon : ℝ) :
    envelope S R w epsilon ≤ 2 * ‖R‖ * ‖w‖ ^ 2 :=
  (envelope_le_previous S R w epsilon).trans (SpectralAnisotropyEnvelope.envelope_le_coarse S R w epsilon)

theorem abs_remainderAnisotropy_le_refinedBound (S : SymmetricStrain)
    (R : R3 →L[ℝ] R3) (w : R3) (epsilon : ℝ) (heps : 0 < epsilon) :
    |remainderAnisotropy R (topVector S) w| ≤ refinedBound S R w epsilon := by
  have hm := lineRemainder_sq_le_weight S w epsilon heps
  have hs := Real.le_sqrt_of_sq_le hm
  have ht := tiltBound_nonneg S R epsilon heps
  apply (abs_anisotropy_le_regularized_commutator S R w epsilon heps).trans
  exact add_le_add (mul_le_mul_of_nonneg_left hm (by positivity))
    (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * tiltBound S R epsilon * ‖w‖))

theorem abs_remainderAnisotropy_le_envelope (S : SymmetricStrain)
    (R : R3 →L[ℝ] R3) (w : R3) (epsilon : ℝ) (heps : 0 < epsilon) :
    |remainderAnisotropy R (topVector S) w| ≤ envelope S R w epsilon :=
  le_min (SpectralAnisotropyEnvelope.abs_remainderAnisotropy_le_envelope S R w epsilon heps)
    ((abs_remainderAnisotropy_le_refinedBound S R w epsilon heps).trans (le_max_left _ _))

theorem envelope_eq_coarse_of_topGap_zero (S : SymmetricStrain) (R : R3 →L[ℝ] R3)
    (w : R3) (epsilon : ℝ) (heps : 0 < epsilon) (hg : topGap S = 0) :
    envelope S R w epsilon = 2 * ‖R‖ * ‖w‖ ^ 2 := by
  have ht := tiltBound_nonneg S R epsilon heps
  rw [envelope, SpectralAnisotropyEnvelope.envelope_eq_coarse_of_topGap_zero S R w epsilon heps hg]
  apply min_eq_left
  apply le_trans ?_ (le_max_left _ _)
  rw [refinedBound, weight_eq_norm_sq_of_topGap_zero S w epsilon heps hg]
  have h : 0 ≤ 2 * tiltBound S R epsilon * ‖w‖ * Real.sqrt (‖w‖ ^ 2) := by positivity
  linarith

theorem continuous_tiltBound {X : Type*} [TopologicalSpace X]
    (S : X → SymmetricStrain) (R : X → R3 →L[ℝ] R3)
    (epsilon : ℝ) (heps : 0 < epsilon) (hS : Continuous S) (hR : Continuous R) :
    Continuous (fun x ↦ tiltBound (S x) (R x) epsilon) :=
  ((continuous_commutator S R hS hR).norm.add (hR.norm.const_mul epsilon)).div
    ((continuous_topGap.comp hS).add continuous_const)
    (fun x ↦ ne_of_gt (add_pos_of_nonneg_of_pos (topGap_nonneg (S x)) heps))

theorem continuous_envelope {X : Type*} [TopologicalSpace X]
    (S : X → SymmetricStrain) (R : X → R3 →L[ℝ] R3) (w : X → R3)
    (epsilon : ℝ) (heps : 0 < epsilon) (hS : Continuous S) (hR : Continuous R) (hw : Continuous w) :
    Continuous (fun x ↦ envelope (S x) (R x) (w x) epsilon) := by
  have ht := continuous_tiltBound S R epsilon heps hS hR
  have hW := continuous_weight S w epsilon heps hS hw
  exact (SpectralAnisotropyEnvelope.continuous_envelope S R w epsilon heps hS hR hw).min
    (((((hR.norm.const_mul 2).mul hW).add (((ht.const_mul 2).mul hw.norm).mul hW.sqrt))).max continuous_const)

end Mettapedia.FluidDynamics.NavierStokes.SpectralCommutatorEnvelope
