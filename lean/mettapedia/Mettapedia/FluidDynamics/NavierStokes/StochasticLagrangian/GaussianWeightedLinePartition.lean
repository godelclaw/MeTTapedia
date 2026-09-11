import Mettapedia.Analysis.NormScaledGaussianPartition
import Mettapedia.Analysis.EuclideanOperatorCoordinates
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.WeightedLineFreezing

/-!
# Explicit Gaussian amplitudes for weighted spectral lines

The Hilbert coordinates of `r P` select finite Gaussian patches. Their
squared amplitudes sum exactly to `r²`, including at `r = 0`; their weighted
line error is bounded by twice the Gaussian distance moment. The same
construction carries a derivative bound inherited from the operator path.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianWeightedLinePartition

open scoped BigOperators RealInnerProductSpace
open Mettapedia.Analysis.EuclideanOperatorCoordinates Mettapedia.Analysis.GaussianPartitionEnergy
open PancakeAnisotropyDepletion SpectralTiltFreezing

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "H9" => EuclideanSpace ℝ (Fin 3 × Fin 3)
local notation "Op" => R3 →L[ℝ] R3

def coordinateProjector (r : ℝ) (e : R3) : H9 := coordinates (r • InnerProductSpace.rankOne ℝ e e)

theorem norm_coordinateProjector (r : ℝ) (hr : 0 ≤ r) (e : R3) (he : ‖e‖ = 1) :
    ‖coordinateProjector r e‖ = r := by
  simp only [coordinateProjector, map_smul, norm_smul, norm_coordinates_rankOne e he,
    Real.norm_eq_abs, abs_of_nonneg hr, mul_one]

theorem sq_mul_lineDistanceSq_le_distance (r s : ℝ) (e f : R3) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) :
    r ^ 2 * lineDistanceSq e f ≤ 2 * ‖coordinateProjector r e - coordinateProjector s f‖ ^ 2 := by
  have h := WeightedLineFreezing.sq_mul_lineDistanceSq_le e f he hf r s
  have hc := norm_le_coordinates (r • InnerProductSpace.rankOne ℝ e e - s • InnerProductSpace.rankOne ℝ f f)
  rw [map_sub] at hc
  have hs := pow_le_pow_left₀ (norm_nonneg _) hc 2
  exact h.trans (mul_le_mul_of_nonneg_left hs (by norm_num))

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def lineAmplitude (r : ι → ℝ) (e : ι → R3) (tau a : ℝ) (f : R3) (i : ι) : ℝ :=
  normScaledAmplitude (fun j ↦ coordinateProjector (r j) (e j)) tau (coordinateProjector a f) i

theorem sum_lineAmplitude_sq (r : ι → ℝ) (e : ι → R3) (tau a : ℝ) (ha : 0 ≤ a)
    (f : R3) (hf : ‖f‖ = 1) : (∑ i, lineAmplitude r e tau a f i ^ 2) = a ^ 2 := by
  rw [show (∑ i, lineAmplitude r e tau a f i ^ 2) = ‖coordinateProjector a f‖ ^ 2
    from sum_normScaledAmplitude_sq _ _ _, norm_coordinateProjector a ha f hf]

theorem sum_lineAmplitude_sq_mul_lineDistanceSq_le (r : ι → ℝ) (e : ι → R3)
    (he : ∀ i, ‖e i‖ = 1) (tau a : ℝ) (ha : 0 ≤ a) (f : R3) (hf : ‖f‖ = 1) :
    (∑ i, lineAmplitude r e tau a f i ^ 2 * lineDistanceSq f (e i)) ≤
      2 * distanceMoment (fun j ↦ coordinateProjector (r j) (e j)) tau (coordinateProjector a f) := by
  have hi (i : ι) := mul_le_mul_of_nonneg_left
    (sq_mul_lineDistanceSq_le_distance a (r i) f (e i) hf (he i))
    (sq_nonneg (gaussianAmplitude (fun j ↦ coordinateProjector (r j) (e j)) tau (coordinateProjector a f) i))
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hi i)
  have hid (i : ι) : lineAmplitude r e tau a f i ^ 2 * lineDistanceSq f (e i) =
      gaussianAmplitude (fun j ↦ coordinateProjector (r j) (e j)) tau (coordinateProjector a f) i ^ 2 *
        (a ^ 2 * lineDistanceSq f (e i)) := by
    simp only [lineAmplitude, normScaledAmplitude, norm_coordinateProjector a ha f hf]
    ring
  simp_rw [hid]
  have hsum : (∑ i, gaussianAmplitude (fun j ↦ coordinateProjector (r j) (e j)) tau
      (coordinateProjector a f) i ^ 2 *
      (2 * ‖coordinateProjector a f - coordinateProjector (r i) (e i)‖ ^ 2)) =
        2 * distanceMoment (fun j ↦ coordinateProjector (r j) (e j)) tau (coordinateProjector a f) := by
    rw [← sum_sq_mul_distance_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  exact h.trans_eq hsum

/-- The factor three compares the Hilbert matrix norm with the operator
norm. It counts spatial coordinates, not patches. -/
theorem sum_operator_path_deriv_sq_le (center : ι → H9) (tau : ℝ) (ht : 0 < tau)
    {A : ℝ → Op} {V : Op} {t : ℝ} (hA : HasDerivAt A V t) (j : ι) :
    (∑ i, deriv (fun s ↦ normScaledAmplitude center tau (coordinates (A s)) i) t ^ 2) ≤
      3 * (1 + ‖coordinates (A t)‖ ^ 2 *
        (‖coordinates (A t) - center j‖ ^ 2 + tau * Real.log (Fintype.card ι)) / tau ^ 2) * ‖V‖ ^ 2 := by
  have hx : HasDerivAt (fun s ↦ coordinates (A s)) (coordinates V) t :=
    (coordinates (ι := Fin 3)).hasFDerivAt.comp_hasDerivAt t hA
  have h := sum_normScaled_deriv_sq_le center tau ht hx j
  have hN : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hlog := Real.log_nonneg hN
  have hv := mul_le_mul_of_nonneg_left (norm_coordinates_sq_le V)
    (show 0 ≤ 1 + ‖coordinates (A t)‖ ^ 2 *
      (‖coordinates (A t) - center j‖ ^ 2 + tau * Real.log (Fintype.card ι)) / tau ^ 2 by positivity)
  norm_num only [Fintype.card_fin, Nat.cast_ofNat] at hv
  exact h.trans (by nlinarith only [hv])

end Mettapedia.FluidDynamics.NavierStokes.GaussianWeightedLinePartition
