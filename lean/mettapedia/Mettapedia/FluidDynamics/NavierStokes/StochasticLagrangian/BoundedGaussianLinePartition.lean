import Mettapedia.Analysis.CompactRangeCover
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.AdaptiveGaussianLinePartition

/-!
# Gaussian line partitions with uniformly bounded cover size

A common amplitude bound places every weighted projector in the same
compact finite-dimensional ball. Adaptive centers remain actual source
points, but their number is bounded independently of oscillation. This
also supplies a positive lower bound for the Gaussian temperature and a
common multiplier in the operator-path derivative estimate.

The constants still depend on the amplitude bound and the requested line
error. No uniformity as those parameters degenerate is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.BoundedGaussianLinePartition

open Mettapedia.Analysis.CompactRangeCover
open GaussianWeightedLinePartition AdaptiveGaussianLinePartition SpectralTiltFreezing

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "H9" => EuclideanSpace ℝ (Fin 3 × Fin 3)
local notation "Op" => R3 →L[ℝ] R3

theorem exists_bounded_gaussian_line_partition {X : Type*} [TopologicalSpace X] [Nonempty X]
    (R : ℝ) (rho : ℝ) (hrho : 0 < rho) :
    ∃ M : ℕ, 0 < M ∧ ∀ r : X → ℝ, (∀ x, 0 ≤ r x) → (∀ x, r x ≤ R) →
      ∀ e : X → R3, (∀ x, ‖e x‖ = 1) →
      Continuous (fun x ↦ r x • InnerProductSpace.rankOne ℝ (e x) (e x)) →
      ∃ centers : Finset X, centers.Nonempty ∧ centers.card ≤ M ∧
        let tau := temperature centers.card rho
        let p := fun (i : ↑centers) x ↦ lineAmplitude (fun j : ↑centers ↦ r j.1)
          (fun j : ↑centers ↦ e j.1) tau (r x) (e x) i
        0 < temperature M rho ∧ temperature M rho ≤ tau ∧
        (∀ i, Continuous (p i)) ∧ (∀ x, (∑ i, p i x ^ 2) = r x ^ 2) ∧
        (∀ x, (∑ i, p i x ^ 2 * lineDistanceSq (e x) (e i.1)) ≤ rho ^ 2) ∧
        ∀ (path : ℝ → X) (t : ℝ) (V : Op),
          HasDerivAt (fun s ↦ r (path s) • InnerProductSpace.rankOne ℝ (e (path s)) (e (path s))) V t →
          (∑ i, deriv (fun s ↦ p i (path s)) t ^ 2) ≤
            3 * (1 + R ^ 2 * rho ^ 2 / (2 * temperature M rho ^ 2)) * ‖V‖ ^ 2 := by
  obtain ⟨M, hM, hcover⟩ := exists_uniform_card_norm_cover (X := X) (E := H9) R (rho / 2)
    (show 0 < rho / 2 by positivity)
  refine ⟨M, hM, ?_⟩
  intro r hr hrR e he hA
  obtain ⟨centers, hcard, hnear⟩ := hcover (fun x ↦ coordinateProjector (r x) (e x))
    (fun x ↦ (norm_coordinateProjector _ (hr x) _ (he x)).le.trans (hrR x))
  obtain ⟨hc, ht, hp, hmass, hline, hpath⟩ :=
    gaussian_line_partition_of_cover r hr e he hA rho hrho centers hnear
  have hT := temperature_pos M hM rho hrho
  have hTle := temperature_antitone_card centers.card M hc.card_pos hcard rho
  refine ⟨centers, hc, hcard, hT, hTle, hp, hmass, hline, ?_⟩
  intro path t V hd
  have hnum : r (path t) ^ 2 * rho ^ 2 ≤ R ^ 2 * rho ^ 2 :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hr _) (hrR _) 2) (sq_nonneg rho)
  have hden : 2 * temperature M rho ^ 2 ≤ 2 * temperature centers.card rho ^ 2 := by
    nlinarith [sq_nonneg (temperature centers.card rho - temperature M rho)]
  have hfrac : r (path t) ^ 2 * rho ^ 2 / (2 * temperature centers.card rho ^ 2) ≤
      R ^ 2 * rho ^ 2 / (2 * temperature M rho ^ 2) := by
    calc
      _ ≤ R ^ 2 * rho ^ 2 / (2 * temperature centers.card rho ^ 2) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  exact (hpath path t V hd).trans
    (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))

end Mettapedia.FluidDynamics.NavierStokes.BoundedGaussianLinePartition
