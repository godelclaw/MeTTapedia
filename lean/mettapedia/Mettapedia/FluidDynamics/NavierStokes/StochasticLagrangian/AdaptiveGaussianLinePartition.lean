import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianWeightedLinePartition

/-!
# Adaptive Gaussian line patches with exact coverage and derivative control

A finite cover of the weighted projector image determines an explicit
temperature. The resulting amplitudes have exact squared coverage and a
prescribed weighted line error. Their operator-path derivative cost has
no patch-count multiplier, but depends on the logarithm of the cover size
through the displayed temperature. This is not a scale-uniform bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.AdaptiveGaussianLinePartition

open scoped BigOperators
open Mettapedia.Analysis.EuclideanOperatorCoordinates Mettapedia.Analysis.GaussianPartitionEnergy
open GaussianWeightedLinePartition SpectralTiltFreezing

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "H9" => EuclideanSpace ℝ (Fin 3 × Fin 3)
local notation "Op" => R3 →L[ℝ] R3

def temperature (n : ℕ) (rho : ℝ) : ℝ := rho ^ 2 / (4 * (1 + Real.log n))

theorem gaussian_line_partition_of_cover {X : Type*} [TopologicalSpace X] [Nonempty X]
    (r : X → ℝ) (hr : ∀ x, 0 ≤ r x) (e : X → R3) (he : ∀ x, ‖e x‖ = 1)
    (hA : Continuous (fun x ↦ r x • InnerProductSpace.rankOne ℝ (e x) (e x)))
    (rho : ℝ) (hrho : 0 < rho) (centers : Finset X)
    (hcover : ∀ x, ∃ y ∈ centers,
      ‖coordinateProjector (r x) (e x) - coordinateProjector (r y) (e y)‖ < rho / 2) :
    centers.Nonempty ∧
      let tau := temperature centers.card rho
      let p := fun (i : ↑centers) x ↦ lineAmplitude (fun j : ↑centers ↦ r j.1)
        (fun j : ↑centers ↦ e j.1) tau (r x) (e x) i
      0 < tau ∧ (∀ i, Continuous (p i)) ∧
      (∀ x, (∑ i, p i x ^ 2) = r x ^ 2) ∧
      (∀ x, (∑ i, p i x ^ 2 * lineDistanceSq (e x) (e i.1)) ≤ rho ^ 2) ∧
      ∀ (path : ℝ → X) (t : ℝ) (V : Op),
        HasDerivAt (fun s ↦ r (path s) • InnerProductSpace.rankOne ℝ (e (path s)) (e (path s))) V t →
        (∑ i, deriv (fun s ↦ p i (path s)) t ^ 2) ≤
          3 * (1 + r (path t) ^ 2 * rho ^ 2 / (2 * tau ^ 2)) * ‖V‖ ^ 2 := by
  let B := fun x ↦ coordinateProjector (r x) (e x)
  have hB : Continuous B := (coordinates (ι := Fin 3)).continuous.comp hA
  have hnonempty : centers.Nonempty := by
    obtain ⟨j, hj, _⟩ := hcover (Classical.arbitrary X)
    exact ⟨j, hj⟩
  letI : Nonempty ↑centers := ⟨⟨hnonempty.choose, hnonempty.choose_spec⟩⟩
  let tau := temperature centers.card rho
  let C : ↑centers → H9 := fun j ↦ B j.1
  have hN : (1 : ℝ) ≤ centers.card := by exact_mod_cast hnonempty.card_pos
  have hlog : 0 ≤ Real.log (centers.card : ℝ) := Real.log_nonneg hN
  have ht : 0 < tau := div_pos (sq_pos_of_pos hrho) (by positivity)
  have hpay : tau * (1 + Real.log (centers.card : ℝ)) = rho ^ 2 / 4 := by
    dsimp [tau, temperature]
    field_simp
  have hm (x : X) : distanceMoment C tau (B x) ≤ rho ^ 2 / 2 := by
    obtain ⟨j, hj, hclose⟩ := hcover x
    have h := distanceMoment_le C tau ht (B x) ⟨j, hj⟩
    simp only [Fintype.card_coe] at h
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hclose.le 2
    change ‖B x - C ⟨j, hj⟩‖ ^ 2 ≤ (rho / 2) ^ 2 at hsq
    nlinarith only [h, hsq, hpay, ht]
  refine ⟨hnonempty, ht, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (continuous_normScaledAmplitude C tau i).comp hB
  · intro x
    exact sum_lineAmplitude_sq _ _ tau (r x) (hr x) (e x) (he x)
  · intro x
    have h := sum_lineAmplitude_sq_mul_lineDistanceSq_le (fun j : ↑centers ↦ r j.1)
      (fun j : ↑centers ↦ e j.1) (fun j ↦ he j.1) tau (r x) (hr x) (e x) (he x)
    have hmoment := hm x
    exact h.trans (by nlinarith only [hmoment])
  · intro path t V hpath
    have hcoords : HasDerivAt (fun s ↦ B (path s)) (coordinates V) t :=
      (coordinates (ι := Fin 3)).hasFDerivAt.comp_hasDerivAt t hpath
    have h := sum_normScaled_deriv_sq_le_moment C tau hcoords
    have hnorm : ‖B (path t)‖ = r (path t) := norm_coordinateProjector _ (hr _) _ (he _)
    rw [hnorm] at h
    have hmoment := mul_le_mul_of_nonneg_right (hm (path t))
      (show 0 ≤ r (path t) ^ 2 * ‖coordinates V‖ ^ 2 / tau ^ 2 by positivity)
    have hv := mul_le_mul_of_nonneg_left (norm_coordinates_sq_le V)
      (show 0 ≤ 1 + r (path t) ^ 2 * rho ^ 2 / (2 * tau ^ 2) by positivity)
    norm_num only [Fintype.card_fin, Nat.cast_ofNat] at hv
    change (∑ i, deriv (fun s ↦ normScaledAmplitude C tau (B (path s)) i) t ^ 2) ≤ _
    simp only [div_eq_mul_inv, mul_inv_rev] at h hmoment hv ⊢
    nlinarith only [h, hmoment, hv]

theorem exists_gaussian_line_partition {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (r : X → ℝ) (hr : ∀ x, 0 ≤ r x) (e : X → R3) (he : ∀ x, ‖e x‖ = 1)
    (hA : Continuous (fun x ↦ r x • InnerProductSpace.rankOne ℝ (e x) (e x)))
    (rho : ℝ) (hrho : 0 < rho) :
    ∃ centers : Finset X, centers.Nonempty ∧
      let tau := temperature centers.card rho
      let p := fun (i : ↑centers) x ↦ lineAmplitude (fun j : ↑centers ↦ r j.1)
        (fun j : ↑centers ↦ e j.1) tau (r x) (e x) i
      0 < tau ∧ (∀ i, Continuous (p i)) ∧
      (∀ x, (∑ i, p i x ^ 2) = r x ^ 2) ∧
      (∀ x, (∑ i, p i x ^ 2 * lineDistanceSq (e x) (e i.1)) ≤ rho ^ 2) ∧
      ∀ (path : ℝ → X) (t : ℝ) (V : Op),
        HasDerivAt (fun s ↦ r (path s) • InnerProductSpace.rankOne ℝ (e (path s)) (e (path s))) V t →
        (∑ i, deriv (fun s ↦ p i (path s)) t ^ 2) ≤
          3 * (1 + r (path t) ^ 2 * rho ^ 2 / (2 * tau ^ 2)) * ‖V‖ ^ 2 := by
  let B := fun x ↦ coordinateProjector (r x) (e x)
  have hB : Continuous B := (coordinates (ι := Fin 3)).continuous.comp hA
  obtain ⟨centers, hcover⟩ := PancakeAdaptiveStrainCover.exists_finite_adaptive_freezing_cover B hB
    (show 0 < rho / 2 by positivity)
  exact ⟨centers, gaussian_line_partition_of_cover r hr e he hA rho hrho centers hcover⟩

theorem temperature_pos (n : ℕ) (hn : 0 < n) (rho : ℝ) (hrho : 0 < rho) :
    0 < temperature n rho := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  exact div_pos (sq_pos_of_pos hrho) (by positivity)

theorem temperature_antitone_card (n m : ℕ) (hn : 0 < n) (hnm : n ≤ m) (rho : ℝ) :
    temperature m rho ≤ temperature n rho := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlog : Real.log (n : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log hn' (by exact_mod_cast hnm)
  unfold temperature
  exact div_le_div_of_nonneg_left (sq_nonneg rho) (by positivity) (by linarith)

end Mettapedia.FluidDynamics.NavierStokes.AdaptiveGaussianLinePartition
