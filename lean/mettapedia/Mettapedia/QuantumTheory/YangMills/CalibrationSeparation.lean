import Mettapedia.QuantumTheory.YangMills.StrongCouplingCrossing

/-!
# Finite-torus separation for the free-field calibration

For each fixed integer displacement, sufficiently large tori preserve every
coordinate distance from the origin. Singleton link supports therefore satisfy
the eventual separation hypothesis of `CrossingInput.false_of_tendsto_dominating`,
with slope `1 / d`, zero offset, and support size one. The volume cutoff may
depend on the displacement; the slope and support bound do not.
-/

set_option autoImplicit false
noncomputable section

open Finset Filter MeasureTheory Topology
open Mettapedia.Combinatorics.PolymerGas
open Mettapedia.QuantumTheory.YangMills.StrongCouplingCrossing

namespace Mettapedia.QuantumTheory.YangMills.CalibrationSeparation

/-- Reduce an integer displacement coordinatewise to a torus site. -/
def displacementSite {d : ℕ} (n : ℕ) (k : Fin d → ℤ) : Site d n :=
  fun i => (k i : ZMod (n + 3))

/-- The link at the origin, with a fixed direction. -/
def firstSupport {d : ℕ} (μ : Fin d) (n : ℕ) (_k : Fin d → ℤ) : Finset (Link d n) :=
  {((0 : Site d n), μ)}

/-- The link at the displaced site, with the same direction. -/
def secondSupport {d : ℕ} (μ : Fin d) (n : ℕ) (k : Fin d → ℤ) : Finset (Link d n) :=
  {(displacementSite n k, μ)}

@[simp] theorem firstSupport_nonempty {d : ℕ} (μ : Fin d) (n : ℕ) (k : Fin d → ℤ) :
    (firstSupport μ n k).Nonempty := singleton_nonempty _

@[simp] theorem secondSupport_nonempty {d : ℕ} (μ : Fin d) (n : ℕ) (k : Fin d → ℤ) :
    (secondSupport μ n k).Nonempty := singleton_nonempty _

@[simp] theorem card_firstSupport {d : ℕ} (μ : Fin d) (n : ℕ) (k : Fin d → ℤ) :
    (firstSupport μ n k).card = 1 := card_singleton _

@[simp] theorem card_secondSupport {d : ℕ} (μ : Fin d) (n : ℕ) (k : Fin d → ℤ) :
    (secondSupport μ n k).card = 1 := card_singleton _

/-- The largest absolute coordinate, as a natural number. -/
def radius {d : ℕ} (k : Fin d → ℤ) : ℕ := univ.sup fun i => (k i).natAbs

theorem natAbs_le_radius {d : ℕ} (k : Fin d → ℤ) (i : Fin d) :
    (k i).natAbs ≤ radius k :=
  le_sup (f := fun j : Fin d => (k j).natAbs) (mem_univ i)

/-- Before wrapping around the circle, an integer coordinate retains its distance. -/
theorem coordinate_dist_eq_abs {n : ℕ} {j : ℤ}
    (hj : 2 * |(j : ℝ)| ≤ n + 3) :
    dist (coordinateCircle n 0) (coordinateCircle n (j : ZMod (n + 3))) = |(j : ℝ)| := by
  rw [map_zero, coordinateCircle_intCast, dist_zero_left]
  apply (AddCircle.norm_coe_eq_abs_iff (n + 3 : ℝ) (by positivity)).mpr
  rw [abs_of_pos (by positivity : (0 : ℝ) < n + 3)]
  linarith

theorem support_dist_eq {d : ℕ} (μ : Fin d) (n : ℕ) (k : Fin d → ℤ) :
    polymerDist (firstSupport μ n k) (secondSupport μ n k) =
      dist ((0 : Site d n), μ) (displacementSite n k, μ) := by
  simp [firstSupport, secondSupport, polymerDist, Metric.infDist_singleton, dist_comm]

/-- Every coordinate distance is bounded by the distance between the singleton supports. -/
theorem abs_coordinate_le_support_dist {d n : ℕ} (μ : Fin d) (k : Fin d → ℤ)
    (hsize : 2 * radius k ≤ n + 3) (i : Fin d) :
    |(k i : ℝ)| ≤ polymerDist (firstSupport μ n k) (secondSupport μ n k) := by
  have hi : 2 * (k i).natAbs ≤ n + 3 :=
    (Nat.mul_le_mul_left 2 (natAbs_le_radius k i)).trans hsize
  have hi' : 2 * |(k i : ℝ)| ≤ n + 3 := by
    have hc : (2 : ℝ) * ((k i).natAbs : ℝ) ≤ n + 3 := by exact_mod_cast hi
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hc
  rw [support_dist_eq, dist_link_eq]
  have h := dist_le_pi_dist (position ((0 : Site d n), μ))
    (position (displacementSite n k, μ)) i
  simpa only [position, displacementSite, Pi.zero_apply, coordinate_dist_eq_abs hi'] using h

/-- A concrete finite-volume separation bound whenever the side accommodates the displacement. -/
theorem separation_of_radius_le {d n : ℕ} (μ : Fin d) (k : Fin d → ℤ)
    (hsize : 2 * radius k ≤ n + 3) :
    (1 / (d : ℝ)) * ∑ i, |(k i : ℝ)| - 0 ≤
      polymerDist (firstSupport μ n k) (secondSupport μ n k) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d from Nat.zero_le μ.val |>.trans_lt μ.isLt)
  have hsum := sum_le_sum (s := (univ : Finset (Fin d)))
    (fun i _ => abs_coordinate_le_support_dist μ k hsize i)
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [sub_zero, one_div, ← div_eq_inv_mul, div_le_iff₀ hd]
  simpa only [mul_comm] using hsum

/-- The positive separation slope is independent of both displacement and volume. -/
theorem slope_pos {d : ℕ} (μ : Fin d) : (0 : ℝ) < 1 / (d : ℝ) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d from Nat.zero_le μ.val |>.trans_lt μ.isLt)
  positivity

/-- For every fixed displacement, the repaired calibration separation holds eventually. -/
theorem eventually_separation {d : ℕ} (μ : Fin d) (k : Fin d → ℤ) :
    ∀ᶠ n : ℕ in atTop, (1 / (d : ℝ)) * ∑ i, |(k i : ℝ)| - 0 ≤
      polymerDist (firstSupport μ n k) (secondSupport μ n k) := by
  refine (eventually_ge_atTop (2 * radius k)).mono fun n hn => ?_
  exact separation_of_radius_le μ k (by omega)

/-- All geometric hypotheses of the calibration, with `M = 1`, `α = 1/d`, and `β = 0`. -/
theorem calibration_geometry {d : ℕ} (μ : Fin d) :
    (0 : ℝ) < 1 / (d : ℝ) ∧ (0 : ℝ) ≤ 0 ∧
      (∀ n k, (firstSupport μ n k).Nonempty ∧ (secondSupport μ n k).Nonempty ∧
        (firstSupport μ n k).card ≤ 1 ∧ (secondSupport μ n k).card ≤ 1) ∧
      ∀ k, ∀ᶠ n : ℕ in atTop, (1 / (d : ℝ)) * ∑ i, |(k i : ℝ)| - 0 ≤
        polymerDist (firstSupport μ n k) (secondSupport μ n k) := by
  exact ⟨slope_pos μ, le_rfl, fun n k => by simp, eventually_separation μ⟩

section Calibration

variable {m : ℕ} {E : Type*} [MeasurableSpace E] [Nonempty E]
  (ν₀ : Measure E) [IsProbabilityMeasure ν₀]

/-- A concrete torus specialization: geometry is discharged, while the observable
limit and its domination of the free-field correlation remain explicit hypotheses. -/
theorem false_of_tendsto_dominating (μ : Fin (m + 3))
    {K : ∀ n (S : Finset (Link (m + 3) n)), (S → E) → ℂ}
    (h : CrossingInput.CrossingInput (Link (m + 3)) E K)
    (Λ : ∀ n, Finset (Finset (Link (m + 3) n)))
    (F₁ : ∀ n k, (firstSupport μ n k → E) → ℂ)
    (F₂ : ∀ n k, (secondSupport μ n k → E) → ℂ)
    (hF₁ : ∀ n k, Measurable (F₁ n k)) (hF₂ : ∀ n k, Measurable (F₂ n k))
    (hF₁b : ∀ n k v, ‖F₁ n k v‖ ≤ 1) (hF₂b : ∀ n k v, ‖F₂ n k v‖ ≤ 1)
    (T : (Fin (m + 3) → ℤ) → ℂ)
    (hT : ∀ k, Tendsto (fun n =>
      expectation ν₀ (fun ω => F₁ n k (restrictTo (firstSupport μ n k) ω) *
        F₂ n k (restrictTo (secondSupport μ n k) ω)) (K n) (Λ n) -
      expectation ν₀ (fun ω => F₁ n k (restrictTo (firstSupport μ n k) ω)) (K n) (Λ n) *
        expectation ν₀ (fun ω => F₂ n k (restrictTo (secondSupport μ n k) ω)) (K n) (Λ n))
      atTop (𝓝 (T k)))
    (A : ℝ) (hA : ∀ k, ‖FreeMaxwellNonClustering.fieldStrengthCorrelation (n := m) k‖ ≤
      A * ‖T k‖) : False := by
  exact CrossingInput.false_of_tendsto_dominating (ν₀ := ν₀) h Λ
    (firstSupport μ) (secondSupport μ) (firstSupport_nonempty μ) 1
    (fun n k => by simp) (fun n k => by simp) (1 / ((m + 3 : ℕ) : ℝ)) 0 (slope_pos μ)
    (eventually_separation μ) F₁ F₂ hF₁ hF₂ hF₁b hF₂b T hT A hA

end Calibration

#print axioms coordinate_dist_eq_abs
#print axioms separation_of_radius_le
#print axioms eventually_separation
#print axioms calibration_geometry
#print axioms false_of_tendsto_dominating

end Mettapedia.QuantumTheory.YangMills.CalibrationSeparation
