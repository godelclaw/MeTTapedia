import Mathlib.Tactic

/-!
# Weighted pressure pairing for retained viscous memory

In an orthonormal eigenbasis of `H = η I + C`, let `a` be its positive
eigenvalues and `d j i k` the spatial derivative of the memory tensor.
This file proves that the matrix metric paid by the entropy reserve
controls `div C` and its action on an arbitrary receiver vector.

The analytic pressure application integrates by parts against the
canonical pressure of the receiver tensor. Its remaining weighted
receiver norm is explicit and is not asserted to have an a priori bound.
The actual NS, stochastic and space-time identifications are in the lab
README. The last two lemmas describe the local rank-one geometric and
solenoidality defects, not an assumption that actual memory has rank one.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ViscousMemoryPressure

abbrev I := Fin 3

def mass (a : I → ℝ) : ℝ := ∑ i, a i

def metric (a : I → ℝ) (d : I → I → I → ℝ) : ℝ :=
  ∑ j, ∑ i, ∑ k, (d j i k) ^ 2 / (a i * a k)

def divergence (d : I → I → I → ℝ) (i : I) : ℝ := ∑ j, d j i j

def receiverCost (a v : I → ℝ) : ℝ := mass a * ∑ i, a i * (v i) ^ 2

theorem metric_nonneg (a : I → ℝ) (d : I → I → I → ℝ)
    (ha : ∀ i, 0 < a i) : 0 ≤ metric a d := by
  exact Finset.sum_nonneg (fun j _ ↦ Finset.sum_nonneg (fun i _ ↦
    Finset.sum_nonneg (fun k _ ↦ div_nonneg (sq_nonneg _) (mul_pos (ha i) (ha k)).le)))

/-- The full spatial tensor metric controls the weighted divergence.
No commutation of the spatial derivatives with `H` is assumed. -/
theorem divergence_metric_bound (a : I → ℝ) (d : I → I → I → ℝ)
    (ha : ∀ i, 0 < a i) :
    ∑ i, (divergence d i) ^ 2 / a i ≤ mass a * metric a d := by
  have hm : 0 ≤ mass a := Finset.sum_nonneg (fun i _ ↦ (ha i).le)
  have hi (i : I) : (divergence d i) ^ 2 / a i ≤
      mass a * ∑ j, (d j i j) ^ 2 / (a i * a j) := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      (s := Finset.univ) (r := fun j ↦ d j i j)
      (f := fun j ↦ (d j i j) ^ 2 / (a i * a j))
      (g := fun j ↦ a i * a j)
      (fun j _ ↦ div_nonneg (sq_nonneg _) (mul_pos (ha i) (ha j)).le)
      (fun j _ ↦ (mul_pos (ha i) (ha j)).le)
      (fun j _ ↦ by rw [div_mul_cancel₀ _ (mul_pos (ha i) (ha j)).ne'])
    rw [← Finset.mul_sum] at hcs
    apply (div_le_iff₀ (ha i)).2
    dsimp [divergence, mass] at *
    nlinarith only [hcs]
  calc
    _ ≤ ∑ i, mass a * ∑ j, (d j i j) ^ 2 / (a i * a j) :=
      Finset.sum_le_sum (fun i _ ↦ hi i)
    _ = mass a * ∑ j, ∑ i, (d j i j) ^ 2 / (a i * a j) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ mass a * metric a d := by
      apply mul_le_mul_of_nonneg_left _ hm
      exact Finset.sum_le_sum (fun j _ ↦ Finset.sum_le_sum (fun i _ ↦
        Finset.single_le_sum (fun k _ ↦
          div_nonneg (sq_nonneg _) (mul_pos (ha i) (ha k)).le) (Finset.mem_univ j)))

/-- The receiver vector is the gradient of the receiver's pressure in
the analytic integration-by-parts application. The bound retains its
anisotropic weight instead of assuming it bounded. -/
theorem pairing_sq_bound (a v : I → ℝ) (d : I → I → I → ℝ)
    (ha : ∀ i, 0 < a i) :
    (∑ i, divergence d i * v i) ^ 2 ≤ metric a d * receiverCost a v := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := Finset.univ) (r := fun i ↦ divergence d i * v i)
    (f := fun i ↦ (divergence d i) ^ 2 / a i)
    (g := fun i ↦ a i * (v i) ^ 2)
    (fun i _ ↦ div_nonneg (sq_nonneg _) (ha i).le)
    (fun i _ ↦ mul_nonneg (ha i).le (sq_nonneg _))
    (fun i _ ↦ by
      have he : (divergence d i * v i) ^ 2 =
          (divergence d i) ^ 2 / a i * (a i * (v i) ^ 2) := by
        field_simp [(ha i).ne']
      exact he.le)
  have hv : 0 ≤ ∑ i, a i * (v i) ^ 2 :=
    Finset.sum_nonneg (fun i _ ↦ mul_nonneg (ha i).le (sq_nonneg _))
  calc
    _ ≤ (∑ i, (divergence d i) ^ 2 / a i) * ∑ i, a i * (v i) ^ 2 := hcs
    _ ≤ (mass a * metric a d) * ∑ i, a i * (v i) ^ 2 :=
      mul_le_mul_of_nonneg_right (divergence_metric_bound a d ha) hv
    _ = _ := by unfold receiverCost; ring

/-- Young's inequality pays the memory factor and leaves the explicit
receiver cost. In the fluid application take `ε = α ν η`. -/
theorem pairing_paid (a v : I → ℝ) (d : I → I → I → ℝ)
    (ha : ∀ i, 0 < a i) (ε : ℝ) (hε : 0 < ε) :
    |∑ i, divergence d i * v i| ≤
      ε * metric a d + receiverCost a v / (4 * ε) := by
  have hf := metric_nonneg a d ha
  have hr : 0 ≤ receiverCost a v := mul_nonneg
    (Finset.sum_nonneg (fun i _ ↦ (ha i).le))
    (Finset.sum_nonneg (fun i _ ↦ mul_nonneg (ha i).le (sq_nonneg _)))
  have hcs := pairing_sq_bound a v d ha
  have he : metric a d * receiverCost a v =
      4 * (ε * metric a d) * (receiverCost a v / (4 * ε)) := by
    field_simp
  rw [he] at hcs
  have h₁ := mul_nonneg hε.le hf
  have h₂ := div_nonneg hr (show 0 ≤ 4 * ε by positivity)
  nlinarith [sq_abs (∑ i, divergence d i * v i),
    sq_nonneg (ε * metric a d - receiverCost a v / (4 * ε)),
    abs_nonneg (∑ i, divergence d i * v i)]

/-- At a unit direction `a=e₁`, its derivative has first row zero.
The six entries below are the remaining two rows. This pays curvature
and directional divergence together with constant two. -/
theorem rank_one_geometry_bound (r₁ r₂ r₃ s₁ s₂ s₃ : ℝ) :
    r₁ ^ 2 + s₁ ^ 2 + (r₂ + s₃) ^ 2 ≤
      2 * (r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2 + s₁ ^ 2 + s₂ ^ 2 + s₃ ^ 2) := by
  nlinarith [sq_nonneg r₁, sq_nonneg s₁, sq_nonneg r₃, sq_nonneg s₂,
    sq_nonneg (r₂ - s₃)]

/-- For `C=b² a⊗a`, the stress divergence has geometric part
`b²((a·∇)a-(div a)a)` and longitudinal defect `2b div(ba) a`.
This keeps that defect even when the orientation is coherent. -/
theorem rank_one_defect_bound (b δ r₁ r₂ r₃ s₁ s₂ s₃ : ℝ) :
    (-b ^ 2 * (r₂ + s₃) + 2 * b * δ) ^ 2 +
        (b ^ 2 * r₁) ^ 2 + (b ^ 2 * s₁) ^ 2 ≤
      4 * b ^ 4 * (r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2 + s₁ ^ 2 + s₂ ^ 2 + s₃ ^ 2) +
        8 * b ^ 2 * δ ^ 2 := by
  have h := mul_le_mul_of_nonneg_left
    (rank_one_geometry_bound r₁ r₂ r₃ s₁ s₂ s₃) (sq_nonneg (b ^ 2))
  nlinarith [sq_nonneg (b ^ 2 * (r₂ + s₃) + 2 * b * δ),
    sq_nonneg (b ^ 2 * r₁), sq_nonneg (b ^ 2 * s₁)]

end Mettapedia.FluidDynamics.NavierStokes.ViscousMemoryPressure
