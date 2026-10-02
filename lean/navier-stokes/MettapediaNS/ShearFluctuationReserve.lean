import MettapediaNS.GeneratedMeanEnstrophy

/-!
# A parent-dependent reserve and a quadratic-weight obstruction

The companion periodic shear calculation identifies `a` with a nonnegative
decaying parent amplitude, `Z` with full enstrophy, and `D` with its gradient
dissipation. This module certifies scalar reserve calculus and the spectral
weight recurrence. The PDE identities and the universal quadratic-storage
obstruction's realization by smooth NS data remain analytic.

The reserve pays the actual fluctuation stretching for the triangular class.
Mutual parent renewal contributes an explicit defect; it is not controlled
here. No arbitrary-data regularity theorem is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ShearFluctuationReserve

def reserve (c a Z : ℝ) : ℝ := (Real.exp (c * a) - 1) * Z

def rate (c a Z a' Z' : ℝ) : ℝ :=
  (Real.exp (c * a) - 1) * Z' + c * Real.exp (c * a) * a' * Z

theorem reserve_nonneg (c a Z : ℝ) (hc : 0 ≤ c) (ha : 0 ≤ a) (hZ : 0 ≤ Z) :
    0 ≤ reserve c a Z := by
  exact mul_nonneg (sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hc ha))) hZ

theorem reserve_derivative (c t : ℝ) (a Z : ℝ → ℝ) (a' Z' : ℝ)
    (ha : HasDerivAt a a' t) (hZ : HasDerivAt Z Z' t) :
    HasDerivAt (fun s ↦ reserve c (a s) (Z s))
      (rate c (a t) (Z t) a' Z') t := by
  have hd := (((ha.const_mul c).exp).sub_const 1).mul hZ
  change HasDerivAt (fun s ↦ reserve c (a s) (Z s)) _ t at hd
  apply hd.congr_deriv
  unfold rate
  ring

/-- The parent source `F`, receiver defect `L`, and additional observed
stretching `extra` survive. Their physical payment is a separate obligation. -/
theorem payment_with_defects (ν c a Z D a' Z' F L g extra : ℝ)
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hprice : c * (2 * ν) = 4)
    (ha' : a' = -2 * ν * a + F)
    (hZ' : Z' ≤ 4 * a * Z - 2 * ν * D + L)
    (hg : 2 * g ≤ 4 * a * Z + extra) :
    rate c a Z a' Z' + 2 * g + 2 * ν * (Real.exp (c * a) - 1) * D ≤
      (Real.exp (c * a) - 1) * L + c * Real.exp (c * a) * F * Z + extra := by
  have hv := sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hc ha))
  have hm := mul_le_mul_of_nonneg_left hZ' hv
  have heq : c * Real.exp (c * a) * a' * Z =
      -4 * Real.exp (c * a) * a * Z + c * Real.exp (c * a) * F * Z := by
    rw [ha']
    calc
      _ = -(c * (2 * ν)) * Real.exp (c * a) * a * Z +
          c * Real.exp (c * a) * F * Z := by ring
      _ = _ := by rw [hprice]
  unfold rate
  rw [heq]
  nlinarith only [hm, hg]

theorem decaying_parent_payment (ν c a Z D a' Z' g : ℝ)
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hprice : c * (2 * ν) = 4)
    (ha' : a' = -2 * ν * a) (hZ' : Z' ≤ 4 * a * Z - 2 * ν * D)
    (hg : 2 * g ≤ 4 * a * Z) :
    rate c a Z a' Z' + 2 * g + 2 * ν * (Real.exp (c * a) - 1) * D ≤ 0 := by
  simpa using payment_with_defects ν c a Z D a' Z' 0 0 g 0 hc ha hprice
    (by simpa using ha') (by simpa using hZ') (by simpa using hg)

theorem price (ν : ℝ) (hν : ν ≠ 0) : (2 / ν) * (2 * ν) = 4 := by
  field_simp
  ring

def radius (n : ℕ) : ℝ := (n : ℝ)^2 + ((n : ℝ) + 1)^2

theorem adjusted_weight_constant (ρ : ℕ → ℝ) (n : ℕ) :
    (∀ j < n, ρ (j+1) + radius (j+1) = ρ j + radius j) →
      ρ n + radius n = ρ 0 + 1 := by
  induction n with
  | zero => intro _; simp [radius]
  | succ n ih =>
    intro h
    exact (h n (Nat.lt_succ_self n)).trans
      (ih (fun j hj ↦ h j (Nat.lt_trans hj (Nat.lt_succ_self n))))

/-- A finite chain can be balanced only by charging its largest spectral
radius already to the lowest receiver. This does not claim NS closure. -/
theorem finite_chain_cost (ρ : ℕ → ℝ) (n : ℕ) (hn : 0 ≤ ρ n)
    (h : ∀ j < n, ρ (j+1) + radius (j+1) = ρ j + radius j) :
    2 * (n : ℝ) * ((n : ℝ) + 1) ≤ ρ 0 := by
  have he := adjusted_weight_constant ρ n h
  unfold radius at he
  nlinarith only [he, hn]

theorem no_nonnegative_balanced_weights :
    ¬ ∃ ρ : ℕ → ℝ, (∀ n, 0 ≤ ρ n) ∧
      (∀ n, ρ (n+1) + radius (n+1) = ρ n + radius n) := by
  rintro ⟨ρ, hρ, h⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (ρ 0 + 1)
  have hcost := finite_chain_cost ρ n (hρ n) (fun j _ ↦ h j)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [sq_nonneg (n : ℝ)]

end Mettapedia.FluidDynamics.NavierStokes.ShearFluctuationReserve
