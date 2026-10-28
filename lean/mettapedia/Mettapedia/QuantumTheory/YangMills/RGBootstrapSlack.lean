import Mettapedia.QuantumTheory.YangMills.RGBootstrap
import Mathlib.Tactic.FieldSimp

/-!
# Yang-Mills RG Bootstrap Slack

The manuscript's RG recursion for the irrelevant remainder has the scalar shape

  `x (j+1) ≤ a * x j + q * (x j)^2 + u j + v j`,

with `a = C1 * b^(3-dmax)`, `q = C1`, and two source terms `u j` (coupling
polynomial) and `v j` (large-field tail), each budgeted by `ε/4`.

This module proves the two-source invariant-ball closure: if `a ≤ 1/3`,
`q * ε ≤ (1 - a) / 4`, both sources stay `≤ ε/4`, and `x 0 ≤ ε`, then
`x j ≤ ε` for all `j ≤ J`.  The `1/3` threshold is strictly stronger than the
linear contraction `a < 1` recorded in `RGBootstrap`; the two conditions
separate at extraction depth `dmax = 15`:

* `dmax = 14`: `2224 * 2^-11 = 139/128 > 1` — no linear contraction;
* `dmax = 15`: `2224 * 2^-12 = 139/256 < 1` — linear contraction holds, but
  `139/256 > 1/3`, so the two-source bootstrap budget does **not** close;
* `dmax = 16`: `2224 * 2^-13 = 139/512 ≤ 1/3` — the bootstrap closes.

Hence with the advertised constant `C1 = 2224` and block factor `b = 2`, the
least depth with linear contraction is `15`, while the least depth supporting
the manuscript's two-`ε/4` source budget is `16`.

Scope: this is scalar real arithmetic and induction about the *shape* of the
RG recursion.  It does not derive `C1 = 2224`, does not construct the RG map,
and asserts nothing about the continuum Yang-Mills endpoint.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-- One-step gain of the extended-extraction recursion: the recursion constant
times the irrelevant scale `b^(3-dmax)`. -/
def rgGain (C : ℝ) (b dmax : ℕ) : ℝ :=
  C * irrelevantScale b dmax

/-- Two-source bootstrap slack: the one-step gain is at most `1/3`.  This is
the arithmetic condition under which the invariant-ball induction below closes
with the manuscript's two separate `ε/4` source budgets.  It is strictly
stronger than the linear condition `rgGain < 1` of
`HasExtendedExtractionContraction`. -/
def HasTwoSourceBootstrapSlack (C : ℝ) (b dmax : ℕ) : Prop :=
  0 ≤ C ∧ rgGain C b dmax ≤ (1 : ℝ) / 3

/-- The irrelevant scale is nonnegative for every natural block factor. -/
theorem irrelevantScale_nonneg (b dmax : ℕ) :
    0 ≤ irrelevantScale b dmax :=
  zpow_nonneg (Nat.cast_nonneg b) _

/-- Two-source bootstrap slack implies the linear extended-extraction
contraction. -/
theorem HasTwoSourceBootstrapSlack.toContraction
    {C : ℝ} {b dmax : ℕ}
    (h : HasTwoSourceBootstrapSlack C b dmax) :
    HasExtendedExtractionContraction C b dmax := by
  refine ⟨h.1, irrelevantScale_nonneg b dmax, ?_⟩
  have := h.2
  unfold rgGain at this
  linarith

/-- **Two-source scalar bootstrap closure.**  If the one-step linear gain
satisfies `a ≤ 1/3`, the quadratic budget satisfies `q * ε ≤ (1 - a) / 4`, the
two source sequences stay below `ε / 4` up to step `J`, and the recursion
`x (j+1) ≤ a * x j + q * (x j)^2 + u j + v j` holds up to step `J`, then the
ball `x ≤ ε` is invariant for all `j ≤ J`.

This is the scalar core of the manuscript's Proposition F.15 bootstrap with
its two independent `ε/4` source budgets.  Nothing here is specific to
Yang-Mills; the hypotheses are exactly the arithmetic obligations that the RG
estimates must eventually supply. -/
theorem scalar_bootstrap_two_sources
    {x u v : ℕ → ℝ} {J : ℕ} {a q ε : ℝ}
    (ha0 : 0 ≤ a)
    (ha13 : a ≤ (1 : ℝ) / 3)
    (hq0 : 0 ≤ q)
    (hε0 : 0 ≤ ε)
    (hquad : q * ε ≤ (1 - a) / 4)
    (hxnonneg : ∀ j, 0 ≤ x j)
    (hx0 : x 0 ≤ ε)
    (hu : ∀ j, j < J → u j ≤ ε / 4)
    (hv : ∀ j, j < J → v j ≤ ε / 4)
    (hrec : ∀ j, j < J →
      x (j + 1) ≤ a * x j + q * (x j) ^ 2 + u j + v j) :
    ∀ j, j ≤ J → x j ≤ ε := by
  intro j hj
  induction j with
  | zero => exact hx0
  | succ j ih =>
      have hjlt : j < J := Nat.lt_of_succ_le hj
      have hxj : x j ≤ ε := ih (Nat.le_of_lt hjlt)
      have hsq : (x j) ^ 2 ≤ ε ^ 2 := by
        nlinarith [hxnonneg j]
      have hlin : a * x j ≤ a * ε :=
        mul_le_mul_of_nonneg_left hxj ha0
      have hquadj : q * (x j) ^ 2 ≤ ((1 - a) * ε) / 4 := by
        have h1 : q * (x j) ^ 2 ≤ q * ε ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hq0
        nlinarith [mul_le_mul_of_nonneg_right hquad hε0]
      have hstep := hrec j hjlt
      have huj := hu j hjlt
      have hvj := hv j hjlt
      nlinarith [hstep, hlin, hquadj, huj, hvj, ha13, hε0]

/-- The invariant-ball radius selected by the manuscript for gain `a` and
quadratic constant `C`: `ε* = (1 - a) / (4 C)`. -/
def twoSourceEpsilonStar (C a : ℝ) : ℝ :=
  (1 - a) / (4 * C)

/-- At `ε = ε*`, the quadratic budget hypothesis of the bootstrap holds with
equality (for positive `C`). -/
theorem twoSourceEpsilonStar_quad_budget
    {C a : ℝ} (hC : 0 < C) :
    C * twoSourceEpsilonStar C a = (1 - a) / 4 := by
  unfold twoSourceEpsilonStar
  field_simp

/-- The advertised constants: exact one-step gain at `b = 2, dmax = 16`. -/
theorem rgGain_2224_two_sixteen :
    rgGain 2224 2 16 = (139 : ℝ) / 512 := by
  unfold rgGain
  exact rgGain_2224_two_sixteen_eq

/-- The advertised constants: exact one-step gain at `b = 2, dmax = 15`. -/
theorem rgGain_2224_two_fifteen :
    rgGain 2224 2 15 = (139 : ℝ) / 256 := by
  unfold rgGain
  exact rgGain_2224_two_fifteen_eq

/-- The advertised constants: exact one-step gain at `b = 2, dmax = 14`. -/
theorem rgGain_2224_two_fourteen :
    rgGain 2224 2 14 = (139 : ℝ) / 128 := by
  unfold rgGain
  exact rgGain_2224_two_fourteen_eq

/-- With the advertised constant, depth `16` has two-source bootstrap slack:
`139/512 ≤ 1/3`. -/
theorem twoSourceBootstrapSlack_2224_two_sixteen :
    HasTwoSourceBootstrapSlack 2224 2 16 := by
  refine ⟨by norm_num, ?_⟩
  rw [rgGain_2224_two_sixteen]
  norm_num

/-- With the advertised constant, depth `15` has **no** two-source bootstrap
slack: `139/256 > 1/3`, although linear contraction holds there
(`rgContraction_2224_two_fifteen`).  This is the machine-checked separation
between "linear contraction" and "bootstrap closure with two `ε/4` budgets". -/
theorem not_twoSourceBootstrapSlack_2224_two_fifteen :
    ¬ HasTwoSourceBootstrapSlack 2224 2 15 := by
  intro h
  have hg := h.2
  rw [rgGain_2224_two_fifteen] at hg
  norm_num at hg

/-- No depth `dmax ≤ 15` has two-source bootstrap slack with the advertised
constant `2224` at block factor `2`. -/
theorem not_twoSourceBootstrapSlack_2224_two_of_dmax_le_fifteen
    {dmax : ℕ} (hdmax : dmax ≤ 15) :
    ¬ HasTwoSourceBootstrapSlack 2224 2 dmax := by
  intro h
  have hg : (2224 : ℝ) * irrelevantScale 2 dmax ≤ 1 / 3 := h.2
  interval_cases dmax <;> norm_num [irrelevantScale] at hg

/-- Least-depth packet for the advertised constant `2224` at block factor `2`:
the least depth with linear contraction is `15`, and the least depth with
two-source bootstrap slack is `16`. -/
theorem leastDepth_2224_two_packet :
    (HasExtendedExtractionContraction 2224 2 15 ∧
      ∀ dmax : ℕ, dmax ≤ 14 → ¬ HasExtendedExtractionContraction 2224 2 dmax) ∧
    (HasTwoSourceBootstrapSlack 2224 2 16 ∧
      ∀ dmax : ℕ, dmax ≤ 15 → ¬ HasTwoSourceBootstrapSlack 2224 2 dmax) := by
  refine ⟨⟨rgContraction_2224_two_fifteen, ?_⟩,
    ⟨twoSourceBootstrapSlack_2224_two_sixteen, ?_⟩⟩
  · intro dmax hdmax
    exact not_rgContraction_2224_two_of_dmax_le_fourteen hdmax
  · intro dmax hdmax
    exact not_twoSourceBootstrapSlack_2224_two_of_dmax_le_fifteen hdmax

/-- The manuscript's invariant-ball radius for the advertised constants:
`ε* = (1 - 139/512) / (4 * 2224) = 373 / 4554752 ≈ 8.19e-5`. -/
def benTwoSourceEpsilonStar : ℝ :=
  twoSourceEpsilonStar 2224 (rgGain 2224 2 16)

theorem benTwoSourceEpsilonStar_eq :
    benTwoSourceEpsilonStar = (373 : ℝ) / 4554752 := by
  unfold benTwoSourceEpsilonStar twoSourceEpsilonStar
  rw [rgGain_2224_two_sixteen]
  norm_num

theorem benTwoSourceEpsilonStar_pos :
    0 < benTwoSourceEpsilonStar := by
  rw [benTwoSourceEpsilonStar_eq]
  norm_num

/-- **Bootstrap closure at the advertised constants.**  With gain
`a = 2224 * 2^(3-16) = 139/512`, quadratic constant `q = 2224`, and ball
radius `ε* = 373/4554752`, any nonnegative sequence starting inside the ball,
driven by the manuscript-shaped recursion with both sources `≤ ε*/4`, stays
inside the ball up to any horizon `J`.

Honest scope: the recursion hypothesis and the source bounds are inputs; only
their arithmetic closure is machine-checked here. -/
theorem ben_scalar_bootstrap_closure
    {x u v : ℕ → ℝ} {J : ℕ}
    (hxnonneg : ∀ j, 0 ≤ x j)
    (hx0 : x 0 ≤ benTwoSourceEpsilonStar)
    (hu : ∀ j, j < J → u j ≤ benTwoSourceEpsilonStar / 4)
    (hv : ∀ j, j < J → v j ≤ benTwoSourceEpsilonStar / 4)
    (hrec : ∀ j, j < J →
      x (j + 1) ≤ rgGain 2224 2 16 * x j + 2224 * (x j) ^ 2 + u j + v j) :
    ∀ j, j ≤ J → x j ≤ benTwoSourceEpsilonStar := by
  have hgain : rgGain 2224 2 16 = (139 : ℝ) / 512 := rgGain_2224_two_sixteen
  refine scalar_bootstrap_two_sources ?_ ?_ (by norm_num)
    (le_of_lt benTwoSourceEpsilonStar_pos) ?_ hxnonneg hx0 hu hv hrec
  · rw [hgain]; norm_num
  · rw [hgain]; norm_num
  · rw [hgain, benTwoSourceEpsilonStar_eq]
    norm_num

/-- Regression guard for the failure mode: at depth `15` the gain `139/256`
violates the `a ≤ 1/3` hypothesis of the closure theorem, so the manuscript's
two-`ε/4` budget cannot be certified there by this route. -/
theorem gain_two_fifteen_violates_one_third :
    (1 : ℝ) / 3 < rgGain 2224 2 15 := by
  rw [rgGain_2224_two_fifteen]
  norm_num

end YangMills
end QuantumTheory
end Mettapedia
