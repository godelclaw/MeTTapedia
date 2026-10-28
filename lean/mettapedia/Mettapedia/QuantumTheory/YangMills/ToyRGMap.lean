import Mettapedia.QuantumTheory.YangMills.RGBootstrapSlack

/-!
# Toy RG dynamics inhabiting the bootstrap slack

An explicit nonlinear finite-dimensional dynamical system whose norm
recursion is *exactly* the manuscript-shaped two-source bootstrap
recursion, with the manuscript constants:

* the state carries the irrelevant-remainder norm `x`, a coupling-polynomial
  source `u`, and a large-field-tail source `v`;
* one step maps `x ↦ a x + q x² + u + v` and damps each source by a factor
  in `[0, 1]`;
* with `a = rgGain C b dmax` and `q = C` the recursion is the hypothesis of
  `scalar_bootstrap_two_sources` with equality, so the slack predicate
  `HasTwoSourceBootstrapSlack C b dmax` yields invariance of the
  `ε* = (1-a)/(4C)` ball for genuine (non-affine) dynamics
  (`toyRG_invariant_ball_of_slack`, `toyRG_ben_invariant_ball` at
  `C = 2224, b = 2, dmax = 16`);
* conversely, whenever the gain exceeds `1/3` — in particular at the
  advertised constants with depth `dmax = 15`, where linear contraction
  still holds — the same dynamics exits the `ε*` ball in one step from the
  boundary with full source budgets (`toyRG_ball_escape_of_gain_gt_third`,
  `toyRG_ball_escape_two_fifteen`).  The `1/3` threshold of the two-source
  bootstrap is therefore dynamically sharp for this map, not merely an
  artifact of the induction;
* the map is genuinely nonlinear: the second difference of the `x`-component
  equals `2 q t²` (`toyRGStep_second_difference`), nonzero for `q ≠ 0`.

Honest scope: this is a toy dynamical system realizing the *shape* and the
*constants* of the manuscript's RG recursion.  It is not the Yang-Mills RG
map; deriving that map's recursion inequality (and the constant `C`) remains
the open analytic input.  No continuum statement is made.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-- State of the toy RG flow: the irrelevant-remainder norm `x`, the
coupling-polynomial source `u`, and the large-field-tail source `v`. -/
structure ToyRGState where
  x : ℝ
  u : ℝ
  v : ℝ

/-- One step of the toy RG dynamics: quadratic recursion on the remainder
norm driven by the two sources, with each source damped by its own factor. -/
def toyRGStep (a q σu σv : ℝ) (s : ToyRGState) : ToyRGState where
  x := a * s.x + q * s.x ^ 2 + s.u + s.v
  u := σu * s.u
  v := σv * s.v

@[simp] theorem toyRGStep_x (a q σu σv : ℝ) (s : ToyRGState) :
    (toyRGStep a q σu σv s).x = a * s.x + q * s.x ^ 2 + s.u + s.v := rfl

@[simp] theorem toyRGStep_u (a q σu σv : ℝ) (s : ToyRGState) :
    (toyRGStep a q σu σv s).u = σu * s.u := rfl

@[simp] theorem toyRGStep_v (a q σu σv : ℝ) (s : ToyRGState) :
    (toyRGStep a q σu σv s).v = σv * s.v := rfl

/-- The orbit of the toy RG dynamics. -/
def toyRGOrbit (a q σu σv : ℝ) (s0 : ToyRGState) : ℕ → ToyRGState
  | 0 => s0
  | j + 1 => toyRGStep a q σu σv (toyRGOrbit a q σu σv s0 j)

@[simp] theorem toyRGOrbit_zero (a q σu σv : ℝ) (s0 : ToyRGState) :
    toyRGOrbit a q σu σv s0 0 = s0 := rfl

@[simp] theorem toyRGOrbit_succ (a q σu σv : ℝ) (s0 : ToyRGState) (j : ℕ) :
    toyRGOrbit a q σu σv s0 (j + 1)
      = toyRGStep a q σu σv (toyRGOrbit a q σu σv s0 j) := rfl

/-! ## Elementary orbit facts -/

/-- The sources evolve by exact geometric damping. -/
theorem toyRGOrbit_u_eq (a q σu σv : ℝ) (s0 : ToyRGState) (j : ℕ) :
    (toyRGOrbit a q σu σv s0 j).u = σu ^ j * s0.u := by
  induction j with
  | zero => simp
  | succ j ih => rw [toyRGOrbit_succ, toyRGStep_u, ih, pow_succ]; ring

theorem toyRGOrbit_v_eq (a q σu σv : ℝ) (s0 : ToyRGState) (j : ℕ) :
    (toyRGOrbit a q σu σv s0 j).v = σv ^ j * s0.v := by
  induction j with
  | zero => simp
  | succ j ih => rw [toyRGOrbit_succ, toyRGStep_v, ih, pow_succ]; ring

/-- Nonnegative data stay nonnegative along the orbit. -/
theorem toyRGOrbit_nonneg
    {a q σu σv : ℝ} (ha : 0 ≤ a) (hq : 0 ≤ q)
    (hσu : 0 ≤ σu) (hσv : 0 ≤ σv)
    {s0 : ToyRGState} (hx : 0 ≤ s0.x) (hu : 0 ≤ s0.u) (hv : 0 ≤ s0.v)
    (j : ℕ) :
    0 ≤ (toyRGOrbit a q σu σv s0 j).x ∧
      0 ≤ (toyRGOrbit a q σu σv s0 j).u ∧
      0 ≤ (toyRGOrbit a q σu σv s0 j).v := by
  induction j with
  | zero => exact ⟨hx, hu, hv⟩
  | succ j ih =>
      obtain ⟨ihx, ihu, ihv⟩ := ih
      refine ⟨?_, mul_nonneg hσu ihu, mul_nonneg hσv ihv⟩
      have h1 : 0 ≤ a * (toyRGOrbit a q σu σv s0 j).x := mul_nonneg ha ihx
      have h2 : 0 ≤ q * (toyRGOrbit a q σu σv s0 j).x ^ 2 :=
        mul_nonneg hq (sq_nonneg _)
      rw [toyRGOrbit_succ, toyRGStep_x]
      linarith

/-- Damped sources never exceed their initial budget. -/
theorem toyRGOrbit_u_le
    {σu : ℝ} (hσu0 : 0 ≤ σu) (hσu1 : σu ≤ 1)
    {s0 : ToyRGState} (hu : 0 ≤ s0.u)
    (a q σv : ℝ) (j : ℕ) :
    (toyRGOrbit a q σu σv s0 j).u ≤ s0.u := by
  rw [toyRGOrbit_u_eq]
  exact mul_le_of_le_one_left hu (pow_le_one₀ hσu0 hσu1)

theorem toyRGOrbit_v_le
    {σv : ℝ} (hσv0 : 0 ≤ σv) (hσv1 : σv ≤ 1)
    {s0 : ToyRGState} (hv : 0 ≤ s0.v)
    (a q σu : ℝ) (j : ℕ) :
    (toyRGOrbit a q σu σv s0 j).v ≤ s0.v := by
  rw [toyRGOrbit_v_eq]
  exact mul_le_of_le_one_left hv (pow_le_one₀ hσv0 hσv1)

/-- The orbit's norm sequence satisfies the manuscript-shaped two-source
recursion with *equality*. -/
theorem toyRGOrbit_x_recursion (a q σu σv : ℝ) (s0 : ToyRGState) (j : ℕ) :
    (toyRGOrbit a q σu σv s0 (j + 1)).x
      = a * (toyRGOrbit a q σu σv s0 j).x
        + q * (toyRGOrbit a q σu σv s0 j).x ^ 2
        + (toyRGOrbit a q σu σv s0 j).u
        + (toyRGOrbit a q σu σv s0 j).v := rfl

/-! ## Genuine nonlinearity -/

/-- The second difference of the `x`-component in the `x`-direction is
`2 q t²`: the step map is not affine for `q ≠ 0`. -/
theorem toyRGStep_second_difference (a q σu σv t : ℝ) :
    (toyRGStep a q σu σv ⟨2 * t, 0, 0⟩).x
        - 2 * (toyRGStep a q σu σv ⟨t, 0, 0⟩).x
        + (toyRGStep a q σu σv ⟨0, 0, 0⟩).x
      = 2 * q * t ^ 2 := by
  simp only [toyRGStep_x]
  ring

/-- Nonlinearity witness at the manuscript quadratic constant `q = 2224`. -/
theorem toyRGStep_not_affine_at_manuscript_constants (a σu σv : ℝ) :
    (toyRGStep a 2224 σu σv ⟨2, 0, 0⟩).x
        - 2 * (toyRGStep a 2224 σu σv ⟨1, 0, 0⟩).x
        + (toyRGStep a 2224 σu σv ⟨0, 0, 0⟩).x
      ≠ 0 := by
  simp only [toyRGStep_x]
  intro h
  nlinarith [h]

/-! ## Slack implies invariant ball for the dynamics -/

/-- **Two-source bootstrap slack makes the `ε*` ball invariant for the toy
dynamics.**  With linear gain `a = rgGain C b dmax`, quadratic constant `C`,
and both sources damped within their `ε*/4` budgets, every orbit starting in
the ball `x ≤ ε* = (1-a)/(4C)` stays in it.  The proof feeds the orbit's
exact recursion into `scalar_bootstrap_two_sources`; the slack `a ≤ 1/3` is
exactly the hypothesis that closes the induction. -/
theorem toyRG_invariant_ball_of_slack
    {C : ℝ} {b dmax : ℕ} {σu σv : ℝ}
    (hC : 0 < C)
    (hslack : HasTwoSourceBootstrapSlack C b dmax)
    (hσu0 : 0 ≤ σu) (hσu1 : σu ≤ 1) (hσv0 : 0 ≤ σv) (hσv1 : σv ≤ 1)
    {s0 : ToyRGState} (hx0 : 0 ≤ s0.x) (hu0 : 0 ≤ s0.u) (hv0 : 0 ≤ s0.v)
    (hx : s0.x ≤ twoSourceEpsilonStar C (rgGain C b dmax))
    (hu : s0.u ≤ twoSourceEpsilonStar C (rgGain C b dmax) / 4)
    (hv : s0.v ≤ twoSourceEpsilonStar C (rgGain C b dmax) / 4)
    (j : ℕ) :
    (toyRGOrbit (rgGain C b dmax) C σu σv s0 j).x
      ≤ twoSourceEpsilonStar C (rgGain C b dmax) := by
  set a := rgGain C b dmax with ha_def
  have ha0 : 0 ≤ a := mul_nonneg hC.le (irrelevantScale_nonneg b dmax)
  have ha13 : a ≤ (1 : ℝ) / 3 := hslack.2
  have hε0 : 0 ≤ twoSourceEpsilonStar C a := by
    unfold twoSourceEpsilonStar
    have h1a : 0 ≤ 1 - a := by linarith
    positivity
  have hquad : C * twoSourceEpsilonStar C a ≤ (1 - a) / 4 :=
    le_of_eq (twoSourceEpsilonStar_quad_budget hC)
  have h := scalar_bootstrap_two_sources
    (x := fun k => (toyRGOrbit a C σu σv s0 k).x)
    (u := fun k => (toyRGOrbit a C σu σv s0 k).u)
    (v := fun k => (toyRGOrbit a C σu σv s0 k).v)
    (J := j) (a := a) (q := C) (ε := twoSourceEpsilonStar C a)
    ha0 ha13 hC.le hε0 hquad
    (fun k => (toyRGOrbit_nonneg ha0 hC.le hσu0 hσv0 hx0 hu0 hv0 k).1)
    hx
    (fun k _ => le_trans (toyRGOrbit_u_le hσu0 hσu1 hu0 a C σv k) hu)
    (fun k _ => le_trans (toyRGOrbit_v_le hσv0 hσv1 hv0 a C σu k) hv)
    (fun k _ => le_of_eq (toyRGOrbit_x_recursion a C σu σv s0 k))
  exact h j le_rfl

/-- **Invariant ball at the manuscript constants.**  At `C = 2224, b = 2,
dmax = 16` (gain `139/512 ≤ 1/3`), the toy dynamics keeps every admissible
orbit inside the ball of radius `ε* = 373/4554752`. -/
theorem toyRG_ben_invariant_ball
    {σu σv : ℝ}
    (hσu0 : 0 ≤ σu) (hσu1 : σu ≤ 1) (hσv0 : 0 ≤ σv) (hσv1 : σv ≤ 1)
    {s0 : ToyRGState} (hx0 : 0 ≤ s0.x) (hu0 : 0 ≤ s0.u) (hv0 : 0 ≤ s0.v)
    (hx : s0.x ≤ benTwoSourceEpsilonStar)
    (hu : s0.u ≤ benTwoSourceEpsilonStar / 4)
    (hv : s0.v ≤ benTwoSourceEpsilonStar / 4)
    (j : ℕ) :
    (toyRGOrbit (rgGain 2224 2 16) 2224 σu σv s0 j).x
      ≤ benTwoSourceEpsilonStar :=
  toyRG_invariant_ball_of_slack (by norm_num)
    twoSourceBootstrapSlack_2224_two_sixteen
    hσu0 hσu1 hσv0 hσv1 hx0 hu0 hv0 hx hu hv j

/-! ## Sharpness: gain above `1/3` escapes the ball in one step -/

/-- **The `1/3` threshold is dynamically sharp.**  For any gain
`1/3 < a < 1`, starting on the boundary of the `ε*` ball with full `ε*/4`
source budgets, one step of the same toy dynamics exits the ball:
the image is `ε* (3a + 3)/4 > ε*`. -/
theorem toyRG_ball_escape_of_gain_gt_third
    {C a : ℝ} (σu σv : ℝ) (hC : 0 < C) (ha1 : a < 1) (ha : (1 : ℝ) / 3 < a) :
    twoSourceEpsilonStar C a <
      (toyRGOrbit a C σu σv
        ⟨twoSourceEpsilonStar C a,
          twoSourceEpsilonStar C a / 4,
          twoSourceEpsilonStar C a / 4⟩ 1).x := by
  have hε : 0 < twoSourceEpsilonStar C a := by
    unfold twoSourceEpsilonStar
    have h1a : 0 < 1 - a := by linarith
    positivity
  have hCε : C * twoSourceEpsilonStar C a = (1 - a) / 4 :=
    twoSourceEpsilonStar_quad_budget hC
  have hx1 : (toyRGOrbit a C σu σv
      ⟨twoSourceEpsilonStar C a,
        twoSourceEpsilonStar C a / 4,
        twoSourceEpsilonStar C a / 4⟩ 1).x
      = a * twoSourceEpsilonStar C a
        + C * twoSourceEpsilonStar C a ^ 2
        + twoSourceEpsilonStar C a / 4
        + twoSourceEpsilonStar C a / 4 := rfl
  have hsq : C * twoSourceEpsilonStar C a ^ 2
      = (1 - a) / 4 * twoSourceEpsilonStar C a := by
    rw [pow_two, ← mul_assoc, hCε]
  rw [hx1, hsq]
  nlinarith [hε, ha]

/-- **One-step escape at depth `15` with the advertised constant.**  At
`C = 2224, b = 2, dmax = 15` the gain is `139/256`: linear contraction holds
(`139/256 < 1`), yet the toy dynamics exits the corresponding `ε*` ball in a
single step.  Together with `toyRG_ben_invariant_ball` this realizes the
depth-15/16 trichotomy as a fact about genuine dynamics. -/
theorem toyRG_ball_escape_two_fifteen (σu σv : ℝ) :
    twoSourceEpsilonStar 2224 (rgGain 2224 2 15) <
      (toyRGOrbit (rgGain 2224 2 15) 2224 σu σv
        ⟨twoSourceEpsilonStar 2224 (rgGain 2224 2 15),
          twoSourceEpsilonStar 2224 (rgGain 2224 2 15) / 4,
          twoSourceEpsilonStar 2224 (rgGain 2224 2 15) / 4⟩ 1).x := by
  refine toyRG_ball_escape_of_gain_gt_third σu σv (by norm_num) ?_ ?_
  · rw [rgGain_2224_two_fifteen]; norm_num
  · exact gain_two_fifteen_violates_one_third

/-! ## The realization packet -/

/-- A toy dynamical realization of the bootstrap predicates at constants
`(C, b, dmax)`: the slack and contraction predicates hold, the `ε*` ball is
invariant for the explicit dynamics, and the dynamics is genuinely
nonlinear. -/
structure ToyRGBootstrapRealization (C : ℝ) (b dmax : ℕ) : Prop where
  slack : HasTwoSourceBootstrapSlack C b dmax
  contraction : HasExtendedExtractionContraction C b dmax
  ballInvariant :
    ∀ {σu σv : ℝ}, 0 ≤ σu → σu ≤ 1 → 0 ≤ σv → σv ≤ 1 →
      ∀ {s0 : ToyRGState}, 0 ≤ s0.x → 0 ≤ s0.u → 0 ≤ s0.v →
        s0.x ≤ twoSourceEpsilonStar C (rgGain C b dmax) →
        s0.u ≤ twoSourceEpsilonStar C (rgGain C b dmax) / 4 →
        s0.v ≤ twoSourceEpsilonStar C (rgGain C b dmax) / 4 →
        ∀ j : ℕ,
          (toyRGOrbit (rgGain C b dmax) C σu σv s0 j).x
            ≤ twoSourceEpsilonStar C (rgGain C b dmax)
  nonlinear :
    ∃ t : ℝ,
      (toyRGStep (rgGain C b dmax) C 1 1 ⟨2 * t, 0, 0⟩).x
          - 2 * (toyRGStep (rgGain C b dmax) C 1 1 ⟨t, 0, 0⟩).x
          + (toyRGStep (rgGain C b dmax) C 1 1 ⟨0, 0, 0⟩).x
        ≠ 0

/-- **The manuscript constants are genuinely realized by dynamics.**  At
`C = 2224, b = 2, dmax = 16` the toy RG map inhabits both
`HasTwoSourceBootstrapSlack` and `HasExtendedExtractionContraction` with a
nonlinear invariant-ball dynamical system, not just as bare arithmetic. -/
theorem benToyRGBootstrapRealization :
    ToyRGBootstrapRealization 2224 2 16 where
  slack := twoSourceBootstrapSlack_2224_two_sixteen
  contraction := twoSourceBootstrapSlack_2224_two_sixteen.toContraction
  ballInvariant := by
    intro σu σv hσu0 hσu1 hσv0 hσv1 s0 hx0 hu0 hv0 hx hu hv j
    exact toyRG_invariant_ball_of_slack (by norm_num)
      twoSourceBootstrapSlack_2224_two_sixteen
      hσu0 hσu1 hσv0 hσv1 hx0 hu0 hv0 hx hu hv j
  nonlinear := by
    refine ⟨1, ?_⟩
    rw [toyRGStep_second_difference]
    norm_num

end YangMills
end QuantumTheory
end Mettapedia
