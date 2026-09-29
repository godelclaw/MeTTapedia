import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StrainCycleDiffusion
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# A coercive envelope of the physical pressure and strain core

The physical moments are `Q=tr(S²)`, `W=|ω|²`, `V=ω·Sω`,
`Z=|Sω|²`, and `N=ω·Pω`. Regularizing `V²/W` by `V²/(W+η)`
retains a smooth expression at vorticity zeros. A smooth maximum with
the nonnegative core removes the directional-pressure sign hypothesis.

This file certifies coercivity, an explicit initial-moment upper bound,
the scalar switching derivatives, and a fixed-radius source conversion.
The actual NS branch equations are analytic and independently checked
in `labs/pressure_core_envelope.py`. Their remaining signed production
has no arbitrary-history bound here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureCoreEnvelope

def pressure (η W V N : ℝ) : ℝ :=
  5 * V ^ 2 / (W + η) + (63/95) * W ^ 2 - 2 * N

def core (η Q W V Z : ℝ) : ℝ :=
  5 * V ^ 2 / (W + η) + (4/7) * Z + (10/21) * Q * W + (44/95) * W ^ 2

def smoothPositive (δ g : ℝ) : ℝ := (g + Real.sqrt (g ^ 2 + δ ^ 2)) / 2

def weight (δ g : ℝ) : ℝ := (1 + g / Real.sqrt (g ^ 2 + δ ^ 2)) / 2

def curvature (δ g : ℝ) : ℝ :=
  δ ^ 2 / (2 * Real.sqrt (g ^ 2 + δ ^ 2) ^ 3)

def reserve (η δ Q W V Z N : ℝ) : ℝ :=
  1 + core η Q W V Z + smoothPositive δ (pressure η W V N - core η Q W V Z)

theorem pressure_sub_core (η Q W V Z N : ℝ) :
    pressure η W V N - core η Q W V Z =
      -2 * (N - StrainCycleDiffusion.corePressurePair Q W Z) := by
  dsimp [pressure, core, StrainCycleDiffusion.corePressurePair]
  ring

theorem smoothPositive_nonneg (δ g : ℝ) : 0 ≤ smoothPositive δ g := by
  have h := Real.abs_le_sqrt (show g ^ 2 ≤ g ^ 2 + δ ^ 2 by nlinarith [sq_nonneg δ])
  have hl := (abs_le.mp h).1
  dsimp [smoothPositive]
  linarith

theorem smoothPositive_le_max (δ g : ℝ) (hδ : 0 ≤ δ) :
    smoothPositive δ g ≤ max g 0 + δ / 2 := by
  have hs : Real.sqrt (g ^ 2 + δ ^ 2) ≤ |g| + δ := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith [sq_abs g, mul_nonneg (abs_nonneg g) hδ]
  dsimp [smoothPositive]
  rcases le_total 0 g with hg | hg
  · rw [abs_of_nonneg hg] at hs
    rw [max_eq_left hg]
    linarith
  · rw [abs_of_nonpos hg] at hs
    rw [max_eq_right hg]
    linarith

theorem core_coercive (η Q W V Z : ℝ) (hη : 0 < η)
    (hQ : 0 ≤ Q) (hW : 0 ≤ W) (hZ : 0 ≤ Z) :
    (44/95) * W ^ 2 ≤ core η Q W V Z := by
  have h : 0 ≤ 5 * V ^ 2 / (W + η) + (4/7) * Z + (10/21) * Q * W := by
    positivity
  dsimp [core]
  linarith

/-- This lower bound has no condition on the physical pressure. -/
theorem reserve_coercive (η δ Q W V Z N : ℝ) (hη : 0 < η)
    (hQ : 0 ≤ Q) (hW : 0 ≤ W) (hZ : 0 ≤ Z) :
    1 + (44/95) * W ^ 2 ≤ reserve η δ Q W V Z N := by
  have hc := core_coercive η Q W V Z hη hQ hW hZ
  have hs := smoothPositive_nonneg δ (pressure η W V N - core η Q W V Z)
  dsimp [reserve]
  linarith

theorem reserve_le_of_branches_le (η δ Q W V Z N B : ℝ) (hδ : 0 ≤ δ)
    (hp : pressure η W V N ≤ B) (hc : core η Q W V Z ≤ B) :
    reserve η δ Q W V Z N ≤ 1 + B + δ / 2 := by
  have hs := smoothPositive_le_max δ (pressure η W V N - core η Q W V Z) hδ
  have hm : max (pressure η W V N - core η Q W V Z) 0 ≤ B - core η Q W V Z := by
    apply max_le <;> linarith
  dsimp [reserve]
  linarith

/-- The moment hypotheses follow from the matrix Cauchy--Schwarz
inequality and a bound `p` on the pressure Hessian operator norm.
This theorem supplies a finite initial value, not a future bound. -/
theorem reserve_initial_upper (η δ Q W V Z N p : ℝ) (hη : 0 < η)
    (hδ : 0 ≤ δ) (hQ : 0 ≤ Q) (hW : 0 ≤ W) (hZ : 0 ≤ Z) (hp : 0 ≤ p)
    (hV : V ^ 2 ≤ W * Z) (hZQ : Z ≤ Q * W) (hN : -p * W ≤ N) :
    reserve η δ Q W V Z N ≤
      1 + δ / 2 + (127/21) * Q * W + (63/95) * W ^ 2 + 2 * p * W := by
  have hd : 0 < W + η := by linarith
  have ht : V ^ 2 / (W + η) ≤ Z := by
    apply (div_le_iff₀ hd).2
    nlinarith [mul_nonneg hZ hη.le]
  have hpw := mul_nonneg hp hW
  have hqw := mul_nonneg hQ hW
  have hc : core η Q W V Z ≤ (127/21) * Q * W + (63/95) * W ^ 2 + 2 * p * W := by
    dsimp [core]
    rw [show 5 * V ^ 2 / (W + η) = 5 * (V ^ 2 / (W + η)) by ring]
    nlinarith [sq_nonneg W]
  have hpr : pressure η W V N ≤ (127/21) * Q * W + (63/95) * W ^ 2 + 2 * p * W := by
    dsimp [pressure]
    rw [show 5 * V ^ 2 / (W + η) = 5 * (V ^ 2 / (W + η)) by ring]
    nlinarith
  have hb := reserve_le_of_branches_le η δ Q W V Z N _ hδ hpr hc
  linarith

private theorem root_pos (δ g : ℝ) (hδ : 0 < δ) :
    0 < Real.sqrt (g ^ 2 + δ ^ 2) := by
  apply Real.sqrt_pos.2
  nlinarith [sq_nonneg g, sq_pos_of_pos hδ]

theorem weight_mem (δ g : ℝ) (hδ : 0 < δ) : 0 ≤ weight δ g ∧ weight δ g ≤ 1 := by
  have hr := root_pos δ g hδ
  have ha := Real.abs_le_sqrt (show g ^ 2 ≤ g ^ 2 + δ ^ 2 by nlinarith [sq_nonneg δ])
  have hu : g / Real.sqrt (g ^ 2 + δ ^ 2) ≤ 1 := (div_le_iff₀ hr).2 (by linarith [(abs_le.mp ha).2])
  have hl : -1 ≤ g / Real.sqrt (g ^ 2 + δ ^ 2) := (le_div_iff₀ hr).2 (by linarith [(abs_le.mp ha).1])
  dsimp [weight]
  constructor <;> linarith

theorem curvature_nonneg (δ g : ℝ) : 0 ≤ curvature δ g := by
  dsimp [curvature]
  positivity

theorem smoothPositive_hasDerivAt (δ g : ℝ) (hδ : 0 < δ) :
    HasDerivAt (smoothPositive δ) (weight δ g) g := by
  have hn : g ^ 2 + δ ^ 2 ≠ 0 := by nlinarith [sq_nonneg g, sq_pos_of_pos hδ]
  have hs := (((hasDerivAt_id g).pow 2).add_const (δ ^ 2)).sqrt hn
  have hd := ((hasDerivAt_id g).add hs).div_const 2
  apply hd.congr_deriv
  dsimp [weight]
  field_simp

theorem weight_hasDerivAt (δ g : ℝ) (hδ : 0 < δ) :
    HasDerivAt (weight δ) (curvature δ g) g := by
  have hn : g ^ 2 + δ ^ 2 ≠ 0 := by nlinarith [sq_nonneg g, sq_pos_of_pos hδ]
  have hr := (root_pos δ g hδ).ne'
  have hs := (((hasDerivAt_id g).pow 2).add_const (δ ^ 2)).sqrt hn
  have hd := (((hasDerivAt_id g).div hs hr).const_add 1).div_const 2
  apply hd.congr_deriv
  dsimp [curvature]
  field_simp
  nlinarith [Real.sq_sqrt (show 0 ≤ g ^ 2 + δ ^ 2 by positivity)]

/-- The scalar chain rule for `D = ∂t + u·∇ - νΔ` yields this
production with `aD = D pressure`, `bD = D core` and
`G = |∇(pressure-core)|²`. The switching term is nonpositive. -/
def production (δ a b aD bD ν G : ℝ) : ℝ :=
  weight δ (a - b) * aD + (1 - weight δ (a - b)) * bD -
    ν * curvature δ (a - b) * G

theorem production_le (δ a b aD bD ν G : ℝ) (hν : 0 ≤ ν) (hG : 0 ≤ G) :
    production δ a b aD bD ν G ≤
      weight δ (a - b) * aD + (1 - weight δ (a - b)) * bD := by
  have hc := mul_nonneg (mul_nonneg hν (curvature_nonneg δ (a - b))) hG
  dsimp [production]
  linarith

/-- The positive offset removes the need for a vorticity-dependent
separation radius. This also applies at `W=0`. -/
theorem linear_weight_le (W Y : ℝ) (hY : 1 + (44/95) * W ^ 2 ≤ Y) :
    2 * W ≤ (3/2) * Y := by
  nlinarith [sq_nonneg (2 * W - 3), sq_nonneg W]

theorem weighted_source_le (θ W Y F : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hW : 0 ≤ W) (hY : 1 + (44/95) * W ^ 2 ≤ Y) :
    |θ * (2 * W * F)| ≤ (3/2) * |F| * Y := by
  have hl := linear_weight_le W Y hY
  have hθw : θ * (2 * W) ≤ 2 * W := by nlinarith
  calc
    _ = θ * (2 * W) * |F| := by
      rw [abs_mul, abs_of_nonneg hθ, abs_mul, abs_of_nonneg (show 0 ≤ 2 * W by positivity)]
      ring
    _ ≤ (3/2) * Y * |F| := mul_le_mul_of_nonneg_right (hθw.trans hl) (abs_nonneg F)
    _ = _ := by ring

end Mettapedia.FluidDynamics.NavierStokes.PressureCoreEnvelope
