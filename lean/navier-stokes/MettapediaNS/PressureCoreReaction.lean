import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoreEnvelope

/-!
# The direct pressure reaction of the coercive reserve

After replacing the pressure pairing in the observation by its nearby
part, the actual strain still evolves with the complete pressure Hessian.
This file bounds the direct reaction of an omitted symmetric tensor `F`
on the strain slots by `(9/4) ‖F‖_F` times the reserve. The moment inputs
are `s=‖S‖_F`, `w=|ω|`, `z=|Sω|`, `V=ω·Sω`; the three contraction
hypotheses are ordinary matrix Cauchy--Schwarz bounds.

The actual tensor/NS identification and the separated Hessian estimate
are analytic in the companion lab. The scalar estimate has no alignment
condition and is uniform in the nearby pressure pairing. It does not
pay the pressure evolution at the parents or its gradient terms.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureCoreReaction

open PressureCoreEnvelope

/-- The omitted tensor acts through `D S = ... - F`. Here
`n=ω·Fω`, `a=(Sω)·Fω`, and `b=tr(SF)`. Its action on the pressure
pairing itself belongs to the separate actual parent-history source. -/
def reaction (η θ W V n a b : ℝ) : ℝ :=
  -(10 * V / (W + η) * n) -
    (1 - θ) * ((8/7) * a + (20/21) * W * b)

/-- Exact strain-slot differentiation with vorticity and the observed
pressure held fixed. A tensor increment `dS=-F` has precisely these
three moment derivatives. This is a partial differential of the reserve,
not an assertion that the other moments stay fixed along an NS flow. -/
theorem reaction_hasDerivAt (η δ W N : ℝ) (Q V Z : ℝ → ℝ) (n a b t : ℝ)
    (hδ : 0 < δ) (hQ : HasDerivAt Q (-2 * b) t)
    (hV : HasDerivAt V (-n) t) (hZ : HasDerivAt Z (-2 * a) t) :
    HasDerivAt (fun r ↦ reserve η δ (Q r) W (V r) (Z r) N)
      (reaction η (weight δ (pressure η W (V t) N - core η (Q t) W (V t) (Z t)))
        W (V t) n a b) t := by
  have ht := ((hV.pow 2).const_mul 5).div_const (W + η)
  have hc : HasDerivAt (fun r ↦ core η (Q r) W (V r) (Z r))
      (10 * V t * (-n) / (W + η) + (4/7) * (-2 * a) + (10/21) * W * (-2 * b)) t := by
    convert! (((ht.add (hZ.const_mul (4/7))).add
      ((hQ.const_mul W).const_mul (10/21))).add_const ((44/95) * W ^ 2)) using 1
    · ext r
      dsimp [core]
      ring
    · ring
  have hp : HasDerivAt (fun r ↦ pressure η W (V r) N)
      (10 * V t * (-n) / (W + η)) t := by
    convert! ((ht.add_const ((63/95) * W ^ 2)).sub_const (2 * N)) using 1
    dsimp [pressure]
    ring
  have hg := hp.sub hc
  have hh := (smoothPositive_hasDerivAt δ
    (pressure η W (V t) N - core η (Q t) W (V t) (Z t)) hδ).comp t hg
  have h := (hc.add hh).const_add 1
  convert! h using 1
  · ext r
    simp only [reserve, core, pressure, Function.comp_def, Pi.add_apply,
      Pi.sub_apply]
    ring
  · dsimp [reaction, core, pressure]
    ring

private theorem perspective_young (η W V : ℝ) (hη : 0 < η) (hW : 0 ≤ W) :
    10 * |V| * W / (W + η) ≤
      (9/4) * (5 * V ^ 2 / (W + η)) + (20/9) * W := by
  have hd : 0 < W + η := by linarith
  apply (div_le_iff₀ hd).2
  rw [show ((9/4) * (5 * V ^ 2 / (W + η)) + (20/9) * W) * (W + η) =
      (45/4) * V ^ 2 + (20/9) * W * (W + η) by field_simp; ring]
  nlinarith [sq_nonneg (9 * |V| - 4 * W), sq_abs V, mul_nonneg hW hη.le]

/-- The quadratic strain part pays its complete directional slope.
The positive offset and quartic vorticity part make the constant uniform
even when the vorticity is small or large. -/
theorem slope_envelope_le (η δ s w z V N : ℝ) (hη : 0 < η) :
    10 * |V| * w ^ 2 / (w ^ 2 + η) + (8/7) * z * w + (20/21) * w ^ 2 * s ≤
      (9/4) * reserve η δ (s ^ 2) (w ^ 2) V (z ^ 2) N := by
  have ht := perspective_young η (w ^ 2) V hη (sq_nonneg w)
  have hz : (8/7) * z * w ≤ (9/4) * ((4/7) * z ^ 2) + (16/63) * w ^ 2 := by
    nlinarith [sq_nonneg (9 * z - 4 * w)]
  have hq : (20/21) * w ^ 2 * s ≤
      (9/4) * ((10/21) * s ^ 2 * w ^ 2) + (40/189) * w ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg w) (sq_nonneg (9 * s - 4))]
  have hw := linear_weight_le (w ^ 2) (1 + (44/95) * (w ^ 2) ^ 2) le_rfl
  have hp := smoothPositive_nonneg δ
    (pressure η (w ^ 2) V N - core η (s ^ 2) (w ^ 2) V (z ^ 2))
  dsimp [core] at hp
  dsimp [reserve, core]
  nlinarith only [ht, hz, hq, hw, hp, sq_nonneg (w ^ 2)]

/-- The hypotheses retain the actual tensor contractions instead of
assigning them independent signs. `p` bounds the Frobenius norm of `F`. -/
theorem reaction_abs_le (η δ θ s w z V N n a b p : ℝ)
    (hη : 0 < η) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hp : 0 ≤ p)
    (hn : |n| ≤ w ^ 2 * p) (ha : |a| ≤ z * w * p) (hb : |b| ≤ s * p) :
    |reaction η θ (w ^ 2) V n a b| ≤
      (9/4) * p * reserve η δ (s ^ 2) (w ^ 2) V (z ^ 2) N := by
  have hd : 0 < w ^ 2 + η := by positivity
  have hfirst : |10 * V / (w ^ 2 + η) * n| ≤
      (10 * |V| * w ^ 2 / (w ^ 2 + η)) * p := by
    rw [abs_mul, abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 10),
      abs_of_pos hd]
    calc
      _ ≤ (10 * |V| / (w ^ 2 + η)) * (w ^ 2 * p) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
      _ = _ := by ring
  have hsecond : |(1 - θ) * ((8/7) * a + (20/21) * w ^ 2 * b)| ≤
      ((8/7) * z * w + (20/21) * w ^ 2 * s) * p := by
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - θ)]
    calc
      _ ≤ 1 * |(8/7) * a + (20/21) * w ^ 2 * b| :=
        mul_le_mul_of_nonneg_right (by linarith : 1 - θ ≤ 1) (abs_nonneg _)
      _ ≤ |(8/7) * a| + |(20/21) * w ^ 2 * b| := by
        simpa only [one_mul] using abs_add_le ((8/7) * a) ((20/21) * w ^ 2 * b)
      _ = (8/7) * |a| + (20/21) * w ^ 2 * |b| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8/7),
          abs_mul, abs_of_nonneg (by positivity : 0 ≤ (20/21) * w ^ 2)]
      _ ≤ (8/7) * (z * w * p) + (20/21) * w ^ 2 * (s * p) :=
        add_le_add (mul_le_mul_of_nonneg_left ha (by norm_num))
          (mul_le_mul_of_nonneg_left hb (by positivity))
      _ = _ := by ring
  calc
    _ ≤ |10 * V / (w ^ 2 + η) * n| +
        |(1 - θ) * ((8/7) * a + (20/21) * w ^ 2 * b)| := by
      rw [show reaction η θ (w ^ 2) V n a b =
        -(10 * V / (w ^ 2 + η) * n +
          (1 - θ) * ((8/7) * a + (20/21) * w ^ 2 * b)) by dsimp [reaction]; ring,
        abs_neg]
      exact abs_add_le _ _
    _ ≤ (10 * |V| * w ^ 2 / (w ^ 2 + η) +
        (8/7) * z * w + (20/21) * w ^ 2 * s) * p := by nlinarith only [hfirst, hsecond]
    _ ≤ ((9/4) * reserve η δ (s ^ 2) (w ^ 2) V (z ^ 2) N) * p :=
      mul_le_mul_of_nonneg_right (slope_envelope_le η δ s w z V N hη) hp
    _ = _ := by ring

theorem normalized_reaction_le (η δ s w z V N n a b p : ℝ)
    (hη : 0 < η) (hδ : 0 < δ)
    (hp : 0 ≤ p) (hn : |n| ≤ w ^ 2 * p) (ha : |a| ≤ z * w * p)
    (hb : |b| ≤ s * p) :
    |reaction η (weight δ (pressure η (w ^ 2) V N -
      core η (s ^ 2) (w ^ 2) V (z ^ 2))) (w ^ 2) V n a b /
      reserve η δ (s ^ 2) (w ^ 2) V (z ^ 2) N| ≤ (9/4) * p := by
  have ht := weight_mem δ
    (pressure η (w ^ 2) V N - core η (s ^ 2) (w ^ 2) V (z ^ 2)) hδ
  have hc := reserve_coercive η δ (s ^ 2) (w ^ 2) V (z ^ 2) N
    hη (sq_nonneg s) (sq_nonneg w) (sq_nonneg z)
  have hY : 0 < reserve η δ (s ^ 2) (w ^ 2) V (z ^ 2) N := by
    nlinarith [sq_nonneg (w ^ 2)]
  rw [abs_div, abs_of_pos hY]
  exact (div_le_iff₀ hY).2 (reaction_abs_le η δ _ s w z V N n a b p
    hη ht.1 ht.2 hp hn ha hb)

/-- The analytic separated-kernel estimate gives `p ≤ 12 E/(π R⁵)`.
After the actual energy inequality this coefficient is fixed by the
initial datum and radius. No near-parent production is included. -/
theorem separated_coefficient_le (p E R : ℝ)
    (hp : p ≤ (12 / (Real.pi * R ^ 5)) * E) :
    (9/4) * p ≤ (27 / (Real.pi * R ^ 5)) * E := by
  calc
    _ ≤ (9/4) * ((12 / (Real.pi * R ^ 5)) * E) :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = _ := by ring

end Mettapedia.FluidDynamics.NavierStokes.PressureCoreReaction
