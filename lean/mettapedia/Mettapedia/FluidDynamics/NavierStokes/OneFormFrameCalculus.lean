import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# One-form Lie-derivative calculus for trigonometric frames

This file develops the coordinate calculus of Lie derivatives of one-forms on
`EuclideanSpace ℝ ι` along *profile modes* — vector fields of the shape
`y ↦ φ ⟪k, y⟫ • e` with a constant direction `e` and a linear phase `⟪k, ·⟫` —
and proves the frame-Laplacian identity: summing the squared Lie derivative
over a divergence-free trigonometric frame (cosine/sine pairs over coordinate
axes with orthogonal polarizations) reproduces the componentwise Laplacian
acting on the one-form.

Under the flat metric of `EuclideanSpace ℝ ι` we identify covector fields with
vector fields (the musical isomorphism is the identity on components), so a
one-form is represented by a function `μ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι`
whose value `μ x` collects the components `μ_a x`.  The Lie derivative of a
one-form along a vector field `E` is, in coordinates,

`(L_E μ)_a = E^b ∂_b μ_a + (∂_a E^b) μ_b`,

which is `lieOneForm` below.  The main results:

* `lieOneForm_profileMode_apply`: the closed form
  `L_{φ(⟪k,·⟫)e} μ = φ • D_e μ + (φ' ⟪e, μ⟫) • k`.
* `lieOneForm_sq_profileMode`: for `⟪k, e⟫ = 0` and `μ` twice differentiable,
  `L²_{φ(⟪k,·⟫)e} μ = φ² • D_e² μ + (2 φ φ' ⟪e, D_e μ⟫) • k`.
* `lieOneForm_sq_cos_add_sin`: the cosine/sine pair of amplitude `a` on the
  same `(k, e)` sums to `a² • D_e² μ` — the phase-dependent terms cancel.
* `frameLaplacian_oneForm`: over the full truncated coordinate frame (all
  axes `j`, all polarizations `p ≠ j`, both phases) the sum of squared Lie
  derivatives equals `(2 a²)` times the coordinate second-derivative sum
  `Σ_p D_{e_p}² μ`; `frameLaplacian_oneForm_normalized` states the normalized
  version (amplitude `1/√2` in dimension `3`).

The frame here is the lowest orbit (unit coordinate wave vectors) of the
divergence-free trigonometric torus frame
`|k|^{-β} cos(k·θ) e_{k,i}`, `|k|^{-β} sin(k·θ) e_{k,i}` (`e_{k,i} ⊥ k`) used
by Fang–Luo to run the Constantin–Iyer representation on manifolds; the
identity `Σ_i L²_{A_i} = Δ` on one-forms is a frame decomposition of the
de Rham–Hodge Laplacian in the style of Elworthy–Le Jan–Li.  In
stochastic-Lagrangian representations of the incompressible Navier–Stokes
equations the momentum one-form is transported along a stochastic flow driven
by such a frame, and the viscous term arises from exactly this sum of squared
Lie derivatives.

## References

* S. Fang, D. Luo, *Constantin and Iyer's representation formula for the
  Navier–Stokes equations on manifolds*, Potential Anal. **48** (2018),
  181–206, §3 and §5.1. arXiv:1508.06387.
* K. D. Elworthy, Y. Le Jan, X.-M. Li, *On the Geometry of Diffusion
  Operators and Stochastic Flows*, Lect. Notes Math. **1720**, Springer, 1999.
* P. Constantin, G. Iyer, *A stochastic Lagrangian representation of the
  three-dimensional incompressible Navier–Stokes equations*,
  Comm. Pure Appl. Math. **61** (2008), 330–345. arXiv:math/0511067.

**Scope.** All identities are pointwise, for one-forms that are (twice)
differentiable at the point considered, and the frame identity is for the
explicit finite single-orbit coordinate frame.  No claim is made here about
infinite frames, nor about any stochastic transport equation.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped RealInnerProductSpace BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lie derivative of a one-form along a vector field, in coordinates:
`(lieOneForm E μ x) a = Σ_b (E x) b • ∂_b μ_a x + Σ_b (∂_a E_b x) • (μ x) b`.
Covectors are represented by their component vectors under the flat metric. -/
def lieOneForm (E μ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  fderiv ℝ μ x (E x) +
    ∑ a, EuclideanSpace.single a ⟪fderiv ℝ E x (EuclideanSpace.single a 1), μ x⟫

/-- Second directional derivative of a (one-form-valued) function along a
constant direction `e`. -/
def dirDeriv2 (e : EuclideanSpace ℝ ι) (μ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  fderiv ℝ (fun y => fderiv ℝ μ y e) x e

/-- Profile mode: a vector field with constant direction `e`, wave vector `k`,
and scalar profile `φ` applied to the linear phase `⟪k, y⟫`. -/
def profileMode (φ : ℝ → ℝ) (k e : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι → EuclideanSpace ℝ ι :=
  fun y => φ ⟪k, y⟫ • e

section Helpers

/-- Collecting coordinates: `Σ_a single a (c * k a) = c • k`. -/
lemma sum_single_mul_apply (c : ℝ) (k : EuclideanSpace ℝ ι) :
    ∑ a, EuclideanSpace.single a (c * k a) = c • k := by
  ext b
  simp

omit [DecidableEq ι] in
/-- The phase function `y ↦ ⟪k, y⟫` has Fréchet derivative `innerSL ℝ k`. -/
lemma hasFDerivAt_inner_left (k x : EuclideanSpace ℝ ι) :
    HasFDerivAt (fun y : EuclideanSpace ℝ ι => ⟪k, y⟫) (innerSL ℝ k) x :=
  (innerSL ℝ k).hasFDerivAt

omit [DecidableEq ι] in
/-- Derivative of a profile mode: if `φ` has derivative `dφ` everywhere, the
profile mode `y ↦ φ ⟪k, y⟫ • e` has Fréchet derivative
`(dφ ⟪k, x⟫ • innerSL ℝ k).smulRight e` at `x`. -/
lemma hasFDerivAt_profileMode {φ dφ : ℝ → ℝ} (hφ : ∀ t, HasDerivAt φ (dφ t) t)
    (k e x : EuclideanSpace ℝ ι) :
    HasFDerivAt (profileMode φ k e)
      ((dφ ⟪k, x⟫ • innerSL ℝ k).smulRight e) x := by
  have hphase : HasFDerivAt (fun y : EuclideanSpace ℝ ι => ⟪k, y⟫)
      (innerSL ℝ k) x := hasFDerivAt_inner_left k x
  have hcomp : HasFDerivAt (fun y : EuclideanSpace ℝ ι => φ ⟪k, y⟫)
      (dφ ⟪k, x⟫ • innerSL ℝ k) x :=
    (hφ ⟪k, x⟫).comp_hasFDerivAt x hphase
  exact hcomp.smul_const e

end Helpers

section ProfileModeEvaluation

variable {φ dφ : ℝ → ℝ} {k e : EuclideanSpace ℝ ι}
variable {μ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {x : EuclideanSpace ℝ ι}

/-- Closed form of the Lie derivative of a one-form along a profile mode:
`L_{φ(⟪k,·⟫)e} μ = φ ⟪k,x⟫ • D_e μ + (dφ ⟪k,x⟫ * ⟪e, μ x⟫) • k`.

This is an identity of the defined quantities; it is meaningful as the Lie
derivative when `μ` is differentiable at `x` (otherwise `fderiv` degenerates
to `0` on both sides in the same way). -/
theorem lieOneForm_profileMode_apply (hφ : ∀ t, HasDerivAt φ (dφ t) t) :
    lieOneForm (profileMode φ k e) μ x =
      φ ⟪k, x⟫ • fderiv ℝ μ x e + (dφ ⟪k, x⟫ * ⟪e, μ x⟫) • k := by
  have hE := hasFDerivAt_profileMode (ι := ι) hφ k e x
  have hEfderiv : fderiv ℝ (profileMode φ k e) x =
      (dφ ⟪k, x⟫ • innerSL ℝ k).smulRight e := hE.fderiv
  unfold lieOneForm
  have hfirst : fderiv ℝ μ x (profileMode φ k e x) = φ ⟪k, x⟫ • fderiv ℝ μ x e := by
    simp [profileMode]
  have hsecond : ∀ a : ι,
      ⟪fderiv ℝ (profileMode φ k e) x (EuclideanSpace.single a 1), μ x⟫ =
        dφ ⟪k, x⟫ * ⟪e, μ x⟫ * k a := by
    intro a
    rw [hEfderiv]
    have hka : ⟪k, EuclideanSpace.single a (1 : ℝ)⟫ = k a := by
      simp [EuclideanSpace.inner_single_right]
    simp [ContinuousLinearMap.smulRight_apply, real_inner_smul_left, hka]
    ring
  calc fderiv ℝ μ x (profileMode φ k e x) +
        ∑ a, EuclideanSpace.single a
          ⟪fderiv ℝ (profileMode φ k e) x (EuclideanSpace.single a 1), μ x⟫
      = φ ⟪k, x⟫ • fderiv ℝ μ x e +
          ∑ a, EuclideanSpace.single a (dφ ⟪k, x⟫ * ⟪e, μ x⟫ * k a) := by
        rw [hfirst]
        congr 1
        exact Finset.sum_congr rfl fun a _ => by rw [hsecond a]
    _ = φ ⟪k, x⟫ • fderiv ℝ μ x e + (dφ ⟪k, x⟫ * ⟪e, μ x⟫) • k := by
        rw [sum_single_mul_apply]

end ProfileModeEvaluation

section SquaredLieDerivative

variable {φ dφ ddφ : ℝ → ℝ} {k e : EuclideanSpace ℝ ι}
variable {μ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}

/-- Squared Lie derivative of a one-form along a profile mode whose direction
is orthogonal to its wave vector (`⟪k, e⟫ = 0`, so the profile is constant
along `e`):

`L²_{φ(⟪k,·⟫)e} μ = φ² • D_e² μ + (2 φ φ' ⟪e, D_e μ⟫) • k`.

This is the single-mode square identity: the second-order term carries the
full weight `φ²` on the second directional derivative, while the only
first-order remainder is the gradient-direction term with coefficient
`2 φ φ'`. -/
theorem lieOneForm_sq_profileMode
    (hφ : ∀ t, HasDerivAt φ (dφ t) t) (hdφ : ∀ t, HasDerivAt dφ (ddφ t) t)
    (horth : ⟪k, e⟫ = 0) (hμ : ContDiff ℝ 2 μ) (x : EuclideanSpace ℝ ι) :
    lieOneForm (profileMode φ k e) (lieOneForm (profileMode φ k e) μ) x =
      φ ⟪k, x⟫ ^ 2 • dirDeriv2 e μ x +
        (2 * φ ⟪k, x⟫ * dφ ⟪k, x⟫ * ⟪e, fderiv ℝ μ x e⟫) • k := by
  have horth' : ⟪e, k⟫ = 0 := by rw [real_inner_comm]; exact horth
  -- Closed form of the inner Lie derivative, as a function of the base point.
  have hν : lieOneForm (profileMode φ k e) μ =
      fun y => φ ⟪k, y⟫ • fderiv ℝ μ y e + (dφ ⟪k, y⟫ * ⟪e, μ y⟫) • k :=
    funext fun _ => lieOneForm_profileMode_apply hφ
  rw [hν, lieOneForm_profileMode_apply hφ]
  -- Differentiability data extracted from `ContDiff ℝ 2 μ`.
  have hμ1 : Differentiable ℝ μ := hμ.differentiable (by norm_num)
  have hw : DifferentiableAt ℝ (fun y => fderiv ℝ μ y e) x := by
    have hfd : ContDiff ℝ 1 (fderiv ℝ μ) := hμ.fderiv_right (by norm_num)
    exact ((hfd.differentiable (by norm_num)).differentiableAt).clm_apply
      (differentiableAt_const e)
  -- Derivative of the scalar coefficients.
  have hc : HasFDerivAt (fun y : EuclideanSpace ℝ ι => φ ⟪k, y⟫)
      (dφ ⟪k, x⟫ • innerSL ℝ k) x :=
    (hφ ⟪k, x⟫).comp_hasFDerivAt x (hasFDerivAt_inner_left k x)
  have hdc : HasFDerivAt (fun y : EuclideanSpace ℝ ι => dφ ⟪k, y⟫)
      (ddφ ⟪k, x⟫ • innerSL ℝ k) x :=
    (hdφ ⟪k, x⟫).comp_hasFDerivAt x (hasFDerivAt_inner_left k x)
  have hp : HasFDerivAt (fun y => ⟪e, μ y⟫)
      ((innerSL ℝ e).comp (fderiv ℝ μ x)) x :=
    ((innerSL ℝ e).hasFDerivAt).comp x (hμ1 x).hasFDerivAt
  -- Derivative of the closed-form inner Lie derivative.
  have hcw : HasFDerivAt (fun y => φ ⟪k, y⟫ • fderiv ℝ μ y e)
      (φ ⟪k, x⟫ • fderiv ℝ (fun y => fderiv ℝ μ y e) x +
        (dφ ⟪k, x⟫ • innerSL ℝ k).smulRight (fderiv ℝ μ x e)) x :=
    hc.smul hw.hasFDerivAt
  have hq : HasFDerivAt (fun y => dφ ⟪k, y⟫ * ⟪e, μ y⟫)
      (dφ ⟪k, x⟫ • ((innerSL ℝ e).comp (fderiv ℝ μ x)) +
        ⟪e, μ x⟫ • (ddφ ⟪k, x⟫ • innerSL ℝ k)) x :=
    hdc.mul hp
  have hqk : HasFDerivAt (fun y => (dφ ⟪k, y⟫ * ⟪e, μ y⟫) • k)
      ((dφ ⟪k, x⟫ • ((innerSL ℝ e).comp (fderiv ℝ μ x)) +
        ⟪e, μ x⟫ • (ddφ ⟪k, x⟫ • innerSL ℝ k)).smulRight k) x :=
    hq.smul_const k
  have htotal : HasFDerivAt
      (fun y => φ ⟪k, y⟫ • fderiv ℝ μ y e + (dφ ⟪k, y⟫ * ⟪e, μ y⟫) • k)
      (φ ⟪k, x⟫ • fderiv ℝ (fun y => fderiv ℝ μ y e) x +
        (dφ ⟪k, x⟫ • innerSL ℝ k).smulRight (fderiv ℝ μ x e) +
        (dφ ⟪k, x⟫ • ((innerSL ℝ e).comp (fderiv ℝ μ x)) +
          ⟪e, μ x⟫ • (ddφ ⟪k, x⟫ • innerSL ℝ k)).smulRight k) x :=
    hcw.add hqk
  -- Evaluate the derivative in the direction `e`, using orthogonality.
  have hde : fderiv ℝ
      (fun y => φ ⟪k, y⟫ • fderiv ℝ μ y e + (dφ ⟪k, y⟫ * ⟪e, μ y⟫) • k) x e =
      φ ⟪k, x⟫ • dirDeriv2 e μ x +
        (dφ ⟪k, x⟫ * ⟪e, fderiv ℝ μ x e⟫) • k := by
    rw [htotal.fderiv]
    simp [dirDeriv2, horth]
  -- Evaluate the inner value pairing with `e`, using orthogonality.
  have hval : ⟪e, φ ⟪k, x⟫ • fderiv ℝ μ x e + (dφ ⟪k, x⟫ * ⟪e, μ x⟫) • k⟫ =
      φ ⟪k, x⟫ * ⟪e, fderiv ℝ μ x e⟫ := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, horth']
    ring
  rw [hde, hval]
  match_scalars <;> ring

end SquaredLieDerivative

section TrigPair

variable {k e : EuclideanSpace ℝ ι}
variable {μ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}

/-- Everywhere-derivative data for the cosine profile of amplitude `a`. -/
lemma hasDerivAt_amp_cos (a t : ℝ) :
    HasDerivAt (fun s => a * Real.cos s) (a * -Real.sin t) t :=
  (Real.hasDerivAt_cos t).const_mul a

/-- Everywhere-derivative data for the sine profile of amplitude `a`. -/
lemma hasDerivAt_amp_sin (a t : ℝ) :
    HasDerivAt (fun s => a * Real.sin s) (a * Real.cos t) t :=
  (Real.hasDerivAt_sin t).const_mul a

/-- Everywhere-derivative data for the negated-sine profile of amplitude `a`. -/
lemma hasDerivAt_amp_neg_sin (a t : ℝ) :
    HasDerivAt (fun s => a * -Real.sin s) (a * -Real.cos t) t := by
  simpa [mul_comm, mul_assoc, neg_mul, mul_neg] using
    (((Real.hasDerivAt_sin t).neg).const_mul a)

/-- The cosine/sine pair collapse: for a wave vector `k` orthogonal to the
polarization `e`, the squared Lie derivatives along the amplitude-`a`
cosine and sine modes sum to `a² • D_e² μ` — the phase-dependent
gradient-direction terms cancel and `cos² + sin² = 1` removes the phase from
the second-order term. -/
theorem lieOneForm_sq_cos_add_sin (a : ℝ) (horth : ⟪k, e⟫ = 0)
    (hμ : ContDiff ℝ 2 μ) (x : EuclideanSpace ℝ ι) :
    lieOneForm (profileMode (fun t => a * Real.cos t) k e)
        (lieOneForm (profileMode (fun t => a * Real.cos t) k e) μ) x +
      lieOneForm (profileMode (fun t => a * Real.sin t) k e)
        (lieOneForm (profileMode (fun t => a * Real.sin t) k e) μ) x =
      a ^ 2 • dirDeriv2 e μ x := by
  rw [lieOneForm_sq_profileMode (dφ := fun t => a * -Real.sin t)
      (ddφ := fun t => a * -Real.cos t)
      (hasDerivAt_amp_cos a) (hasDerivAt_amp_neg_sin a) horth hμ x,
    lieOneForm_sq_profileMode (dφ := fun t => a * Real.cos t)
      (ddφ := fun t => a * -Real.sin t)
      (hasDerivAt_amp_sin a) (hasDerivAt_amp_cos a) horth hμ x]
  match_scalars
  · linear_combination a ^ 2 * Real.sin_sq_add_cos_sq ⟪k, x⟫
  · ring

end TrigPair

section FrameLaplacian

variable {μ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}

/-- Coordinate form of the componentwise (flat) Laplacian on one-forms: the
sum of second directional derivatives along the coordinate directions. -/
def coordLaplacian (μ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  ∑ p, dirDeriv2 (EuclideanSpace.single p 1) μ x

/-- Frame-Laplacian identity on the truncated coordinate frame: summing the
squared Lie derivative of a one-form over all axes `j`, all polarizations
`p ≠ j`, and both trigonometric phases of amplitude `a` yields
`((card ι − 1) · a²)` times the coordinate Laplacian.  In dimension `3` each
polarization direction is hit by exactly `2` axes, giving the factor `2a²`. -/
theorem frameLaplacian_oneForm (a : ℝ) (hμ : ContDiff ℝ 2 μ)
    (x : EuclideanSpace ℝ ι) :
    ∑ j, ∑ p ∈ Finset.univ.erase j,
        (lieOneForm (profileMode (fun t => a * Real.cos t)
            (EuclideanSpace.single j 1) (EuclideanSpace.single p 1))
          (lieOneForm (profileMode (fun t => a * Real.cos t)
            (EuclideanSpace.single j 1) (EuclideanSpace.single p 1)) μ) x +
        lieOneForm (profileMode (fun t => a * Real.sin t)
            (EuclideanSpace.single j 1) (EuclideanSpace.single p 1))
          (lieOneForm (profileMode (fun t => a * Real.sin t)
            (EuclideanSpace.single j 1) (EuclideanSpace.single p 1)) μ) x) =
      ((Fintype.card ι - 1 : ℕ) * a ^ 2) • coordLaplacian μ x := by
  have hterm : ∀ j : ι, ∀ p ∈ Finset.univ.erase j,
      (lieOneForm (profileMode (fun t => a * Real.cos t)
          (EuclideanSpace.single j 1) (EuclideanSpace.single p 1))
        (lieOneForm (profileMode (fun t => a * Real.cos t)
          (EuclideanSpace.single j 1) (EuclideanSpace.single p 1)) μ) x +
      lieOneForm (profileMode (fun t => a * Real.sin t)
          (EuclideanSpace.single j 1) (EuclideanSpace.single p 1))
        (lieOneForm (profileMode (fun t => a * Real.sin t)
          (EuclideanSpace.single j 1) (EuclideanSpace.single p 1)) μ) x) =
      a ^ 2 • dirDeriv2 (EuclideanSpace.single p 1) μ x := by
    intro j p hp
    have hpj : p ≠ j := Finset.ne_of_mem_erase hp
    have horth : ⟪(EuclideanSpace.single j 1 : EuclideanSpace ℝ ι),
        EuclideanSpace.single p 1⟫ = 0 := by
      simp [EuclideanSpace.inner_single_left, hpj]
    exact lieOneForm_sq_cos_add_sin a horth hμ x
  calc ∑ j, ∑ p ∈ Finset.univ.erase j,
        (lieOneForm (profileMode (fun t => a * Real.cos t)
            (EuclideanSpace.single j 1) (EuclideanSpace.single p 1))
          (lieOneForm (profileMode (fun t => a * Real.cos t)
            (EuclideanSpace.single j 1) (EuclideanSpace.single p 1)) μ) x +
        lieOneForm (profileMode (fun t => a * Real.sin t)
            (EuclideanSpace.single j 1) (EuclideanSpace.single p 1))
          (lieOneForm (profileMode (fun t => a * Real.sin t)
            (EuclideanSpace.single j 1) (EuclideanSpace.single p 1)) μ) x)
      = ∑ j : ι, ∑ p ∈ Finset.univ.erase j,
          a ^ 2 • dirDeriv2 (EuclideanSpace.single p 1) μ x := by
        exact Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun p hp => hterm j p hp
    _ = ∑ p : ι, ∑ j ∈ Finset.univ.erase p,
          a ^ 2 • dirDeriv2 (EuclideanSpace.single p 1) μ x := by
        apply Finset.sum_comm'
        intro j p
        constructor
        · rintro ⟨-, hp⟩
          exact ⟨Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hp).symm,
            Finset.mem_univ j⟩, Finset.mem_univ p⟩
        · rintro ⟨hj, -⟩
          exact ⟨Finset.mem_univ j, Finset.mem_erase.mpr
            ⟨(Finset.ne_of_mem_erase hj).symm, Finset.mem_univ p⟩⟩
    _ = ∑ p : ι, ((Fintype.card ι - 1 : ℕ) * a ^ 2) •
          dirDeriv2 (EuclideanSpace.single p 1) μ x := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ p),
          Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    _ = ((Fintype.card ι - 1 : ℕ) * a ^ 2) • coordLaplacian μ x := by
        rw [coordLaplacian, Finset.smul_sum]

/-- Normalized frame-Laplacian identity in dimension `3`: with amplitude
`1/√2` the truncated coordinate frame reproduces the coordinate Laplacian on
one-forms exactly, `Σ_i L²_{E_i} μ = Δ μ`. -/
theorem frameLaplacian_oneForm_normalized
    {μ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hμ : ContDiff ℝ 2 μ) (x : EuclideanSpace ℝ (Fin 3)) :
    ∑ j, ∑ p ∈ Finset.univ.erase j,
        (lieOneForm (profileMode (fun t => (Real.sqrt 2)⁻¹ * Real.cos t)
            (EuclideanSpace.single j 1) (EuclideanSpace.single p 1))
          (lieOneForm (profileMode (fun t => (Real.sqrt 2)⁻¹ * Real.cos t)
            (EuclideanSpace.single j 1) (EuclideanSpace.single p 1)) μ) x +
        lieOneForm (profileMode (fun t => (Real.sqrt 2)⁻¹ * Real.sin t)
            (EuclideanSpace.single j 1) (EuclideanSpace.single p 1))
          (lieOneForm (profileMode (fun t => (Real.sqrt 2)⁻¹ * Real.sin t)
            (EuclideanSpace.single j 1) (EuclideanSpace.single p 1)) μ) x) =
      coordLaplacian μ x := by
  rw [frameLaplacian_oneForm ((Real.sqrt 2)⁻¹) hμ x]
  have hcoeff : ((Fintype.card (Fin 3) - 1 : ℕ) : ℝ) * ((Real.sqrt 2)⁻¹) ^ 2 = 1 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [hcoeff, one_smul]

end FrameLaplacian

section ProfileModeDerivatives

variable {φ dφ ddφ : ℝ → ℝ} {k e : EuclideanSpace ℝ ι}

omit [DecidableEq ι] in
/-- The directional derivative of a profile mode, as a function of the base
point, is itself a profile mode: the profile picks up the factor `⟪k, v⟫`
and differentiates. -/
lemma fderiv_profileMode_eval (hφ : ∀ t, HasDerivAt φ (dφ t) t)
    (v : EuclideanSpace ℝ ι) :
    (fun y => fderiv ℝ (profileMode φ k e) y v) =
      profileMode (fun t => ⟪k, v⟫ * dφ t) k e := by
  funext y
  rw [(hasFDerivAt_profileMode hφ k e y).fderiv]
  rw [ContinuousLinearMap.smulRight_apply]
  unfold profileMode
  rw [smul_apply, innerSL_apply_apply, smul_eq_mul]
  simp [mul_comm]

omit [DecidableEq ι] in
/-- Second directional derivative of a profile mode:
`D_v² (φ(⟪k,·⟫) e) = ddφ(⟪k,x⟫) ⟪k, v⟫² • e`. -/
lemma dirDeriv2_profileMode (hφ : ∀ t, HasDerivAt φ (dφ t) t)
    (hdφ : ∀ t, HasDerivAt dφ (ddφ t) t) (v x : EuclideanSpace ℝ ι) :
    dirDeriv2 v (profileMode φ k e) x = (ddφ ⟪k, x⟫ * ⟪k, v⟫ ^ 2) • e := by
  unfold dirDeriv2
  rw [fderiv_profileMode_eval hφ v]
  have hmode := hasFDerivAt_profileMode
    (φ := fun t => ⟪k, v⟫ * dφ t) (dφ := fun t => ⟪k, v⟫ * ddφ t)
    (fun t => (hdφ t).const_mul ⟪k, v⟫) k e x
  rw [hmode.fderiv]
  rw [ContinuousLinearMap.smulRight_apply, smul_apply, innerSL_apply_apply,
    smul_eq_mul]
  match_scalars
  ring

/-- Laplacian of a profile mode:
`Δ (φ(⟪k,·⟫) e) = ddφ(⟪k,x⟫) ⟪k, k⟫ • e`. -/
lemma coordLaplacian_profileMode (hφ : ∀ t, HasDerivAt φ (dφ t) t)
    (hdφ : ∀ t, HasDerivAt dφ (ddφ t) t) (x : EuclideanSpace ℝ ι) :
    coordLaplacian (profileMode φ k e) x = (ddφ ⟪k, x⟫ * ⟪k, k⟫) • e := by
  unfold coordLaplacian
  have hterm : ∀ p : ι,
      dirDeriv2 (EuclideanSpace.single p 1) (profileMode φ k e) x =
        (ddφ ⟪k, x⟫ * k p ^ 2) • e := by
    intro p
    rw [dirDeriv2_profileMode hφ hdφ]
    have hkp : ⟪k, (EuclideanSpace.single p 1 : EuclideanSpace ℝ ι)⟫ = k p := by
      simp [EuclideanSpace.inner_single_right]
    rw [hkp]
  calc ∑ p, dirDeriv2 (EuclideanSpace.single p 1) (profileMode φ k e) x
      = ∑ p, (ddφ ⟪k, x⟫ * k p ^ 2) • e :=
        Finset.sum_congr rfl fun p _ => hterm p
    _ = (∑ p, ddφ ⟪k, x⟫ * k p ^ 2) • e := by rw [Finset.sum_smul]
    _ = (ddφ ⟪k, x⟫ * ⟪k, k⟫) • e := by
        have hkk : ⟪k, k⟫ = ∑ p, k p ^ 2 := by
          rw [PiLp.inner_apply]
          exact Finset.sum_congr rfl fun p _ => by
            simp [pow_two]
        rw [← Finset.mul_sum, hkk]

end ProfileModeDerivatives


end NavierStokes
end FluidDynamics
end Mettapedia
