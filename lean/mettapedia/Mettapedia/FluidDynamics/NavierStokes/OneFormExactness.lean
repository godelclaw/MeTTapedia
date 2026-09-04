import Mettapedia.FluidDynamics.NavierStokes.OneFormFrameCalculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Exactness of one-forms and the divergence-free non-closed witness

A one-form `μ` on `EuclideanSpace ℝ ι` (represented by its component vector
field under the flat metric) is *exact* when it is the differential of a `C²`
scalar potential: `∀ y v, fderiv ℝ W y v = ⟪μ y, v⟫`.  This file proves:

* `oneFormExtDerivAt_eq_zero_of_exact`: exact one-forms are closed — the
  coordinate exterior derivative
  `dμ(v, w) = ⟪D_v μ, w⟫ − ⟪D_w μ, v⟫` vanishes, by symmetry of the second
  derivative of the potential.
* `coordDivergence_profileMode`: a profile mode `φ(⟪k,·⟫) • e` has pointwise
  divergence `dφ(⟪k,x⟫) ⟪k, e⟫`; in particular transverse modes
  (`⟪k, e⟫ = 0`) are divergence-free.
* `oneFormExtDerivAt_sinMode`: the transverse sine mode `sin(⟪k,·⟫) • e` has
  exterior derivative `⟪k, v⟫⟪e, w⟫ − ⟪k, w⟫⟪e, v⟫` at the origin; on a
  distinct coordinate pair this equals `1`.
* `exists_divergenceFree_smooth_not_exact`: there is a smooth,
  everywhere-divergence-free field whose one-form is **not** exact.

## Context

In stochastic-Lagrangian representations of the incompressible Navier–Stokes
equations the transported momentum is the pullback one-form
`μ_t = A_t^* u₀` and the velocity is recovered as `u = P 𝔼[μ_t]` (Leray
projection of the expected covector); see P. Constantin, G. Iyer,
*A stochastic Lagrangian representation of the three-dimensional
incompressible Navier–Stokes equations*, Comm. Pure Appl. Math. **61** (2008),
330–345, arXiv:math/0511067, and, for the classical pullback form of the
momentum, H. Weber, *Ueber eine Transformation der hydrodynamischen
Gleichungen*, J. Reine Angew. Math. **68** (1868), 286–292.

At time `0` the transported covector is the initial datum `u₀` itself.  The
witness below therefore shows that a scalar potential ansatz `μ = dW` cannot
represent a general divergence-free initial momentum: any initial datum
carrying vorticity (here a single transverse Fourier mode) already has a
non-closed momentum one-form, while `d(dW) = 0`.  The state space for the
transported momentum must admit non-exact covectors.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped RealInnerProductSpace BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coordinate exterior derivative of a one-form, evaluated on a pair of
constant vectors: `dμ(v, w) = ⟪D_v μ, w⟫ − ⟪D_w μ, v⟫` at `x`. -/
def oneFormExtDerivAt (μ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (x v w : EuclideanSpace ℝ ι) : ℝ :=
  ⟪fderiv ℝ μ x v, w⟫ - ⟪fderiv ℝ μ x w, v⟫

/-- A one-form is exact when it is the differential of a `C²` scalar
potential. -/
def IsExactOneForm (μ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) : Prop :=
  ∃ W : EuclideanSpace ℝ ι → ℝ,
    ContDiff ℝ 2 W ∧ ∀ y v, fderiv ℝ W y v = ⟪μ y, v⟫

/-- Pointwise coordinate divergence of a vector field. -/
def coordDivergence (u : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ a, ⟪fderiv ℝ u x (EuclideanSpace.single a 1), EuclideanSpace.single a 1⟫

section Exactness

variable {μ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}

omit [DecidableEq ι] in
/-- Exact one-forms are closed: the coordinate exterior derivative vanishes
wherever `μ` is differentiable, by symmetry of the second derivative of the
`C²` potential. -/
theorem oneFormExtDerivAt_eq_zero_of_exact (hexact : IsExactOneForm μ)
    (x : EuclideanSpace ℝ ι) (hμ : DifferentiableAt ℝ μ x)
    (v w : EuclideanSpace ℝ ι) :
    oneFormExtDerivAt μ x v w = 0 := by
  obtain ⟨W, hW, hdW⟩ := hexact
  -- The second derivative of the potential computes the paired derivative of μ.
  have hpair : ∀ z : EuclideanSpace ℝ ι,
      fderiv ℝ (fun y => fderiv ℝ W y z) x = (innerSL ℝ z).comp (fderiv ℝ μ x) := by
    intro z
    have hfun : (fun y => fderiv ℝ W y z) = fun y => ⟪z, μ y⟫ := by
      funext y
      rw [hdW y z, real_inner_comm]
    rw [hfun]
    exact (((innerSL ℝ z).hasFDerivAt).comp x hμ.hasFDerivAt).fderiv
  -- Symmetry of the second derivative of the C² potential.
  have hsymm : IsSymmSndFDerivAt ℝ W x :=
    (hW.contDiffAt).isSymmSndFDerivAt (by norm_num)
  -- Express both pairings through the second derivative of W.
  have hWdiff : DifferentiableAt ℝ (fderiv ℝ W) x := by
    have : ContDiff ℝ 1 (fderiv ℝ W) := hW.fderiv_right (by norm_num)
    exact (this.differentiable (by norm_num)).differentiableAt
  have hclm : ∀ z : EuclideanSpace ℝ ι,
      fderiv ℝ (fun y => fderiv ℝ W y z) x =
        (fderiv ℝ (fderiv ℝ W) x).flip z := by
    intro z
    rw [fderiv_clm_apply hWdiff (differentiableAt_const z)]
    simp
  have hvw : ⟪fderiv ℝ μ x v, w⟫ = fderiv ℝ (fderiv ℝ W) x v w := by
    have h1 := hpair w
    have h2 := hclm w
    have := h2.symm.trans h1
    have happ := congrArg (fun L => L v) this
    simpa [real_inner_comm] using happ.symm
  have hwv : ⟪fderiv ℝ μ x w, v⟫ = fderiv ℝ (fderiv ℝ W) x w v := by
    have h1 := hpair v
    have h2 := hclm v
    have := h2.symm.trans h1
    have happ := congrArg (fun L => L w) this
    simpa [real_inner_comm] using happ.symm
  rw [oneFormExtDerivAt, hvw, hwv, hsymm.eq v w, sub_self]

end Exactness

section ProfileModeWitness

variable {φ dφ : ℝ → ℝ} {k e : EuclideanSpace ℝ ι}

/-- Divergence of a profile mode: `dφ(⟪k,x⟫) ⟪k, e⟫`.  Transverse modes
(`⟪k, e⟫ = 0`) are divergence-free. -/
theorem coordDivergence_profileMode (hφ : ∀ t, HasDerivAt φ (dφ t) t)
    (x : EuclideanSpace ℝ ι) :
    coordDivergence (profileMode φ k e) x = dφ ⟪k, x⟫ * ⟪k, e⟫ := by
  have hE := hasFDerivAt_profileMode (ι := ι) hφ k e x
  unfold coordDivergence
  rw [hE.fderiv]
  have hterm : ∀ a : ι,
      ⟪((dφ ⟪k, x⟫ • innerSL ℝ k).smulRight e) (EuclideanSpace.single a 1),
        EuclideanSpace.single a 1⟫ = dφ ⟪k, x⟫ * (k a * e a) := by
    intro a
    have hka : ⟪k, EuclideanSpace.single a (1 : ℝ)⟫ = k a := by
      simp [EuclideanSpace.inner_single_right]
    have hea : ⟪e, EuclideanSpace.single a (1 : ℝ)⟫ = e a := by
      simp [EuclideanSpace.inner_single_right]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [real_inner_smul_left, smul_apply, innerSL_apply_apply, hka, hea]
    ring
  calc ∑ a, ⟪((dφ ⟪k, x⟫ • innerSL ℝ k).smulRight e) (EuclideanSpace.single a 1),
        EuclideanSpace.single a 1⟫
      = ∑ a, dφ ⟪k, x⟫ * (k a * e a) :=
        Finset.sum_congr rfl fun a _ => hterm a
    _ = dφ ⟪k, x⟫ * ∑ a, k a * e a := by rw [Finset.mul_sum]
    _ = dφ ⟪k, x⟫ * ⟪k, e⟫ := by
        congr 1
        rw [PiLp.inner_apply]
        simp [mul_comm]

omit [DecidableEq ι] in
/-- Exterior derivative of a profile mode at a point, on constant vectors:
`dφ(⟪k,x⟫) (⟪k, v⟫⟪e, w⟫ − ⟪k, w⟫⟪e, v⟫)`. -/
theorem oneFormExtDerivAt_profileMode (hφ : ∀ t, HasDerivAt φ (dφ t) t)
    (x v w : EuclideanSpace ℝ ι) :
    oneFormExtDerivAt (profileMode φ k e) x v w =
      dφ ⟪k, x⟫ * (⟪k, v⟫ * ⟪e, w⟫ - ⟪k, w⟫ * ⟪e, v⟫) := by
  have hE := hasFDerivAt_profileMode (ι := ι) hφ k e x
  unfold oneFormExtDerivAt
  rw [hE.fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, smul_apply,
    innerSL_apply_apply, real_inner_smul_left, smul_eq_mul]
  ring

end ProfileModeWitness

section Witness

/-- **Divergence-free, smooth, non-exact witness.**  On any coordinate space
with two distinct coordinates there is a smooth everywhere-divergence-free
vector field whose one-form is not exact: the transverse sine mode
`y ↦ sin(y j) • eᵢ`.  Its exterior derivative at the origin on the coordinate
pair `(eⱼ, eᵢ)` equals `1`, while exact one-forms are closed.  Consequently a
scalar-potential ansatz cannot carry a general divergence-free momentum. -/
theorem exists_divergenceFree_smooth_not_exact {i j : ι} (hij : i ≠ j) :
    ∃ u₀ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι,
      ContDiff ℝ 2 u₀ ∧
      (∀ x, coordDivergence u₀ x = 0) ∧
      ¬ IsExactOneForm u₀ := by
  classical
  refine ⟨profileMode Real.sin (EuclideanSpace.single j 1)
    (EuclideanSpace.single i 1), ?_, ?_, ?_⟩
  · -- Smoothness of the sine mode.
    have hphase : ContDiff ℝ 2
        (fun y : EuclideanSpace ℝ ι => ⟪(EuclideanSpace.single j 1 :
          EuclideanSpace ℝ ι), y⟫) :=
      (innerSL ℝ (EuclideanSpace.single j 1 : EuclideanSpace ℝ ι)).contDiff
    exact (Real.contDiff_sin.comp hphase).smul contDiff_const
  · -- Divergence-free: the mode is transverse.
    intro x
    rw [coordDivergence_profileMode (dφ := Real.cos) Real.hasDerivAt_sin x]
    have horth : ⟪(EuclideanSpace.single j 1 : EuclideanSpace ℝ ι),
        EuclideanSpace.single i 1⟫ = 0 := by
      simp [EuclideanSpace.inner_single_left, hij]
    rw [horth, mul_zero]
  · -- Non-exactness: the exterior derivative is 1 ≠ 0 at the origin.
    intro hexact
    have hdiff := (hasFDerivAt_profileMode (dφ := Real.cos) Real.hasDerivAt_sin
      (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)
      (0 : EuclideanSpace ℝ ι)).differentiableAt
    have hzero := oneFormExtDerivAt_eq_zero_of_exact hexact 0 hdiff
      (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)
    rw [oneFormExtDerivAt_profileMode (dφ := Real.cos) Real.hasDerivAt_sin]
      at hzero
    have hjj : ⟪(EuclideanSpace.single j 1 : EuclideanSpace ℝ ι),
        EuclideanSpace.single j 1⟫ = 1 := by
      simp
    have hii : ⟪(EuclideanSpace.single i 1 : EuclideanSpace ℝ ι),
        EuclideanSpace.single i 1⟫ = 1 := by
      simp
    have hji : ⟪(EuclideanSpace.single j 1 : EuclideanSpace ℝ ι),
        EuclideanSpace.single i 1⟫ = 0 := by
      simp [EuclideanSpace.inner_single_left, hij]
    have hij' : ⟪(EuclideanSpace.single i 1 : EuclideanSpace ℝ ι),
        EuclideanSpace.single j 1⟫ = 0 := by
      simp [EuclideanSpace.inner_single_left, hij]
    rw [hjj, hii, hji, hij'] at hzero
    have hzeroinner : ⟪(EuclideanSpace.single j 1 : EuclideanSpace ℝ ι),
        (0 : EuclideanSpace ℝ ι)⟫ = 0 := inner_zero_right _
    rw [hzeroinner, Real.cos_zero] at hzero
    norm_num at hzero

/-- The dimension-3 form of the witness, on the first two coordinates. -/
theorem exists_divergenceFree_smooth_not_exact_dim3 :
    ∃ u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      ContDiff ℝ 2 u₀ ∧
      (∀ x, coordDivergence u₀ x = 0) ∧
      ¬ IsExactOneForm u₀ :=
  exists_divergenceFree_smooth_not_exact (i := (0 : Fin 3)) (j := 1)
    (by decide)

end Witness

end NavierStokes
end FluidDynamics
end Mettapedia
