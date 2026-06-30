import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Abstract Bakry-Emery conditional reduction

This file isolates the conditional replacement for the false uniform adjoint
bound used in the SG heat route.  It proves the reusable abstract
Bakry-Emery gradient estimate from an explicit local curvature-dimension
hypothesis and then packages the Navier-Stokes consequence as a conditional
scaffold.

Nothing here proves a Navier-Stokes regularity theorem.  The single geometric
input for the SG generator is the local `CD(-K, infinity)` hypothesis; it is a
field of the conditional datum and is never discharged in this file.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- A minimal abstract carré-du-champ semigroup.

The analytic identities that usually require diffusion, symmetry, and
self-adjointness arguments are kept as structure fields.  The checked theorems
below are conditional on an explicitly provided structure. -/
structure CarreDuChampSemigroup where
  Func : Type
  funcAddCommGroup : AddCommGroup Func
  funcModule : Module ℝ Func
  Point : Type
  P : ℝ → Func →ₗ[ℝ] Func
  L : Func →ₗ[ℝ] Func
  Gamma : Func → Func → Func
  eval : Point → Func →ₗ[ℝ] ℝ
  mul : Func → Func → Func
  semigroup_zero : ∀ f : Func, P 0 f = f
  semigroup_add : ∀ (s t : ℝ) (f : Func), P (s + t) f = P s (P t f)
  gamma_symm : ∀ (f g : Func) (x : Point), eval x (Gamma f g) = eval x (Gamma g f)
  gamma_nonneg : ∀ (f : Func) (x : Point), 0 ≤ eval x (Gamma f f)
  gamma_smul_right :
    ∀ (a : ℝ) (f g : Func), Gamma f (a • g) = a • Gamma f g
  semigroup_mono :
    ∀ {f g : Func} {t : ℝ} {x : Point},
      0 ≤ t →
        (∀ y : Point, eval y f ≤ eval y g) → eval x (P t f) ≤ eval x (P t g)
  semigroup_le_const :
    ∀ {f : Func} {c t : ℝ} {x : Point},
      0 ≤ t → (∀ y : Point, eval y f ≤ c) → eval x (P t f) ≤ c
  generator_product_rule :
    ∀ f g : Func,
      L (mul f g) = mul f (L g) + mul g (L f) + (2 : ℝ) • Gamma f g
  timeDeriv : (ℝ → Func) → ℝ → Func
  semigroup_derivative_const :
    ∀ (s : ℝ) (f : Func), timeDeriv (fun r => P r f) s = P s (L f)
  semigroup_generator_commute :
    ∀ (s : ℝ) (f : Func), P s (L f) = L (P s f)
  timeDeriv_semigroup_interpolation :
    ∀ (t s : ℝ) (f : Func),
      timeDeriv
          (fun r => P r (Gamma (P (t - r) f) (P (t - r) f))) s =
        P s (L (Gamma (P (t - s) f) (P (t - s) f))) +
          P s
            (timeDeriv
              (fun r => Gamma (P (t - r) f) (P (t - r) f)) s)
  timeDeriv_reverse_semigroup :
    ∀ (t s : ℝ) (f : Func),
      timeDeriv (fun r => P (t - r) f) s = -L (P (t - s) f)
  timeDeriv_gamma_self_reverse :
    ∀ (t s : ℝ) (f : Func),
      timeDeriv
          (fun r => Gamma (P (t - r) f) (P (t - r) f)) s =
        (2 : ℝ) •
          Gamma (P (t - s) f)
            (timeDeriv (fun r => P (t - r) f) s)
  interpolation_scalar_continuous :
    ∀ {t : ℝ} {f : Func} {x : Point}, 0 ≤ t →
      ContinuousOn
        (fun s : ℝ => eval x (P s (Gamma (P (t - s) f) (P (t - s) f))))
        (Set.Icc 0 t)
  interpolation_scalar_hasDerivWithinAt :
    ∀ {t : ℝ} {f : Func} {x : Point} {s : ℝ}, s ∈ Set.Ioo 0 t →
      HasDerivWithinAt
        (fun r : ℝ => eval x (P r (Gamma (P (t - r) f) (P (t - r) f))))
        (eval x
          (timeDeriv
            (fun r : ℝ => P r (Gamma (P (t - r) f) (P (t - r) f))) s))
        (Set.Ioo 0 t) s
  generator_carre_du_champ_identity : Prop
  semigroup_self_adjoint : Prop

attribute [instance] CarreDuChampSemigroup.funcAddCommGroup
attribute [instance] CarreDuChampSemigroup.funcModule

namespace CarreDuChampSemigroup

/-- The square field `Gamma(f) = Gamma(f,f)`. -/
def gammaSelf (M : CarreDuChampSemigroup) (f : M.Func) : M.Func :=
  M.Gamma f f

/-- The iterated carré-du-champ, defined by the Bochner generator identity. -/
def gamma2 (M : CarreDuChampSemigroup) (f : M.Func) : M.Func :=
  (1 / 2 : ℝ) • (M.L (M.gammaSelf f) - (2 : ℝ) • M.Gamma f (M.L f))

/-- The Bochner identity is definitional in this abstract API. -/
theorem gamma2_bochner_identity (M : CarreDuChampSemigroup) (f : M.Func) :
    M.gamma2 f =
      (1 / 2 : ℝ) •
        (M.L (M.gammaSelf f) - (2 : ℝ) • M.Gamma f (M.L f)) := by
  rfl

/-- Twice `Gamma2` is the Bochner numerator. -/
theorem two_smul_gamma2 (M : CarreDuChampSemigroup) (f : M.Func) :
    (2 : ℝ) • M.gamma2 f =
      M.L (M.gammaSelf f) - (2 : ℝ) • M.Gamma f (M.L f) := by
  simp [gamma2, smul_smul]

/-- The semigroup-linear form of the Bochner numerator. -/
theorem two_smul_P_gamma2 (M : CarreDuChampSemigroup)
    (s : ℝ) (f : M.Func) :
    (2 : ℝ) • M.P s (M.gamma2 f) =
      M.P s (M.L (M.gammaSelf f)) -
        (2 : ℝ) • M.P s (M.Gamma f (M.L f)) := by
  calc
    (2 : ℝ) • M.P s (M.gamma2 f)
        = M.P s ((2 : ℝ) • M.gamma2 f) := by
          simp
    _ = M.P s (M.L (M.gammaSelf f) - (2 : ℝ) • M.Gamma f (M.L f)) := by
          rw [M.two_smul_gamma2]
    _ = M.P s (M.L (M.gammaSelf f)) -
          (2 : ℝ) • M.P s (M.Gamma f (M.L f)) := by
          simp

/-- The one-sided local curvature-dimension input `Gamma2(f) >= -K Gamma(f)`. -/
def CDMinusInfinity (M : CarreDuChampSemigroup) (K : ℝ) : Prop :=
  ∀ (f : M.Func) (x : M.Point),
    -K * M.eval x (M.gammaSelf f) ≤ M.eval x (M.gamma2 f)

/-- Variable-curvature curvature-dimension input
`Gamma2(f)(x) >= rho(x) * Gamma(f)(x)`. -/
def CDVariableInfinity (M : CarreDuChampSemigroup)
    (rho : M.Point → ℝ) : Prop :=
  ∀ (f : M.Func) (x : M.Point),
    rho x * M.eval x (M.gammaSelf f) ≤ M.eval x (M.gamma2 f)

/-- A variable-curvature lower bound reduces to the constant one-sided
`CD(-K, infinity)` input used by the checked Gronwall proof. -/
theorem cdMinusInfinity_of_cdVariable_lowerBound
    (M : CarreDuChampSemigroup) {rho : M.Point → ℝ} {rhoMin : ℝ}
    (hCD : M.CDVariableInfinity rho)
    (hmin : ∀ x : M.Point, rhoMin ≤ rho x) :
    M.CDMinusInfinity (-rhoMin) := by
  intro f x
  have hgamma : 0 ≤ M.eval x (M.gammaSelf f) :=
    M.gamma_nonneg f x
  have hmul :
      rhoMin * M.eval x (M.gammaSelf f) ≤
        rho x * M.eval x (M.gammaSelf f) :=
    mul_le_mul_of_nonneg_right (hmin x) hgamma
  calc
    -(-rhoMin) * M.eval x (M.gammaSelf f)
        = rhoMin * M.eval x (M.gammaSelf f) := by ring
    _ ≤ rho x * M.eval x (M.gammaSelf f) := hmul
    _ ≤ M.eval x (M.gamma2 f) := hCD f x

/-- Bakry-Emery interpolation:
`s |-> P_s (Gamma(P_{t-s} f))`. -/
def beInterpolation (M : CarreDuChampSemigroup)
    (t s : ℝ) (f : M.Func) : M.Func :=
  M.P s (M.gammaSelf (M.P (t - s) f))

theorem beInterpolation_zero (M : CarreDuChampSemigroup)
    (t : ℝ) (f : M.Func) :
    M.beInterpolation t 0 f = M.gammaSelf (M.P t f) := by
  unfold beInterpolation
  rw [sub_zero, M.semigroup_zero]

theorem beInterpolation_time (M : CarreDuChampSemigroup)
    (t : ℝ) (f : M.Func) :
    M.beInterpolation t t f = M.P t (M.gammaSelf f) := by
  unfold beInterpolation
  rw [sub_self, M.semigroup_zero]

/-- Checked interpolation derivative identity:
`d/ds P_s Gamma(P_{t-s} f) = 2 P_s Gamma2(P_{t-s} f)`.

The derivative operator is abstract, but the result is no longer an assumed
lower-bound field: it follows from the supplied semigroup derivative laws,
the reverse heat-flow derivative, right-linearity of `Gamma`, and the
generator definition of `gamma2`. -/
theorem interpolationDerivativeIdentity_func (M : CarreDuChampSemigroup)
    (t s : ℝ) (f : M.Func) :
    M.timeDeriv (fun r => M.beInterpolation t r f) s =
      (2 : ℝ) • M.P s (M.gamma2 (M.P (t - s) f)) := by
  unfold beInterpolation gammaSelf
  rw [M.timeDeriv_semigroup_interpolation]
  rw [M.timeDeriv_gamma_self_reverse]
  rw [M.timeDeriv_reverse_semigroup]
  have hgamma :
      M.Gamma (M.P (t - s) f) (-M.L (M.P (t - s) f)) =
        -M.Gamma (M.P (t - s) f) (M.L (M.P (t - s) f)) := by
    calc
      M.Gamma (M.P (t - s) f) (-M.L (M.P (t - s) f))
          = M.Gamma (M.P (t - s) f)
              ((-1 : ℝ) • M.L (M.P (t - s) f)) := by
            simp
      _ = (-1 : ℝ) •
            M.Gamma (M.P (t - s) f) (M.L (M.P (t - s) f)) := by
            rw [M.gamma_smul_right]
      _ = -M.Gamma (M.P (t - s) f) (M.L (M.P (t - s) f)) := by
            simp
  have htwo :=
    (M.two_smul_P_gamma2 s (M.P (t - s) f)).symm
  have hPgamma :
      M.P s ((2 : ℝ) •
          M.Gamma (M.P (t - s) f) (-M.L (M.P (t - s) f))) =
        -(2 : ℝ) •
          M.P s (M.Gamma (M.P (t - s) f) (M.L (M.P (t - s) f))) := by
    rw [hgamma]
    simp
  rw [hPgamma]
  simpa [gammaSelf, sub_eq_add_neg] using htwo

/-- Pointwise form of the checked interpolation derivative identity. -/
def InterpolationDerivativeIdentity (M : CarreDuChampSemigroup)
    (t : ℝ) (f : M.Func) (x : M.Point) : Prop :=
  ∀ s : ℝ, 0 ≤ s → s ≤ t →
    M.eval x (M.timeDeriv (fun r => M.beInterpolation t r f) s) =
      2 * M.eval x (M.P s (M.gamma2 (M.P (t - s) f)))

/-- The checked pointwise interpolation derivative identity. -/
theorem interpolationDerivativeIdentity (M : CarreDuChampSemigroup)
    (t : ℝ) (f : M.Func) (x : M.Point) :
    M.InterpolationDerivativeIdentity t f x := by
  intro s _hs _hst
  have h :=
    congrArg (fun g : M.Func => M.eval x g)
      (M.interpolationDerivativeIdentity_func t s f)
  simpa using h

/-- The checked endpoint form of the interpolation differential lower bound.

Analytically this is obtained from
`d/ds P_s Gamma(P_{t-s} f) = 2 P_s Gamma2(P_{t-s} f)` plus the local
`CD(-K, infinity)` inequality and positivity/order preservation of the
semigroup. -/
def InterpolationDerivativeLowerBound (M : CarreDuChampSemigroup)
    (K t : ℝ) (f : M.Func) (x : M.Point) : Prop :=
  ∀ s : ℝ, 0 ≤ s → s ≤ t →
    -2 * K * M.eval x (M.beInterpolation t s f) ≤
      2 * M.eval x (M.P s (M.gamma2 (M.P (t - s) f)))

/-- `CD(-K, infinity)` and semigroup order preservation imply the
interpolation lower bound used by the comparison step. -/
theorem interpolationDerivativeLowerBound_of_CD
    (M : CarreDuChampSemigroup) {K t : ℝ} {f : M.Func} {x : M.Point}
    (hCD : M.CDMinusInfinity K) :
    M.InterpolationDerivativeLowerBound K t f x := by
  intro s _hs _hst
  let g : M.Func := M.P (t - s) f
  change -2 * K * M.eval x (M.P s (M.gammaSelf g)) ≤
    2 * M.eval x (M.P s (M.gamma2 g))
  have hpoint :
      ∀ y : M.Point,
        M.eval y ((-K) • M.gammaSelf g) ≤ M.eval y (M.gamma2 g) := by
    intro y
    have hy := hCD g y
    simpa using hy
  have hmono :
      M.eval x (M.P s ((-K) • M.gammaSelf g)) ≤
        M.eval x (M.P s (M.gamma2 g)) :=
    M.semigroup_mono (f := (-K) • M.gammaSelf g)
      (g := M.gamma2 g) (t := s) (x := x) _hs hpoint
  have hscaled :
      -K * M.eval x (M.P s (M.gammaSelf g)) ≤
        M.eval x (M.P s (M.gamma2 g)) := by
    simpa using hmono
  have htwo :
      2 * (-K * M.eval x (M.P s (M.gammaSelf g))) ≤
        2 * M.eval x (M.P s (M.gamma2 g)) :=
    mul_le_mul_of_nonneg_left hscaled (by norm_num)
  calc
    -2 * K * M.eval x (M.P s (M.gammaSelf g))
        = 2 * (-K * M.eval x (M.P s (M.gammaSelf g))) := by
          ring
    _ ≤ 2 * M.eval x (M.P s (M.gamma2 g)) := htwo

/-- Weighted Bakry-Emery interpolation used in the scalar comparison step. -/
def weightedBEInterpolation (M : CarreDuChampSemigroup)
    (K t : ℝ) (f : M.Func) (x : M.Point) (s : ℝ) : ℝ :=
  Real.exp (2 * K * s) * M.eval x (M.beInterpolation t s f)

/-- The weighted interpolation is monotone once the interpolation differential
lower bound has been derived. -/
theorem weightedBEInterpolation_monoOn
    (M : CarreDuChampSemigroup) {K t : ℝ} {f : M.Func} {x : M.Point}
    (_hK : 0 ≤ K) (ht : 0 ≤ t)
    (hIdentity : M.InterpolationDerivativeIdentity t f x)
    (hLower : M.InterpolationDerivativeLowerBound K t f x) :
    MonotoneOn (M.weightedBEInterpolation K t f x) (Set.Icc 0 t) := by
  let φ : ℝ → ℝ := fun s => M.eval x (M.beInterpolation t s f)
  let φ' : ℝ → ℝ :=
    fun s => M.eval x
      (M.timeDeriv (fun r : ℝ => M.beInterpolation t r f) s)
  have hφcont : ContinuousOn φ (Set.Icc 0 t) := by
    simpa [φ, beInterpolation, gammaSelf]
      using M.interpolation_scalar_continuous (t := t) (f := f) (x := x) ht
  have hmonoProd :
      MonotoneOn ((fun s : ℝ => Real.exp (2 * K * s)) * φ) (Set.Icc 0 t) := by
    have hexpcont :
        ContinuousOn (fun s : ℝ => Real.exp (2 * K * s)) (Set.Icc 0 t) := by
      fun_prop
    refine
      monotoneOn_of_hasDerivWithinAt_nonneg
        (D := Set.Icc 0 t)
        (f := ((fun s : ℝ => Real.exp (2 * K * s)) * φ))
        (f' := fun s : ℝ => Real.exp (2 * K * s) * (2 * K * φ s + φ' s))
        (convex_Icc 0 t) (hexpcont.mul hφcont) ?_ ?_
    · rw [interior_Icc]
      intro s hs
      have hφder : HasDerivWithinAt φ (φ' s) (Set.Ioo 0 t) s := by
        simpa [φ, φ', beInterpolation, gammaSelf]
          using M.interpolation_scalar_hasDerivWithinAt
            (t := t) (f := f) (x := x) hs
      have hlinear :
          HasDerivWithinAt (fun r : ℝ => (2 * K) * r) (2 * K) (Set.Ioo 0 t) s := by
        simpa using
          ((hasDerivWithinAt_id (x := s) (s := Set.Ioo 0 t)).const_mul (2 * K))
      have hexpder :
          HasDerivWithinAt (fun r : ℝ => Real.exp (2 * K * r))
            (Real.exp (2 * K * s) * (2 * K)) (Set.Ioo 0 t) s := by
        simpa [mul_assoc] using hlinear.exp
      have hwder := hexpder.mul hφder
      simpa [Pi.mul_apply, mul_add, mul_assoc, mul_left_comm, mul_comm]
        using hwder
    · rw [interior_Icc]
      intro s hs
      have hderiv_lower : -2 * K * φ s ≤ φ' s := by
        have hId := hIdentity s hs.1.le hs.2.le
        have hLow := hLower s hs.1.le hs.2.le
        rw [← hId] at hLow
        simpa [φ, φ'] using hLow
      have hsum : 0 ≤ 2 * K * φ s + φ' s := by
        have h := add_le_add_left hderiv_lower (2 * K * φ s)
        ring_nf at h
        simpa [mul_assoc, mul_left_comm, mul_comm] using h
      have hexp_nonneg : 0 ≤ Real.exp (2 * K * s) :=
        le_of_lt (Real.exp_pos _)
      have hweighted :
          0 ≤ Real.exp (2 * K * s) * (2 * K * φ s + φ' s) :=
        mul_nonneg hexp_nonneg hsum
      simpa [mul_add, mul_assoc, mul_left_comm, mul_comm]
        using hweighted
  intro a ha b hb hab
  simpa [weightedBEInterpolation, φ, Pi.mul_apply] using hmonoProd ha hb hab

/-- Scalar comparison closing the Bakry-Emery interpolation argument.

The proof is the standard integrating-factor step: from
`φ'(s) >= -2K φ(s)` it proves monotonicity of
`s |-> exp(2*K*s) * φ(s)`, then evaluates at `0` and `t`. -/
theorem gronwallFromInterpolation
    (M : CarreDuChampSemigroup) {K t : ℝ} {f : M.Func} {x : M.Point}
    (hK : 0 ≤ K) (ht : 0 ≤ t)
    (hIdentity : M.InterpolationDerivativeIdentity t f x)
    (hLower : M.InterpolationDerivativeLowerBound K t f x) :
    M.eval x (M.gammaSelf (M.P t f)) ≤
      Real.exp (2 * K * t) *
        M.eval x (M.P t (M.gammaSelf f)) := by
  have hmono :=
    M.weightedBEInterpolation_monoOn (K := K) (t := t) (f := f) (x := x)
      hK ht hIdentity hLower
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 t := Set.left_mem_Icc.mpr ht
  have htmem : t ∈ Set.Icc 0 t := Set.right_mem_Icc.mpr ht
  have hle := hmono h0mem htmem ht
  simpa [weightedBEInterpolation, beInterpolation_zero, beInterpolation_time]
    using hle

end CarreDuChampSemigroup

/-- A carré-du-champ semigroup packaged for the Bakry-Emery estimate.

The final gradient estimate is not a field.  It is proved from the structure
fields and the explicit `CD(-K, infinity)` hypothesis. -/
structure BakryEmeryGronwallFramework where
  base : CarreDuChampSemigroup

/-- Bakry-Emery gradient estimate in abstract carré-du-champ form:

`CD(-K, infinity)` implies
`Gamma(P_t f) <= exp(2*K*t) P_t(Gamma f)`.

The proof genuinely passes through the interpolation derivative identity, the
CD-derived interpolation lower bound, and the checked scalar integrating-factor
comparison; the estimate itself is not assumed. -/
theorem bakryEmeryGradientEstimate
    (G : BakryEmeryGronwallFramework) {K t : ℝ}
    (hK : 0 ≤ K) (ht : 0 ≤ t)
    (hCD : G.base.CDMinusInfinity K)
    (f : G.base.Func) (x : G.base.Point) :
    G.base.eval x (G.base.gammaSelf (G.base.P t f)) ≤
      Real.exp (2 * K * t) *
        G.base.eval x (G.base.P t (G.base.gammaSelf f)) := by
  exact
    G.base.gronwallFromInterpolation (K := K) (t := t) (f := f) (x := x)
      hK ht
      (G.base.interpolationDerivativeIdentity t f x)
      (G.base.interpolationDerivativeLowerBound_of_CD
        (K := K) (t := t) (f := f) (x := x) hCD)

/-- Variable-curvature lower-bound form of the Bakry-Emery estimate.

When `rho(x) >= rhoMin` and `rhoMin <= 0`, the variable condition
`CD(rho, infinity)` implies the checked constant estimate with
`K = -rhoMin`.  A genuinely variable weighted interpolation would require
extra Feynman-Kac/invariant-measure structure not present in the minimal
`CarreDuChampSemigroup` API. -/
theorem bakryEmeryGradientEstimate_variableLowerBound
    (G : BakryEmeryGronwallFramework) {rho : G.base.Point → ℝ}
    {rhoMin t : ℝ}
    (hrhoMin_nonpos : rhoMin ≤ 0) (ht : 0 ≤ t)
    (hCD : G.base.CDVariableInfinity rho)
    (hmin : ∀ x : G.base.Point, rhoMin ≤ rho x)
    (f : G.base.Func) (x : G.base.Point) :
    G.base.eval x (G.base.gammaSelf (G.base.P t f)) ≤
      Real.exp (2 * (-rhoMin) * t) *
        G.base.eval x (G.base.P t (G.base.gammaSelf f)) := by
  exact
    bakryEmeryGradientEstimate G
      (K := -rhoMin) (t := t) (by linarith) ht
      (G.base.cdMinusInfinity_of_cdVariable_lowerBound hCD hmin) f x

/-!
## A concrete two-state witness

The next section instantiates the scaffold on the continuous-time reversible
two-point chain with jump rate `1`.  The heat semigroup is written in closed
form:

`P_t f(0) = mean(f) - exp(-2t) diff(f)/2`,
`P_t f(1) = mean(f) + exp(-2t) diff(f)/2`.

This is the usual closed form of `Matrix.exp (t • L)` for
`L = [[-1, 1], [1, -1]]`; the checked Lean instance below uses the explicit
formula so that all structure fields reduce to finite arithmetic and scalar
`Real.exp` differentiation.
-/

namespace TwoPointChain

abbrev State := Fin 2

abbrev Func := State → ℝ

def mean (f : Func) : ℝ :=
  (f 0 + f 1) / 2

def diff (f : Func) : ℝ :=
  f 1 - f 0

def mul (f g : Func) : Func :=
  fun x => f x * g x

def LFun (f : Func) : Func
  | 0 => diff f
  | 1 => -diff f

def PFun (t : ℝ) (f : Func) : Func
  | 0 => mean f - Real.exp (-2 * t) * diff f / 2
  | 1 => mean f + Real.exp (-2 * t) * diff f / 2

def GammaFun (f g : Func) : Func :=
  fun _ => diff f * diff g / 2

noncomputable def timeDeriv (u : ℝ → Func) (s : ℝ) : Func :=
  fun x => deriv (fun r : ℝ => u r x) s

lemma mean_PFun (t : ℝ) (f : Func) :
    mean (PFun t f) = mean f := by
  simp [mean, PFun]

lemma diff_PFun (t : ℝ) (f : Func) :
    diff (PFun t f) = Real.exp (-2 * t) * diff f := by
  simp [diff, PFun]

lemma mean_LFun (f : Func) :
    mean (LFun f) = 0 := by
  simp [mean, LFun, diff]

lemma diff_LFun (f : Func) :
    diff (LFun f) = -2 * diff f := by
  simp [diff, LFun]
  ring

lemma PFun_zero (f : Func) :
    PFun 0 f = f := by
  funext x
  fin_cases x <;> simp [PFun, mean, diff] <;> ring

lemma PFun_add (s t : ℝ) (f : Func) :
    PFun (s + t) f = PFun s (PFun t f) := by
  have hexp : Real.exp (-(2 * (s + t))) =
      Real.exp (-(2 * s)) * Real.exp (-(2 * t)) := by
    rw [← Real.exp_add]
    ring_nf
  funext x
  fin_cases x <;> simp [PFun, mean_PFun, diff_PFun]
  all_goals
    rw [hexp]
    ring_nf

noncomputable def P (t : ℝ) : Func →ₗ[ℝ] Func where
  toFun := PFun t
  map_add' := by
    intro f g
    funext x
    fin_cases x <;> simp [PFun, mean, diff] <;> ring
  map_smul' := by
    intro a f
    funext x
    fin_cases x <;> simp [PFun, mean, diff] <;> ring

def L : Func →ₗ[ℝ] Func where
  toFun := LFun
  map_add' := by
    intro f g
    funext x
    fin_cases x <;> simp [LFun, diff] <;> ring
  map_smul' := by
    intro a f
    funext x
    fin_cases x <;> simp [LFun, diff] <;> ring

def eval (x : State) : Func →ₗ[ℝ] ℝ where
  toFun := fun f => f x
  map_add' := by
    intro f g
    rfl
  map_smul' := by
    intro a f
    rfl

lemma GammaFun_symm (f g : Func) (x : State) :
    GammaFun f g x = GammaFun g f x := by
  simp [GammaFun]
  ring

lemma GammaFun_nonneg (f : Func) (x : State) :
    0 ≤ GammaFun f f x := by
  have hsq : 0 ≤ diff f ^ (2 : ℕ) := sq_nonneg (diff f)
  simp [GammaFun]
  nlinarith

lemma GammaFun_smul_right (a : ℝ) (f g : Func) :
    GammaFun f (a • g) = a • GammaFun f g := by
  funext x
  simp [GammaFun, diff]
  ring

lemma generator_product_rule (f g : Func) :
    L (mul f g) = mul f (L g) + mul g (L f) + (2 : ℝ) • GammaFun f g := by
  funext x
  fin_cases x <;> simp [L, LFun, mul, GammaFun, diff] <;> ring

lemma P_generator_commute (s : ℝ) (f : Func) :
    P s (L f) = L (P s f) := by
  funext x
  fin_cases x <;> simp [P, L, LFun, PFun, diff_PFun, diff_LFun, mean_LFun] <;>
    ring_nf

lemma hasDerivAt_exp_decay_half (a s : ℝ) :
    HasDerivAt (fun r : ℝ => Real.exp (-2 * r) * a / 2)
      (-(Real.exp (-2 * s) * a)) s := by
  have hlinear :
      HasDerivAt (fun r : ℝ => -2 * r) (-2) s := by
    simpa using (hasDerivAt_id s).const_mul (-2 : ℝ)
  have h := (hlinear.exp.mul_const (a / 2))
  simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using h

lemma timeDeriv_PFun (s : ℝ) (f : Func) :
    timeDeriv (fun r => PFun r f) s = PFun s (LFun f) := by
  funext x
  fin_cases x
  · have hterm := hasDerivAt_exp_decay_half (diff f) s
    have hder :
        HasDerivAt
          (fun r : ℝ => mean f - Real.exp (-2 * r) * diff f / 2)
          (Real.exp (-2 * s) * diff f) s := by
      simpa using (hterm.const_sub (mean f))
    change deriv (fun r : ℝ => PFun r f 0) s = PFun s (LFun f) 0
    rw [show (fun r : ℝ => PFun r f 0) =
        (fun r : ℝ => mean f - Real.exp (-2 * r) * diff f / 2) by
          funext r
          simp [PFun]]
    rw [hder.deriv]
    simp [PFun, mean_LFun, diff_LFun]
    ring_nf
  · have hterm := hasDerivAt_exp_decay_half (diff f) s
    have hder :
        HasDerivAt
          (fun r : ℝ => mean f + Real.exp (-2 * r) * diff f / 2)
          (-(Real.exp (-2 * s) * diff f)) s := by
      simpa using (hterm.const_add (mean f))
    change deriv (fun r : ℝ => PFun r f 1) s = PFun s (LFun f) 1
    rw [show (fun r : ℝ => PFun r f 1) =
        (fun r : ℝ => mean f + Real.exp (-2 * r) * diff f / 2) by
          funext r
          simp [PFun]]
    rw [hder.deriv]
    simp [PFun, mean_LFun, diff_LFun]
    ring_nf

lemma timeDeriv_reverse_PFun (t s : ℝ) (f : Func) :
    timeDeriv (fun r => PFun (t - r) f) s = -LFun (PFun (t - s) f) := by
  funext x
  fin_cases x
  · have hlinear :
        HasDerivAt (fun r : ℝ => -2 * (t - r)) 2 s := by
      simpa using ((hasDerivAt_const (x := s) t).sub (hasDerivAt_id s)).const_mul (-2 : ℝ)
    have hexp := hlinear.exp
    have hterm := hexp.mul_const (diff f / 2)
    have hder :
        HasDerivAt
          (fun r : ℝ => mean f - Real.exp (-2 * (t - r)) * diff f / 2)
          (-(Real.exp (-2 * (t - s)) * diff f)) s := by
      simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
        (hterm.const_sub (mean f))
    change deriv (fun r : ℝ => PFun (t - r) f 0) s =
      (-LFun (PFun (t - s) f)) 0
    rw [show (fun r : ℝ => PFun (t - r) f 0) =
        (fun r : ℝ => mean f - Real.exp (-2 * (t - r)) * diff f / 2) by
          funext r
          simp [PFun]]
    rw [hder.deriv]
    simp [LFun, diff_PFun]
  · have hlinear :
        HasDerivAt (fun r : ℝ => -2 * (t - r)) 2 s := by
      simpa using ((hasDerivAt_const (x := s) t).sub (hasDerivAt_id s)).const_mul (-2 : ℝ)
    have hexp := hlinear.exp
    have hterm := hexp.mul_const (diff f / 2)
    have hder :
        HasDerivAt
          (fun r : ℝ => mean f + Real.exp (-2 * (t - r)) * diff f / 2)
          (Real.exp (-2 * (t - s)) * diff f) s := by
      simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
        (hterm.const_add (mean f))
    change deriv (fun r : ℝ => PFun (t - r) f 1) s =
      (-LFun (PFun (t - s) f)) 1
    rw [show (fun r : ℝ => PFun (t - r) f 1) =
        (fun r : ℝ => mean f + Real.exp (-2 * (t - r)) * diff f / 2) by
          funext r
          simp [PFun]]
    rw [hder.deriv]
    simp [LFun, diff_PFun]

lemma P_mono {f g : Func} {t : ℝ} {x : State}
    (ht : 0 ≤ t) (hfg : ∀ y : State, f y ≤ g y) :
    eval x (P t f) ≤ eval x (P t g) := by
  have hexp_le : Real.exp (-2 * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hexp_nonneg : 0 ≤ Real.exp (-2 * t) := Real.exp_nonneg _
  have hcoef0 : 0 ≤ (1 + Real.exp (-2 * t)) / 2 := by nlinarith
  have hcoef1 : 0 ≤ (1 - Real.exp (-2 * t)) / 2 := by nlinarith
  fin_cases x
  · have hf0 := hfg 0
    have hf1 := hfg 1
    calc
      eval 0 (P t f)
          = ((1 + Real.exp (-2 * t)) / 2) * f 0 +
              ((1 - Real.exp (-2 * t)) / 2) * f 1 := by
              simp [eval, P, PFun, mean, diff]
              ring_nf
      _ ≤ ((1 + Real.exp (-2 * t)) / 2) * g 0 +
              ((1 - Real.exp (-2 * t)) / 2) * g 1 :=
              add_le_add
                (mul_le_mul_of_nonneg_left hf0 hcoef0)
                (mul_le_mul_of_nonneg_left hf1 hcoef1)
      _ = eval 0 (P t g) := by
              simp [eval, P, PFun, mean, diff]
              ring_nf
  · have hf0 := hfg 0
    have hf1 := hfg 1
    calc
      eval 1 (P t f)
          = ((1 - Real.exp (-2 * t)) / 2) * f 0 +
              ((1 + Real.exp (-2 * t)) / 2) * f 1 := by
              simp [eval, P, PFun, mean, diff]
              ring_nf
      _ ≤ ((1 - Real.exp (-2 * t)) / 2) * g 0 +
              ((1 + Real.exp (-2 * t)) / 2) * g 1 :=
              add_le_add
                (mul_le_mul_of_nonneg_left hf0 hcoef1)
                (mul_le_mul_of_nonneg_left hf1 hcoef0)
      _ = eval 1 (P t g) := by
              simp [eval, P, PFun, mean, diff]
              ring_nf

lemma P_le_const {f : Func} {c t : ℝ} {x : State}
    (ht : 0 ≤ t) (hf : ∀ y : State, eval y f ≤ c) :
    eval x (P t f) ≤ c := by
  have hconst : ∀ y : State, eval y f ≤ eval y (fun _ : State => c) := by
    intro y
    exact hf y
  have hmono := P_mono (f := f) (g := fun _ : State => c) (t := t) (x := x) ht hconst
  have hconstP : eval x (P t (fun _ : State => c)) = c := by
    fin_cases x <;> simp [eval, P, PFun, mean, diff]
  exact hmono.trans_eq hconstP

lemma PFun_const (t c : ℝ) :
    PFun t (fun _ : State => c) = fun _ : State => c := by
  funext x
  fin_cases x <;> simp [PFun, mean, diff]

lemma LFun_const (c : ℝ) :
    LFun (fun _ : State => c) = 0 := by
  funext x
  fin_cases x <;> simp [LFun, diff]

lemma GammaFun_PFun_self (t : ℝ) (f : Func) :
    GammaFun (PFun t f) (PFun t f) =
      fun _ : State => (Real.exp (-2 * t) * diff f) ^ (2 : ℕ) / 2 := by
  funext x
  simp [GammaFun, diff_PFun, pow_two]

lemma hasDerivAt_reverse_mode (a t s : ℝ) :
    HasDerivAt (fun r : ℝ => Real.exp (-2 * (t - r)) * a)
      (2 * Real.exp (-2 * (t - s)) * a) s := by
  have hlinear :
      HasDerivAt (fun r : ℝ => -2 * (t - r)) 2 s := by
    simpa using ((hasDerivAt_const (x := s) t).sub (hasDerivAt_id s)).const_mul (-2 : ℝ)
  have h := hlinear.exp.mul_const a
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

lemma hasDerivAt_reverse_gamma_scalar (t s : ℝ) (f : Func) :
    HasDerivAt
      (fun r : ℝ => (Real.exp (-2 * (t - r)) * diff f) ^ (2 : ℕ) / 2)
      (2 * (Real.exp (-2 * (t - s)) * diff f) ^ (2 : ℕ)) s := by
  have hmode := hasDerivAt_reverse_mode (diff f) t s
  have hsquare := hmode.mul hmode
  have h := hsquare.div_const 2
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
    using h.congr_deriv (by ring_nf)

lemma timeDeriv_gamma_reverse (t s : ℝ) (f : Func) :
    timeDeriv
        (fun r => GammaFun (PFun (t - r) f) (PFun (t - r) f)) s =
      (2 : ℝ) •
        GammaFun (PFun (t - s) f)
          (timeDeriv (fun r => PFun (t - r) f) s) := by
  have hscalar := hasDerivAt_reverse_gamma_scalar t s f
  funext x
  fin_cases x
  ·
    change deriv
        (fun r : ℝ => GammaFun (PFun (t - r) f) (PFun (t - r) f) 0) s =
      ((2 : ℝ) •
        GammaFun (PFun (t - s) f)
          (timeDeriv (fun r => PFun (t - r) f) s)) 0
    rw [show
        (fun r : ℝ => GammaFun (PFun (t - r) f) (PFun (t - r) f) 0) =
          (fun r : ℝ => (Real.exp (-2 * (t - r)) * diff f) ^ (2 : ℕ) / 2) by
        funext r
        simp [GammaFun, diff_PFun, pow_two]
        ]
    rw [hscalar.deriv]
    simp [GammaFun, timeDeriv_reverse_PFun, LFun, PFun, mean, diff, pow_two]
    ring_nf
  ·
    change deriv
        (fun r : ℝ => GammaFun (PFun (t - r) f) (PFun (t - r) f) 1) s =
      ((2 : ℝ) •
        GammaFun (PFun (t - s) f)
          (timeDeriv (fun r => PFun (t - r) f) s)) 1
    rw [show
        (fun r : ℝ => GammaFun (PFun (t - r) f) (PFun (t - r) f) 1) =
          (fun r : ℝ => (Real.exp (-2 * (t - r)) * diff f) ^ (2 : ℕ) / 2) by
        funext r
        simp [GammaFun, diff_PFun, pow_two]
        ]
    rw [hscalar.deriv]
    simp [GammaFun, timeDeriv_reverse_PFun, LFun, PFun, mean, diff, pow_two]
    ring_nf

lemma timeDeriv_semigroup_interpolation (t s : ℝ) (f : Func) :
    timeDeriv
        (fun r => PFun r (GammaFun (PFun (t - r) f) (PFun (t - r) f))) s =
      PFun s (LFun (GammaFun (PFun (t - s) f) (PFun (t - s) f))) +
        PFun s
          (timeDeriv
            (fun r => GammaFun (PFun (t - r) f) (PFun (t - r) f)) s) := by
  have hscalar := hasDerivAt_reverse_gamma_scalar t s f
  funext x
  fin_cases x
  ·
    change deriv
        (fun r : ℝ =>
          PFun r (GammaFun (PFun (t - r) f) (PFun (t - r) f)) 0) s =
      (PFun s (LFun (GammaFun (PFun (t - s) f) (PFun (t - s) f))) +
        PFun s
          (timeDeriv
            (fun r => GammaFun (PFun (t - r) f) (PFun (t - r) f)) s)) 0
    rw [show
        (fun r : ℝ =>
          PFun r (GammaFun (PFun (t - r) f) (PFun (t - r) f)) 0) =
          (fun r : ℝ => (Real.exp (-2 * (t - r)) * diff f) ^ (2 : ℕ) / 2) by
        funext r
        simp [PFun, GammaFun, mean, diff, pow_two]
        ]
    rw [hscalar.deriv]
    rw [timeDeriv_gamma_reverse t s f]
    simp [PFun, LFun, GammaFun, timeDeriv_reverse_PFun, mean, diff, pow_two]
    ring_nf
  ·
    change deriv
        (fun r : ℝ =>
          PFun r (GammaFun (PFun (t - r) f) (PFun (t - r) f)) 1) s =
      (PFun s (LFun (GammaFun (PFun (t - s) f) (PFun (t - s) f))) +
        PFun s
          (timeDeriv
            (fun r => GammaFun (PFun (t - r) f) (PFun (t - r) f)) s)) 1
    rw [show
        (fun r : ℝ =>
          PFun r (GammaFun (PFun (t - r) f) (PFun (t - r) f)) 1) =
          (fun r : ℝ => (Real.exp (-2 * (t - r)) * diff f) ^ (2 : ℕ) / 2) by
        funext r
        simp [PFun, GammaFun, mean, diff, pow_two]
        ]
    rw [hscalar.deriv]
    rw [timeDeriv_gamma_reverse t s f]
    simp [PFun, LFun, GammaFun, timeDeriv_reverse_PFun, mean, diff, pow_two]
    ring_nf

lemma interpolation_scalar_curve_eq (t : ℝ) (f : Func) (x : State) :
    (fun s : ℝ =>
      eval x (P s (GammaFun (P (t - s) f) (P (t - s) f)))) =
      fun s : ℝ => (Real.exp (-2 * (t - s)) * diff f) ^ (2 : ℕ) / 2 := by
  funext s
  fin_cases x <;> simp [eval, P, PFun, GammaFun, mean, diff, pow_two]

lemma interpolation_scalar_timeDeriv_eq (t s : ℝ) (f : Func) (x : State) :
    eval x
      (timeDeriv
        (fun r : ℝ => P r (GammaFun (P (t - r) f) (P (t - r) f))) s) =
      2 * (Real.exp (-2 * (t - s)) * diff f) ^ (2 : ℕ) := by
  have hscalar := hasDerivAt_reverse_gamma_scalar t s f
  fin_cases x
  · change deriv
        (fun r : ℝ =>
          PFun r (GammaFun (PFun (t - r) f) (PFun (t - r) f)) 0) s =
        2 * (Real.exp (-2 * (t - s)) * diff f) ^ (2 : ℕ)
    rw [show
        (fun r : ℝ =>
          PFun r (GammaFun (PFun (t - r) f) (PFun (t - r) f)) 0) =
          (fun r : ℝ => (Real.exp (-2 * (t - r)) * diff f) ^ (2 : ℕ) / 2) by
        funext r
        simp [PFun, GammaFun, mean, diff, pow_two]]
    exact hscalar.deriv
  · change deriv
        (fun r : ℝ =>
          PFun r (GammaFun (PFun (t - r) f) (PFun (t - r) f)) 1) s =
        2 * (Real.exp (-2 * (t - s)) * diff f) ^ (2 : ℕ)
    rw [show
        (fun r : ℝ =>
          PFun r (GammaFun (PFun (t - r) f) (PFun (t - r) f)) 1) =
          (fun r : ℝ => (Real.exp (-2 * (t - r)) * diff f) ^ (2 : ℕ) / 2) by
        funext r
        simp [PFun, GammaFun, mean, diff, pow_two]]
    exact hscalar.deriv

noncomputable def semigroup : CarreDuChampSemigroup where
  Func := Func
  funcAddCommGroup := inferInstance
  funcModule := inferInstance
  Point := State
  P := P
  L := L
  Gamma := GammaFun
  eval := eval
  mul := mul
  semigroup_zero := by
    intro f
    exact PFun_zero f
  semigroup_add := by
    intro s t f
    exact PFun_add s t f
  gamma_symm := GammaFun_symm
  gamma_nonneg := GammaFun_nonneg
  gamma_smul_right := GammaFun_smul_right
  semigroup_mono := by
    intro f g t x ht hfg
    exact P_mono (f := f) (g := g) (t := t) (x := x) ht hfg
  semigroup_le_const := by
    intro f c t x ht hf
    exact P_le_const (f := f) (c := c) (t := t) (x := x) ht hf
  generator_product_rule := generator_product_rule
  timeDeriv := timeDeriv
  semigroup_derivative_const := by
    intro s f
    exact timeDeriv_PFun s f
  semigroup_generator_commute := P_generator_commute
  timeDeriv_semigroup_interpolation := timeDeriv_semigroup_interpolation
  timeDeriv_reverse_semigroup := by
    intro t s f
    exact timeDeriv_reverse_PFun t s f
  timeDeriv_gamma_self_reverse := timeDeriv_gamma_reverse
  interpolation_scalar_continuous := by
    intro t f x ht
    rw [interpolation_scalar_curve_eq t f x]
    fun_prop
  interpolation_scalar_hasDerivWithinAt := by
    intro t f x s hs
    have hscalar := (hasDerivAt_reverse_gamma_scalar t s f).hasDerivWithinAt
      (s := Set.Ioo 0 t)
    rw [interpolation_scalar_curve_eq t f x]
    exact hscalar.congr_deriv
      (by exact (interpolation_scalar_timeDeriv_eq t s f x).symm)
  generator_carre_du_champ_identity := True
  semigroup_self_adjoint := True

noncomputable def framework : BakryEmeryGronwallFramework where
  base := semigroup

lemma gamma2_eq_square_diff (f : Func) :
    semigroup.gamma2 f = fun _ : State => diff f ^ (2 : ℕ) := by
  funext x
  fin_cases x
  · change
      ((1 / 2 : ℝ) •
        (L (GammaFun f f) - (2 : ℝ) • GammaFun f (L f))) 0 =
        diff f ^ (2 : ℕ)
    simp [L, LFun, GammaFun, diff, pow_two]
    ring
  · change
      ((1 / 2 : ℝ) •
        (L (GammaFun f f) - (2 : ℝ) • GammaFun f (L f))) 1 =
        diff f ^ (2 : ℕ)
    simp [L, LFun, GammaFun, diff, pow_two]
    ring

def unitSlope : Func
  | 0 => 0
  | 1 => 1

theorem unitSlope_nonconstant : unitSlope 0 ≠ unitSlope 1 := by
  norm_num [unitSlope]

theorem cdZero : semigroup.CDMinusInfinity 0 := by
  unfold CarreDuChampSemigroup.CDMinusInfinity
  change ∀ (f : Func) (x : State),
    -0 * (eval x) (GammaFun f f) ≤ (eval x) (semigroup.gamma2 f)
  intro f x
  rw [gamma2_eq_square_diff f]
  have hsq : 0 ≤ diff f ^ (2 : ℕ) := sq_nonneg (diff f)
  fin_cases x <;> simpa [eval] using hsq

theorem unitSlope_bakryEmeryEstimate_fires :
    semigroup.eval (0 : State)
        (semigroup.gammaSelf (semigroup.P 1 unitSlope)) ≤
      Real.exp (2 * (0 : ℝ) * 1) *
        semigroup.eval (0 : State)
          (semigroup.P 1 (semigroup.gammaSelf unitSlope)) := by
  exact
    bakryEmeryGradientEstimate framework
      (K := 0) (t := 1) (by norm_num) (by norm_num)
      cdZero unitSlope (0 : State)

theorem unitSlope_bakryEmeryEstimate_strict :
    semigroup.eval (0 : State)
        (semigroup.gammaSelf (semigroup.P 1 unitSlope)) <
      semigroup.eval (0 : State)
        (semigroup.P 1 (semigroup.gammaSelf unitSlope)) := by
  have hexp_lt_one : Real.exp (-4) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  change GammaFun (PFun 1 unitSlope) (PFun 1 unitSlope) (0 : State) <
    PFun 1 (GammaFun unitSlope unitSlope) (0 : State)
  simp [PFun, GammaFun, unitSlope, mean, diff]
  have hexp_mul : Real.exp (-2) * Real.exp (-2) = Real.exp (-4) := by
    rw [← Real.exp_add]
    norm_num
  rw [hexp_mul]
  nlinarith [Real.exp_pos (-4), hexp_lt_one]

end TwoPointChain

/-- Abstract version of Ben's downstream chain:

identity heat-gradient bound -> log-heat energy bound (Proposition 7.1),
log-heat energy bound -> vorticity control (G.7), and vorticity control ->
finite BKM gate (G.8). -/
structure AbstractBKMIdentityGate
    (M : CarreDuChampSemigroup) (id : M.Point) (phi : M.Func)
    (K Cphi T : ℝ) where
  logHeatEnergyBound : Prop
  vorticityBound : Prop
  bkmIntegralFinite : Prop
  bkmGate : Prop
  proposition7_1_of_identityGradientBound :
    (∀ t : ℝ, 0 ≤ t → t ≤ T →
      M.eval id (M.gammaSelf (M.P t phi)) ≤
        Real.exp (2 * K * t) * Cphi ^ 2) →
      logHeatEnergyBound
  propositionG7_of_logHeatEnergy :
    logHeatEnergyBound → vorticityBound
  theoremG8_of_vorticityBound :
    vorticityBound → bkmIntegralFinite
  bkmGate_of_finiteIntegral :
    bkmIntegralFinite → bkmGate

/-- The one open geometric input for the SG repair: a local
`CD(-K, infinity)` bound for the SG generator near the identity. -/
def LocalSGCurvatureDimensionOpenInput
    (G : BakryEmeryGronwallFramework) (K : ℝ) : Prop :=
  G.base.CDMinusInfinity K

/-- The variable-curvature SG input: pointwise `CD(rho, infinity)`.

This is only a hypothesis package.  Nothing here proves that the SG generator
satisfies it. -/
def LocalSGVariableCurvatureDimensionOpenInput
    (G : BakryEmeryGronwallFramework) (rho : G.base.Point → ℝ) : Prop :=
  G.base.CDVariableInfinity rho

/-- Integrated positivity datum for a variable-curvature SG route.

The `rhoWeight` field is the function-level representative of the pointwise
curvature `rho`; the final field states the open averaged positivity condition
against an invariant mean.  This records the stronger Cattiaux-style target
for a future SG proof while keeping it explicit and undischarged here. -/
structure LocalSGVariableCurvatureIntegratedOpenInput
    (G : BakryEmeryGronwallFramework) where
  rho : G.base.Point → ℝ
  rhoWeight : G.base.Func
  rhoWeight_eval : ∀ x : G.base.Point, G.base.eval x rhoWeight = rho x
  rhoMin : ℝ
  rhoMin_nonpos : rhoMin ≤ 0
  lowerBound : ∀ x : G.base.Point, rhoMin ≤ rho x
  localVariableCurvatureDimension :
    LocalSGVariableCurvatureDimensionOpenInput G rho
  invariantMean : G.base.Func →ₗ[ℝ] ℝ
  semigroupInvariant :
    ∀ (t : ℝ) (f : G.base.Func),
      invariantMean (G.base.P t f) = invariantMean f
  integratedPositivityConstant : ℝ
  integratedPositivityPositive : 0 < integratedPositivityConstant
  integratedCurvaturePositivity :
    ∀ f : G.base.Func,
      integratedPositivityConstant * invariantMean (G.base.gammaSelf f) ≤
        invariantMean (G.base.mul rhoWeight (G.base.gammaSelf f))

namespace LocalSGVariableCurvatureIntegratedOpenInput

variable {G : BakryEmeryGronwallFramework}

/-- The variable SG package supplies the constant lower-bound CD input used by
the checked Bakry-Emery estimate. -/
theorem constantCurvatureDimension
    (H : LocalSGVariableCurvatureIntegratedOpenInput G) :
    G.base.CDMinusInfinity (-H.rhoMin) :=
  G.base.cdMinusInfinity_of_cdVariable_lowerBound
    H.localVariableCurvatureDimension H.lowerBound

/-- The checked gradient estimate available from the variable SG package via
its constant lower bound.  The integrated positivity condition remains an
explicit additional field of `H`; it is not proved here. -/
theorem gradientEstimate
    (H : LocalSGVariableCurvatureIntegratedOpenInput G)
    {t : ℝ} (ht : 0 ≤ t)
    (f : G.base.Func) (x : G.base.Point) :
    G.base.eval x (G.base.gammaSelf (G.base.P t f)) ≤
      Real.exp (2 * (-H.rhoMin) * t) *
        G.base.eval x (G.base.P t (G.base.gammaSelf f)) :=
  bakryEmeryGradientEstimate_variableLowerBound G
    H.rhoMin_nonpos ht
    H.localVariableCurvatureDimension H.lowerBound f x

end LocalSGVariableCurvatureIntegratedOpenInput

/-- Conditional NS reduction datum.

`localCurvatureDimension` is the explicit open hypothesis replacing the false
uniform adjoint bound.  The H2 input is the globalized cutoff-energy bound
`Gamma(phi) <= Cphi^2`; in the manuscript this comes from support in the
cutoff set plus boundedness there. -/
structure NSBakryEmeryConditionalReduction
    (G : BakryEmeryGronwallFramework) where
  id : G.base.Point
  phi : G.base.Func
  K : ℝ
  Cphi : ℝ
  T : ℝ
  K_nonneg : 0 ≤ K
  T_nonneg : 0 ≤ T
  h2_bound :
    ∀ x : G.base.Point,
      G.base.eval x (G.base.gammaSelf phi) ≤ Cphi ^ 2
  localCurvatureDimension : G.base.CDMinusInfinity K
  gate : AbstractBKMIdentityGate G.base id phi K Cphi T

namespace NSBakryEmeryConditionalReduction

variable {G : BakryEmeryGronwallFramework}

/-- From local `CD(-K, infinity)` and H2, the identity heat-gradient bound
needed by the BKM gate follows. -/
theorem identityGradientBound
    (D : NSBakryEmeryConditionalReduction G) :
    ∀ t : ℝ, 0 ≤ t → t ≤ D.T →
      G.base.eval D.id (G.base.gammaSelf (G.base.P t D.phi)) ≤
        Real.exp (2 * D.K * t) * D.Cphi ^ 2 := by
  intro t ht _htT
  have hBE :
      G.base.eval D.id (G.base.gammaSelf (G.base.P t D.phi)) ≤
        Real.exp (2 * D.K * t) *
          G.base.eval D.id (G.base.P t (G.base.gammaSelf D.phi)) :=
    bakryEmeryGradientEstimate G D.K_nonneg ht
      D.localCurvatureDimension D.phi D.id
  have hH2 :
      G.base.eval D.id (G.base.P t (G.base.gammaSelf D.phi)) ≤
        D.Cphi ^ 2 :=
    G.base.semigroup_le_const
      (f := G.base.gammaSelf D.phi) (c := D.Cphi ^ 2)
      (t := t) (x := D.id) ht D.h2_bound
  have hexp_nonneg : 0 ≤ Real.exp (2 * D.K * t) :=
    le_of_lt (Real.exp_pos _)
  exact hBE.trans (mul_le_mul_of_nonneg_left hH2 hexp_nonneg)

/-- The abstract BKM gate closes conditionally from the checked
Bakry-Emery/H2 gradient bound and the supplied downstream gate scaffold. -/
theorem abstractBKMGate
    (D : NSBakryEmeryConditionalReduction G) :
    D.gate.bkmGate := by
  exact
    D.gate.bkmGate_of_finiteIntegral
      (D.gate.theoremG8_of_vorticityBound
        (D.gate.propositionG7_of_logHeatEnergy
          (D.gate.proposition7_1_of_identityGradientBound
            D.identityGradientBound)))

/-- The remaining SG input is exactly the local curvature-dimension bound. -/
theorem exactOpenInput
    (D : NSBakryEmeryConditionalReduction G) :
    LocalSGCurvatureDimensionOpenInput G D.K :=
  D.localCurvatureDimension

/-- Full conditional packet:
CD + H2 imply the identity heat-gradient bound, which is then consumed by the
abstract log-heat/vorticity/BKM gate chain. -/
theorem reductionPacket
    (D : NSBakryEmeryConditionalReduction G) :
    (∀ t : ℝ, 0 ≤ t → t ≤ D.T →
      G.base.eval D.id (G.base.gammaSelf (G.base.P t D.phi)) ≤
        Real.exp (2 * D.K * t) * D.Cphi ^ 2) ∧
      D.gate.logHeatEnergyBound ∧
        D.gate.vorticityBound ∧
          D.gate.bkmIntegralFinite ∧
            D.gate.bkmGate ∧
              LocalSGCurvatureDimensionOpenInput G D.K := by
  have hgrad := D.identityGradientBound
  have hlog := D.gate.proposition7_1_of_identityGradientBound hgrad
  have hvort := D.gate.propositionG7_of_logHeatEnergy hlog
  have hint := D.gate.theoremG8_of_vorticityBound hvort
  have hgate := D.gate.bkmGate_of_finiteIntegral hint
  exact ⟨hgrad, hlog, hvort, hint, hgate, D.exactOpenInput⟩

end NSBakryEmeryConditionalReduction

end NavierStokes
end FluidDynamics
end Mettapedia
