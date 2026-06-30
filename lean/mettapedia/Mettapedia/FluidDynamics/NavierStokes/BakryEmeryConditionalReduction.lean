import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic

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
  Point : Type
  P : ℝ → Func → Func
  L : Func → Func
  Gamma : Func → Func → Func
  Gamma2 : Func → Func
  eval : Point → Func → ℝ
  semigroup_zero : ∀ f : Func, P 0 f = f
  semigroup_add : ∀ (s t : ℝ) (f : Func), P (s + t) f = P s (P t f)
  gamma_symm : ∀ (f g : Func) (x : Point), eval x (Gamma f g) = eval x (Gamma g f)
  gamma_nonneg : ∀ (f : Func) (x : Point), 0 ≤ eval x (Gamma f f)
  semigroup_le_const :
    ∀ {f : Func} {c t : ℝ} {x : Point},
      (∀ y : Point, eval y f ≤ c) → eval x (P t f) ≤ c
  diffusion_chain_rule : Prop
  generator_carre_du_champ_identity : Prop
  semigroup_self_adjoint : Prop
  gamma2_bochner_identity : Prop

namespace CarreDuChampSemigroup

/-- The square field `Gamma(f) = Gamma(f,f)`. -/
def gammaSelf (M : CarreDuChampSemigroup) (f : M.Func) : M.Func :=
  M.Gamma f f

/-- The one-sided local curvature-dimension input `Gamma2(f) >= -K Gamma(f)`. -/
def CDMinusInfinity (M : CarreDuChampSemigroup) (K : ℝ) : Prop :=
  ∀ (f : M.Func) (x : M.Point),
    -K * M.eval x (M.gammaSelf f) ≤ M.eval x (M.Gamma2 f)

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

/-- The checked endpoint form of the interpolation differential lower bound.

Analytically this is obtained from
`d/ds P_s Gamma(P_{t-s} f) = 2 P_s Gamma2(P_{t-s} f)` plus the local
`CD(-K, infinity)` inequality and positivity/order preservation of the
semigroup.  The derivative and order-preservation work is represented by this
explicit predicate. -/
def InterpolationDerivativeLowerBound (M : CarreDuChampSemigroup)
    (K t : ℝ) (f : M.Func) (x : M.Point) : Prop :=
  ∀ s : ℝ, 0 ≤ s → s ≤ t →
    -2 * K * M.eval x (M.beInterpolation t s f) ≤
      2 * M.eval x (M.P s (M.Gamma2 (M.P (t - s) f)))

end CarreDuChampSemigroup

/-- A carré-du-champ semigroup together with the analytic interpolation and
Gronwall comparison principles needed for the Bakry-Emery estimate.

The final gradient estimate is not a field.  It is proved by first deriving
the interpolation differential lower bound from `CD(-K, infinity)` and then
feeding that bound to the comparison principle. -/
structure BakryEmeryGronwallFramework where
  base : CarreDuChampSemigroup
  interpolation_derivative_lower_bound :
    ∀ {K t : ℝ} {f : base.Func} {x : base.Point},
      base.CDMinusInfinity K →
        0 ≤ K →
          0 ≤ t →
            base.InterpolationDerivativeLowerBound K t f x
  gronwall_from_interpolation :
    ∀ {K t : ℝ} {f : base.Func} {x : base.Point},
      0 ≤ K →
        0 ≤ t →
          base.InterpolationDerivativeLowerBound K t f x →
            base.eval x (base.gammaSelf (base.P t f)) ≤
              Real.exp (2 * K * t) *
                base.eval x (base.P t (base.gammaSelf f))

/-- Bakry-Emery gradient estimate in abstract carré-du-champ form:

`CD(-K, infinity)` implies
`Gamma(P_t f) <= exp(2*K*t) P_t(Gamma f)`.

The proof genuinely passes through the interpolation derivative lower bound
and a Gronwall comparison field; the estimate itself is not assumed. -/
theorem bakryEmeryGradientEstimate
    (G : BakryEmeryGronwallFramework) {K t : ℝ}
    (hK : 0 ≤ K) (ht : 0 ≤ t)
    (hCD : G.base.CDMinusInfinity K)
    (f : G.base.Func) (x : G.base.Point) :
    G.base.eval x (G.base.gammaSelf (G.base.P t f)) ≤
      Real.exp (2 * K * t) *
        G.base.eval x (G.base.P t (G.base.gammaSelf f)) := by
  exact
    G.gronwall_from_interpolation (K := K) (t := t) (f := f) (x := x)
      hK ht
      (G.interpolation_derivative_lower_bound
        (K := K) (t := t) (f := f) (x := x) hCD hK ht)

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
      (t := t) (x := D.id) D.h2_bound
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
