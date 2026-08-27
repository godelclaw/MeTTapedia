import Mettapedia.FluidDynamics.NavierStokes.GalerkinBakryEmeryCurvature

/-!
# Bi-invariant su(N) trace-metric curvature sanity table

The validation lab `ns_sun_sine_bracket_curvature_lab.py` computes the
bracket-closed `su(N)` matrix model for `N = 2,3,4,5,6` using the
Ad-invariant trace/Killing metric `<A,B> = -Tr(AB)`.  In the orthonormal
anti-Hermitian Hilbert-Schmidt normalization, this bi-invariant metric gives
the scalar Ricci/Bochner lower eigenvalue `rho_N = N / 2`; hence the one-sided
`CD(-K, infinity)` constant is the computed value `K = 0` for every row in this
finite table.

This file records that computed table and wires the computed constants into
the generic `FiniteGalerkinBochnerRealization` API from
`GalerkinBakryEmeryCurvature.lean` only as a finite Lie-algebra arithmetic
sanity check.  The full matrix-commutator arithmetic is kept in the validation
report; Lean checks the exact downstream finite-jet CD inequality and the
conversion to the existing Bakry-Emery scaffold once matching bi-invariant
Bochner realization data are supplied.

This is not the Navier-Stokes/Arnold curvature computation.  The NS-relevant
metric is right-invariant and Sobolev-weighted, hence not Ad-invariant; its
structure constants are not totally antisymmetric in an orthonormal frame and
the Arnold/Misiolek curvature picture is mixed-sign.  Ben's v7 route also uses
local (H1)/(H2) chart estimates rather than a global curvature bound.  No
Navier-Stokes regularity theorem, SG curvature-dimension input, or realization
of Ben's curvature intuition is claimed here.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace FiniteGalerkin
namespace SuNComputedCurvature

open scoped BigOperators

/-- The finite `su(N)` rows computed by the bi-invariant trace-metric lab. -/
inductive Row where
  | N2
  | N3
  | N4
  | N5
  | N6
deriving DecidableEq, Repr

/-- Matrix size `N`. -/
def matrixN : Row → Nat
  | .N2 => 2
  | .N3 => 3
  | .N4 => 4
  | .N5 => 5
  | .N6 => 6

/-- `dim su(N) = N^2 - 1` for the computed rows. -/
def modeCount : Row → Nat
  | .N2 => 3
  | .N3 => 8
  | .N4 => 15
  | .N5 => 24
  | .N6 => 35

/-- The finite mode type for a computed row. -/
abbrev Mode (r : Row) : Type :=
  Fin (modeCount r)

/-- The computed lowest Ricci/Bochner eigenvalue for the bi-invariant
trace/Killing metric. -/
def rho : Row → ℝ
  | .N2 => 1
  | .N3 => (3 : ℝ) / 2
  | .N4 => 2
  | .N5 => (5 : ℝ) / 2
  | .N6 => 3

/-- The computed one-sided `CD(-K, infinity)` constant for the bi-invariant
trace/Killing sanity table.  The finite table has positive curvature, so this
is `0` in every row. -/
def cdK (_r : Row) : ℝ :=
  0

/-- The exact trace/Killing-metric table from the archived numpy report:
`(N, dim su(N), rho_min, CD(-K) constant)`. -/
def kNTable : List (Nat × Nat × ℝ × ℝ) :=
  [ (2, 3, 1, 0)
  , (3, 8, (3 : ℝ) / 2, 0)
  , (4, 15, 2, 0)
  , (5, 24, (5 : ℝ) / 2, 0)
  , (6, 35, 3, 0) ]

theorem kNTable_exact :
    kNTable =
      [ (2, 3, 1, 0)
      , (3, 8, (3 : ℝ) / 2, 0)
      , (4, 15, 2, 0)
      , (5, 24, (5 : ℝ) / 2, 0)
      , (6, 35, 3, 0) ] := by
  rfl

theorem modeCount_eq_matrixN_sq_sub_one (r : Row) :
    modeCount r = matrixN r * matrixN r - 1 := by
  cases r <;> norm_num [modeCount, matrixN]

theorem rho_eq_matrixN_over_two (r : Row) :
    rho r = (matrixN r : ℝ) / 2 := by
  cases r <;> norm_num [rho, matrixN]

theorem rho_uniform_lower_bound (r : Row) :
    (1 : ℝ) ≤ rho r := by
  cases r <;> norm_num [rho]

theorem rho_nonneg (r : Row) :
    0 ≤ rho r :=
  (by linarith [rho_uniform_lower_bound r] : 0 ≤ rho r)

theorem cdK_nonneg (r : Row) :
    0 ≤ cdK r := by
  simp [cdK]

theorem cdK_lower (r : Row) :
    -(cdK r) ≤ (1 : ℝ) * rho r := by
  have hrho := rho_nonneg r
  simp [cdK, hrho]

/-- Human-readable scope of the computed table. -/
def metricScope : String :=
  "bi-invariant su(N) trace/Killing curvature sanity check only"

theorem metricScope_exact :
    metricScope =
      "bi-invariant su(N) trace/Killing curvature sanity check only" := by
  rfl

/-- The genuine NS/SG curvature computation left open by this sanity check.

An inhabitant of this structure would have to replace the Ad-invariant
trace/Killing metric by the right-invariant Sobolev-weighted Arnold metric,
track the resulting non-totally-antisymmetric structure constants, handle the
mixed-sign curvature behavior, and connect the result to Ben's local (H1)/(H2)
generator rather than a global bi-invariant curvature bound. -/
structure RightInvariantSobolevArnoldOpenInput where
  rightInvariantSobolevMetric : Prop
  nonAdInvariantMetric : Prop
  nonTotallyAntisymmetricStructureConstants : Prop
  mixedSignArnoldCurvatureHandled : Prop
  benLocalH1H2GeneratorConnected : Prop

/-- Diagonal Ricci matrix with the computed lower eigenvalue. -/
def ricci (r : Row) (i j : Mode r) : ℝ :=
  if i = j then rho r else 0

/-- Nonnegative Hessian-square term used by the finite Bochner model. -/
def hessianSquare (r : Row) (H : (Mode r × Mode r) → ℝ) : ℝ :=
  ∑ p : Mode r × Mode r, H p ^ (2 : ℕ)

theorem hessianSquare_nonneg (r : Row) (H : (Mode r × Mode r) → ℝ) :
    0 ≤ hessianSquare r H := by
  unfold hessianSquare
  exact Finset.sum_nonneg (fun p _hp => sq_nonneg (H p))

theorem finiteJetRicciQuadratic_diagonal
    {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    (a : ℝ) (u : Mode → ℝ) :
    finiteJetRicciQuadratic (fun i j : Mode => if i = j then a else 0) u =
      a * finiteJetEnergy u := by
  unfold finiteJetRicciQuadratic finiteJetEnergy
  simp [Finset.mul_sum, pow_two]
  apply Finset.sum_congr rfl
  intro x _hx
  ring

theorem ricciLowerBound (r : Row) (u : Mode r → ℝ) :
    rho r * finiteJetEnergy u ≤ finiteJetRicciQuadratic (ricci r) u := by
  change rho r * finiteJetEnergy u ≤
    finiteJetRicciQuadratic
      (fun i j : Mode r => if i = j then rho r else 0) u
  rw [finiteJetRicciQuadratic_diagonal]

/-- The computed bi-invariant finite su(N) table gives the finite-jet
`Gamma2 >= -K Gamma` bound with `K = 0` for this trace/Killing sanity model. -/
theorem computedFiniteJetGamma2_lowerBound
    (r : Row) (H : (Mode r × Mode r) → ℝ) (u : Mode r → ℝ) :
    -(cdK r) * finiteJetGamma 1 u ≤
      finiteJetGamma2 1 (ricci r) (hessianSquare r) H u := by
  exact
    finiteJetGamma2_lowerBound
      (viscosity := 1) (rho := rho r) (K := cdK r)
      (ricci := ricci r) (hessianSquare := hessianSquare r)
      (by norm_num) (cdK_lower r) (hessianSquare_nonneg r)
      (ricciLowerBound r) H u

/-- Data still needed from a finite bi-invariant trace/Killing su(N) model to
realize the computed table as an abstract carré-du-champ semigroup.

The curvature constants are not fields here: `rho` and `K` are fixed by
`kNTable`.  The fields are exactly the remaining finite model Bochner
realization facts.  This is intentionally not a right-invariant Sobolev/Arnold
or Ben-H^m generator interface. -/
structure BochnerData
    (G : BakryEmeryGronwallFramework) (r : Row) where
  structureConstant : Mode r → Mode r → Mode r → ℝ
  structureConstant_skew :
    ∀ i j k : Mode r,
      structureConstant i j k = -structureConstant j i k
  structureConstant_jacobi :
    ∀ i j k l : Mode r,
      (∑ m : Mode r, structureConstant j k m * structureConstant i m l) +
          (∑ m : Mode r, structureConstant k i m * structureConstant j m l) +
            (∑ m : Mode r, structureConstant i j m * structureConstant k m l) =
        0
  firstJet : G.base.Point → G.base.Func → Mode r → ℝ
  hessianJet : G.base.Point → G.base.Func → (Mode r × Mode r) → ℝ
  gamma_eval_eq :
    ∀ (x : G.base.Point) (f : G.base.Func),
      G.base.eval x (G.base.gammaSelf f) =
        finiteJetGamma 1 (firstJet x f)
  gamma2_eval_eq :
    ∀ (x : G.base.Point) (f : G.base.Func),
      G.base.eval x (G.base.gamma2 f) =
        finiteJetGamma2 1 (ricci r) (hessianSquare r)
          (hessianJet x f) (firstJet x f)

namespace BochnerData

variable {G : BakryEmeryGronwallFramework} {r : Row}

/-- Build the generic finite Galerkin realization using the computed
bi-invariant trace/Killing su(N) curvature row. -/
def toFiniteGalerkinBochnerRealization
    (D : BochnerData G r) :
    FiniteGalerkinBochnerRealization G where
  Mode := Mode r
  modeFintype := inferInstance
  modeDecidableEq := inferInstance
  modeCount := modeCount r
  modeCount_eq_card := by
    simp [Mode]
  viscosity := 1
  viscosity_nonneg := by norm_num
  rho := rho r
  K := cdK r
  K_nonneg := cdK_nonneg r
  K_lower := cdK_lower r
  structureConstant := D.structureConstant
  structureConstant_skew := D.structureConstant_skew
  structureConstant_jacobi := D.structureConstant_jacobi
  hessianSquare := hessianSquare r
  hessianSquare_nonneg := hessianSquare_nonneg r
  ricci := ricci r
  ricciLowerBound := ricciLowerBound r
  firstJet := D.firstJet
  hessianJet := D.hessianJet
  gamma_eval_eq := D.gamma_eval_eq
  gamma2_eval_eq := D.gamma2_eval_eq

/-- The computed bi-invariant su(N) row supplies `CD(-0, infinity)` once the
matching finite Bochner realization data are available. -/
theorem curvatureDimension
    (D : BochnerData G r) :
    G.base.CDMinusInfinity (cdK r) :=
  D.toFiniteGalerkinBochnerRealization.curvatureDimension

/-- The checked Bakry-Emery gradient estimate with the computed bi-invariant
su(N) constant `K = 0`. -/
theorem gradientEstimate
    (D : BochnerData G r)
    {t : ℝ} (ht : 0 ≤ t)
    (f : G.base.Func) (x : G.base.Point) :
    G.base.eval x (G.base.gammaSelf (G.base.P t f)) ≤
      Real.exp (2 * cdK r * t) *
        G.base.eval x (G.base.P t (G.base.gammaSelf f)) :=
  D.toFiniteGalerkinBochnerRealization.gradientEstimate ht f x

end BochnerData

end SuNComputedCurvature
end FiniteGalerkin
end NavierStokes
end FluidDynamics
end Mettapedia
