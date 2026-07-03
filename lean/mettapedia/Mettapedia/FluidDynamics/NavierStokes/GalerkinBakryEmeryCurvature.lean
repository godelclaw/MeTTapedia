import Mettapedia.FluidDynamics.NavierStokes.BakryEmeryConditionalReduction

/-!
# Finite Galerkin Bakry-Emery curvature certificates

This module is the finite-dimensional certificate layer for the
Bakry-Emery repair route.  It does not prove a Navier-Stokes regularity
theorem, and it does not assert that a Fourier cutoff of the SG generator is
closed under brackets.  Instead it records exactly what a finite Galerkin
truncation must supply:

* a finite mode set and structure constants;
* skew and Jacobi/closure evidence for the finite bracket model;
* a Bochner jet formula for `Gamma` and `Gamma2`;
* a Ricci/quadratic-form lower bound.

From those fields Lean proves the constant `CD(-K, infinity)` input required by
`bakryEmeryGradientEstimate`, and then reuses the existing conditional
Navier-Stokes BKM gate.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped BigOperators

namespace FiniteGalerkin

/-- The first-jet energy `|df|^2` over a finite mode set. -/
def finiteJetEnergy {Mode : Type*} [Fintype Mode]
    (u : Mode → ℝ) : ℝ :=
  ∑ i : Mode, u i ^ (2 : ℕ)

/-- The Ricci quadratic form associated to a finite Bochner matrix. -/
def finiteJetRicciQuadratic {Mode : Type*} [Fintype Mode]
    (ricci : Mode → Mode → ℝ) (u : Mode → ℝ) : ℝ :=
  ∑ i : Mode, ∑ j : Mode, u i * ricci i j * u j

/-- The `Gamma` value represented on finite first jets.  Scaling the generator
by viscosity scales `Gamma` by the same factor. -/
def finiteJetGamma {Mode : Type*} [Fintype Mode]
    (viscosity : ℝ) (u : Mode → ℝ) : ℝ :=
  viscosity * finiteJetEnergy u

/-- The finite Bochner-model `Gamma2` value:
viscosity squared times a nonnegative Hessian square plus the Ricci quadratic
form. -/
def finiteJetGamma2 {Mode : Type*} [Fintype Mode]
    (viscosity : ℝ) (ricci : Mode → Mode → ℝ)
    (hessianSquare : ((Mode × Mode) → ℝ) → ℝ)
    (H : (Mode × Mode) → ℝ) (u : Mode → ℝ) : ℝ :=
  viscosity ^ (2 : ℕ) *
    (hessianSquare H + finiteJetRicciQuadratic ricci u)

theorem finiteJetEnergy_nonneg {Mode : Type*} [Fintype Mode]
    (u : Mode → ℝ) :
    0 ≤ finiteJetEnergy u := by
  unfold finiteJetEnergy
  exact Finset.sum_nonneg (fun i _hi => sq_nonneg (u i))

/-- Algebraic finite-jet CD estimate.

If the Ricci quadratic form is bounded below by `rho |u|^2`, the Hessian
part is nonnegative, and `-K <= viscosity * rho`, then the finite Bochner jet
satisfies `Gamma2 >= -K Gamma`. -/
theorem finiteJetGamma2_lowerBound {Mode : Type*} [Fintype Mode]
    {viscosity rho K : ℝ}
    {ricci : Mode → Mode → ℝ}
    {hessianSquare : ((Mode × Mode) → ℝ) → ℝ}
    (hvisc : 0 ≤ viscosity)
    (hK : -K ≤ viscosity * rho)
    (hHess : ∀ H : (Mode × Mode) → ℝ, 0 ≤ hessianSquare H)
    (hRicci :
      ∀ u : Mode → ℝ,
        rho * finiteJetEnergy u ≤ finiteJetRicciQuadratic ricci u)
    (H : (Mode × Mode) → ℝ) (u : Mode → ℝ) :
    -K * finiteJetGamma viscosity u ≤
      finiteJetGamma2 viscosity ricci hessianSquare H u := by
  have hE : 0 ≤ finiteJetEnergy u := finiteJetEnergy_nonneg u
  have hGamma_nonneg : 0 ≤ viscosity * finiteJetEnergy u :=
    mul_nonneg hvisc hE
  have hleft :
      -K * (viscosity * finiteJetEnergy u) ≤
        (viscosity * rho) * (viscosity * finiteJetEnergy u) :=
    mul_le_mul_of_nonneg_right hK hGamma_nonneg
  have hRicci_u := hRicci u
  have hHess_H := hHess H
  have hBochnerCore :
      rho * finiteJetEnergy u ≤
        hessianSquare H + finiteJetRicciQuadratic ricci u := by
    linarith
  have hvisc_sq_nonneg : 0 ≤ viscosity ^ (2 : ℕ) :=
    sq_nonneg viscosity
  have hBochnerScaled :
      viscosity ^ (2 : ℕ) * (rho * finiteJetEnergy u) ≤
        viscosity ^ (2 : ℕ) *
          (hessianSquare H + finiteJetRicciQuadratic ricci u) :=
    mul_le_mul_of_nonneg_left hBochnerCore hvisc_sq_nonneg
  calc
    -K * finiteJetGamma viscosity u
        = -K * (viscosity * finiteJetEnergy u) := by
          rfl
    _ ≤ (viscosity * rho) * (viscosity * finiteJetEnergy u) := hleft
    _ = viscosity ^ (2 : ℕ) * (rho * finiteJetEnergy u) := by
          ring
    _ ≤ viscosity ^ (2 : ℕ) *
          (hessianSquare H + finiteJetRicciQuadratic ricci u) :=
          hBochnerScaled
    _ = finiteJetGamma2 viscosity ricci hessianSquare H u := by
          rfl

namespace AbelianTranslationJet

/-- The flat two-translation truncation on a torus: two constant
divergence-free directions, zero bracket, and zero Ricci curvature. -/
abbrev Mode := Fin 2

def structureConstant (_i _j _k : Mode) : ℝ :=
  0

def ricci (_i _j : Mode) : ℝ :=
  0

def hessianSquare (H : (Mode × Mode) → ℝ) : ℝ :=
  ∑ p : Mode × Mode, H p ^ (2 : ℕ)

theorem structureConstant_skew (i j k : Mode) :
    structureConstant i j k = -structureConstant j i k := by
  simp [structureConstant]

theorem structureConstant_jacobi (i j k l : Mode) :
    (∑ m : Mode, structureConstant j k m * structureConstant i m l) +
        (∑ m : Mode, structureConstant k i m * structureConstant j m l) +
          (∑ m : Mode, structureConstant i j m * structureConstant k m l) =
      0 := by
  simp [structureConstant]

theorem hessianSquare_nonneg (H : (Mode × Mode) → ℝ) :
    0 ≤ hessianSquare H := by
  unfold hessianSquare
  exact Finset.sum_nonneg (fun p _hp => sq_nonneg (H p))

theorem ricciLowerBound_zero (u : Mode → ℝ) :
    (0 : ℝ) * finiteJetEnergy u ≤ finiteJetRicciQuadratic ricci u := by
  simp [finiteJetRicciQuadratic, ricci]

/-- The exact flat finite jet bound for the two translation modes. -/
theorem gamma2_lowerBound_zero (H : (Mode × Mode) → ℝ) (u : Mode → ℝ) :
    -(0 : ℝ) * finiteJetGamma 1 u ≤
      finiteJetGamma2 1 ricci hessianSquare H u := by
  exact
    finiteJetGamma2_lowerBound
      (viscosity := 1) (rho := 0) (K := 0)
      (ricci := ricci) (hessianSquare := hessianSquare)
      (by norm_num) (by norm_num) hessianSquare_nonneg
      ricciLowerBound_zero H u

end AbelianTranslationJet

/-- A finite Galerkin Bochner realization of an abstract
`CarreDuChampSemigroup`.

The closure/Jacobi and Bochner fields are deliberately explicit.  For a
nontrivial Fourier cutoff these are the mathematical obligations exposed by
the validation lab, not assumptions silently discharged by this file. -/
structure FiniteGalerkinBochnerRealization
    (G : BakryEmeryGronwallFramework) where
  Mode : Type
  modeFintype : Fintype Mode
  modeDecidableEq : DecidableEq Mode
  modeCount : Nat
  modeCount_eq_card :
    letI := modeFintype
    modeCount = Fintype.card Mode
  viscosity : ℝ
  viscosity_nonneg : 0 ≤ viscosity
  rho : ℝ
  K : ℝ
  K_nonneg : 0 ≤ K
  K_lower : -K ≤ viscosity * rho
  structureConstant : Mode → Mode → Mode → ℝ
  structureConstant_skew :
    ∀ i j k : Mode,
      structureConstant i j k = -structureConstant j i k
  structureConstant_jacobi :
    letI := modeFintype
    ∀ i j k l : Mode,
      (∑ m : Mode, structureConstant j k m * structureConstant i m l) +
          (∑ m : Mode, structureConstant k i m * structureConstant j m l) +
            (∑ m : Mode, structureConstant i j m * structureConstant k m l) =
        0
  hessianSquare : ((Mode × Mode) → ℝ) → ℝ
  hessianSquare_nonneg :
    ∀ H : (Mode × Mode) → ℝ, 0 ≤ hessianSquare H
  ricci : Mode → Mode → ℝ
  ricciLowerBound :
    letI := modeFintype
    ∀ u : Mode → ℝ,
      rho * finiteJetEnergy u ≤ finiteJetRicciQuadratic ricci u
  firstJet : G.base.Point → G.base.Func → Mode → ℝ
  hessianJet : G.base.Point → G.base.Func → (Mode × Mode) → ℝ
  gamma_eval_eq :
    letI := modeFintype
    ∀ (x : G.base.Point) (f : G.base.Func),
      G.base.eval x (G.base.gammaSelf f) =
        finiteJetGamma viscosity (firstJet x f)
  gamma2_eval_eq :
    letI := modeFintype
    ∀ (x : G.base.Point) (f : G.base.Func),
      G.base.eval x (G.base.gamma2 f) =
        finiteJetGamma2 viscosity ricci hessianSquare
          (hessianJet x f) (firstJet x f)

namespace FiniteGalerkinBochnerRealization

attribute [instance] modeFintype modeDecidableEq

variable {G : BakryEmeryGronwallFramework}

/-- The finite Bochner realization supplies the constant CD input required by
the checked Bakry-Emery theorem. -/
theorem curvatureDimension
    (R : FiniteGalerkinBochnerRealization G) :
    G.base.CDMinusInfinity R.K := by
  intro f x
  rw [R.gamma_eval_eq x f, R.gamma2_eval_eq x f]
  exact
    finiteJetGamma2_lowerBound
      (viscosity := R.viscosity) (rho := R.rho) (K := R.K)
      (ricci := R.ricci) (hessianSquare := R.hessianSquare)
      R.viscosity_nonneg R.K_lower R.hessianSquare_nonneg
      R.ricciLowerBound (R.hessianJet x f) (R.firstJet x f)

/-- The finite Galerkin realization is exactly a local SG curvature input for
the abstract BE scaffold, at the truncation level. -/
theorem localCurvatureInput
    (R : FiniteGalerkinBochnerRealization G) :
    LocalSGCurvatureDimensionOpenInput G R.K :=
  R.curvatureDimension

/-- Once the finite certificate is supplied, the existing checked
Bakry-Emery gradient estimate applies directly to the truncation. -/
theorem gradientEstimate
    (R : FiniteGalerkinBochnerRealization G)
    {t : ℝ} (ht : 0 ≤ t)
    (f : G.base.Func) (x : G.base.Point) :
    G.base.eval x (G.base.gammaSelf (G.base.P t f)) ≤
      Real.exp (2 * R.K * t) *
        G.base.eval x (G.base.P t (G.base.gammaSelf f)) :=
  bakryEmeryGradientEstimate G R.K_nonneg ht
    R.curvatureDimension f x

end FiniteGalerkinBochnerRealization

/-- A finite Galerkin version of the conditional Navier-Stokes BE reduction.

Compared with `NSBakryEmeryConditionalReduction`, the curvature input is not a
bare CD hypothesis.  It is a finite Bochner realization certificate, from
which CD is derived by `FiniteGalerkinBochnerRealization.curvatureDimension`. -/
structure FiniteGalerkinNSBakryEmeryReduction
    (G : BakryEmeryGronwallFramework) where
  realization : FiniteGalerkinBochnerRealization G
  id : G.base.Point
  phi : G.base.Func
  Cphi : ℝ
  T : ℝ
  T_nonneg : 0 ≤ T
  h2_bound :
    ∀ x : G.base.Point,
      G.base.eval x (G.base.gammaSelf phi) ≤ Cphi ^ 2
  gate : AbstractBKMIdentityGate G.base id phi realization.K Cphi T

namespace FiniteGalerkinNSBakryEmeryReduction

variable {G : BakryEmeryGronwallFramework}

/-- Forget the finite certificate to the already checked conditional BE
reduction, using the derived CD theorem as the curvature field. -/
def toConditionalReduction
    (D : FiniteGalerkinNSBakryEmeryReduction G) :
    NSBakryEmeryConditionalReduction G where
  id := D.id
  phi := D.phi
  K := D.realization.K
  Cphi := D.Cphi
  T := D.T
  K_nonneg := D.realization.K_nonneg
  T_nonneg := D.T_nonneg
  h2_bound := D.h2_bound
  localCurvatureDimension := D.realization.curvatureDimension
  gate := D.gate

/-- Finite certificate + H2 give the identity heat-gradient bound. -/
theorem identityGradientBound
    (D : FiniteGalerkinNSBakryEmeryReduction G) :
    ∀ t : ℝ, 0 ≤ t → t ≤ D.T →
      G.base.eval D.id (G.base.gammaSelf (G.base.P t D.phi)) ≤
        Real.exp (2 * D.realization.K * t) * D.Cphi ^ 2 :=
  D.toConditionalReduction.identityGradientBound

/-- Finite certificate + H2 feed the abstract BKM gate. -/
theorem abstractBKMGate
    (D : FiniteGalerkinNSBakryEmeryReduction G) :
    D.gate.bkmGate :=
  D.toConditionalReduction.abstractBKMGate

/-- Full finite Galerkin conditional packet: the finite Bochner certificate
derives CD, CD plus H2 derives the identity gradient bound, and the existing
abstract Proposition 7.1/G.7/G.8 gate consumes it. -/
theorem reductionPacket
    (D : FiniteGalerkinNSBakryEmeryReduction G) :
    (∀ t : ℝ, 0 ≤ t → t ≤ D.T →
      G.base.eval D.id (G.base.gammaSelf (G.base.P t D.phi)) ≤
        Real.exp (2 * D.realization.K * t) * D.Cphi ^ 2) ∧
      D.gate.logHeatEnergyBound ∧
        D.gate.vorticityBound ∧
          D.gate.bkmIntegralFinite ∧
            D.gate.bkmGate ∧
              LocalSGCurvatureDimensionOpenInput G D.realization.K :=
  D.toConditionalReduction.reductionPacket

end FiniteGalerkinNSBakryEmeryReduction

end FiniteGalerkin

end NavierStokes
end FluidDynamics
end Mettapedia
