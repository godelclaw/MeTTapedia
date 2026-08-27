import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMVorticityStretching

/-!
# BKM vorticity-equation surface

The hard standard vorticity equation is driven by the pressure-free curl of the
momentum equation.  This module proves the part already available from the
finite-time witness API: every certified witness has zero curl of the exact
pressure residual on its slab.  It also names the standard transport,
diffusion, and stretching terms so the remaining analytic lemma can target the
right equation rather than the raw momentum equation.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BKMContinuation

/-- Pressure-free curl form of the vorticity equation on a slab.  Expanding this
residual into `partial_t omega + (u . grad) omega = nu Delta omega +
(omega . grad)u` is the remaining vector-calculus product-rule part of the
BKM analytic lemma. -/
def vorticityResidualCurlEquationOn
    (ν : ℝ) (u : NSVelocityField) (T : ℝ) : Prop :=
  ∀ t x, 0 ≤ t → t ≤ T →
    spatialVorticity (momentumPressureResidual ν u) t x = 0

/-- Time derivative of the concrete vorticity field. -/
def timeVorticityDerivative
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) : NSSpace :=
  fderiv ℝ (fun s : NSTime => spatialVorticity u s x) t (1 : ℝ)

/-- Transport of vorticity by the velocity field, `(u . grad) omega`. -/
def vorticityTransportTerm
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) : NSSpace :=
  spatialFDeriv (fun s y => spatialVorticity u s y) t x (u t x)

/-- Spatial diffusion of vorticity, `Delta omega`. -/
def vorticityDiffusionTerm
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) : NSSpace :=
  spatialLaplacian (fun s y => spatialVorticity u s y) t x

/-- Standard pointwise vorticity equation on a slab, with the stretching term
made explicit. -/
def concreteVorticityEquationOn
    (ν : ℝ) (u : NSVelocityField) (T : ℝ) : Prop :=
  ∀ t x, 0 ≤ t → t ≤ T →
    timeVorticityDerivative u t x + vorticityTransportTerm u t x =
      ν • vorticityDiffusionTerm u t x + vorticityStretchingTerm u t x

/-- Every finite-time witness satisfies the pressure-free residual-curl form of
the vorticity equation on its certified slab. -/
theorem ExplicitFiniteTimeRegularityWitness.vorticityResidualCurlEquationOn
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T) :
    vorticityResidualCurlEquationOn ν W.velocity T := by
  intro t x ht0 htT
  exact
    ExplicitFiniteTimeRegularityWitness.spatialVorticity_momentumPressureResidual_zero_on
      (ν := ν) (T := T) (u₀ := u₀) W (t := t) (x := x) ht0 htT

/-- The same residual-curl equation is available on any witness carrying BKM
envelope data; the envelope hypotheses do not alter the pressure-free curl
identity. -/
theorem BKMData_vorticityResidualCurlEquationOn
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (_hBKM : ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn W.velocity T Ω ∧
        integrableVorticityEnvelopeOn Ω T B) :
    vorticityResidualCurlEquationOn ν W.velocity T :=
  W.vorticityResidualCurlEquationOn

/-- Route-facing packet: finite-time BKM data provides the pressure-free
vorticity equation in residual-curl form.  The standard transport/diffusion
form remains part of the named analytic continuation lemma. -/
theorem finiteTimeWitness_BKMData_vorticityResidualCurl_packet
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hBKM : ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn W.velocity T Ω ∧
        integrableVorticityEnvelopeOn Ω T B) :
    vorticityResidualCurlEquationOn ν W.velocity T ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        spatialVorticity (momentumPressureResidual ν W.velocity) t x = 0) := by
  exact ⟨BKMData_vorticityResidualCurlEquationOn W hBKM, fun t x ht0 htT =>
    ExplicitFiniteTimeRegularityWitness.spatialVorticity_momentumPressureResidual_zero_on
      (ν := ν) (T := T) (u₀ := u₀) W (t := t) (x := x) ht0 htT⟩

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
