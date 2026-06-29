import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMVorticityGrowth

/-!
# BKM residual-curl expansion defect

The finite-time witness API supplies the pressure-free residual-curl equation
`curl (nu Delta u - partial_t u - (u . grad)u) = 0`.  The standard vorticity
equation additionally needs the vector-calculus expansion of that curl.  This
module names the exact defect and proves the algebraic bridge from a vanishing
defect to `concreteVorticityEquationOn`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BKMContinuation

/-- Pointwise residual of the standard vorticity equation after moving all
terms to the left-hand side.  Vanishing of this vector is equivalent to
`partial_t omega + (u . grad)omega = nu Delta omega + (omega . grad)u`. -/
def vorticityEquationResidual
    (ν : ℝ) (u : NSVelocityField) (t : NSTime) (x : NSSpace) : NSSpace :=
  vorticityMaterialDiffusionRemainder ν u t x - vorticityStretchingTerm u t x

/-- The defect in expanding the residual curl into the standard vorticity
equation.  For smooth incompressible velocity fields, the intended
vector-calculus identity is that this defect vanishes:
`curl(nu Delta u - partial_t u - (u.grad)u) +`
`(partial_t omega + (u.grad)omega - nu Delta omega - (omega.grad)u) = 0`. -/
def residualCurlExpansionDefect
    (ν : ℝ) (u : NSVelocityField) (t : NSTime) (x : NSSpace) : NSSpace :=
  spatialVorticity (momentumPressureResidual ν u) t x +
    vorticityEquationResidual ν u t x

/-- Slabwise vanishing of the residual-curl expansion defect. -/
def residualCurlExpansionClosedOn
    (ν : ℝ) (u : NSVelocityField) (T : ℝ) : Prop :=
  ∀ t x, 0 ≤ t → t ≤ T → residualCurlExpansionDefect ν u t x = 0

/-- Precise missing vector-calculus lemma for the residual-curl expansion:
smooth incompressible velocities have vanishing expansion defect on the slab.
This is a named open analytic target, not an assumed theorem. -/
def BKMResidualCurlExpansionDefectVanishes : Prop :=
  ∀ (ν : ℝ) (u : NSVelocityField) (T : ℝ),
    smoothSpaceTimeVelocity u →
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) →
        residualCurlExpansionClosedOn ν u T

/-- A zero standard-vorticity residual is the pointwise standard vorticity
equation. -/
theorem concreteVorticityEquationOn_at_of_vorticityEquationResidual_eq_zero
    {ν : ℝ} {u : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hres : vorticityEquationResidual ν u t x = 0) :
    timeVorticityDerivative u t x + vorticityTransportTerm u t x =
      ν • vorticityDiffusionTerm u t x + vorticityStretchingTerm u t x := by
  have hmain :
      timeVorticityDerivative u t x + vorticityTransportTerm u t x -
          (ν • vorticityDiffusionTerm u t x + vorticityStretchingTerm u t x) =
        0 := by
    rw [← hres]
    simp [vorticityEquationResidual, vorticityMaterialDiffusionRemainder]
    abel
  exact sub_eq_zero.mp hmain

/-- The standard vorticity equation gives zero pointwise standard-vorticity
residual. -/
theorem vorticityEquationResidual_eq_zero_of_concreteVorticityEquationOn_at
    {ν : ℝ} {u : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hEq :
      timeVorticityDerivative u t x + vorticityTransportTerm u t x =
        ν • vorticityDiffusionTerm u t x + vorticityStretchingTerm u t x) :
    vorticityEquationResidual ν u t x = 0 := by
  unfold vorticityEquationResidual vorticityMaterialDiffusionRemainder
  rw [hEq]
  abel

/-- Pointwise equivalence between zero standard-vorticity residual and the
standard vorticity equation. -/
theorem vorticityEquationResidual_eq_zero_iff_concreteVorticityEquationOn_at
    {ν : ℝ} {u : NSVelocityField} {t : NSTime} {x : NSSpace} :
    vorticityEquationResidual ν u t x = 0 ↔
      timeVorticityDerivative u t x + vorticityTransportTerm u t x =
        ν • vorticityDiffusionTerm u t x + vorticityStretchingTerm u t x :=
  ⟨concreteVorticityEquationOn_at_of_vorticityEquationResidual_eq_zero,
    vorticityEquationResidual_eq_zero_of_concreteVorticityEquationOn_at⟩

/-- If the residual-curl equation holds and the expansion defect vanishes, then
the standard vorticity equation holds on the same slab. -/
theorem concreteVorticityEquationOn_of_residualCurlExpansionClosedOn
    {ν T : ℝ} {u : NSVelocityField}
    (hCurl : vorticityResidualCurlEquationOn ν u T)
    (hExpand : residualCurlExpansionClosedOn ν u T) :
    concreteVorticityEquationOn ν u T := by
  intro t x ht0 htT
  have hdef := hExpand t x ht0 htT
  have hcurl := hCurl t x ht0 htT
  have hres : vorticityEquationResidual ν u t x = 0 := by
    unfold residualCurlExpansionDefect at hdef
    rw [hcurl] at hdef
    simpa using hdef
  exact concreteVorticityEquationOn_at_of_vorticityEquationResidual_eq_zero hres

/-- Algebraic closure of the residual-curl-to-standard-vorticity-equation
bridge, once the vector-calculus expansion defect is known to vanish. -/
def BKMResidualCurlExpansionAlgebraClosed : Prop :=
  ∀ (ν : ℝ) (u : NSVelocityField) (T : ℝ),
    vorticityResidualCurlEquationOn ν u T →
      residualCurlExpansionClosedOn ν u T →
        concreteVorticityEquationOn ν u T

/-- Checked proof of the algebraic residual-curl expansion bridge. -/
theorem BKMResidualCurlExpansionAlgebraClosed_proved :
    BKMResidualCurlExpansionAlgebraClosed := by
  intro ν u T hCurl hExpand
  exact concreteVorticityEquationOn_of_residualCurlExpansionClosedOn hCurl hExpand

/-- A proof of the exact defect-vanishing vector-calculus lemma turns the
finite-time residual-curl equation into the standard vorticity equation for
any smooth incompressible slab. -/
theorem BKMResidualCurlExpansionDefectVanishes.implies_concreteVorticityEquationOn
    (hDefect : BKMResidualCurlExpansionDefectVanishes)
    {ν T : ℝ} {u : NSVelocityField}
    (hsmooth : smoothSpaceTimeVelocity u)
    (hdiv : ∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0)
    (hCurl : vorticityResidualCurlEquationOn ν u T) :
    concreteVorticityEquationOn ν u T :=
  concreteVorticityEquationOn_of_residualCurlExpansionClosedOn hCurl
    (hDefect ν u T hsmooth hdiv)

/-- Finite-time witnesses would supply the standard vorticity equation as soon
as the exact residual-curl expansion defect is proved to vanish for smooth
incompressible fields. -/
theorem ExplicitFiniteTimeRegularityWitness.concreteVorticityEquationOn_of_residualCurlExpansionDefectVanishes
    (hDefect : BKMResidualCurlExpansionDefectVanishes)
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T) :
    concreteVorticityEquationOn ν W.velocity T :=
  hDefect.implies_concreteVorticityEquationOn W.smooth_velocity
    (fun t x ht0 htT => W.incompressible_on t x ht0 htT)
    W.vorticityResidualCurlEquationOn

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
