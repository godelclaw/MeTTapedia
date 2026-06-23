import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationEquivalences

/-!
# Projection Lemmas for Concrete Navier-Stokes Differential Kits

This module states the definitional iff lemmas exposing the concrete operators,
smoothness predicates, and energy predicates of the kit constructors.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section ConcreteEquationTarget

open scoped Laplacian ContDiff

/-- For the partially concrete kit, incompressibility is literally the vanishing
of the spatial divergence defined above. -/
theorem isIncompressible_mkWithConcreteDivergence_iff
    {timeDerivative : NSVelocityField → NSTime → NSSpace → NSSpace}
    {convection : NSVelocityField → NSTime → NSSpace → NSSpace}
    {pressureGradient : NSPressureField → NSTime → NSSpace → NSSpace}
    {laplacian : NSVelocityField → NSTime → NSSpace → NSSpace}
    {smoothVelocity : NSVelocityField → Prop}
    {smoothPressure : NSPressureField → Prop}
    {boundedEnergy : NSVelocityField → Prop}
    {smoothInitialData : NSInitialVelocity → Prop}
    {u : NSVelocityField} :
    IsIncompressible
        (mkWithConcreteDivergence timeDerivative convection pressureGradient laplacian
          smoothVelocity smoothPressure boundedEnergy smoothInitialData)
        u
      ↔ ∀ t x, spatialDivergence u t x = 0 := by
  rfl

/-- Likewise, divergence-free initial data are now literally the vanishing of
the spatial initial divergence. -/
theorem divergenceFreeInitialData_mkWithConcreteDivergence_iff
    {timeDerivative : NSVelocityField → NSTime → NSSpace → NSSpace}
    {convection : NSVelocityField → NSTime → NSSpace → NSSpace}
    {pressureGradient : NSPressureField → NSTime → NSSpace → NSSpace}
    {laplacian : NSVelocityField → NSTime → NSSpace → NSSpace}
    {smoothVelocity : NSVelocityField → Prop}
    {smoothPressure : NSPressureField → Prop}
    {boundedEnergy : NSVelocityField → Prop}
    {smoothInitialData : NSInitialVelocity → Prop}
    {u₀ : NSInitialVelocity} :
    (mkWithConcreteDivergence timeDerivative convection pressureGradient laplacian
      smoothVelocity smoothPressure boundedEnergy smoothInitialData).divergenceFreeInitialData u₀
      ↔ ∀ x, initialSpatialDivergence u₀ x = 0 := by
  rfl

/-- For the more concrete kit, the momentum equation literally uses the actual
spatial pressure gradient on `ℝ^3`. -/
theorem satisfiesMomentumEquation_mkWithConcreteGradientAndDivergence_iff
    {timeDerivative : NSVelocityField → NSTime → NSSpace → NSSpace}
    {convection : NSVelocityField → NSTime → NSSpace → NSSpace}
    {laplacian : NSVelocityField → NSTime → NSSpace → NSSpace}
    {smoothVelocity : NSVelocityField → Prop}
    {smoothPressure : NSPressureField → Prop}
    {boundedEnergy : NSVelocityField → Prop}
    {smoothInitialData : NSInitialVelocity → Prop}
    {ν : ℝ} {u : NSVelocityField} {p : NSPressureField} :
    SatisfiesMomentumEquation
        (mkWithConcreteGradientAndDivergence timeDerivative convection laplacian
          smoothVelocity smoothPressure boundedEnergy smoothInitialData)
        ν u p
      ↔
        ∀ t x,
          timeDerivative u t x + convection u t x + spatialPressureGradient p t x =
            ν • laplacian u t x := by
  rfl

/-- In the same concrete kit, incompressibility is again the vanishing of the
explicit spatial divergence. -/
theorem isIncompressible_mkWithConcreteGradientAndDivergence_iff
    {timeDerivative : NSVelocityField → NSTime → NSSpace → NSSpace}
    {convection : NSVelocityField → NSTime → NSSpace → NSSpace}
    {laplacian : NSVelocityField → NSTime → NSSpace → NSSpace}
    {smoothVelocity : NSVelocityField → Prop}
    {smoothPressure : NSPressureField → Prop}
    {boundedEnergy : NSVelocityField → Prop}
    {smoothInitialData : NSInitialVelocity → Prop}
    {u : NSVelocityField} :
    IsIncompressible
        (mkWithConcreteGradientAndDivergence timeDerivative convection laplacian
          smoothVelocity smoothPressure boundedEnergy smoothInitialData)
        u
      ↔ ∀ t x, spatialDivergence u t x = 0 := by
  rfl

/-- For the most concrete current kit, the momentum equation literally uses the
actual time derivative, spatial pressure gradient, and the chosen convection
and Laplacian operators. -/
theorem satisfiesMomentumEquation_mkWithConcreteTimeGradientAndDivergence_iff
    {convection : NSVelocityField → NSTime → NSSpace → NSSpace}
    {laplacian : NSVelocityField → NSTime → NSSpace → NSSpace}
    {smoothVelocity : NSVelocityField → Prop}
    {smoothPressure : NSPressureField → Prop}
    {boundedEnergy : NSVelocityField → Prop}
    {smoothInitialData : NSInitialVelocity → Prop}
    {ν : ℝ} {u : NSVelocityField} {p : NSPressureField} :
    SatisfiesMomentumEquation
        (mkWithConcreteTimeGradientAndDivergence convection laplacian
          smoothVelocity smoothPressure boundedEnergy smoothInitialData)
        ν u p
      ↔
        ∀ t x,
          timeVelocityDerivative u t x + convection u t x + spatialPressureGradient p t x =
            ν • laplacian u t x := by
  rfl

/-- In the same fully concrete current kit, incompressibility is the vanishing
of the explicit spatial divergence. -/
theorem isIncompressible_mkWithConcreteTimeGradientAndDivergence_iff
    {convection : NSVelocityField → NSTime → NSSpace → NSSpace}
    {laplacian : NSVelocityField → NSTime → NSSpace → NSSpace}
    {smoothVelocity : NSVelocityField → Prop}
    {smoothPressure : NSPressureField → Prop}
    {boundedEnergy : NSVelocityField → Prop}
    {smoothInitialData : NSInitialVelocity → Prop}
    {u : NSVelocityField} :
    IsIncompressible
        (mkWithConcreteTimeGradientAndDivergence convection laplacian
          smoothVelocity smoothPressure boundedEnergy smoothInitialData)
        u
      ↔ ∀ t x, spatialDivergence u t x = 0 := by
  rfl

/-- Divergence-free initial data remain the explicit vanishing condition in the
same fully concrete current kit. -/
theorem divergenceFreeInitialData_mkWithConcreteTimeGradientAndDivergence_iff
    {convection : NSVelocityField → NSTime → NSSpace → NSSpace}
    {laplacian : NSVelocityField → NSTime → NSSpace → NSSpace}
    {smoothVelocity : NSVelocityField → Prop}
    {smoothPressure : NSPressureField → Prop}
    {boundedEnergy : NSVelocityField → Prop}
    {smoothInitialData : NSInitialVelocity → Prop}
    {u₀ : NSInitialVelocity} :
    (mkWithConcreteTimeGradientAndDivergence convection laplacian
      smoothVelocity smoothPressure boundedEnergy smoothInitialData).divergenceFreeInitialData u₀
      ↔ ∀ x, initialSpatialDivergence u₀ x = 0 := by
  rfl

/-- In the currently most concrete kit, the momentum equation literally uses
the actual time derivative, convection term, and pressure gradient on
`ℝ × ℝ^3`. -/
theorem satisfiesMomentumEquation_mkWithConcreteTimeConvectionGradientAndDivergence_iff
    {laplacian : NSVelocityField → NSTime → NSSpace → NSSpace}
    {smoothVelocity : NSVelocityField → Prop}
    {smoothPressure : NSPressureField → Prop}
    {boundedEnergy : NSVelocityField → Prop}
    {smoothInitialData : NSInitialVelocity → Prop}
    {ν : ℝ} {u : NSVelocityField} {p : NSPressureField} :
    SatisfiesMomentumEquation
        (mkWithConcreteTimeConvectionGradientAndDivergence laplacian
          smoothVelocity smoothPressure boundedEnergy smoothInitialData)
        ν u p
      ↔
        ∀ t x,
          timeVelocityDerivative u t x + spatialConvection u t x +
              spatialPressureGradient p t x =
            ν • laplacian u t x := by
  rfl

/-- In the same most concrete current kit, incompressibility is still exactly
the vanishing of the explicit spatial divergence. -/
theorem isIncompressible_mkWithConcreteTimeConvectionGradientAndDivergence_iff
    {laplacian : NSVelocityField → NSTime → NSSpace → NSSpace}
    {smoothVelocity : NSVelocityField → Prop}
    {smoothPressure : NSPressureField → Prop}
    {boundedEnergy : NSVelocityField → Prop}
    {smoothInitialData : NSInitialVelocity → Prop}
    {u : NSVelocityField} :
    IsIncompressible
        (mkWithConcreteTimeConvectionGradientAndDivergence laplacian
          smoothVelocity smoothPressure boundedEnergy smoothInitialData)
        u
      ↔ ∀ t x, spatialDivergence u t x = 0 := by
  rfl

/-- Divergence-free initial data remain the explicit vanishing condition in the
same most concrete current kit. -/
theorem divergenceFreeInitialData_mkWithConcreteTimeConvectionGradientAndDivergence_iff
    {laplacian : NSVelocityField → NSTime → NSSpace → NSSpace}
    {smoothVelocity : NSVelocityField → Prop}
    {smoothPressure : NSPressureField → Prop}
    {boundedEnergy : NSVelocityField → Prop}
    {smoothInitialData : NSInitialVelocity → Prop}
    {u₀ : NSInitialVelocity} :
    (mkWithConcreteTimeConvectionGradientAndDivergence laplacian
      smoothVelocity smoothPressure boundedEnergy smoothInitialData).divergenceFreeInitialData u₀
      ↔ ∀ x, initialSpatialDivergence u₀ x = 0 := by
  rfl

/-- In the fully differential-side concrete kit, the momentum equation is
literally the NS equation with explicit `∂ₜ u`, `(u · ∇)u`, `∇p`, and `Δu`. -/
theorem satisfiesMomentumEquation_mkWithConcreteDifferentialOperators_iff
    {smoothVelocity : NSVelocityField → Prop}
    {smoothPressure : NSPressureField → Prop}
    {boundedEnergy : NSVelocityField → Prop}
    {smoothInitialData : NSInitialVelocity → Prop}
    {ν : ℝ} {u : NSVelocityField} {p : NSPressureField} :
    SatisfiesMomentumEquation
        (mkWithConcreteDifferentialOperators
          smoothVelocity smoothPressure boundedEnergy smoothInitialData)
        ν u p
      ↔
        ∀ t x,
          timeVelocityDerivative u t x + spatialConvection u t x +
              spatialPressureGradient p t x =
            ν • spatialLaplacian u t x := by
  rfl

/-- In the same fully differential-side concrete kit, incompressibility is still
exactly the vanishing of the explicit spatial divergence. -/
theorem isIncompressible_mkWithConcreteDifferentialOperators_iff
    {smoothVelocity : NSVelocityField → Prop}
    {smoothPressure : NSPressureField → Prop}
    {boundedEnergy : NSVelocityField → Prop}
    {smoothInitialData : NSInitialVelocity → Prop}
    {u : NSVelocityField} :
    IsIncompressible
        (mkWithConcreteDifferentialOperators
          smoothVelocity smoothPressure boundedEnergy smoothInitialData)
        u
      ↔ ∀ t x, spatialDivergence u t x = 0 := by
  rfl

/-- Divergence-free initial data remain the explicit vanishing condition in the
same fully differential-side concrete kit. -/
theorem divergenceFreeInitialData_mkWithConcreteDifferentialOperators_iff
    {smoothVelocity : NSVelocityField → Prop}
    {smoothPressure : NSPressureField → Prop}
    {boundedEnergy : NSVelocityField → Prop}
    {smoothInitialData : NSInitialVelocity → Prop}
    {u₀ : NSInitialVelocity} :
    (mkWithConcreteDifferentialOperators
      smoothVelocity smoothPressure boundedEnergy smoothInitialData).divergenceFreeInitialData u₀
      ↔ ∀ x, initialSpatialDivergence u₀ x = 0 := by
  rfl

/-- On the stronger theorem surface, the velocity smoothness predicate is
literally `C^∞` smoothness on `ℝ × ℝ^3`. -/
theorem smoothVelocity_mkWithConcreteDifferentialOperatorsAndSmoothness_iff
    {boundedEnergy : NSVelocityField → Prop}
    {u : NSVelocityField} :
    (mkWithConcreteDifferentialOperatorsAndSmoothness boundedEnergy).smoothVelocity u
      ↔ ContDiff ℝ ∞ (spaceTimeVelocityMap u) := by
  rfl

/-- Likewise, the pressure smoothness predicate is literally `C^∞` smoothness
on `ℝ × ℝ^3`. -/
theorem smoothPressure_mkWithConcreteDifferentialOperatorsAndSmoothness_iff
    {boundedEnergy : NSVelocityField → Prop}
    {p : NSPressureField} :
    (mkWithConcreteDifferentialOperatorsAndSmoothness boundedEnergy).smoothPressure p
      ↔ ContDiff ℝ ∞ (spaceTimePressureMap p) := by
  rfl

/-- Likewise, the initial-data smoothness predicate is literally `C^∞`
smoothness on `ℝ^3`. -/
theorem smoothInitialData_mkWithConcreteDifferentialOperatorsAndSmoothness_iff
    {boundedEnergy : NSVelocityField → Prop}
    {u₀ : NSInitialVelocity} :
    (mkWithConcreteDifferentialOperatorsAndSmoothness boundedEnergy).smoothInitialData u₀
      ↔ ContDiff ℝ ∞ u₀ := by
  rfl

/-- On the stronger theorem surface, the momentum equation still literally uses
the explicit differential operators `∂ₜ u`, `(u · ∇)u`, `∇p`, and `Δu`. -/
theorem satisfiesMomentumEquation_mkWithConcreteDifferentialOperatorsAndSmoothness_iff
    {boundedEnergy : NSVelocityField → Prop}
    {ν : ℝ} {u : NSVelocityField} {p : NSPressureField} :
    SatisfiesMomentumEquation
        (mkWithConcreteDifferentialOperatorsAndSmoothness boundedEnergy)
        ν u p
      ↔
        ∀ t x,
          timeVelocityDerivative u t x + spatialConvection u t x +
              spatialPressureGradient p t x =
            ν • spatialLaplacian u t x := by
  rfl

/-- Incompressibility remains the explicit vanishing of the spatial divergence
on the stronger theorem surface. -/
theorem isIncompressible_mkWithConcreteDifferentialOperatorsAndSmoothness_iff
    {boundedEnergy : NSVelocityField → Prop}
    {u : NSVelocityField} :
    IsIncompressible
        (mkWithConcreteDifferentialOperatorsAndSmoothness boundedEnergy)
        u
      ↔ ∀ t x, spatialDivergence u t x = 0 := by
  rfl

/-- Divergence-free initial data remain the explicit vanishing condition on the
stronger theorem surface. -/
theorem divergenceFreeInitialData_mkWithConcreteDifferentialOperatorsAndSmoothness_iff
    {boundedEnergy : NSVelocityField → Prop}
    {u₀ : NSInitialVelocity} :
    (mkWithConcreteDifferentialOperatorsAndSmoothness boundedEnergy).divergenceFreeInitialData u₀
      ↔ ∀ x, initialSpatialDivergence u₀ x = 0 := by
  rfl

/-- On the fully concrete theorem surface, the bounded-energy predicate is
literally uniform boundedness of the kinetic energy integrals. -/
theorem boundedEnergy_mkFullyConcreteNavierStokesSurface_iff
    {u : NSVelocityField} :
    mkFullyConcreteNavierStokesSurface.boundedEnergy u
      ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ t,
          MeasureTheory.Integrable (fun x => ‖u t x‖ ^ (2 : ℕ)) ∧
            (∫ x, ‖u t x‖ ^ (2 : ℕ) ∂(MeasureTheory.volume : MeasureTheory.Measure NSSpace)) ≤ C := by
  rfl

/-- The fully concrete theorem surface still literally uses the explicit NS
operators `∂ₜ u`, `(u · ∇)u`, `∇p`, and `Δu`. -/
theorem satisfiesMomentumEquation_mkFullyConcreteNavierStokesSurface_iff
    {ν : ℝ} {u : NSVelocityField} {p : NSPressureField} :
    SatisfiesMomentumEquation mkFullyConcreteNavierStokesSurface ν u p
      ↔
        ∀ t x,
          timeVelocityDerivative u t x + spatialConvection u t x +
              spatialPressureGradient p t x =
            ν • spatialLaplacian u t x := by
  rfl

/-- On the fully concrete theorem surface, incompressibility is literally the
vanishing of the explicit spatial divergence. -/
theorem isIncompressible_mkFullyConcreteNavierStokesSurface_iff
    {u : NSVelocityField} :
    IsIncompressible mkFullyConcreteNavierStokesSurface u
      ↔ ∀ t x, spatialDivergence u t x = 0 := by
  rfl

/-- On the fully concrete theorem surface, velocity smoothness is literal
`C^∞` smoothness on `ℝ × ℝ^3`. -/
theorem smoothVelocity_mkFullyConcreteNavierStokesSurface_iff
    {u : NSVelocityField} :
    mkFullyConcreteNavierStokesSurface.smoothVelocity u
      ↔ ContDiff ℝ ∞ (spaceTimeVelocityMap u) := by
  rfl

/-- On the fully concrete theorem surface, pressure smoothness is literal
`C^∞` smoothness on `ℝ × ℝ^3`. -/
theorem smoothPressure_mkFullyConcreteNavierStokesSurface_iff
    {p : NSPressureField} :
    mkFullyConcreteNavierStokesSurface.smoothPressure p
      ↔ ContDiff ℝ ∞ (spaceTimePressureMap p) := by
  rfl

/-- On the fully concrete theorem surface, initial-data smoothness is literal
`C^∞` smoothness on `ℝ^3`. -/
theorem smoothInitialData_mkFullyConcreteNavierStokesSurface_iff
    {u₀ : NSInitialVelocity} :
    mkFullyConcreteNavierStokesSurface.smoothInitialData u₀
      ↔ ContDiff ℝ ∞ u₀ := by
  rfl

/-- On the fully concrete theorem surface, divergence-free initial data are
literally the vanishing of the explicit initial divergence. -/
theorem divergenceFreeInitialData_mkFullyConcreteNavierStokesSurface_iff
    {u₀ : NSInitialVelocity} :
    mkFullyConcreteNavierStokesSurface.divergenceFreeInitialData u₀
      ↔ ∀ x, initialSpatialDivergence u₀ x = 0 := by
  rfl

end ConcreteEquationTarget

end NavierStokes
end FluidDynamics
end Mettapedia
