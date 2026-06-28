import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzSolutionKernel
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzDirectionalRigidity

/-!
# Line-Invariant Obstruction for Nonzero Slice-Schwartz Solutions

This module rules out the tempting line-invariant shear shortcut inside the
nonzero slice-Schwartz energy-identity lane.  A Schwartz spatial slice on
`R^3` that is invariant along any nonzero direction must vanish.  Consequently,
an exact nonzero slice-Schwartz Navier-Stokes solution cannot have all velocity
slices invariant along such a direction.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap

namespace SchwartzConcreteNavierStokesSolution

variable {ν : ℝ} (S : SchwartzConcreteNavierStokesSolution ν)

/-- If one velocity slice of a slice-Schwartz concrete solution is invariant
along a nonzero direction, Schwartz decay forces that entire slice to vanish. -/
theorem velocity_eq_zero_of_velocitySlice_translationInvariantAlong
    {t : NSTime} {v : NSSpace} (hv : v ≠ 0)
    (hinv : TranslationInvariantAlong v (fun x : NSSpace => S.velocitySlice t x)) :
    ∀ x, S.velocity t x = 0 := by
  intro x
  have hslice_zero : S.velocitySlice t = 0 :=
    schwartzMap_eq_zero_of_translationInvariantAlong (S.velocitySlice t) hv hinv
  have hslice_x : S.velocitySlice t x = 0 := by
    simpa using congrArg (fun f : 𝓢(NSSpace, NSSpace) => f x) hslice_zero
  simpa [hslice_x] using S.velocitySlice_eq t x

/-- A time-independent velocity in the slice-Schwartz concrete solution
interface has zero corrected coordinate dissipation at every time.  This is a
stationary-energy gate: the exact energy identity and constant kinetic energy
leave no room for positive dissipation. -/
theorem coordinateEnergyDissipationRate_eq_zero_of_velocity_timeIndependent
    {u₀ : NSInitialVelocity}
    (hvelocity : S.velocity = timeIndependentVelocity u₀) (t : NSTime) :
    coordinateEnergyDissipationRate S.velocity ν t = 0 := by
  have hconst :
      normalizedKineticEnergy (timeIndependentVelocity u₀) =
        fun _ : NSTime => normalizedKineticEnergy (timeIndependentVelocity u₀) t := by
    funext s
    simp [normalizedKineticEnergy, kineticEnergyAt_timeIndependentVelocity]
  have hzeroDeriv :
      HasDerivAt (normalizedKineticEnergy S.velocity) 0 t := by
    rw [hvelocity, hconst]
    simpa using
      (hasDerivAt_const t (normalizedKineticEnergy (timeIndependentVelocity u₀) t))
  have hidentity := S.coordinateEnergyDissipationIdentity t
  have hsame :
      0 = -(coordinateEnergyDissipationRate S.velocity ν t) :=
    hzeroDeriv.unique hidentity
  have hneg :
      -(coordinateEnergyDissipationRate S.velocity ν t) = 0 := by
    exact hsame.symm
  exact neg_eq_zero.mp hneg

/-- Contrapositive stationary gate for the ordinary slice-Schwartz solution
interface: a time-independent candidate with nonzero corrected dissipation at
some time cannot inhabit the concrete solution interface. -/
theorem not_exists_velocity_timeIndependent_of_coordinateEnergyDissipationRate_ne_zero
    {u₀ : NSInitialVelocity}
    (hdiss :
      ∃ t : NSTime,
        coordinateEnergyDissipationRate (timeIndependentVelocity u₀) ν t ≠ 0) :
    ¬ ∃ S : SchwartzConcreteNavierStokesSolution ν,
      S.velocity = timeIndependentVelocity u₀ := by
  rintro ⟨S, hvelocity⟩
  rcases hdiss with ⟨t, ht⟩
  have hzero :=
    S.coordinateEnergyDissipationRate_eq_zero_of_velocity_timeIndependent hvelocity t
  exact ht (by simpa [hvelocity] using hzero)

end SchwartzConcreteNavierStokesSolution

namespace NonzeroSchwartzConcreteNavierStokesSolution

variable {ν : ℝ} (S : NonzeroSchwartzConcreteNavierStokesSolution ν)

/-- A nonzero slice-Schwartz concrete solution cannot be line-invariant at
every time slice along a fixed nonzero direction. -/
theorem not_all_velocitySlices_translationInvariantAlong
    {v : NSSpace} (hv : v ≠ 0) :
    ¬ ∀ t : NSTime,
      TranslationInvariantAlong v (fun x : NSSpace => S.velocitySlice t x) := by
  intro hall
  rcases S.nonzero_velocity with ⟨t, x, hne⟩
  have hzero :=
    SchwartzConcreteNavierStokesSolution.velocity_eq_zero_of_velocitySlice_translationInvariantAlong
      S.toSchwartzConcreteNavierStokesSolution hv (hall t) x
  exact hne hzero

/-- Equivalently, in every nonzero spatial direction, a nonzero
slice-Schwartz concrete solution has at least one velocity slice that breaks
line invariance. -/
theorem exists_velocitySlice_not_translationInvariantAlong
    {v : NSSpace} (hv : v ≠ 0) :
    ∃ t : NSTime,
      ¬ TranslationInvariantAlong v (fun x : NSSpace => S.velocitySlice t x) := by
  by_contra hnone
  exact S.not_all_velocitySlices_translationInvariantAlong hv (by
    intro t
    by_contra ht
    exact hnone ⟨t, ht⟩)

/-- Nonzero solutions inherit the stationary-energy gate from the underlying
slice-Schwartz solution. -/
theorem coordinateEnergyDissipationRate_eq_zero_of_velocity_timeIndependent
    {u₀ : NSInitialVelocity}
    (hvelocity : S.velocity = timeIndependentVelocity u₀) (t : NSTime) :
    coordinateEnergyDissipationRate S.velocity ν t = 0 :=
  SchwartzConcreteNavierStokesSolution.coordinateEnergyDissipationRate_eq_zero_of_velocity_timeIndependent
    S.toSchwartzConcreteNavierStokesSolution hvelocity t

end NonzeroSchwartzConcreteNavierStokesSolution

/-- No nonzero slice-Schwartz concrete solution can keep all velocity slices
translation-invariant along a fixed nonzero spatial direction. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_all_velocitySlices_translationInvariantAlong
    {ν : ℝ} {v : NSSpace} (hv : v ≠ 0) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∀ t : NSTime,
        TranslationInvariantAlong v (fun x : NSSpace => S.velocitySlice t x) := by
  rintro ⟨S, hall⟩
  exact S.not_all_velocitySlices_translationInvariantAlong hv hall

/-- Necessary condition for any future explicit nonzero slice-Schwartz canary:
for each nonzero direction, some velocity slice must break line invariance. -/
theorem every_nonzeroSchwartzConcreteSolution_has_non_lineInvariant_slice
    {ν : ℝ} (S : NonzeroSchwartzConcreteNavierStokesSolution ν)
    {v : NSSpace} (hv : v ≠ 0) :
    ∃ t : NSTime,
      ¬ TranslationInvariantAlong v (fun x : NSSpace => S.velocitySlice t x) :=
  S.exists_velocitySlice_not_translationInvariantAlong hv

/-- Contrapositive stationary gate for nonzero slice-Schwartz solutions:
nonzero corrected dissipation rules out a time-independent velocity
representation. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_velocity_timeIndependent_of_coordinateEnergyDissipationRate_ne_zero
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hdiss :
      ∃ t : NSTime,
        coordinateEnergyDissipationRate (timeIndependentVelocity u₀) ν t ≠ 0) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      S.velocity = timeIndependentVelocity u₀ := by
  rintro ⟨S, hvelocity⟩
  exact
    (SchwartzConcreteNavierStokesSolution.not_exists_velocity_timeIndependent_of_coordinateEnergyDissipationRate_ne_zero
      (ν := ν) hdiss)
      ⟨S.toSchwartzConcreteNavierStokesSolution, hvelocity⟩

end NavierStokes
end FluidDynamics
end Mettapedia
