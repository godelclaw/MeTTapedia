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

open MeasureTheory
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

/-- Zero corrected coordinate enstrophy on a Schwartz velocity slice forces the
entire slice to vanish.  This packages the positivity of the coordinate
gradient square together with Schwartz directional rigidity. -/
theorem velocity_eq_zero_of_coordinateEnstrophyAt_eq_zero
    {t : NSTime} (henst : coordinateEnstrophyAt S.velocity t = 0) :
    ∀ x, S.velocity t x = 0 := by
  let f : 𝓢(NSSpace, NSSpace) := S.velocitySlice t
  let g : NSSpace → ℝ :=
    fun x => ∑ i : NSStdBasisIndex, ‖∂_{nsStdBasis i} f x‖ ^ (2 : ℕ)
  have hsliceFun : (fun x : NSSpace => S.velocity t x) = (f : NSSpace → NSSpace) := by
    funext x
    exact S.velocitySlice_eq t x
  have hdensity : coordinateEnstrophyDensity S.velocity t = g := by
    funext x
    simp only [coordinateEnstrophyDensity, g]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [spatialFDeriv, hsliceFun]
    rw [← SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hgint : Integrable g := by
    refine integrable_finsetSum (Finset.univ : Finset NSStdBasisIndex) ?_
    intro i _hi
    exact integrable_norm_sq_of_schwartz (∂_{nsStdBasis i} f)
  have hgcont : Continuous g := by
    refine continuous_finsetSum Finset.univ ?_
    intro i _hi
    exact ((∂_{nsStdBasis i} f).continuous.norm.pow 2)
  have hgnonneg : 0 ≤ g := by
    intro x
    exact Finset.sum_nonneg fun _i _hi => by positivity
  have hgintegral : ∫ x, g x ∂volume = 0 := by
    simpa [coordinateEnstrophyAt, hdensity] using henst
  let i0 : NSStdBasisIndex := ⟨0, by simp [NSSpace]⟩
  have hv0 : nsStdBasis i0 ≠ 0 := by
    have hnorm := OrthonormalBasis.norm_eq_one nsStdBasis i0
    intro hzero
    rw [hzero] at hnorm
    norm_num at hnorm
  have hderiv_zero : ∀ x : NSSpace,
      fderiv ℝ (fun z : NSSpace => f z) x (nsStdBasis i0) = 0 := by
    intro x
    by_contra hnonzero
    have hline_nonzero : (∂_{nsStdBasis i0} f) x ≠ 0 := by
      simpa [SchwartzMap.lineDerivOp_apply_eq_fderiv] using hnonzero
    have htermpos : 0 < ‖(∂_{nsStdBasis i0} f) x‖ ^ (2 : ℕ) := by
      exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hline_nonzero)
    have hle : ‖(∂_{nsStdBasis i0} f) x‖ ^ (2 : ℕ) ≤ g x := by
      have hle' :
          ‖(∂_{nsStdBasis i0} f) x‖ ^ (2 : ℕ) ≤
            ∑ i : NSStdBasisIndex, ‖(∂_{nsStdBasis i} f) x‖ ^ (2 : ℕ) := by
        exact Finset.single_le_sum
          (s := Finset.univ)
          (f := fun i : NSStdBasisIndex => ‖(∂_{nsStdBasis i} f) x‖ ^ (2 : ℕ))
          (fun _i _hi => by positivity)
          (Finset.mem_univ i0)
      simpa [g] using hle'
    have hgxpos : 0 < g x := lt_of_lt_of_le htermpos hle
    have hgx_ne : g x ≠ 0 := ne_of_gt hgxpos
    have hpos : 0 < ∫ y, g y ∂volume :=
      MeasureTheory.integral_pos_of_integrable_nonneg_nonzero
        (x := x) hgcont hgint hgnonneg hgx_ne
    have hnot : ¬ 0 < ∫ y, g y ∂volume := by
      rw [hgintegral]
      exact lt_irrefl 0
    exact hnot hpos
  have hfzero : f = 0 :=
    schwartzMap_eq_zero_of_fderiv_eq_zero_along f hv0 hderiv_zero
  intro x
  have hslice_x : f x = 0 := by
    simpa using congrArg (fun F : 𝓢(NSSpace, NSSpace) => F x) hfzero
  simpa [f, hslice_x] using S.velocitySlice_eq t x

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

/-- At positive viscosity, a time-independent velocity in the slice-Schwartz
concrete solution interface must vanish identically. -/
theorem velocity_eq_zero_of_velocity_timeIndependent_of_pos_viscosity
    (hν : 0 < ν) {u₀ : NSInitialVelocity}
    (hvelocity : S.velocity = timeIndependentVelocity u₀) :
    ∀ t x, S.velocity t x = 0 := by
  intro t x
  have hrate :=
    S.coordinateEnergyDissipationRate_eq_zero_of_velocity_timeIndependent hvelocity t
  have hmul : ν * coordinateEnstrophyAt S.velocity t = 0 := by
    simpa [coordinateEnergyDissipationRate] using hrate
  have henst : coordinateEnstrophyAt S.velocity t = 0 := by
    rcases mul_eq_zero.mp hmul with hνzero | henst
    · exact (ne_of_gt hν hνzero).elim
    · exact henst
  exact S.velocity_eq_zero_of_coordinateEnstrophyAt_eq_zero henst x

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

/-- Nonzero solutions inherit the positive-viscosity stationary obstruction
from the underlying slice-Schwartz solution. -/
theorem velocity_eq_zero_of_velocity_timeIndependent_of_pos_viscosity
    (hν : 0 < ν) {u₀ : NSInitialVelocity}
    (hvelocity : S.velocity = timeIndependentVelocity u₀) :
    ∀ t x, S.velocity t x = 0 :=
  SchwartzConcreteNavierStokesSolution.velocity_eq_zero_of_velocity_timeIndependent_of_pos_viscosity
    S.toSchwartzConcreteNavierStokesSolution hν hvelocity

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

/-- Positive-viscosity strengthening: no nonzero slice-Schwartz concrete
solution can have a time-independent velocity.  Any exact nonzero canary in
this interface must therefore be genuinely time-dependent. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_velocity_timeIndependent_of_pos_viscosity
    {ν : ℝ} (hν : 0 < ν) {u₀ : NSInitialVelocity} :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      S.velocity = timeIndependentVelocity u₀ := by
  rintro ⟨S, hvelocity⟩
  rcases S.nonzero_velocity with ⟨t, x, hne⟩
  have hzero :=
    NonzeroSchwartzConcreteNavierStokesSolution.velocity_eq_zero_of_velocity_timeIndependent_of_pos_viscosity
      S hν hvelocity t x
  exact hne hzero

end NavierStokes
end FluidDynamics
end Mettapedia
