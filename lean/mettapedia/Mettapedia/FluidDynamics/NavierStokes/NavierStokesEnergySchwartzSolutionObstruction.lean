import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzSolutionKernel
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzHeatShearObstruction
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
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap Topology

/-- Calculus helper used by the energy gates: a negative derivative forces an
immediate strict decrease on the right. -/
theorem eventually_right_lt_of_hasDerivAt_lt_zero
    {f : ℝ → ℝ} {t d : ℝ}
    (hderiv : HasDerivAt f d t) (hd : d < 0) :
    ∀ᶠ s in 𝓝[>] t, f s < f t := by
  let g : ℝ → ℝ := fun s => f s - f t
  have hgderiv : HasDerivAt g d t := by
    simpa [g] using hderiv.sub_const (f t)
  have hslope_neg_ne : ∀ᶠ s in 𝓝[≠] t, slope g t s < 0 := by
    exact hgderiv.tendsto_slope.eventually (eventually_lt_nhds hd)
  filter_upwards [nhdsGT_le_nhdsNE t hslope_neg_ne, self_mem_nhdsWithin] with s hslope_neg hgt
  have hden : 0 < s - t := sub_pos.mpr hgt
  have hquot : (g s - g t) / (s - t) < 0 := by
    simpa [slope_def_field] using hslope_neg
  have hnum : g s - g t < 0 := by
    have hmul : ((g s - g t) / (s - t)) * (s - t) < 0 * (s - t) :=
      mul_lt_mul_of_pos_right hquot hden
    rwa [div_mul_cancel₀, zero_mul] at hmul
    exact ne_of_gt hden
  have hg : g s < 0 := by
    simpa [g] using hnum
  simpa [g, sub_lt_iff_lt_add] using hg

/-- A right-neighborhood strict drop gives an actual strict-drop sample in
every positive right interval. -/
theorem exists_right_drop_sample_of_eventually_right_lt
    {f : ℝ → ℝ} {t ε : ℝ}
    (hdrop : ∀ᶠ s in 𝓝[>] t, f s < f t) (hε : 0 < ε) :
    ∃ s, t < s ∧ s < t + ε ∧ f s < f t := by
  have hinterval : Set.Ioo t (t + ε) ∈ 𝓝[>] t := by
    exact Ioo_mem_nhdsGT (by linarith)
  rcases (hdrop.and hinterval).exists with ⟨s, hlt, hsinterval⟩
  exact ⟨s, hsinterval.1, hsinterval.2, hlt⟩

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

/-- Any nonzero value in a Schwartz velocity slice forces strictly positive
corrected coordinate enstrophy on that time slice. -/
theorem coordinateEnstrophyAt_pos_of_velocity_ne_zero
    {t : NSTime} {x : NSSpace} (hne : S.velocity t x ≠ 0) :
    0 < coordinateEnstrophyAt S.velocity t := by
  have hnonneg : 0 ≤ coordinateEnstrophyAt S.velocity t :=
    coordinateEnstrophyAt_nonneg S.velocity t
  have hne_enst : coordinateEnstrophyAt S.velocity t ≠ 0 := by
    intro hzero
    have hvelzero := S.velocity_eq_zero_of_coordinateEnstrophyAt_eq_zero hzero x
    exact hne hvelzero
  exact lt_of_le_of_ne hnonneg (Ne.symm hne_enst)

/-- At positive viscosity, any nonzero value in a Schwartz velocity slice makes
the corrected energy-dissipation rate strictly positive at that time. -/
theorem coordinateEnergyDissipationRate_pos_of_velocity_ne_zero
    (hν : 0 < ν) {t : NSTime} {x : NSSpace} (hne : S.velocity t x ≠ 0) :
    0 < coordinateEnergyDissipationRate S.velocity ν t := by
  simpa [coordinateEnergyDissipationRate] using
    mul_pos hν (S.coordinateEnstrophyAt_pos_of_velocity_ne_zero hne)

/-- At positive viscosity, any nonzero value on a time slice makes the
corrected energy-dissipation rate strictly positive on that whole slice. -/
theorem coordinateEnergyDissipationRate_pos_of_exists_velocity_ne_zero
    (hν : 0 < ν) {t : NSTime}
    (hne : ∃ x : NSSpace, S.velocity t x ≠ 0) :
    0 < coordinateEnergyDissipationRate S.velocity ν t := by
  rcases hne with ⟨x, hx⟩
  exact S.coordinateEnergyDissipationRate_pos_of_velocity_ne_zero hν hx

/-- At positive viscosity, if a velocity slice is nonzero, then every
derivative witness for normalized kinetic energy at that time is strictly
negative. -/
theorem normalizedKineticEnergy_derivative_lt_zero_of_exists_velocity_ne_zero
    (hν : 0 < ν) {t d : ℝ}
    (hne : ∃ x : NSSpace, S.velocity t x ≠ 0)
    (hderiv : HasDerivAt (normalizedKineticEnergy S.velocity) d t) :
    d < 0 := by
  have hrate :
      0 < coordinateEnergyDissipationRate S.velocity ν t :=
    S.coordinateEnergyDissipationRate_pos_of_exists_velocity_ne_zero hν hne
  have hidentity := S.coordinateEnergyDissipationIdentity t
  have hd :
      d = -(coordinateEnergyDissipationRate S.velocity ν t) :=
    hderiv.unique hidentity
  rw [hd]
  exact neg_neg_of_pos hrate

/-- At positive viscosity, if a velocity slice is nonzero at time `t`, then
normalized kinetic energy is eventually strictly lower on the right of `t`. -/
theorem normalizedKineticEnergy_eventually_right_lt_of_exists_velocity_ne_zero
    (hν : 0 < ν) {t : NSTime}
    (hne : ∃ x : NSSpace, S.velocity t x ≠ 0) :
    ∀ᶠ s in 𝓝[>] t,
      normalizedKineticEnergy S.velocity s <
        normalizedKineticEnergy S.velocity t := by
  have hidentity := S.coordinateEnergyDissipationIdentity t
  have hlt :
      -(coordinateEnergyDissipationRate S.velocity ν t) < 0 :=
    S.normalizedKineticEnergy_derivative_lt_zero_of_exists_velocity_ne_zero
      hν hne hidentity
  exact eventually_right_lt_of_hasDerivAt_lt_zero hidentity hlt

/-- Sampled form of the immediate energy-drop gate: every positive right
interval contains an actual later time with strictly smaller normalized kinetic
energy. -/
theorem exists_normalizedKineticEnergy_right_drop_sample_of_exists_velocity_ne_zero
    (hν : 0 < ν) {t ε : NSTime}
    (hne : ∃ x : NSSpace, S.velocity t x ≠ 0) (hε : 0 < ε) :
    ∃ s, t < s ∧ s < t + ε ∧
      normalizedKineticEnergy S.velocity s <
        normalizedKineticEnergy S.velocity t :=
  exists_right_drop_sample_of_eventually_right_lt
    (S.normalizedKineticEnergy_eventually_right_lt_of_exists_velocity_ne_zero
      hν hne)
    hε

/-- Zero normalized-energy derivative at every time is rigid at positive
viscosity: an ordinary slice-Schwartz concrete solution satisfying this
energy-flat condition has identically zero velocity. -/
theorem velocity_eq_zero_of_forall_normalizedKineticEnergy_hasDerivAt_zero_of_pos_viscosity
    (hν : 0 < ν)
    (hzero : ∀ t : NSTime, HasDerivAt (normalizedKineticEnergy S.velocity) 0 t) :
    ∀ t x, S.velocity t x = 0 := by
  intro t x
  have hidentity := S.coordinateEnergyDissipationIdentity t
  have hsame :
      0 = -(coordinateEnergyDissipationRate S.velocity ν t) :=
    (hzero t).unique hidentity
  have hrate : coordinateEnergyDissipationRate S.velocity ν t = 0 := by
    have hneg :
        -(coordinateEnergyDissipationRate S.velocity ν t) = 0 :=
      hsame.symm
    exact neg_eq_zero.mp hneg
  have hmul : ν * coordinateEnstrophyAt S.velocity t = 0 := by
    simpa [coordinateEnergyDissipationRate] using hrate
  have henst : coordinateEnstrophyAt S.velocity t = 0 := by
    rcases mul_eq_zero.mp hmul with hνzero | henst
    · exact (ne_of_gt hν hνzero).elim
    · exact henst
  exact S.velocity_eq_zero_of_coordinateEnstrophyAt_eq_zero henst x

/-- Constant normalized kinetic energy is also rigid at positive viscosity:
inside the slice-Schwartz concrete solution interface it forces zero
velocity. -/
theorem velocity_eq_zero_of_exists_const_normalizedKineticEnergy_of_pos_viscosity
    (hν : 0 < ν)
    (hconst :
      ∃ E : ℝ, normalizedKineticEnergy S.velocity = fun _ : NSTime => E) :
    ∀ t x, S.velocity t x = 0 := by
  rcases hconst with ⟨E, hconst⟩
  exact
    S.velocity_eq_zero_of_forall_normalizedKineticEnergy_hasDerivAt_zero_of_pos_viscosity
      hν
      (by
        intro t
        rw [hconst]
        exact hasDerivAt_const t E)

/-- At positive viscosity, a local minimum of normalized kinetic energy can
occur only on a zero velocity slice.  This rules out local-minimum energy
shortcuts for any nonzero positive-viscosity canary. -/
theorem velocity_eq_zero_of_isLocalMin_normalizedKineticEnergy_of_pos_viscosity
    (hν : 0 < ν) {t : NSTime}
    (hmin : IsLocalMin (normalizedKineticEnergy S.velocity) t) :
    ∀ x, S.velocity t x = 0 := by
  have hidentity := S.coordinateEnergyDissipationIdentity t
  have hneg :
      -(coordinateEnergyDissipationRate S.velocity ν t) = 0 :=
    hmin.hasDerivAt_eq_zero hidentity
  have hrate : coordinateEnergyDissipationRate S.velocity ν t = 0 :=
    neg_eq_zero.mp hneg
  have hmul : ν * coordinateEnstrophyAt S.velocity t = 0 := by
    simpa [coordinateEnergyDissipationRate] using hrate
  have henst : coordinateEnstrophyAt S.velocity t = 0 := by
    rcases mul_eq_zero.mp hmul with hνzero | henst
    · exact (ne_of_gt hν hνzero).elim
    · exact henst
  exact S.velocity_eq_zero_of_coordinateEnstrophyAt_eq_zero henst

/-- At positive viscosity, a local maximum of normalized kinetic energy can
occur only on a zero velocity slice. -/
theorem velocity_eq_zero_of_isLocalMax_normalizedKineticEnergy_of_pos_viscosity
    (hν : 0 < ν) {t : NSTime}
    (hmax : IsLocalMax (normalizedKineticEnergy S.velocity) t) :
    ∀ x, S.velocity t x = 0 := by
  have hidentity := S.coordinateEnergyDissipationIdentity t
  have hneg :
      -(coordinateEnergyDissipationRate S.velocity ν t) = 0 :=
    hmax.hasDerivAt_eq_zero hidentity
  have hrate : coordinateEnergyDissipationRate S.velocity ν t = 0 :=
    neg_eq_zero.mp hneg
  have hmul : ν * coordinateEnstrophyAt S.velocity t = 0 := by
    simpa [coordinateEnergyDissipationRate] using hrate
  have henst : coordinateEnstrophyAt S.velocity t = 0 := by
    rcases mul_eq_zero.mp hmul with hνzero | henst
    · exact (ne_of_gt hν hνzero).elim
    · exact henst
  exact S.velocity_eq_zero_of_coordinateEnstrophyAt_eq_zero henst

/-- At positive viscosity, a locally constant normalized-energy neighborhood
can occur only on a zero velocity slice.  This packages the local-extremum
obstruction in the form needed to reject plateau/recurrent canary shortcuts. -/
theorem velocity_eq_zero_of_eventually_eq_normalizedKineticEnergy_of_pos_viscosity
    (hν : 0 < ν) {t : NSTime}
    (hplateau : ∀ᶠ s in nhds t,
      normalizedKineticEnergy S.velocity s =
        normalizedKineticEnergy S.velocity t) :
    ∀ x, S.velocity t x = 0 := by
  have hmin : IsLocalMin (normalizedKineticEnergy S.velocity) t := by
    exact hplateau.mono (by
      intro s hs
      exact le_of_eq hs.symm)
  exact
    S.velocity_eq_zero_of_isLocalMin_normalizedKineticEnergy_of_pos_viscosity
      hν hmin

/-- Pressure-closure curl gate for the ordinary slice-Schwartz concrete
solution interface: the residual vector field that the pressure gradient must
equal has zero spatial vorticity everywhere. -/
theorem momentumPressureResidual_spatialVorticity_zero :
    ∀ t x, spatialVorticity (momentumPressureResidual ν S.velocity) t x = 0 := by
  intro t x
  exact
    spatialVorticity_momentumPressureResidual_of_momentumEquation
      S.smooth_pressure S.momentumEquation_explicit t x

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

/-- Every nonzero positive-viscosity slice-Schwartz solution has a time with
strictly positive corrected coordinate dissipation. -/
theorem exists_coordinateEnergyDissipationRate_pos_of_pos_viscosity
    (hν : 0 < ν) :
    ∃ t : NSTime, 0 < coordinateEnergyDissipationRate S.velocity ν t := by
  rcases S.nonzero_velocity with ⟨t, x, hne⟩
  exact ⟨t,
    SchwartzConcreteNavierStokesSolution.coordinateEnergyDissipationRate_pos_of_velocity_ne_zero
      S.toSchwartzConcreteNavierStokesSolution hν hne⟩

/-- Nonzero-interface version of the pointwise strict derivative gate.  At a
time slice with a nonzero velocity value, normalized kinetic energy has only
strictly negative derivative witnesses. -/
theorem normalizedKineticEnergy_derivative_lt_zero_of_exists_velocity_ne_zero
    (hν : 0 < ν) {t d : ℝ}
    (hne : ∃ x : NSSpace, S.velocity t x ≠ 0)
    (hderiv : HasDerivAt (normalizedKineticEnergy S.velocity) d t) :
    d < 0 :=
  SchwartzConcreteNavierStokesSolution.normalizedKineticEnergy_derivative_lt_zero_of_exists_velocity_ne_zero
    S.toSchwartzConcreteNavierStokesSolution hν hne hderiv

/-- Strict nonzero energy-identity kernel: at positive viscosity, any nonzero
slice-Schwartz solution has a witness time where the exact coordinate energy
identity carries a strictly negative derivative. -/
theorem exists_strict_coordinateEnergyDissipationIdentity_of_pos_viscosity
    (hν : 0 < ν) :
    ∃ t : NSTime,
      0 < coordinateEnergyDissipationRate S.velocity ν t ∧
        HasDerivAt (normalizedKineticEnergy S.velocity)
          (-(coordinateEnergyDissipationRate S.velocity ν t)) t ∧
        -(coordinateEnergyDissipationRate S.velocity ν t) < 0 := by
  rcases S.exists_coordinateEnergyDissipationRate_pos_of_pos_viscosity hν with ⟨t, hpos⟩
  exact ⟨t, hpos, S.coordinateEnergyDissipationIdentity t, neg_neg_of_pos hpos⟩

/-- Positive-viscosity nonzero slice-Schwartz solutions cannot have zero
kinetic-energy derivative at every time.  Any exact nonzero canary in this
interface must therefore exhibit a genuinely dissipative time. -/
theorem not_forall_normalizedKineticEnergy_hasDerivAt_zero_of_pos_viscosity
    (hν : 0 < ν) :
    ¬ ∀ t : NSTime, HasDerivAt (normalizedKineticEnergy S.velocity) 0 t := by
  intro hzero
  rcases S.exists_strict_coordinateEnergyDissipationIdentity_of_pos_viscosity hν with
    ⟨t, _hpos, hidentity, hneg⟩
  have hsame :
      0 = -(coordinateEnergyDissipationRate S.velocity ν t) :=
    (hzero t).unique hidentity
  exact (ne_of_lt hneg) hsame.symm

/-- Constant normalized kinetic energy is impossible for positive-viscosity
nonzero slice-Schwartz solutions. -/
theorem not_exists_const_normalizedKineticEnergy_of_pos_viscosity
    (hν : 0 < ν) :
    ¬ ∃ E : ℝ, normalizedKineticEnergy S.velocity = fun _ : NSTime => E := by
  rintro ⟨E, hconst⟩
  exact S.not_forall_normalizedKineticEnergy_hasDerivAt_zero_of_pos_viscosity hν
    (by
      intro t
      rw [hconst]
      exact hasDerivAt_const t E)

/-- At any nonzero spacetime witness of a positive-viscosity solution, the
normalized kinetic energy cannot have a local minimum. -/
theorem not_isLocalMin_normalizedKineticEnergy_at_nonzero_of_pos_viscosity
    (hν : 0 < ν) {t : NSTime} {x : NSSpace}
    (hne : S.velocity t x ≠ 0) :
    ¬ IsLocalMin (normalizedKineticEnergy S.velocity) t := by
  intro hmin
  have hzero :=
    SchwartzConcreteNavierStokesSolution.velocity_eq_zero_of_isLocalMin_normalizedKineticEnergy_of_pos_viscosity
      S.toSchwartzConcreteNavierStokesSolution hν hmin x
  exact hne hzero

/-- At any nonzero spacetime witness of a positive-viscosity solution, the
normalized kinetic energy cannot have a local maximum. -/
theorem not_isLocalMax_normalizedKineticEnergy_at_nonzero_of_pos_viscosity
    (hν : 0 < ν) {t : NSTime} {x : NSSpace}
    (hne : S.velocity t x ≠ 0) :
    ¬ IsLocalMax (normalizedKineticEnergy S.velocity) t := by
  intro hmax
  have hzero :=
    SchwartzConcreteNavierStokesSolution.velocity_eq_zero_of_isLocalMax_normalizedKineticEnergy_of_pos_viscosity
      S.toSchwartzConcreteNavierStokesSolution hν hmax x
  exact hne hzero

/-- At a nonzero witness of a positive-viscosity nonzero solution, normalized
kinetic energy cannot be locally constant. -/
theorem not_eventually_eq_normalizedKineticEnergy_at_nonzero_of_pos_viscosity
    (hν : 0 < ν) {t : NSTime} {x : NSSpace}
    (hne : S.velocity t x ≠ 0) :
    ¬ ∀ᶠ s in nhds t,
      normalizedKineticEnergy S.velocity s =
        normalizedKineticEnergy S.velocity t := by
  intro hplateau
  have hzero :=
    SchwartzConcreteNavierStokesSolution.velocity_eq_zero_of_eventually_eq_normalizedKineticEnergy_of_pos_viscosity
      S.toSchwartzConcreteNavierStokesSolution hν hplateau x
  exact hne hzero

/-- At a nonzero witness of a positive-viscosity nonzero solution, normalized
kinetic energy cannot be eventually nondecreasing to the right. -/
theorem not_eventually_right_normalizedKineticEnergy_nondecreasing_at_nonzero_of_pos_viscosity
    (hν : 0 < ν) {t : NSTime} {x : NSSpace}
    (hne : S.velocity t x ≠ 0) :
    ¬ ∀ᶠ s in 𝓝[>] t,
      normalizedKineticEnergy S.velocity t ≤
        normalizedKineticEnergy S.velocity s := by
  intro hnondec
  have hdrop :
      ∀ᶠ s in 𝓝[>] t,
        normalizedKineticEnergy S.velocity s <
          normalizedKineticEnergy S.velocity t :=
    SchwartzConcreteNavierStokesSolution.normalizedKineticEnergy_eventually_right_lt_of_exists_velocity_ne_zero
      S.toSchwartzConcreteNavierStokesSolution hν ⟨x, hne⟩
  have hfalse : ∀ᶠ s in 𝓝[>] t, False := by
    filter_upwards [hdrop, hnondec] with s hlt hle
    exact not_lt_of_ge hle hlt
  exact (by infer_instance : (𝓝[>] t).NeBot).ne
    (Filter.eventually_false_iff_eq_bot.mp hfalse)

/-- At a positive-viscosity nonzero witness, every positive right interval
contains an actual lower normalized-energy sample. -/
theorem exists_normalizedKineticEnergy_right_drop_sample_at_nonzero_of_pos_viscosity
    (hν : 0 < ν) {t ε : NSTime} {x : NSSpace}
    (hne : S.velocity t x ≠ 0) (hε : 0 < ε) :
    ∃ s, t < s ∧ s < t + ε ∧
      normalizedKineticEnergy S.velocity s <
        normalizedKineticEnergy S.velocity t :=
  SchwartzConcreteNavierStokesSolution.exists_normalizedKineticEnergy_right_drop_sample_of_exists_velocity_ne_zero
    S.toSchwartzConcreteNavierStokesSolution hν ⟨x, hne⟩ hε

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

/-- Residual-curl pressure-closure obstruction for the ordinary
slice-Schwartz solution interface.  If the vector field
`ν Δu - ∂ₜu - (u · ∇)u` has nonzero spatial vorticity anywhere, it cannot be
the pressure gradient of a smooth pressure in a concrete solution. -/
theorem not_exists_schwartzConcreteSolution_velocity_of_momentumPressureResidual_vorticity_ne_zero
    {ν : ℝ} {u : NSVelocityField}
    (hcurl :
      ∃ t : NSTime, ∃ x : NSSpace,
        spatialVorticity (momentumPressureResidual ν u) t x ≠ 0) :
    ¬ ∃ S : SchwartzConcreteNavierStokesSolution ν, S.velocity = u := by
  rintro ⟨S, hvelocity⟩
  rcases hcurl with ⟨t, x, hne⟩
  have hzero :
      spatialVorticity (momentumPressureResidual ν S.velocity) t x = 0 :=
    S.momentumPressureResidual_spatialVorticity_zero t x
  have hzero_u :
      spatialVorticity (momentumPressureResidual ν u) t x = 0 := by
    simpa [← hvelocity] using hzero
  exact hne hzero_u

/-- Nonzero refinement of the same residual-curl pressure-closure obstruction. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_velocity_of_momentumPressureResidual_vorticity_ne_zero
    {ν : ℝ} {u : NSVelocityField}
    (hcurl :
      ∃ t : NSTime, ∃ x : NSSpace,
        spatialVorticity (momentumPressureResidual ν u) t x ≠ 0) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν, S.velocity = u := by
  rintro ⟨S, hvelocity⟩
  exact
    not_exists_schwartzConcreteSolution_velocity_of_momentumPressureResidual_vorticity_ne_zero
      hcurl
      ⟨S.toSchwartzConcreteNavierStokesSolution, hvelocity⟩

/-- A nondegenerate heat-shear field is genuinely nonzero as a spacetime
velocity field. -/
theorem heatShearVelocityField_exists_nonzero_of_amplitude_ne_zero_of_wavenumber_ne_zero
    {ν a k : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) :
    ∃ t : NSTime, ∃ x : NSSpace, heatShearVelocityField ν a k t x ≠ 0 := by
  by_contra hnone
  have hvelocity_zero : heatShearVelocityField ν a k = (0 : NSVelocityField) := by
    funext t x
    by_contra hne
    exact hnone ⟨t, x, hne⟩
  have hinitial_zero : heatShearInitialVelocity a k = (0 : NSInitialVelocity) := by
    funext x
    have hfield_zero : heatShearVelocityField ν a k 0 x = 0 := by
      simpa using congrArg (fun u : NSVelocityField => u 0 x) hvelocity_zero
    rw [← matchesInitialVelocity_heatShearVelocityField ν a k x]
    exact hfield_zero
  exact
    heatShearInitialVelocity_ne_zero_of_amplitude_ne_zero_of_wavenumber_ne_zero
      ha hk hinitial_zero

/-- The classical heat-shear family solves the zero-pressure equation at its
own viscosity, but no nondegenerate member can be the velocity of a
slice-Schwartz concrete solution: the time-zero Schwartz slice would equal the
nondecaying heat-shear initial datum. -/
theorem not_exists_schwartzConcreteSolution_velocity_heatShearVelocityField
    {ν a k : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ ∃ S : SchwartzConcreteNavierStokesSolution ν,
      S.velocity = heatShearVelocityField ν a k := by
  rintro ⟨S, hvelocity⟩
  have hslice :
      (S.velocitySlice 0 : NSInitialVelocity) = heatShearInitialVelocity a k := by
    funext x
    calc
      (S.velocitySlice 0 : NSSpace → NSSpace) x = S.velocity 0 x := by
        exact (S.velocitySlice_eq 0 x).symm
      _ = heatShearVelocityField ν a k 0 x := by
        simp [hvelocity]
      _ = heatShearInitialVelocity a k x := by
        exact matchesInitialVelocity_heatShearVelocityField ν a k x
  exact
    not_exists_schwartzInitialVelocity_eq_heatShearInitialVelocity_of_amplitude_ne_zero_of_wavenumber_ne_zero
      ha hk ⟨S.velocitySlice 0, hslice⟩

/-- Nonzero-interface version of the heat-shear Schwartz-decay obstruction. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_velocity_heatShearVelocityField
    {ν a k : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      S.velocity = heatShearVelocityField ν a k := by
  rintro ⟨S, hvelocity⟩
  exact
    not_exists_schwartzConcreteSolution_velocity_heatShearVelocityField
      ha hk ⟨S.toSchwartzConcreteNavierStokesSolution, hvelocity⟩

/-- Tested at the wrong viscosity, the same heat-shear family also fails the
pressure-closure curl gate. -/
theorem not_exists_schwartzConcreteSolution_velocity_heatShearVelocityField_wrongViscosity
    {μ ν a k : ℝ} (hμν : μ ≠ ν) (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ ∃ S : SchwartzConcreteNavierStokesSolution μ,
      S.velocity = heatShearVelocityField ν a k := by
  exact
    not_exists_schwartzConcreteSolution_velocity_of_momentumPressureResidual_vorticity_ne_zero
      (ν := μ) (u := heatShearVelocityField ν a k)
      ⟨0, 0,
        spatialVorticity_momentumPressureResidual_heatShearVelocityField_origin_ne_zero
          hμν ha hk⟩

/-- Nonzero-interface version of the wrong-viscosity heat-shear curl
obstruction. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_velocity_heatShearVelocityField_wrongViscosity
    {μ ν a k : ℝ} (hμν : μ ≠ ν) (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution μ,
      S.velocity = heatShearVelocityField ν a k := by
  rintro ⟨S, hvelocity⟩
  exact
    not_exists_schwartzConcreteSolution_velocity_heatShearVelocityField_wrongViscosity
      hμν ha hk ⟨S.toSchwartzConcreteNavierStokesSolution, hvelocity⟩

/-- Boundary packet for the classical shear-flow shortcut: nondegenerate
heat-shear is nonzero, divergence-free, and solves the zero-pressure
Navier-Stokes equation at its own viscosity, but it cannot inhabit the
slice-Schwartz concrete-solution interface. -/
theorem heatShearVelocityField_exact_nonzero_and_not_schwartzConcreteSolution
    (ν : ℝ) {a k : ℝ} (ha : a ≠ 0) (hk : k ≠ 0) :
    (∃ t : NSTime, ∃ x : NSSpace, heatShearVelocityField ν a k t x ≠ 0) ∧
      (∀ t x, spatialDivergence (heatShearVelocityField ν a k) t x = 0) ∧
      (∀ t x,
        timeVelocityDerivative (heatShearVelocityField ν a k) t x +
            spatialConvection (heatShearVelocityField ν a k) t x +
            spatialPressureGradient (0 : NSPressureField) t x =
          ν • spatialLaplacian (heatShearVelocityField ν a k) t x) ∧
      (¬ ∃ S : SchwartzConcreteNavierStokesSolution ν,
        S.velocity = heatShearVelocityField ν a k) ∧
      (¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
        S.velocity = heatShearVelocityField ν a k) := by
  exact
    ⟨heatShearVelocityField_exists_nonzero_of_amplitude_ne_zero_of_wavenumber_ne_zero
        ha hk,
      spatialDivergence_heatShearVelocityField ν a k,
      momentumEquation_heatShearVelocityField_zeroPressure ν a k,
      not_exists_schwartzConcreteSolution_velocity_heatShearVelocityField ha hk,
      not_exists_nonzeroSchwartzConcreteSolution_velocity_heatShearVelocityField
        ha hk⟩

/-- Local residual identity for the constant-amplitude two-mode branch.  Under
the inviscid convection closure, the pressure residual is exactly the viscous
Laplacian residual that a pressure gradient would have to supply. -/
theorem
    momentumPressureResidual_oneOneTwoModeSchwartzVelocity_of_inviscidClosure_forSchwartzKernel
    {ν : ℝ} (f g : NSSchwartzInitialVelocity)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0) :
    momentumPressureResidual ν
        (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) =
      (fun t x =>
        (ν : ℝ) •
          (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x)) := by
  funext t x
  unfold momentumPressureResidual
  rw [timeVelocityDerivative_twoModeSchwartzVelocity_deriv
      (a := fun _ : NSTime => 1) (b := fun _ : NSTime => 1)
      contDiff_const contDiff_const f g t x,
    spatialConvection_twoModeSchwartzVelocity
      (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x,
    spatialLaplacian_twoModeSchwartzVelocity
      (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x]
  simp [hclosure t x]

/-- Direct slice-Schwartz interface form of the one-one two-mode residual-curl
gate.  Once the constant-amplitude two-mode branch is inviscidly closed, any
actual concrete solution with that velocity forces the viscous Laplacian
residual to be curl-free everywhere. -/
theorem
    oneOneTwoModeSchwartzVelocity_lapSum_residualVorticity_zero_of_schwartzConcreteSolution
    {ν : ℝ} (S : SchwartzConcreteNavierStokesSolution ν)
    (f g : NSSchwartzInitialVelocity)
    (hvelocity :
      S.velocity =
        twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0) :
    ∀ t x,
      spatialVorticity
        (fun s y =>
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) s y +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) s y)) t x =
        0 := by
  intro t x
  have hzero :=
    S.momentumClosureKernel.pressureResidual_vorticity_zero t x
  simpa [hvelocity,
    momentumPressureResidual_oneOneTwoModeSchwartzVelocity_of_inviscidClosure_forSchwartzKernel
      (ν := ν) f g hclosure] using hzero

/-- Pressure-agnostic no-go for the exact slice-Schwartz interface on the
constant-amplitude two-mode branch: if the inviscidly closed branch has a
viscous Laplacian residual with nonzero curl anywhere, no pressure slices can
make it a concrete solution. -/
theorem
    not_exists_schwartzConcreteSolution_oneOneTwoModeSchwartzVelocity_of_inviscidClosure_residualVorticity_ne_zero
    {ν : ℝ} (f g : NSSchwartzInitialVelocity)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hcurl : ∃ t x,
      spatialVorticity
        (fun s y =>
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) s y +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) s y)) t x ≠
        0) :
    ¬ ∃ S : SchwartzConcreteNavierStokesSolution ν,
      S.velocity =
        twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g := by
  rintro ⟨S, hvelocity⟩
  rcases hcurl with ⟨t, x, hne⟩
  exact hne
    (oneOneTwoModeSchwartzVelocity_lapSum_residualVorticity_zero_of_schwartzConcreteSolution
      S f g hvelocity hclosure t x)

/-- Nonzero-interface version of the one-one two-mode residual-curl no-go. -/
theorem
    not_exists_nonzeroSchwartzConcreteSolution_oneOneTwoModeSchwartzVelocity_of_inviscidClosure_residualVorticity_ne_zero
    {ν : ℝ} (f g : NSSchwartzInitialVelocity)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hcurl : ∃ t x,
      spatialVorticity
        (fun s y =>
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) s y +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) s y)) t x ≠
        0) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      S.velocity =
        twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g := by
  rintro ⟨S, hvelocity⟩
  exact
    not_exists_schwartzConcreteSolution_oneOneTwoModeSchwartzVelocity_of_inviscidClosure_residualVorticity_ne_zero
      f g hclosure hcurl
      ⟨S.toSchwartzConcreteNavierStokesSolution, hvelocity⟩

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

/-- No positive-viscosity nonzero slice-Schwartz concrete solution can have
zero normalized kinetic-energy derivative at every time. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_forall_normalizedKineticEnergy_hasDerivAt_zero
    {ν : ℝ} (hν : 0 < ν) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∀ t : NSTime, HasDerivAt (normalizedKineticEnergy S.velocity) 0 t := by
  rintro ⟨S, hzero⟩
  exact S.not_forall_normalizedKineticEnergy_hasDerivAt_zero_of_pos_viscosity hν hzero

/-- Constant normalized kinetic energy is impossible for positive-viscosity
nonzero slice-Schwartz concrete solutions. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_const_normalizedKineticEnergy_of_pos_viscosity
    {ν : ℝ} (hν : 0 < ν) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ E : ℝ, normalizedKineticEnergy S.velocity = fun _ : NSTime => E := by
  rintro ⟨S, hconst⟩
  exact S.not_exists_const_normalizedKineticEnergy_of_pos_viscosity hν hconst

/-- No positive-viscosity nonzero slice-Schwartz solution can present a
nonzero witness time where normalized kinetic energy has a local minimum. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_nonzero_localMin_energy_of_pos_viscosity
    {ν : ℝ} (hν : 0 < ν) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ t x,
        S.velocity t x ≠ 0 ∧
          IsLocalMin (normalizedKineticEnergy S.velocity) t := by
  rintro ⟨S, t, x, hne, hmin⟩
  exact S.not_isLocalMin_normalizedKineticEnergy_at_nonzero_of_pos_viscosity
    hν hne hmin

/-- No positive-viscosity nonzero slice-Schwartz solution can present a
nonzero witness time where normalized kinetic energy has a local maximum. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_nonzero_localMax_energy_of_pos_viscosity
    {ν : ℝ} (hν : 0 < ν) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ t x,
        S.velocity t x ≠ 0 ∧
          IsLocalMax (normalizedKineticEnergy S.velocity) t := by
  rintro ⟨S, t, x, hne, hmax⟩
  exact S.not_isLocalMax_normalizedKineticEnergy_at_nonzero_of_pos_viscosity
    hν hne hmax

/-- No positive-viscosity nonzero slice-Schwartz solution can have a nonzero
velocity witness at a time where normalized kinetic energy has a nonnegative
derivative witness. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_nonzero_nonneg_energy_derivative_of_pos_viscosity
    {ν : ℝ} (hν : 0 < ν) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ t x d,
        S.velocity t x ≠ 0 ∧
          HasDerivAt (normalizedKineticEnergy S.velocity) d t ∧
            0 ≤ d := by
  rintro ⟨S, t, x, d, hne, hderiv, hnonneg⟩
  have hlt :
      d < 0 :=
    S.normalizedKineticEnergy_derivative_lt_zero_of_exists_velocity_ne_zero
      hν ⟨x, hne⟩ hderiv
  exact not_lt_of_ge hnonneg hlt

/-- No positive-viscosity nonzero slice-Schwartz solution can present a
nonzero witness time at which normalized kinetic energy is locally constant. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_nonzero_energy_plateau_of_pos_viscosity
    {ν : ℝ} (hν : 0 < ν) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ t x,
        S.velocity t x ≠ 0 ∧
          (∀ᶠ s in nhds t,
            normalizedKineticEnergy S.velocity s =
              normalizedKineticEnergy S.velocity t) := by
  rintro ⟨S, t, x, hne, hplateau⟩
  exact S.not_eventually_eq_normalizedKineticEnergy_at_nonzero_of_pos_viscosity
    hν hne hplateau

/-- No positive-viscosity nonzero slice-Schwartz solution can present a
nonzero witness time at which normalized kinetic energy is eventually
nondecreasing to the right. -/
theorem
    not_exists_nonzeroSchwartzConcreteSolution_nonzero_eventually_right_energy_nondecreasing_of_pos_viscosity
    {ν : ℝ} (hν : 0 < ν) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      ∃ t x,
        S.velocity t x ≠ 0 ∧
          (∀ᶠ s in 𝓝[>] t,
            normalizedKineticEnergy S.velocity t ≤
              normalizedKineticEnergy S.velocity s) := by
  rintro ⟨S, t, x, hne, hnondec⟩
  exact
    S.not_eventually_right_normalizedKineticEnergy_nondecreasing_at_nonzero_of_pos_viscosity
      hν hne hnondec

end NavierStokes
end FluidDynamics
end Mettapedia
