import MettapediaNS.FullEnergyParentReserve

/-!
# Exact returns retain the full viscous energy loss

Equal endpoint energy forces zero dissipation at every interior time.
The adapter uses the literal kinetic derivative of an actual whole-space
NS evolution. A positive interior gradient energy therefore excludes an
exact return of the full velocity. Approximate pattern returns, rescaled
observations, and transfer into smaller scales are not excluded.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceEnergyReturn

open Set Filter
open scoped Topology

theorem dissipation_zero_of_energy_return (ν T : ℝ) (E D : ℝ → ℝ)
    (hν : 0 < ν) (hT : 0 ≤ T) (hE : ContinuousOn E (Icc 0 T))
    (hD : ∀ t ∈ Ioo 0 T, 0 ≤ D t)
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt E (-2*ν*D t) t)
    (hr : E T = E 0) (t : ℝ) (ht : t ∈ Ioo 0 T) : D t = 0 := by
  have ha : AntitoneOn E (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hE
    · intro s hs
      exact (hd s (by simpa only [interior_Icc] using hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      have hsi : s ∈ Ioo 0 T := by simpa only [interior_Icc] using hs
      rw [(hd s hsi).deriv]
      nlinarith [hD s hsi]
  have hc : EqOn E (fun _ ↦ E 0) (Icc 0 T) := by
    intro s hs
    apply le_antisymm (ha ⟨le_rfl, hT⟩ hs hs.1)
    have hb := ha hs ⟨hT, le_rfl⟩ hs.2
    simpa only [hr] using hb
  have hz : HasDerivAt E 0 t := by
    apply (hasDerivAt_const t (E 0)).congr_of_eventuallyEq
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs using hc hs
  have he := (hd t ht).unique hz
  nlinarith

open EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerContinuousTimeIntegral EulerVolterraConvolution WholeSpaceViscousFlow WholeSpaceOrderEnergy

/-- An exact full-field return in an actual positive-viscosity evolution
has no interior gradient energy. No assumed energy ledger is used. -/
theorem actual_return_zero_dissipation {ν T : ℝ} {hT : 0 ≤ T}
    (U : NSEvolution ν T hT) (hν : 0 < ν)
    (hr : U.velocity ⟨T, hT, le_rfl⟩ = U.velocity ⟨0, le_rfl, hT⟩)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    orderEnergy 1 (U.velocity ⟨t, ht.1.le, ht.2.le⟩) = 0 := by
  let E := extendPath T hT (U.orderEnergyPath 0)
  let D := extendPath T hT (U.orderEnergyPath 1)
  have hd (s : ℝ) (hs : s ∈ Ioo 0 T) : HasDerivAt E (-2*ν*D s) s := by
    have h := (U.orderEnergy_hasDerivWithinAt 0 ⟨s, hs.1.le, hs.2.le⟩).hasDerivAt
      (Icc_mem_nhds hs.1 hs.2)
    rw [FullEnergyParentReserve.actual_kinetic_rate] at h
    simpa only [E, D, extendPath, NSEvolution.orderEnergyPath, ContinuousMap.coe_mk,
      projIcc_of_mem hT (show s ∈ Icc 0 T from ⟨hs.1.le, hs.2.le⟩)] using h
  have hD (s : ℝ) (_hs : s ∈ Ioo 0 T) : 0 ≤ D s := orderEnergy_nonneg 1 _
  have hE : ContinuousOn E (Icc 0 T) :=
    ((U.orderEnergyPath 0).continuous.comp continuous_projIcc).continuousOn
  have hret : E T = E 0 := by
    simp only [E, extendPath, NSEvolution.orderEnergyPath, ContinuousMap.coe_mk,
      projIcc_of_mem hT (show T ∈ Icc 0 T from ⟨hT, le_rfl⟩),
      projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩), hr]
  have h := dissipation_zero_of_energy_return ν T E D hν hT hE hD hd hret t ht
  simpa only [D, extendPath, NSEvolution.orderEnergyPath, ContinuousMap.coe_mk,
    projIcc_of_mem hT (show t ∈ Icc 0 T from ⟨ht.1.le, ht.2.le⟩)] using h

theorem actual_no_return_of_positive_dissipation {ν T : ℝ} {hT : 0 ≤ T}
    (U : NSEvolution ν T hT) (hν : 0 < ν)
    (t : ℝ) (ht : t ∈ Ioo 0 T)
    (hpos : 0 < orderEnergy 1 (U.velocity ⟨t, ht.1.le, ht.2.le⟩)) :
    U.velocity ⟨T, hT, le_rfl⟩ ≠ U.velocity ⟨0, le_rfl, hT⟩ := by
  intro hr
  have hz := actual_return_zero_dissipation U hν hr t ht
  linarith

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceEnergyReturn
