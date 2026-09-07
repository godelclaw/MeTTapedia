import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeAEMaterialChainRule

/-!
# The compact periodic material rate is the derivative of the spatial mean

The weak transport cancellation identifies the actual mean material rate
with the time derivative. Uniform local Lipschitz bounds justify moving
the derivative through the spatial integral. Absolute continuity then
gives an interval identity, with time integrability proved as a conclusion.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeMeanMaterialBalance

open scoped Topology
open MeasureTheory Set
open PancakeMaterialChainRule PancakeAEMaterialChainRule PancakeCompactMeanDerivative
open PancakePeriodicLipschitz PancakeFourierMaterialPaths PancakeWeakIncompressibleTransport

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "ST" => ℝ × X3

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem ae_hasDerivAt_mean_materialRate
    (f : ℝ → T3 → ℝ) (v : ℝ → T3 → R3)
    (hf : Continuous f.uncurry) (hv : ∀ t, Continuous (v t))
    (hfL : LocallyLipschitz (fun z : ST ↦ f z.1 (torusPoint z.2)))
    (hvL : ∀ t j, LocallyLipschitz (fun r : X3 ↦ v t (torusPoint r) j))
    (hdiv : ∀ t, ∀ᵐ x : T3, coordinateDivergence (fun j y ↦ v t y j) x = 0) :
    ∀ᵐ t : ℝ, Integrable (scalarMaterialRate f (v t) t) ∧
      HasDerivAt (fun s ↦ ∫ x : T3, f s x) (∫ x : T3, scalarMaterialRate f (v t) t x) t := by
  filter_upwards [ae_ae_materialRate_split f v hf hv hfL] with t ht
  obtain ⟨C, hC⟩ := exists_uniform_time_lipschitz f hfL (Icc (t - 1) (t + 1)) isCompact_Icc
  obtain ⟨hIp, hmean⟩ := hasDerivAt_mean_of_uniform_lipschitz f hf t _
    (Icc_mem_nhds (by linarith) (by linarith)) C hC (ht.mono (fun _ hx ↦ hx.1))
  have hft : Continuous (f t) := hf.comp (continuous_const.prodMk continuous_id)
  have hvc : ∀ j, Continuous (fun x : T3 ↦ v t x j) := fun j ↦
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 ↦ ℝ) j).continuous.comp (hv t)
  have hftL : LocallyLipschitz (fun r : X3 ↦ f t (torusPoint r)) :=
    hfL.comp (LipschitzWith.prodMk_left t).locallyLipschitz
  obtain ⟨hIt, hzero⟩ := integral_coordinateTransport_zero (f t) _ hft hvc hftL (hvL t) (hdiv t)
  have heq : scalarMaterialRate f (v t) t =ᵐ[volume]
      (fun x ↦ parameterRate f t x + coordinateTransport (f t) (fun j y ↦ v t y j) x) :=
    ht.mono (fun _ hx ↦ hx.2)
  have hIm : Integrable (scalarMaterialRate f (v t) t) := (hIp.add hIt).congr heq.symm
  have hei : (∫ x : T3, scalarMaterialRate f (v t) t x) = ∫ x : T3, parameterRate f t x := by
    rw [integral_congr_ae heq, integral_add hIp hIt, hzero, add_zero]
  rw [← hei] at hmean
  exact ⟨hIm, hmean⟩

theorem absolutelyContinuousOnInterval_mean
    (f : ℝ → T3 → ℝ) (hf : Continuous f.uncurry)
    (hfL : LocallyLipschitz (fun z : ST ↦ f z.1 (torusPoint z.2))) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t ↦ ∫ x : T3, f t x) a b := by
  obtain ⟨C, hC⟩ := exists_uniform_time_lipschitz f hfL (uIcc a b) isCompact_Icc
  exact (lipschitzOnWith_mean f hf _ C hC).absolutelyContinuousOnInterval

theorem intervalIntegral_materialRate_eq
    (f : ℝ → T3 → ℝ) (v : ℝ → T3 → R3)
    (hf : Continuous f.uncurry) (hv : ∀ t, Continuous (v t))
    (hfL : LocallyLipschitz (fun z : ST ↦ f z.1 (torusPoint z.2)))
    (hvL : ∀ t j, LocallyLipschitz (fun r : X3 ↦ v t (torusPoint r) j))
    (hdiv : ∀ t, ∀ᵐ x : T3, coordinateDivergence (fun j y ↦ v t y j) x = 0) (a b : ℝ) :
    IntervalIntegrable (fun t ↦ ∫ x : T3, scalarMaterialRate f (v t) t x) volume a b ∧
      (∫ t in a..b, ∫ x : T3, scalarMaterialRate f (v t) t x) =
        (∫ x : T3, f b x) - ∫ x : T3, f a x := by
  have hac := absolutelyContinuousOnInterval_mean f hf hfL a b
  have heq : (fun t ↦ ∫ x : T3, scalarMaterialRate f (v t) t x) =ᵐ[volume]
      deriv (fun t ↦ ∫ x : T3, f t x) :=
    (ae_hasDerivAt_mean_materialRate f v hf hv hfL hvL hdiv).mono (fun _ ht ↦ ht.2.deriv.symm)
  refine ⟨hac.intervalIntegrable_deriv.congr_ae (ae_restrict_of_ae heq.symm), ?_⟩
  rw [intervalIntegral.integral_congr_ae (heq.mono (fun _ ht _ ↦ ht))]
  exact hac.integral_deriv_eq_sub

end Mettapedia.FluidDynamics.NavierStokes.PancakeMeanMaterialBalance
