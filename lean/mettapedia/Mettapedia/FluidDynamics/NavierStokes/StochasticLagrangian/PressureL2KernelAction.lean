import Mettapedia.Analysis.BilinearTranslatedKernel
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureIntegrableKernelAction
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoherentChannelPeriodization

/-!
# The pressure-kernel integral with an L² input

The actual torus integral is defined almost everywhere for an L² input
and a continuous input. Its output is in L², with the squared kernel-mass
bound. Both slots and invariance under almost-everywhere input changes
are covered. The coherent channels retain their uniform ratio gain.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureL2KernelAction

open MeasureTheory PancakeBilinearPeriodization PressureKernelAction
open Mettapedia.Analysis.BilinearTranslatedKernel
open PressureCoherentDivergenceChannel (Factor)
open PressureCoherentChannelPeriodization
open PressureLowOutputCutoff (ratio)

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)
local notation "Op" => C3 →L[ℂ] C3 →L[ℂ] C3
local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem kernelAction_memLp_two_and_energy_le (K : T6 → Op) (hK : Integrable K)
    (f : T3 → C3) (g : C(T3, C3)) (hf : MemLp f 2) :
    (∀ᵐ x : T3, Integrable (fun q : T6 ↦ K q (f (x - firstTorusDisplacement q))
      (g (x - secondTorusDisplacement q)))) ∧
      MemLp (kernelAction K f g) 2 ∧
        (∫ x : T3, ‖kernelAction K f g x‖ ^ 2) ≤
          (∫ q : T6, ‖K q‖) ^ 2 * ‖g‖ ^ 2 * ∫ x : T3, ‖f x‖ ^ 2 :=
  action_memLp_two_and_energy_le K hK firstTorusDisplacement secondTorusDisplacement
    (by fun_prop) (by fun_prop) f g hf g.continuous.aestronglyMeasurable
    (norm_nonneg _) g.norm_coe_le_norm

theorem kernelAction_memLp_two_and_energy_le_right (K : T6 → Op) (hK : Integrable K)
    (f : C(T3, C3)) (g : T3 → C3) (hg : MemLp g 2) :
    (∀ᵐ x : T3, Integrable (fun q : T6 ↦ K q (f (x - firstTorusDisplacement q))
      (g (x - secondTorusDisplacement q)))) ∧
      MemLp (kernelAction K f g) 2 ∧
        (∫ x : T3, ‖kernelAction K f g x‖ ^ 2) ≤
          (∫ q : T6, ‖K q‖) ^ 2 * ‖f‖ ^ 2 * ∫ x : T3, ‖g x‖ ^ 2 :=
  action_memLp_two_and_energy_le_right K hK firstTorusDisplacement secondTorusDisplacement
    (by fun_prop) (by fun_prop) f g f.continuous.aestronglyMeasurable hg
    (norm_nonneg _) f.norm_coe_le_norm

theorem kernelAction_congr_ae (K L : T6 → Op) (hKL : K =ᵐ[volume] L)
    (f f' g g' : T3 → C3) (hf : f =ᵐ[volume] f') (hg : g =ᵐ[volume] g') :
    kernelAction K f g =ᵐ[volume] kernelAction L f' g' :=
  action_congr_ae K L hKL firstTorusDisplacement secondTorusDisplacement
    (by fun_prop) (by fun_prop) f f' g g' hf hg

theorem exists_uniform_coherent_energy_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2),
      ∀ e : R3, ‖e‖ = 1 → ∀ c : Factor, ∀ f : T3 → C3, ∀ g : C(T3, C3), MemLp f 2 →
        (∫ x : T3, ‖kernelAction (periodicKernel N hN t e c) f g x‖ ^ 2) ≤
          C * ratio t ^ 2 * ‖g‖ ^ 2 * ∫ x : T3, ‖f x‖ ^ 2 := by
  obtain ⟨C, hC, M, hb⟩ := exists_uniform_periodic_envelope
  refine ⟨C ^ 2, sq_nonneg _, fun N hN t ht e he c f g hf ↦ ?_⟩
  obtain ⟨_, _, hMi, _, hdom, hmass, _⟩ := hb N hN t ht
  have hK := integrable_periodicKernel N hN t e c
  have hm : (∫ q : T6, ‖periodicKernel N hN t e c q‖) ≤ ratio t * C := by
    apply (integral_mono_ae hK.norm hMi ?_).trans hmass
    filter_upwards [hdom] with q hq
    exact hq e he c
  have h := (kernelAction_memLp_two_and_energy_le _ hK f g hf).2.2
  apply h.trans
  have hs := pow_le_pow_left₀ (integral_nonneg (fun q ↦ norm_nonneg _)) hm 2
  calc
    _ ≤ (ratio t * C) ^ 2 * ‖g‖ ^ 2 * ∫ x : T3, ‖f x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs (sq_nonneg _))
        (integral_nonneg (fun _ ↦ sq_nonneg _))
    _ = _ := by ring

end Mettapedia.FluidDynamics.NavierStokes.PressureL2KernelAction
