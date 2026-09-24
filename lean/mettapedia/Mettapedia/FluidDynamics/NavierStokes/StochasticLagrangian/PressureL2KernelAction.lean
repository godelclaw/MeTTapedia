import Mettapedia.Analysis.BilinearTranslatedKernel
import Mettapedia.Analysis.L2IntegralEnergy
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

open MeasureTheory Filter PancakeBilinearPeriodization PressureKernelAction
open scoped Topology
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

theorem kernelAction_sub_left_energy_le (K : T6 → Op) (hK : Integrable K)
    (f f' : T3 → C3) (g : C(T3, C3)) (hf : MemLp f 2) (hf' : MemLp f' 2) :
    (∫ x : T3, ‖kernelAction K f g x - kernelAction K f' g x‖ ^ 2) ≤
      (∫ q : T6, ‖K q‖) ^ 2 * ‖g‖ ^ 2 * ∫ x : T3, ‖f x - f' x‖ ^ 2 :=
  action_sub_left_energy_le K hK firstTorusDisplacement secondTorusDisplacement
    (by fun_prop) (by fun_prop) f f' g hf hf' g.continuous.aestronglyMeasurable
    (norm_nonneg _) g.norm_coe_le_norm

theorem kernelAction_sub_right_ae (K : T6 → Op) (hK : Integrable K)
    (f : T3 → C3) (g g' : C(T3, C3)) (hf : MemLp f 2) :
    kernelAction K f ⇑(g - g') =ᵐ[volume]
      fun x ↦ kernelAction K f g x - kernelAction K f g' x := by
  filter_upwards [(kernelAction_memLp_two_and_energy_le K hK f g hf).1,
    (kernelAction_memLp_two_and_energy_le K hK f g' hf).1] with x hx hx'
  simp only [kernelAction, ContinuousMap.sub_apply, map_sub]
  exact integral_sub hx hx'

theorem kernelAction_sub_right_energy_le (K : T6 → Op) (hK : Integrable K)
    (f : T3 → C3) (g g' : C(T3, C3)) (hf : MemLp f 2) :
    (∫ x : T3, ‖kernelAction K f g x - kernelAction K f g' x‖ ^ 2) ≤
      (∫ q : T6, ‖K q‖) ^ 2 * ‖g - g'‖ ^ 2 * ∫ x : T3, ‖f x‖ ^ 2 := by
  have h := (kernelAction_memLp_two_and_energy_le K hK f (g - g') hf).2.2
  convert h using 1
  apply integral_congr_ae
  filter_upwards [kernelAction_sub_right_ae K hK f g g' hf] with x hx
  rw [hx]

/-- The L² class of the actual pressure integral. -/
def toLpAction (K : T6 → Op) (hK : Integrable K)
    (f : T3 → C3) (hf : MemLp f 2) (g : C(T3, C3)) : Lp C3 2 (volume : Measure T3) :=
  (kernelAction_memLp_two_and_energy_le K hK f g hf).2.1.toLp (kernelAction K f g)

theorem coeFn_toLpAction (K : T6 → Op) (hK : Integrable K)
    (f : T3 → C3) (hf : MemLp f 2) (g : C(T3, C3)) :
    ⇑(toLpAction K hK f hf g) =ᵐ[volume] kernelAction K f g :=
  (kernelAction_memLp_two_and_energy_le K hK f g hf).2.1.coeFn_toLp

theorem smul_toLpAction_eq_iff (K L : T6 → Op) (hK : Integrable K) (hL : Integrable L)
    (f d : T3 → C3) (hf : MemLp f 2) (hd : MemLp d 2) (g : C(T3, C3)) (z : ℂ) :
    z • toLpAction K hK f hf g = toLpAction L hL d hd g ↔
      (fun x ↦ z • kernelAction K f g x) =ᵐ[volume] kernelAction L d g := by
  have ha : ⇑(z • toLpAction K hK f hf g) =ᵐ[volume]
      fun x ↦ z • kernelAction K f g x := by
    filter_upwards [Lp.coeFn_smul z (toLpAction K hK f hf g),
      coeFn_toLpAction K hK f hf g] with x hx hy
    simp only [hx, Pi.smul_apply, hy]
  have hb := coeFn_toLpAction L hL d hd g
  constructor
  · intro h
    rw [h] at ha
    exact ha.symm.trans hb
  · intro h
    exact Lp.ext (ha.trans (h.trans hb.symm))

theorem tendsto_toLpAction_left {ι : Type*} {l : Filter ι}
    (K : T6 → Op) (hK : Integrable K) (f : ι → T3 → C3) (f' : T3 → C3)
    (hf : ∀ i, MemLp (f i) 2) (hf' : MemLp f' 2) (g : C(T3, C3))
    (h : Tendsto (fun i ↦ ∫ x : T3, ‖f i x - f' x‖ ^ 2) l (𝓝 0)) :
    Tendsto (fun i ↦ toLpAction K hK (f i) (hf i) g) l (𝓝 (toLpAction K hK f' hf' g)) := by
  apply Mettapedia.Analysis.L2IntegralEnergy.tendsto_toLp_of_integral_sub_sq
  apply squeeze_zero (fun _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _))
    (fun i ↦ kernelAction_sub_left_energy_le K hK (f i) f' g (hf i) hf')
  simpa only [mul_zero] using h.const_mul ((∫ q : T6, ‖K q‖) ^ 2 * ‖g‖ ^ 2)

theorem tendsto_toLpAction_right {ι : Type*} {l : Filter ι}
    (K : T6 → Op) (hK : Integrable K) (f : T3 → C3) (hf : MemLp f 2)
    (g : ι → C(T3, C3)) (g' : C(T3, C3)) (h : Tendsto g l (𝓝 g')) :
    Tendsto (fun i ↦ toLpAction K hK f hf (g i)) l (𝓝 (toLpAction K hK f hf g')) := by
  apply Mettapedia.Analysis.L2IntegralEnergy.tendsto_toLp_of_integral_sub_sq
  apply squeeze_zero (fun _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _))
    (fun i ↦ kernelAction_sub_right_energy_le K hK f (g i) g' hf)
  have hn := (tendsto_iff_norm_sub_tendsto_zero.mp h).pow 2
  simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul] using
    (hn.const_mul ((∫ q : T6, ‖K q‖) ^ 2)).mul_const (∫ x : T3, ‖f x‖ ^ 2)

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
