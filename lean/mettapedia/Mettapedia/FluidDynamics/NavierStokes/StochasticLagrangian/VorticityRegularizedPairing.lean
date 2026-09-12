import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityRegularizedSource
import Mettapedia.Analysis.SignedCrossKernelIntegrable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # Signed exchange and source reconstruction for the actual annular kernels -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedPairing

open MeasureTheory Filter PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeBlockReality LocalLowDiffusionBudget
open VorticityRegularizedQuadratic VorticityRegularizedSource
open Mettapedia.Analysis SignedCrossKernel
open scoped RealInnerProductSpace Topology
local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "H" => PeriodicRieszOperator.kernel (d := 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Measure.IsNegInvariant (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsNegInvariant AddCircle.haarAddCircle)

theorem integrable_entryKernel_sub (i j : Fin 3) (N : ℕ) :
    Integrable (fun p : T3 × T3 ↦ PeriodicRieszOperator.entryKernel i j N (p.1 - p.2))
      ((volume : Measure T3).prod volume) := by
  have hi := (PeriodicRieszOperator.integrable_entryKernel i j N).comp_fst (volume : Measure T3)
  exact (measurePreserving_sub_prod (volume : Measure T3) volume).integrable_comp_of_integrable hi

theorem continuous_crossEntryWeight (i j l : Fin 3) : Continuous (fun a : R3 ↦ crossEntryWeight a i j l) := by
  unfold crossEntryWeight
  have hc : Continuous (fun a : R3 ↦ EuclideanCrossProduct.cross a (EuclideanSpace.single l 1)) :=
    SignedCrossKernel.continuous_cross.comp (continuous_id.prodMk continuous_const)
  exact ((EuclideanSpace.proj i).continuous.comp hc).mul (EuclideanSpace.proj j).continuous

theorem integrable_weightedStretch (n N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    Integrable (fun p : T3 × T3 ↦ weightedStretch n (H N (p.1 - p.2))
      (fullVorticity u p.1) (fullVorticity u p.2)) ((volume : Measure T3).prod volume) := by
  have hw := continuous_fullVorticity u hu
  have ht (i j l : Fin 3) : Integrable (fun p : T3 × T3 ↦
      PeriodicRieszOperator.entryKernel i j N (p.1 - p.2) *
        (‖fullVorticity u p.1‖ ^ n * crossEntryWeight (fullVorticity u p.1) i j l *
          fullVorticity u p.2 l)) ((volume : Measure T3).prod volume) := by
    let f : C(T3 × T3, ℝ) := ⟨fun p ↦ ‖fullVorticity u p.1‖ ^ n *
        crossEntryWeight (fullVorticity u p.1) i j l * fullVorticity u p.2 l,
      (((hw.comp continuous_fst).norm.pow n).mul
        ((continuous_crossEntryWeight i j l).comp (hw.comp continuous_fst))).mul
          ((EuclideanSpace.proj l).continuous.comp (hw.comp continuous_snd))⟩
    exact IntegrableKernelPairing.integrable_mul ((volume : Measure T3).prod volume) _
      (integrable_entryKernel_sub i j N) f
  have hi := integrable_finsetSum Finset.univ (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) ↦
    integrable_finsetSum Finset.univ (fun j _ ↦ integrable_finsetSum Finset.univ (fun l _ ↦ ht i j l)))
  apply hi.congr
  filter_upwards [] with p
  simp only [weightedStretch, inner_cross_kernel, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

def pairedSource (n N : ℕ) (u : FourierVelocity) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : T3, ∫ y : T3,
    pairedStretch n (H N (x - y)) (fullVorticity u x) (fullVorticity u y)

theorem source_eq_pairedSource (n N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) : source n N u = pairedSource n N u := by
  have h := integral_weightedStretch_eq_half_pair_of_integrable volume
    (fun x y : T3 ↦ H N (x - y)) (fullVorticity u) n
    (integrable_weightedStretch n N u hu) (PeriodicRieszOperator.kernel_sub_swap N)
  change _ = pairedSource n N u at h
  rw [← h]
  unfold source
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [weightedStretch, integral_const_mul]
  congr 1
  unfold quadraticStretch
  rw [← integral_sub_left_eq_self (fun h : T3 ↦
    ⟪EuclideanCrossProduct.cross (fullVorticity u x) (fullVorticity u (x - h)),
      H N h (fullVorticity u x)⟫) volume x]
  simp only [sub_sub_cancel]

theorem tendsto_pairedSource (n : ℕ) (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) :
    Tendsto (fun N : ℕ ↦ pairedSource n N u) atTop (𝓝 (VorticityWeightedStretching.fullStretching n u)) := by
  simpa only [← source_eq_pairedSource n _ u hu] using tendsto_source n u hu hr hd

end Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedPairing
