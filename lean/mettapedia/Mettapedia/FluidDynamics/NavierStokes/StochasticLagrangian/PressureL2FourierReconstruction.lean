import Mettapedia.Analysis.UnitTorusL2Projection
import Mettapedia.Analysis.UnitTorusFourierApproximation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureL2KernelAction
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureKernelFourier
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureKernelSwap

/-!
# Reconstructing weak-input pressure identities from Fourier coefficients

Finite polynomial actions require only integrability of the kernel.
Finite L² projections of the actual fields preserve the coefficient
identity before passage to the physical-space limit.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureL2FourierReconstruction

open MeasureTheory Filter PeriodicFourierTriad PancakeBilinearPeriodization
open scoped Topology
open PressureKernelAction (kernelAction)
open PressureIntegrableKernelAction PressureL2KernelAction
open PressureTwoInputReconstruction (vectorPolynomial)
open Mettapedia.Analysis.UnitTorusL2Projection (vectorProjection vectorProjection_eq_sum)

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

theorem kernelAction_vectorPolynomial (B : T6 → Op) (hB : Integrable B)
    (P Q : Finset Wavevector) (w v : Wavevector → C3) (x : T3) :
    kernelAction B (vectorPolynomial P w) (vectorPolynomial Q v) x =
      ∑ p ∈ P, ∑ k ∈ Q, (UnitAddTorus.mFourier p x * UnitAddTorus.mFourier k x) •
        (UnitAddTorus.mFourierCoeff B (pairWavevector p k)) (w p) (v k) := by
  have hint (p k : Wavevector) : Integrable (fun q : T6 ↦
      B q (UnitAddTorus.mFourier p (x - firstTorusDisplacement q) • w p)
        (UnitAddTorus.mFourier k (x - secondTorusDisplacement q) • v k)) :=
    integrable_action_integrand B _ _ x hB
      ((UnitAddTorus.mFourier p).continuous.smul continuous_const)
      ((UnitAddTorus.mFourier k).continuous.smul continuous_const)
  unfold kernelAction
  simp only [vectorPolynomial, map_sum, sum_apply]
  conv_lhs => arg 2; ext q; rw [Finset.sum_comm]
  rw [integral_finsetSum P]
  · apply Finset.sum_congr rfl
    intro p _
    rw [integral_finsetSum Q]
    · apply Finset.sum_congr rfl
      intro k _
      exact kernelAction_monomials B hB p k (w p) (v k) x
    · exact fun k _ ↦ hint p k
  · exact fun p _ ↦ integrable_finsetSum Q (fun k _ ↦ hint p k)

theorem smul_kernelAction_vectorProjection_eq
    (K L : T6 → Op) (hK : Integrable K) (hL : Integrable L)
    (f d : T3 → C3) (hf : MemLp f 2) (hd : MemLp d 2) (z : ℂ)
    (hc : ∀ k p : Wavevector, ∀ v : C3,
      z • (UnitAddTorus.mFourierCoeff K (pairWavevector k p)
        (UnitAddTorus.mFourierCoeff f k) v) =
      UnitAddTorus.mFourierCoeff L (pairWavevector k p) (UnitAddTorus.mFourierCoeff d k) v)
    (P Q : Finset Wavevector) (v : Wavevector → C3) (x : T3) :
    z • kernelAction K (vectorProjection f P) (vectorPolynomial Q v) x =
      kernelAction L (vectorProjection d P) (vectorPolynomial Q v) x := by
  have hfP : ⇑(vectorProjection f P) = vectorPolynomial P (UnitAddTorus.mFourierCoeff f) :=
    funext (vectorProjection_eq_sum f (hf.integrable (by norm_num)) P)
  have hdP : ⇑(vectorProjection d P) = vectorPolynomial P (UnitAddTorus.mFourierCoeff d) :=
    funext (vectorProjection_eq_sum d (hd.integrable (by norm_num)) P)
  rw [hfP, hdP, kernelAction_vectorPolynomial K hK, kernelAction_vectorPolynomial L hL]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro p _
  rw [smul_comm z, hc]

/-- First pass to the L² limit while holding a polynomial in the other slot. -/
theorem smul_toLpAction_polynomial_eq
    (K L : T6 → Op) (hK : Integrable K) (hL : Integrable L)
    (f d : T3 → C3) (hf : MemLp f 2) (hd : MemLp d 2) (z : ℂ)
    (hc : ∀ k p : Wavevector, ∀ v : C3,
      z • (UnitAddTorus.mFourierCoeff K (pairWavevector k p)
        (UnitAddTorus.mFourierCoeff f k) v) =
      UnitAddTorus.mFourierCoeff L (pairWavevector k p) (UnitAddTorus.mFourierCoeff d k) v)
    (Q : Finset Wavevector) (v : Wavevector → C3) :
    z • toLpAction K hK f hf (Mettapedia.Analysis.UnitTorusFourierApproximation.polynomial Q v) =
      toLpAction L hL d hd (Mettapedia.Analysis.UnitTorusFourierApproximation.polynomial Q v) := by
  let g := Mettapedia.Analysis.UnitTorusFourierApproximation.polynomial Q v
  have hg : ⇑g = vectorPolynomial Q v := by
    funext x
    exact Mettapedia.Analysis.UnitTorusFourierApproximation.polynomial_apply Q v x
  have hproj (a : T3 → C3) (P : Finset Wavevector) : MemLp (vectorProjection a P) 2 :=
    (vectorProjection a P).continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hconv (a : T3 → C3) (ha : MemLp a 2) (B : T6 → Op) (hB : Integrable B) :=
    tendsto_toLpAction_left B hB (fun P ↦ ⇑(vectorProjection a P)) a (hproj a) ha g
      (Mettapedia.Analysis.UnitTorusL2Projection.tendsto_integral_vectorProjection_error a ha)
  have he (P : Finset Wavevector) :
      z • toLpAction K hK (vectorProjection f P) (hproj f P) g =
        toLpAction L hL (vectorProjection d P) (hproj d P) g := by
    apply (smul_toLpAction_eq_iff _ _ _ _ _ _ _ _ _ _).mpr
    apply Eventually.of_forall
    intro x
    rw [hg]
    exact smul_kernelAction_vectorProjection_eq K L hK hL f d hf hd z hc P Q v x
  exact tendsto_nhds_unique (tendsto_const_nhds.smul (hconv f hf K hK))
    ((hconv d hd L hL).congr' (Eventually.of_forall (fun P ↦ (he P).symm)))

/-- A coefficient identity identifies the actual L² output almost everywhere. -/
theorem smul_kernelAction_eq_ae
    (K L : T6 → Op) (hK : Integrable K) (hL : Integrable L)
    (f d : T3 → C3) (hf : MemLp f 2) (hd : MemLp d 2) (g : C(T3, C3)) (z : ℂ)
    (hc : ∀ k p : Wavevector, ∀ v : C3,
      z • (UnitAddTorus.mFourierCoeff K (pairWavevector k p)
        (UnitAddTorus.mFourierCoeff f k) v) =
      UnitAddTorus.mFourierCoeff L (pairWavevector k p) (UnitAddTorus.mFourierCoeff d k) v) :
    (fun x ↦ z • kernelAction K f g x) =ᵐ[volume] kernelAction L d g := by
  apply (smul_toLpAction_eq_iff _ _ _ _ _ _ _ _ _ _).mp
  have hcont (B : T6 → Op) (hB : Integrable B) (a : T3 → C3) (ha : MemLp a 2) :
      Continuous (fun g : C(T3, C3) ↦ toLpAction B hB a ha g) :=
    continuous_iff_continuousAt.mpr (fun g ↦
      tendsto_toLpAction_right B hB a ha (fun g ↦ g) g tendsto_id)
  have hclosed : IsClosed {g : C(T3, C3) |
      z • toLpAction K hK f hf g = toLpAction L hL d hd g} :=
    isClosed_eq (continuous_const.smul (hcont K hK f hf)) (hcont L hL d hd)
  apply hclosed.closure_subset_iff.mpr ?_
    (Mettapedia.Analysis.UnitTorusFourierApproximation.dense_polynomial_range g)
  rintro _ ⟨⟨Q, v⟩, rfl⟩
  exact smul_toLpAction_polynomial_eq K L hK hL f d hf hd z hc Q v

/-- Second-slot reconstruction by a proved displacement-and-input change of variables. -/
theorem smul_kernelAction_eq_ae_right
    (K L : T6 → Op) (hK : Integrable K) (hL : Integrable L)
    (f : C(T3, C3)) (g d : T3 → C3) (hg : MemLp g 2) (hd : MemLp d 2) (z : ℂ)
    (hc : ∀ k p : Wavevector, ∀ v : C3,
      z • (UnitAddTorus.mFourierCoeff K (pairWavevector k p)
        v (UnitAddTorus.mFourierCoeff g p)) =
      UnitAddTorus.mFourierCoeff L (pairWavevector k p) v (UnitAddTorus.mFourierCoeff d p)) :
    (fun x ↦ z • kernelAction K f g x) =ᵐ[volume] kernelAction L f d := by
  have h := smul_kernelAction_eq_ae (PressureKernelSwap.swapKernel K) (PressureKernelSwap.swapKernel L)
    (PressureKernelSwap.integrable_swapKernel K hK) (PressureKernelSwap.integrable_swapKernel L hL)
    g d hg hd f z (fun k p v ↦ ?_)
  · filter_upwards [h] with x hx
    simpa only [PressureKernelSwap.kernelAction_swapKernel] using hx
  · rw [PressureKernelSwap.mFourierCoeff_swapKernel_apply K hK,
      PressureKernelSwap.mFourierCoeff_swapKernel_apply L hL]
    exact hc p k v

end Mettapedia.FluidDynamics.NavierStokes.PressureL2FourierReconstruction
