import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalMaterialStretchingFlux

/-!
# Signed pressure-resolved flux balance on constructed material paths

The actual inviscid flux has a continuous material rate on compact
subintervals of the local solution. Its vector and quadratic balances
therefore retain the signed pressure and viscous terms under time
integration. Physical data construct both the solution and paths.

This is not the projected Eulerian Gram balance: transporting the
spatial gradient projection still has a commutator to account for.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalMaterialFluxBalance

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeLocalInfiniteVelocity
open PancakeLocalMaterialTrajectories PancakeFourierMaterialPaths PancakeCurlOutputTail
open PancakeHigherDerivativeMoments LocalMaterialVorticity LocalMaterialStrain LocalVorticityDiffusion
open LocalMaterialStretching LocalMaterialStretchingFlux
open PancakeHigherLocalVelocity PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks
open LongitudinalGradientFlux

local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B) (hB : 0 ≤ B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
  (X : ℝ → X3)
  (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
  {a b : ℝ} (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)

include hB hg hSum hu hX hI

theorem continuousOn_rateAlong (j : Fin 3) :
    ContinuousOn (fun t ↦ rateAlong s X t j) (Set.Icc a b) := by
  have hw := (contDiffOn_vorticityAlong s g hg hSum hu X hX).continuousOn.mono hI
  have hS := (contDiffOn_strainAlong s g hg hSum hu hB X hX).continuousOn.mono hI
  have hR := (continuousOn_strainRemainderAlong s g hg hSum hu hB X hX).mono hI
  have hf := continuousOn_diffusionAlong s g hSum hu X hX hI
  have ha : ContinuousOn (stretchingAlong s X) (Set.Icc a b) := hS.clm_apply hw
  have hsource := (hR.clm_apply hw).add (hS.clm_apply hf)
  have hc := ((((EuclideanSpace.proj j).continuous.comp_continuousOn (ha.add hf)).smul ha).add
    (((EuclideanSpace.proj j).continuous.comp_continuousOn hw).smul hsource)).neg
  apply hc.congr
  intro t ht
  change rateAlong s X t j = -((stretchingAlong s X t j + diffusionAlong s X t j) •
    stretchingAlong s X t + vorticityAlong s X t j •
      (strainRemainderAlong s X t (vorticityAlong s X t) + strainAlong s X t (diffusionAlong s X t)))
  rw [strainRemainderAlong_apply_vorticity s X t
    (summable_fourierMoment_of_le _ (by omega : 1 ≤ 3)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t (Set.Ioo_subset_Icc_self (hI ht)))))]
  simp only [rateAlong, pressureRateAlong, viscousRateAlong, stretchingDiffusionAlong,
    add_smul, smul_add, smul_neg]
  abel

omit hB in
theorem continuousOn_fluxAlong (j : Fin 3) :
    ContinuousOn (fun t ↦ fluxAlong s X t j) (Set.Icc a b) :=
  fun t ht ↦ (hasDerivAt_fluxAlong s g hg hSum hu X hX t (hI ht) j).continuousAt.continuousWithinAt

theorem intervalIntegrable_rateAlong (hab : a ≤ b) (j : Fin 3) :
    IntervalIntegrable (fun t ↦ rateAlong s X t j) volume a b :=
  ContinuousOn.intervalIntegrable_of_Icc hab (continuousOn_rateAlong s hB g hg hSum hu X hX hI j)

theorem fluxAlong_eq_initial_add_integral (hab : a ≤ b) (j : Fin 3) :
    fluxAlong s X b j = fluxAlong s X a j + ∫ t in a..b, rateAlong s X t j := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hasDerivAt_fluxAlong s g hg hSum hu X hX t
      (hI (Set.uIcc_of_le hab ▸ ht)) j)
    (intervalIntegrable_rateAlong s hB g hg hSum hu X hX hI hab j)
  rw [h]
  abel

theorem intervalIntegrable_signed_work (hab : a ≤ b) :
    IntervalIntegrable (fun t ↦ ∑ j : Fin 3, ⟪fluxAlong s X t j, rateAlong s X t j⟫) volume a b :=
  ContinuousOn.intervalIntegrable_of_Icc hab (continuousOn_finsetSum _ (fun j _ ↦
    (continuousOn_fluxAlong s g hg hSum hu X hX hI j).inner
      (continuousOn_rateAlong s hB g hg hSum hu X hX hI j)))

theorem energy_identity (hab : a ≤ b) :
    (∑ j : Fin 3, ‖fluxAlong s X b j‖ ^ 2) =
      (∑ j : Fin 3, ‖fluxAlong s X a j‖ ^ 2) +
        2 * ∫ t in a..b, ∑ j : Fin 3, ⟪fluxAlong s X t j, rateAlong s X t j⟫ := by
  have hi := (intervalIntegrable_signed_work s hB g hg hSum hu X hX hI hab).const_mul 2
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hasDerivAt_fluxAlong_energy s g hg hSum hu X hX t (hI (Set.uIcc_of_le hab ▸ ht))) hi
  rw [intervalIntegral.integral_const_mul] at h
  linarith

omit hB hg hSum hu hX hI in
/-- Neither the local solution nor its material trajectory is assumed as input. -/
theorem exists_physical_local_material_flux_balance (ν : ℝ) (hν : 0 < ν)
    (f : UnitAddTorus (Fin 3) → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 9 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution ν (torusFourierVelocity f) T B,
        ∀ x : X3, ∃ X : ℝ → X3, X 0 = x ∧ ContinuousOn X (Set.Icc (0 : ℝ) T) ∧
          (∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s t (X t)) t) ∧
          (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ j : Fin 3,
            HasDerivAt (fun τ ↦ fluxField 0 (s.coefficients τ) j (torusPoint (X τ)))
              (rateAlong s X t j) t) ∧
          (∀ a b : ℝ, a ≤ b → Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T →
            (∑ j : Fin 3, ‖fluxAlong s X b j‖ ^ 2) =
              (∑ j : Fin 3, ‖fluxAlong s X a j‖ ^ 2) +
                2 * ∫ t in a..b, ∑ j : Fin 3, ⟪fluxAlong s X t j, rateAlong s X t j⟫) := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    exists_physical_localMomentEnvelope 3 ν hν f hf hr hd hzero
  refine ⟨T, hT, B, hB, s, fun x ↦ ?_⟩
  have hu1 : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 1 (s.coefficients t) q ≤ g q :=
    fun t ht q ↦ (fourierMoment_mono _ (by omega : 1 ≤ 3) q).trans (hu t ht q)
  obtain ⟨X, hX0, hcX, hX⟩ := exists_materialTrajectory_interior s g hg hSum hu1 hT x
  exact ⟨X, hX0, hcX, hX, hasDerivAt_fluxField_material s g hg hSum hu X hX,
    fun a b hab hI ↦ energy_identity s hB g hg hSum hu X hX hI hab⟩

end Mettapedia.FluidDynamics.NavierStokes.LocalMaterialFluxBalance
