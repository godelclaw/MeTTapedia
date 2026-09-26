import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierUniqueness
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierSmallData
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPlanarRegularity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierOfficialTheorems

/-!
# Stability of the Fourier solutions: continuous dependence in energy

Two tame solutions of order at least seven stay close in energy on any interval
where their Wiener amplitudes have summable envelopes `g_c`, `g_d`. With
`w = c - d`, the argument of the uniqueness theorem gives, for every finite
output set,

```text
∑_{q∈F} |w_q(t)|² ≤ ‖w(0)‖² + κ ∫₀ᵗ ∑_q |w_q|²,   κ = 9 (‖g_c‖²_{ℓ¹} + ‖g_d‖²_{ℓ¹}) / ν,
```

and Grönwall's inequality closes it:

```text
‖w(t)‖² ≤ ‖w(0)‖² exp(κ t).
```

No smallness and no nonlinear cancellation is used; the dissipation absorbs
the whole convection difference.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierStability

open scoped BigOperators Topology ComplexConjugate
open MeasureTheory Set Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeSobolevWeights PancakeSobolevVelocityRate PancakeHigherSobolevWeights
open PancakeHigherSobolevVelocityRate PancakeCurlOutputTail PancakeLatticeDecayEnvelope
open PancakeHigherLocalVelocity PancakeGalerkinKineticEnergy PancakeLocalInfiniteVelocity
open PancakeHigherDerivativeMoments PancakeCoefficientLimitEquation PancakeSobolevFiberEnvelope
open PancakeSignedTransportEnergy PancakeLowPressureBudget PancakeHigherSobolevWindow
open PancakePeriodicVorticityEquation PancakeIncomingLowSourceEnergy PancakeBlockReality
open FourierTameTriad FourierContinuation FourierTameContinuation
open FourierVorticitySupContinuation FourierDyadicBlockContinuation FourierInfiniteTameRate
open FourierUniqueness

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

section Dependence

variable {nu : ℝ} {m : ℕ} {u₀ v₀ : FourierVelocity} {T : ℝ}

/-- **Continuous dependence in energy.** Two tame solutions of order at least
seven whose amplitudes are bounded by summable envelopes on `[0, S]` satisfy
`‖c(τ) - d(τ)‖² ≤ ‖u₀ - v₀‖² exp(κ τ)` there, with
`κ = 9 (‖g_c‖²_{ℓ¹} + ‖g_d‖²_{ℓ¹}) / ν`. -/
theorem velocityEnergy_diff_le (hm : 7 ≤ m) (hnu : 0 < nu)
    (c : TameSolutionOn nu m u₀ T) (d : TameSolutionOn nu m v₀ T) {S : ℝ} (hS0 : 0 < S)
    (hST : S < T) {gc gd : Wavevector → ℝ} (hgc : ∀ k, 0 ≤ gc k) (hgd : ∀ k, 0 ≤ gd k)
    (hSc : Summable gc) (hSd : Summable gd)
    (hac : ∀ τ ∈ Icc (0 : ℝ) S, ∀ k, amplitude (c.coefficients τ) k ≤ gc k)
    (had : ∀ τ ∈ Icc (0 : ℝ) S, ∀ k, amplitude (d.coefficients τ) k ≤ gd k)
    {D₀ : ℝ} (hD₀ : ∀ F, velocityEnergy 0 F (diff u₀ v₀) ≤ D₀) :
    ∀ τ ∈ Icc (0 : ℝ) S, ∀ F, velocityEnergy 0 F (diff (c.coefficients τ) (d.coefficients τ)) ≤
      D₀ * Real.exp (9 / nu * ((∑' k, gc k) ^ 2 + (∑' k, gd k) ^ 2) * τ) := by
  obtain ⟨Bc, sc, hsc, -, -, -, -⟩ := local_envelope_at hm c hST
  obtain ⟨Bd, sd, hsd, -, -, -, -⟩ := local_envelope_at hm d hST
  let w : ℝ → FourierVelocity := fun τ ↦ diff (c.coefficients τ) (d.coefficients τ)
  set Mc := ∑' k, gc k with hMc
  set Md := ∑' k, gd k with hMd
  have hMc0 : 0 ≤ Mc := tsum_nonneg hgc
  have hMd0 : 0 ≤ Md := tsum_nonneg hgd
  have hgcle : ∀ k, gc k ≤ Mc := fun k ↦ hSc.le_tsum k fun j _ ↦ hgc j
  have hgdle : ∀ k, gd k ≤ Md := fun k ↦ hSd.le_tsum k fun j _ ↦ hgd j
  -- the energy envelope of the difference
  let env : Wavevector → ℝ := fun k ↦ (Mc + Md) * (gc k + gd k)
  have henv : Summable env := (hSc.add hSd).mul_left _
  have hwk : ∀ τ ∈ Icc (0 : ℝ) S, ∀ k, coefficientEnergy (w τ k) ≤ env k := by
    intro τ hτ k
    rw [coefficientEnergy_diff_eq]
    have h1 := (amplitude_diff_le _ _ k).trans (add_le_add (hac τ hτ k) (had τ hτ k))
    have h0 : 0 ≤ amplitude (diff (c.coefficients τ) (d.coefficients τ)) k := norm_nonneg _
    calc amplitude (diff (c.coefficients τ) (d.coefficients τ)) k ^ 2
        ≤ (gc k + gd k) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ ≤ (Mc + Md) * (gc k + gd k) := by
          rw [sq]
          exact mul_le_mul_of_nonneg_right (add_le_add (hgcle k) (hgdle k))
            (add_nonneg (hgc k) (hgd k))
  have hE0 : ∀ τ k, 0 ≤ coefficientEnergy (w τ k) := fun τ k ↦ by
    rw [coefficientEnergy_diff_eq]
    positivity
  -- the full energy of the difference
  let Z : ℝ → ℝ := fun τ ↦ ∑' k, coefficientEnergy (w τ k)
  have hZs : ∀ τ ∈ Icc (0 : ℝ) S, Summable (fun k ↦ coefficientEnergy (w τ k)) :=
    fun τ hτ ↦ henv.of_nonneg_of_le (hE0 τ) (hwk τ hτ)
  have hZ0 : ∀ τ, 0 ≤ Z τ := fun τ ↦ tsum_nonneg (hE0 τ)
  have hZc : ContinuousOn Z (Icc 0 S) := by
    refine continuousOn_iff_continuous_domRestrict.mpr ?_
    refine continuous_tsum (f := fun k (τ : Icc (0 : ℝ) S) ↦ coefficientEnergy (w τ k))
      (fun k ↦ ?_) henv (fun k τ ↦ ?_)
    · have hc (i : Fin 3) : Continuous (fun τ : Icc (0 : ℝ) S ↦ w τ k i) :=
        ((c.continuous k i).sub (d.continuous k i)).comp continuous_subtype_val
      show Continuous fun τ : Icc (0 : ℝ) S ↦ ∑ i : Fin 3, Complex.normSq (w τ k i)
      exact continuous_finsetSum _ fun i _ ↦ Complex.continuous_normSq.comp (hc i)
    · rw [Real.norm_eq_abs, abs_of_nonneg (hE0 _ _)]
      exact hwk τ τ.2 k
  have hsumle : ∀ τ ∈ Icc (0 : ℝ) S, ∀ H : Finset Wavevector,
      ∑ j ∈ H, amplitude (w τ) j ^ 2 ≤ Z τ := by
    intro τ hτ H
    calc ∑ j ∈ H, amplitude (w τ) j ^ 2 = ∑ j ∈ H, coefficientEnergy (w τ j) :=
          Finset.sum_congr rfl fun j _ ↦ (coefficientEnergy_diff_eq _ _ j).symm
      _ ≤ Z τ := (hZs τ hτ).sum_le_tsum H fun j _ ↦ hE0 τ j
  -- the rate bound at interior times
  set κ := 9 / nu * (Mc ^ 2 + Md ^ 2) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hrate : ∀ τ ∈ Ioo (0 : ℝ) S, ∀ F : Finset Wavevector,
      orderVelocityRate 0 F (w τ)
        (fun q ↦ infiniteVelocityRHS nu (c.coefficients τ) q -
          infiniteVelocityRHS nu (d.coefficients τ) q) ≤ κ * Z τ := by
    intro τ hτ F
    have hτS : τ ∈ Icc (0 : ℝ) S := Ioo_subset_Icc_self hτ
    set cτ := c.coefficients τ
    set dτ := d.coefficients τ
    have hcs : ∀ q i, Summable (fun k ↦ outputFiber q cτ k i) := by
      intro q i
      have h := sc.summable_convection τ hτS q i
      rwa [hsc] at h
    have hds : ∀ q i, Summable (fun k ↦ outputFiber q dτ k i) := by
      intro q i
      have h := sd.summable_convection τ hτS q i
      rwa [hsd] at h
    let Y1 : Wavevector → ℝ := fun q ↦ ∑' k, amplitude cτ k * amplitude (w τ) (q - k)
    let Y2 : Wavevector → ℝ := fun q ↦ ∑' k, amplitude dτ k * amplitude (w τ) (q - k)
    have hwb : ∀ j, amplitude (w τ) j ≤ Real.sqrt (Z τ) := fun j ↦ by
      have h := hsumle τ hτS {j}
      rw [Finset.sum_singleton] at h
      exact Real.le_sqrt_of_sq_le h
    have hcl1 : Summable (fun k ↦ amplitude cτ k) :=
      hSc.of_nonneg_of_le (fun k ↦ norm_nonneg _) (hac τ hτS)
    have hdl1 : Summable (fun k ↦ amplitude dτ k) :=
      hSd.of_nonneg_of_le (fun k ↦ norm_nonneg _) (had τ hτS)
    have hs1 : ∀ q, Summable (fun k ↦ amplitude cτ k * amplitude (w τ) (q - k)) := fun q ↦
      (hcl1.mul_right (Real.sqrt (Z τ))).of_nonneg_of_le
        (fun k ↦ mul_nonneg (amplitude_nonneg _ _) (amplitude_nonneg _ _))
        (fun k ↦ mul_le_mul_of_nonneg_left (hwb _) (norm_nonneg _))
    have hs2 : ∀ q, Summable (fun k ↦ amplitude dτ k * amplitude (w τ) (q - k)) := fun q ↦
      (hdl1.mul_right (Real.sqrt (Z τ))).of_nonneg_of_le
        (fun k ↦ mul_nonneg (amplitude_nonneg _ _) (amplitude_nonneg _ _))
        (fun k ↦ mul_le_mul_of_nonneg_left (hwb _) (norm_nonneg _))
    -- the component bound for the convection difference
    have hX : ∀ q i, ‖infiniteConvection cτ q i - infiniteConvection dτ q i‖ ≤
        ‖frequencyVec q‖ * (Y1 q + Y2 q) := by
      intro q i
      have hfs : Summable (fun k ↦ ‖frequencyVec q‖ * (amplitude (w τ) k * amplitude cτ (q - k) +
          amplitude dτ k * amplitude (w τ) (q - k))) := by
        refine Summable.mul_left _ (Summable.add ?_ (hs2 q))
        have h := (Equiv.subLeft q).summable_iff.mpr (hs1 q)
        refine h.congr fun k ↦ ?_
        simp only [Function.comp_apply, Equiv.subLeft_apply, sub_sub_cancel]
        ring
      have hdiff : infiniteConvection cτ q i - infiniteConvection dτ q i =
          ∑' k, (outputFiber q cτ k i - outputFiber q dτ k i) := by
        simp only [infiniteConvection]
        exact ((hcs q i).tsum_sub (hds q i)).symm
      rw [hdiff]
      refine (norm_tsum_le_tsum_norm ?_).trans ?_
      · exact hfs.of_nonneg_of_le (fun k ↦ norm_nonneg _)
          (fun k ↦ norm_outputFiber_sub_le q cτ dτ k i)
      · refine (hfs.of_nonneg_of_le (fun k ↦ norm_nonneg _)
            (fun k ↦ norm_outputFiber_sub_le q cτ dτ k i)).tsum_le_tsum
            (fun k ↦ norm_outputFiber_sub_le q cτ dτ k i) hfs |>.trans ?_
        rw [tsum_mul_left]
        refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (norm_nonneg _)
        have hr : (∑' k, amplitude (w τ) k * amplitude cτ (q - k)) = Y1 q := by
          rw [← (Equiv.subLeft q).tsum_eq]
          refine tsum_congr fun k ↦ ?_
          simp only [Equiv.subLeft_apply, sub_sub_cancel]
          ring
        have hsA : Summable (fun k ↦ amplitude (w τ) k * amplitude cτ (q - k)) := by
          have h := (Equiv.subLeft q).summable_iff.mpr (hs1 q)
          refine h.congr fun k ↦ ?_
          simp only [Function.comp_apply, Equiv.subLeft_apply, sub_sub_cancel]
          ring
        rw [Summable.tsum_add hsA (hs2 q), hr]
    -- sum over the output set
    have hmode : ∀ q ∈ F, 2 * (coefficientHermitian (w τ q)
        (infiniteVelocityRHS nu cτ q - infiniteVelocityRHS nu dτ q)).re ≤
          9 / (2 * nu) * (Y1 q + Y2 q) ^ 2 := by
      intro q _
      have h1 : modeDot q (cτ q) = 0 := c.transverse τ q
      have h2 : modeDot q (dτ q) = 0 := d.transverse τ q
      have hw : modeDot q (diff cτ dτ q) = 0 := by
        simp only [FourierUniqueness.diff, FourierUniqueness.modeDot_sub, h1, h2, sub_zero]
      exact two_re_hermitian_rhs_sub_le nu hnu cτ dτ q hw (hX q)
    have hyoung1 := sum_sq_tsum_conv_le F (amplitude (w τ)) (amplitude cτ)
      (fun k ↦ norm_nonneg _) (fun k ↦ norm_nonneg _) hcl1 (hsumle τ hτS)
    have hyoung2 := sum_sq_tsum_conv_le F (amplitude (w τ)) (amplitude dτ)
      (fun k ↦ norm_nonneg _) (fun k ↦ norm_nonneg _) hdl1 (hsumle τ hτS)
    have hMc' : (∑' k, amplitude cτ k) ≤ Mc :=
      hcl1.tsum_le_tsum (hac τ hτS) hSc
    have hMd' : (∑' k, amplitude dτ k) ≤ Md :=
      hdl1.tsum_le_tsum (had τ hτS) hSd
    have hc0 : 0 ≤ ∑' k, amplitude cτ k := tsum_nonneg fun k ↦ norm_nonneg _
    have hd0 : 0 ≤ ∑' k, amplitude dτ k := tsum_nonneg fun k ↦ norm_nonneg _
    have hZτ := hZ0 τ
    have hsq : ∑ q ∈ F, (Y1 q + Y2 q) ^ 2 ≤ 2 * (Mc ^ 2 + Md ^ 2) * Z τ := by
      calc ∑ q ∈ F, (Y1 q + Y2 q) ^ 2 ≤ ∑ q ∈ F, (2 * Y1 q ^ 2 + 2 * Y2 q ^ 2) :=
            Finset.sum_le_sum fun q _ ↦ by nlinarith [sq_nonneg (Y1 q - Y2 q)]
        _ = 2 * ∑ q ∈ F, Y1 q ^ 2 + 2 * ∑ q ∈ F, Y2 q ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ ≤ 2 * ((∑' k, amplitude cτ k) ^ 2 * Z τ) + 2 * ((∑' k, amplitude dτ k) ^ 2 * Z τ) := by
            gcongr
        _ ≤ 2 * (Mc ^ 2 * Z τ) + 2 * (Md ^ 2 * Z τ) := by
            gcongr
        _ = 2 * (Mc ^ 2 + Md ^ 2) * Z τ := by ring
    have hrw : orderVelocityRate 0 F (w τ)
        (fun q ↦ infiniteVelocityRHS nu cτ q - infiniteVelocityRHS nu dτ q) =
          ∑ q ∈ F, 2 * (coefficientHermitian (w τ q)
            (infiniteVelocityRHS nu cτ q - infiniteVelocityRHS nu dτ q)).re := by
      simp only [orderVelocityRate, orderWeight, pow_zero, one_pow, one_mul, Finset.mul_sum]
    rw [hrw]
    calc ∑ q ∈ F, 2 * (coefficientHermitian (w τ q)
          (infiniteVelocityRHS nu cτ q - infiniteVelocityRHS nu dτ q)).re
        ≤ ∑ q ∈ F, 9 / (2 * nu) * (Y1 q + Y2 q) ^ 2 := Finset.sum_le_sum hmode
      _ = 9 / (2 * nu) * ∑ q ∈ F, (Y1 q + Y2 q) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 9 / (2 * nu) * (2 * (Mc ^ 2 + Md ^ 2) * Z τ) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = κ * Z τ := by
          rw [hκ]
          field_simp
  -- the truncated energies stay below the data plus the integral
  have htrunc : ∀ F : Finset Wavevector, ∀ τ ∈ Icc (0 : ℝ) S,
      velocityEnergy 0 F (w τ) ≤ D₀ + κ * ∫ r in (0 : ℝ)..τ, Z r := by
    intro F
    let φ : ℝ → ℝ := fun τ ↦ velocityEnergy 0 F (w τ) - κ * ∫ r in (0 : ℝ)..τ, Z r
    have hint : IntegrableOn Z (uIcc 0 S) := by
      rw [uIcc_of_le hS0.le]
      exact hZc.integrableOn_Icc
    have hprim : ContinuousOn (fun τ ↦ ∫ r in (0 : ℝ)..τ, Z r) (Icc 0 S) := by
      have h := intervalIntegral.continuousOn_primitive_interval hint
      rwa [uIcc_of_le hS0.le] at h
    have hwc : ∀ q i, Continuous (fun τ ↦ w τ q i) := fun q i ↦
      (c.continuous q i).sub (d.continuous q i)
    have hφc : ContinuousOn φ (Icc 0 S) :=
      (continuous_velocityEnergy_along 0 F hwc).continuousOn.sub (hprim.const_smul κ)
    have hder : ∀ τ ∈ Ioo (0 : ℝ) S, HasDerivAt φ
        (orderVelocityRate 0 F (w τ)
          (fun q ↦ infiniteVelocityRHS nu (c.coefficients τ) q -
            infiniteVelocityRHS nu (d.coefficients τ) q) - κ * Z τ) τ := by
      intro τ hτ
      have hτT : τ ∈ Ioo (0 : ℝ) T := ⟨hτ.1, hτ.2.trans hST⟩
      have hE := hasDerivAt_velocityEnergy 0 F w
        (fun q ↦ infiniteVelocityRHS nu (c.coefficients τ) q -
          infiniteVelocityRHS nu (d.coefficients τ) q) τ
        (fun q _ i ↦ (c.equation τ hτT q i).sub (d.equation τ hτT q i))
      have hsub : Icc (0 : ℝ) τ ⊆ Icc 0 S := Icc_subset_Icc le_rfl hτ.2.le
      have hi : IntervalIntegrable Z volume 0 τ :=
        (hZc.mono hsub).intervalIntegrable_of_Icc hτ.1.le
      have hms : StronglyMeasurableAtFilter Z (𝓝 τ) :=
        (hZc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo τ hτ
      have hcz : ContinuousAt Z τ := hZc.continuousAt (Icc_mem_nhds hτ.1 hτ.2)
      exact hE.sub ((intervalIntegral.integral_hasDerivAt_right hi hms hcz).const_mul κ)
    have hanti : AntitoneOn φ (Icc 0 S) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 S) hφc
      · intro τ hτ
        rw [interior_Icc] at hτ
        exact (hder τ hτ).differentiableAt.differentiableWithinAt
      · intro τ hτ
        rw [interior_Icc] at hτ
        rw [(hder τ hτ).deriv]
        linarith [hrate τ hτ F]
    intro τ hτ
    have h := hanti ⟨le_rfl, hS0.le⟩ hτ hτ.1
    have h0 : φ 0 ≤ D₀ := by
      have hw0 : w 0 = diff u₀ v₀ := by
        funext k
        simp only [w, FourierUniqueness.diff, c.initial, d.initial]
      simp only [φ, hw0, intervalIntegral.integral_same, mul_zero, sub_zero]
      exact hD₀ F
    change velocityEnergy 0 F (w τ) - κ * ∫ r in (0 : ℝ)..τ, Z r ≤ φ 0 at h
    linarith
  -- the full energy obeys the same bound, and Grönwall closes it
  have hZle : ∀ τ ∈ Icc (0 : ℝ) S, Z τ ≤ D₀ + κ * ∫ r in (0 : ℝ)..τ, 1 * Z r := by
    intro τ hτ
    simp only [one_mul]
    have hD₀0 : 0 ≤ D₀ := le_trans (by simp [velocityEnergy_eq]) (hD₀ ∅)
    have hint0 : 0 ≤ κ * ∫ r in (0 : ℝ)..τ, Z r :=
      mul_nonneg hκ0 (intervalIntegral.integral_nonneg hτ.1 fun r _ ↦ hZ0 r)
    refine Real.tsum_le_of_sum_le (hE0 τ) fun H ↦ ?_
    have h := htrunc H τ hτ
    simpa only [velocityEnergy_eq, orderWeight, pow_zero, one_pow, one_mul] using h
  intro τ hτ F
  have hG := le_mul_exp_of_le_add_integral hτ.1 hκ0 (hZc.mono (Icc_subset_Icc le_rfl hτ.2))
    continuousOn_const (fun _ _ ↦ zero_le_one)
    (fun r hr ↦ hZle r (Icc_subset_Icc le_rfl hτ.2 hr))
  have hint1 : (∫ r in (0 : ℝ)..τ, (1 : ℝ)) = τ := by simp
  rw [hint1] at hG
  have hle : velocityEnergy 0 F (w τ) ≤ Z τ := by
    have he : velocityEnergy 0 F (w τ) = ∑ j ∈ F, coefficientEnergy (w τ j) := by
      simp only [velocityEnergy_eq, orderWeight, pow_zero, one_pow, one_mul]
    rw [he]
    exact (hZs τ hτ).sum_le_tsum F fun j _ ↦ hE0 τ j
  calc velocityEnergy 0 F (diff (c.coefficients τ) (d.coefficients τ)) = velocityEnergy 0 F (w τ) := rfl
    _ ≤ Z τ := hle
    _ ≤ D₀ * Real.exp (κ * τ) := hG
    _ = D₀ * Real.exp (9 / nu * (Mc ^ 2 + Md ^ 2) * τ) := by rw [hκ]

end Dependence

section Energies

theorem velocityEnergy_eq_weightedMass (m : ℕ) (F : Finset Wavevector) (u : FourierVelocity) :
    velocityEnergy m F u = weightedMass F (amplitude u) (2 * m) :=
  orderEnergy_eq_weightedMass m F (amplitude u)

theorem velocityEnergy_nonneg' (m : ℕ) (F : Finset Wavevector) (u : FourierVelocity) :
    0 ≤ velocityEnergy m F u := orderEnergy_nonneg m F _

/-- **The order-five energy between orders one and eleven.** -/
theorem velocityEnergy_five_le (F : Finset Wavevector) (u : FourierVelocity) :
    velocityEnergy 5 F u ≤
      velocityEnergy 1 F u ^ ((3 : ℝ) / 5) * velocityEnergy 11 F u ^ ((2 : ℝ) / 5) := by
  have h := weightedMass_interp 10 (by norm_num) F (amplitude u) (r := 10) (by norm_num)
    (by norm_num)
  rw [velocityEnergy_eq_weightedMass, velocityEnergy_eq_weightedMass,
    velocityEnergy_eq_weightedMass]
  have e1 : ((2 * (5 : ℕ) : ℕ) : ℝ) = 10 := by norm_num
  have e2 : (1 : ℝ) - (10 - 2) / (2 * ((10 : ℕ) : ℝ)) = 3 / 5 := by norm_num
  have e3 : (10 - 2) / (2 * ((10 : ℕ) : ℝ)) = 2 / 5 := by norm_num
  have e4 : 2 * ((10 : ℕ) : ℝ) + 2 = 2 * ((11 : ℕ) : ℝ) := by norm_num
  have e5 : (2 : ℝ) = 2 * ((1 : ℕ) : ℝ) := by norm_num
  rw [e2, e3, e4] at h
  rw [← e5]
  convert h using 2
  norm_num

/-- **Cauchy–Schwarz between orders.** If `2a = b + c`, then
`E_a² ≤ E_b E_c` on every finite set. -/
theorem velocityEnergy_sq_le_mul (a b c : ℕ) (h : 2 * a = b + c) (F : Finset Wavevector)
    (u : FourierVelocity) :
    velocityEnergy a F u ^ 2 ≤ velocityEnergy b F u * velocityEnergy c F u := by
  simp only [velocityEnergy_eq]
  have he : ∀ k, 0 ≤ coefficientEnergy (u k) := fun k ↦ by
    rw [← norm_coefficientVec_sq]
    positivity
  have hs := Finset.sum_mul_sq_le_sq_mul_sq F
    (fun k ↦ orderWeight b k * Real.sqrt (coefficientEnergy (u k)))
    (fun k ↦ orderWeight c k * Real.sqrt (coefficientEnergy (u k)))
  have hw : ∀ k, orderWeight a k ^ 2 = orderWeight b k * orderWeight c k := fun k ↦ by
    simp only [orderWeight]
    rw [← pow_mul, ← pow_add, mul_comm a 2, h]
  have e1 : ∀ k ∈ F, orderWeight b k * Real.sqrt (coefficientEnergy (u k)) *
      (orderWeight c k * Real.sqrt (coefficientEnergy (u k))) =
        orderWeight a k ^ 2 * coefficientEnergy (u k) := fun k _ ↦ by
    rw [hw k, mul_mul_mul_comm, Real.mul_self_sqrt (he k)]
  have e2 : ∀ (d : ℕ), ∀ k ∈ F, (orderWeight d k * Real.sqrt (coefficientEnergy (u k))) ^ 2 =
      orderWeight d k ^ 2 * coefficientEnergy (u k) := fun d k _ ↦ by
    rw [mul_pow, Real.sq_sqrt (he k)]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl (e2 b), Finset.sum_congr rfl (e2 c)] at hs
  exact hs

/-- **Cauchy–Schwarz between orders zero, one and two.** -/
theorem velocityEnergy_one_sq_le (F : Finset Wavevector) (u : FourierVelocity) :
    velocityEnergy 1 F u ^ 2 ≤ velocityEnergy 0 F u * velocityEnergy 2 F u := by
  simp only [velocityEnergy_eq]
  have he : ∀ k, 0 ≤ coefficientEnergy (u k) := fun k ↦ by
    rw [← norm_coefficientVec_sq]
    positivity
  have h := Finset.sum_mul_sq_le_sq_mul_sq F (fun k ↦ Real.sqrt (coefficientEnergy (u k)))
    (fun k ↦ orderWeight 1 k ^ 2 * Real.sqrt (coefficientEnergy (u k)))
  have e1 : ∀ k ∈ F, Real.sqrt (coefficientEnergy (u k)) *
      (orderWeight 1 k ^ 2 * Real.sqrt (coefficientEnergy (u k))) =
        orderWeight 1 k ^ 2 * coefficientEnergy (u k) := fun k _ ↦ by
    rw [mul_left_comm, Real.mul_self_sqrt (he k)]
  have e2 : ∀ k ∈ F, Real.sqrt (coefficientEnergy (u k)) ^ 2 =
      orderWeight 0 k ^ 2 * coefficientEnergy (u k) := fun k _ ↦ by
    rw [Real.sq_sqrt (he k)]
    simp [orderWeight]
  have e3 : ∀ k ∈ F, (orderWeight 1 k ^ 2 * Real.sqrt (coefficientEnergy (u k))) ^ 2 =
      orderWeight 2 k ^ 2 * coefficientEnergy (u k) := fun k _ ↦ by
    rw [mul_pow, Real.sq_sqrt (he k)]
    simp only [orderWeight]
    ring
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3] at h
  exact h

theorem coefficientEnergy_sub_le (a b : VelocityCoefficient) :
    coefficientEnergy (a - b) ≤ 2 * coefficientEnergy a + 2 * coefficientEnergy b := by
  rw [← norm_coefficientVec_sq, ← norm_coefficientVec_sq, ← norm_coefficientVec_sq]
  have hs : coefficientVec (a - b) = coefficientVec a - coefficientVec b := by
    simp [coefficientVec]
  rw [hs]
  have h := norm_sub_le (coefficientVec a) (coefficientVec b)
  nlinarith [norm_nonneg (coefficientVec a - coefficientVec b), norm_nonneg (coefficientVec a),
    norm_nonneg (coefficientVec b), sq_nonneg (‖coefficientVec a‖ - ‖coefficientVec b‖)]

/-- The energy of a difference is at most twice the sum of the energies. -/
theorem velocityEnergy_diff_le_two (m : ℕ) (F : Finset Wavevector) (c d : FourierVelocity) :
    velocityEnergy m F (FourierUniqueness.diff c d) ≤
      2 * velocityEnergy m F c + 2 * velocityEnergy m F d := by
  simp only [velocityEnergy_eq, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ ↦ ?_
  have h := coefficientEnergy_sub_le (c k) (d k)
  have hw : 0 ≤ orderWeight m k ^ 2 := sq_nonneg _
  simp only [FourierUniqueness.diff]
  nlinarith [mul_le_mul_of_nonneg_left h hw]

/-- A field's energy is at most twice that of a second field plus twice that of
their difference. -/
theorem velocityEnergy_le_two_diff (m : ℕ) (F : Finset Wavevector) (c d : FourierVelocity) :
    velocityEnergy m F c ≤
      2 * velocityEnergy m F d + 2 * velocityEnergy m F (FourierUniqueness.diff c d) := by
  have h := velocityEnergy_diff_le_two m F d (fun k ↦ d k - c k)
  have e1 : FourierUniqueness.diff d (fun k ↦ d k - c k) = c := by
    funext k
    simp [FourierUniqueness.diff]
  have e2 : velocityEnergy m F (fun k ↦ d k - c k) = velocityEnergy m F (FourierUniqueness.diff c d) := by
    simp only [velocityEnergy_eq, FourierUniqueness.diff]
    have hs : ∀ a b : VelocityCoefficient, coefficientVec (a - b) = coefficientVec a - coefficientVec b :=
      fun a b ↦ by simp [coefficientVec]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← norm_coefficientVec_sq, ← norm_coefficientVec_sq, hs, hs, norm_sub_rev]
  rw [e1, e2] at h
  exact h

end Energies

section Constructions

variable {nu : ℝ} {u₀ : FourierVelocity} {T : ℝ}

/-- A tame solution of a higher order is a tame solution of every lower order. -/
def _root_.Mettapedia.FluidDynamics.NavierStokes.FourierTameContinuation.TameSolutionOn.ofLe {m m' : ℕ} (hmm' : m ≤ m') (c : TameSolutionOn nu m' u₀ T) :
    TameSolutionOn nu m u₀ T where
  toSolutionOn := c.toSolutionOn
  order_local := fun S hS ↦ by
    obtain ⟨B, hB⟩ := c.order_local S hS
    exact ⟨B, fun τ hτ F ↦ (velocityEnergy_le_of_order_le hmm' _ F).trans (hB τ hτ F)⟩
  dissipation_local := fun S hS ↦ by
    obtain ⟨X, hX⟩ := c.dissipation_local S hS
    refine ⟨max X 0, fun G ↦ ?_⟩
    rcases le_or_gt 0 S with hS0 | hS0
    · have hmono : ∫ τ in (0 : ℝ)..S, velocityDissipation m G (c.coefficients τ) ≤
          ∫ τ in (0 : ℝ)..S, velocityDissipation m' G (c.coefficients τ) := by
        refine intervalIntegral.integral_mono_on hS0
          ((continuous_velocityDissipation_along m G c.continuous).intervalIntegrable 0 S)
          ((continuous_velocityDissipation_along m' G c.continuous).intervalIntegrable 0 S)
          fun τ _ ↦ ?_
        unfold velocityDissipation orderDissipation orderEnergy
        refine Finset.sum_le_sum fun k _ ↦ ?_
        have hw : orderWeight m k ≤ orderWeight m' k :=
          pow_le_pow_right₀ (by linarith [norm_nonneg (frequencyVec k)]) hmm'
        have h0 : 0 ≤ orderWeight m k := by unfold orderWeight; positivity
        have ha : 0 ≤ ‖frequencyVec k‖ * amplitude (c.coefficients τ) k := by
          unfold amplitude; positivity
        exact pow_le_pow_left₀ (mul_nonneg h0 ha) (mul_le_mul_of_nonneg_right hw ha) 2
      exact hmono.trans ((hX G).trans (le_max_left _ _))
    · have h : ∫ τ in (0 : ℝ)..S, velocityDissipation m G (c.coefficients τ) ≤ 0 := by
        rw [intervalIntegral.integral_symm]
        have : 0 ≤ ∫ τ in S..(0 : ℝ), velocityDissipation m G (c.coefficients τ) :=
          intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) hS0.le fun τ _ ↦
            orderDissipation_nonneg m G (amplitude (c.coefficients τ))
        change -(∫ τ in S..(0 : ℝ), velocityDissipation m G (c.coefficients τ)) ≤ 0
        linarith
      exact h.trans (le_max_right _ _)

/-- **Restarting a tame solution at a later time.** -/
def _root_.Mettapedia.FluidDynamics.NavierStokes.FourierTameContinuation.TameSolutionOn.shift {m : ℕ} (c : TameSolutionOn nu m u₀ T) {T₀ : ℝ} (h0 : 0 ≤ T₀) : TameSolutionOn nu m (c.coefficients T₀) (T - T₀) where
  coefficients := fun t ↦ c.coefficients (t + T₀)
  continuous := fun q i ↦ (c.continuous q i).comp (continuous_id.add continuous_const)
  initial := by simp
  reality := fun t q ↦ c.reality _ q
  transverse := fun t q ↦ c.transverse _ q
  zero := fun t ↦ c.zero _
  sobolev_local := fun S hS ↦ by
    obtain ⟨B, hB⟩ := c.sobolev_local (S + T₀) (by linarith)
    exact ⟨B, fun t ht F ↦ hB (t + T₀) ⟨by linarith [ht.1], by linarith [ht.2]⟩ F⟩
  equation := fun t ht q i ↦ by
    have h := c.equation (t + T₀) ⟨by linarith [ht.1], by linarith [ht.2]⟩ q i
    exact h.comp_add_const t T₀
  order_local := fun S hS ↦ by
    obtain ⟨B, hB⟩ := c.order_local (S + T₀) (by linarith)
    exact ⟨B, fun t ht F ↦ hB (t + T₀) ⟨by linarith [ht.1], by linarith [ht.2]⟩ F⟩
  dissipation_local := fun S hS ↦ by
    obtain ⟨X, hX⟩ := c.dissipation_local (S + T₀) (by linarith)
    refine ⟨max X 0, fun G ↦ ?_⟩
    have hc := continuous_velocityDissipation_along m G c.continuous
    have hsh : (∫ τ in (0 : ℝ)..S, velocityDissipation m G (c.coefficients (τ + T₀))) =
        ∫ τ in T₀..(S + T₀), velocityDissipation m G (c.coefficients τ) := by
      have h := intervalIntegral.integral_comp_add_right
        (fun τ ↦ velocityDissipation m G (c.coefficients τ)) (a := 0) (b := S) T₀
      simpa only [zero_add] using h
    have hsplit : (∫ τ in T₀..(S + T₀), velocityDissipation m G (c.coefficients τ)) =
        (∫ τ in (0 : ℝ)..(S + T₀), velocityDissipation m G (c.coefficients τ)) -
          ∫ τ in (0 : ℝ)..T₀, velocityDissipation m G (c.coefficients τ) := by
      rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)]
    have hT₀ : 0 ≤ ∫ τ in (0 : ℝ)..T₀, velocityDissipation m G (c.coefficients τ) :=
      intervalIntegral.integral_nonneg h0 fun τ _ ↦
        orderDissipation_nonneg m G (amplitude (c.coefficients τ))
    change (∫ τ in (0 : ℝ)..S, velocityDissipation m G (c.coefficients (τ + T₀))) ≤ max X 0
    rw [hsh, hsplit]
    linarith [hX G, le_max_left X 0]

end Constructions

section PlanarDecay

open LocalEnstrophyDiffusion LocalLowDiffusionBudget FourierPlanarRegularity FourierEighthMomentControl
open FourierGlobalSolution

variable {nu : ℝ} {m : ℕ} {v₀ : FourierVelocity}

/-- **Planar enstrophy never grows**, between any two times. -/
theorem meanEnstrophy_antitone_of_planar (hm : 7 ≤ m) (hnu : 0 < nu) (hv : IsPlanar v₀)
    {T : ℝ} (c : TameSolutionOn nu m v₀ T) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (htT : t < T) :
    meanEnstrophy (c.coefficients t) ≤ meanEnstrophy (c.coefficients r) := by
  have hp : IsPlanar (c.coefficients r) := isPlanar_of_tame hm hnu hv c ⟨hr, hrt.trans_lt htT⟩
  have h := meanEnstrophy_le_of_planar hm hnu hp (c.shift hr) (τ := t - r)
    ⟨by linarith, by linarith⟩
  have e : (c.shift hr).coefficients (t - r) = c.coefficients t := by
    simp [TameSolutionOn.shift]
  rwa [e] at h

/-- **Planar enstrophy decays like the inverse of time**: the energy identity
pays its time integral, and it never grows. -/
theorem meanEnstrophy_le_div_of_planar (hm : 7 ≤ m) (hnu : 0 < nu) (hv : IsPlanar v₀)
    {T : ℝ} (c : TameSolutionOn nu m v₀ T) {t : ℝ} (ht : 0 < t) (htT : t < T) :
    meanEnstrophy (c.coefficients t) ≤ InfiniteConvectionEnergy.kineticEnergy v₀ / (2 * nu * t) := by
  set S := (t + T) / 2 with hSdef
  have htS' : t < S := by linarith
  obtain ⟨B, s, hs, g, hg, hSum, hu3⟩ := local_envelope_at hm c (S := S) (by linarith)
  have htS : t ∈ Icc (0 : ℝ) S := ⟨ht.le, htS'.le⟩
  have hu2 : ∀ τ ∈ Icc (0 : ℝ) S, ∀ q, fourierMoment 2 (s.coefficients τ) q ≤ g q := fun τ hτ q ↦
    (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu3 τ hτ q)
  have hint := LocalKineticEnergy.enstrophy_integral_le_initial s g hg hSum hu2 t htS
  have hZc : ContinuousOn (fun τ ↦ meanEnstrophy (s.coefficients τ)) (Icc 0 S) :=
    continuousOn_meanEnstrophy s g hSum hu3
  have hKc := LocalKineticEnergy.continuousOn_enstrophy s g hg hSum hu2
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 S := Icc_subset_Icc le_rfl htS.2
  have hmono : (∫ τ in (0 : ℝ)..t, meanEnstrophy (c.coefficients t)) ≤
      ∫ τ in (0 : ℝ)..t, meanEnstrophy (s.coefficients τ) := by
    refine intervalIntegral.integral_mono_on ht.le intervalIntegrable_const
      ((hZc.mono hsub).intervalIntegrable_of_Icc ht.le) fun τ hτ ↦ ?_
    rw [hs]
    exact meanEnstrophy_antitone_of_planar hm hnu hv c hτ.1 hτ.2 htT
  have hle : (∫ τ in (0 : ℝ)..t, meanEnstrophy (s.coefficients τ)) ≤
      ∫ τ in (0 : ℝ)..t, InfiniteConvectionEnergy.kineticEnergy (fourierCurl (s.coefficients τ)) := by
    refine intervalIntegral.integral_mono_on ht.le ((hZc.mono hsub).intervalIntegrable_of_Icc ht.le)
      ((hKc.mono hsub).intervalIntegrable_of_Icc ht.le) fun τ hτ ↦ ?_
    have hu1 : Summable (fourierMoment 1 (s.coefficients τ)) :=
      hSum.of_nonneg_of_le (fourierMoment_nonneg 1 _)
        (fun k ↦ (fourierMoment_mono _ (by omega : 1 ≤ 3) k).trans (hu3 τ (hsub hτ) k))
    exact integral_norm_fullVorticity_sq_le _ hu1
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
  rw [le_div_iff₀ (by positivity)]
  have hZ0 : 0 ≤ meanEnstrophy (c.coefficients t) := integral_nonneg fun x ↦ by
    unfold LocalEnstrophyDiffusion.energy
    positivity
  nlinarith

/-- The order-one energy of a planar solution decays like the inverse of time. -/
theorem velocityEnergy_one_le_div_of_planar (hm : 7 ≤ m) (hnu : 0 < nu) (hv : IsPlanar v₀)
    {T : ℝ} (c : TameSolutionOn nu m v₀ T) {t : ℝ} (ht : 0 < t) (htT : t < T)
    (F : Finset Wavevector) :
    velocityEnergy 1 F (c.coefficients t) ≤
      InfiniteConvectionEnergy.kineticEnergy v₀ / (2 * nu * t) / Real.pi ^ 2 := by
  obtain ⟨B, hB⟩ := c.order_local t htT
  have hB5 : ∀ G : Finset Wavevector, velocityEnergy 5 G (c.coefficients t) ≤ B := fun G ↦
    (velocityEnergy_le_of_order_le (by omega) _ G).trans (hB t ⟨ht.le, le_rfl⟩ G)
  calc velocityEnergy 1 F (c.coefficients t)
      ≤ (∫ x : UnitAddTorus (Fin 3), ‖fullVorticity (c.coefficients t) x‖ ^ 2) / Real.pi ^ 2 :=
        velocityEnergy_one_le _ (summable_fourierMoment_one _ hB5) (c.reality t)
          (c.transverse t) (c.zero t) F
    _ ≤ _ := div_le_div_of_nonneg_right (meanEnstrophy_le_div_of_planar hm hnu hv c ht htT)
        (by positivity)

/-- The order-one energy of a planar solution never exceeds its initial
enstrophy over `π²`. -/
theorem velocityEnergy_one_le_of_planar (hm : 7 ≤ m) (hnu : 0 < nu) (hv : IsPlanar v₀)
    {T : ℝ} (c : TameSolutionOn nu m v₀ T) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T)
    (F : Finset Wavevector) :
    velocityEnergy 1 F (c.coefficients t) ≤ meanEnstrophy v₀ / Real.pi ^ 2 := by
  obtain ⟨B, hB⟩ := c.order_local t ht.2
  have hB5 : ∀ G : Finset Wavevector, velocityEnergy 5 G (c.coefficients t) ≤ B := fun G ↦
    (velocityEnergy_le_of_order_le (by omega) _ G).trans (hB t ⟨ht.1, le_rfl⟩ G)
  calc velocityEnergy 1 F (c.coefficients t)
      ≤ (∫ x : UnitAddTorus (Fin 3), ‖fullVorticity (c.coefficients t) x‖ ^ 2) / Real.pi ^ 2 :=
        velocityEnergy_one_le _ (summable_fourierMoment_one _ hB5) (c.reality t)
          (c.transverse t) (c.zero t) F
    _ ≤ _ := div_le_div_of_nonneg_right (meanEnstrophy_le_of_planar hm hnu hv c ht)
        (by positivity)

/-- **The order-eleven energy of a planar solution grows at most linearly.** -/
theorem velocityEnergy_eleven_le_of_planar (hnu : 0 < nu) (hv : IsPlanar v₀)
    (g : GlobalSolution nu 11 v₀) {E₁₁ : ℝ} (hE : ∀ F, velocityEnergy 11 F v₀ ≤ E₁₁)
    {t : ℝ} (ht : 0 ≤ t) (F : Finset Wavevector) :
    velocityEnergy 11 F (g.coefficients t) ≤
      2 * (E₁₁ + tameRateConst 11 nu * (meanEnstrophy v₀ / Real.pi ^ 2) ^ (4 * 11 + 1) * t) := by
  obtain ⟨B, hB⟩ := g.order_local t
  obtain ⟨X, hX⟩ := g.dissipation_local t
  have hK : ∀ τ ∈ Icc (0 : ℝ) t, ∀ F, velocityEnergy 1 F (g.coefficients τ) ≤
      meanEnstrophy v₀ / Real.pi ^ 2 := fun τ hτ F ↦
    velocityEnergy_one_le_of_planar (by norm_num) hnu hv (g.toTame (t + 1)) ⟨hτ.1, by linarith [hτ.2]⟩ F
  exact orderEnergy_le_of_orderOne 11 (by norm_num) hnu (g.toTame (t + 1)).toSolutionOn ht
    (by linarith) hB hX hK hE F

/-- **A planar solution eventually has arbitrarily small order-five energy.** -/
theorem exists_time_small_of_planar (hnu : 0 < nu) (hv : IsPlanar v₀)
    (g : GlobalSolution nu 11 v₀) {E₁₁ : ℝ} (hE : ∀ F, velocityEnergy 11 F v₀ ≤ E₁₁)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ F, velocityEnergy 5 F (g.coefficients T₀) ≤ ε := by
  have hE0 : 0 ≤ E₁₁ := le_trans (velocityEnergy_nonneg' 11 ∅ _) (hE ∅)
  set A := InfiniteConvectionEnergy.kineticEnergy v₀ / (2 * nu) / Real.pi ^ 2 with hA
  have hA0 : 0 ≤ A := by
    have := LocalKineticEnergy.kineticEnergy_nonneg v₀
    positivity
  set K := meanEnstrophy v₀ / Real.pi ^ 2 with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ meanEnstrophy v₀ := integral_nonneg fun x ↦ by
      unfold LocalEnstrophyDiffusion.energy
      positivity
    positivity
  set B' := 2 * (E₁₁ + tameRateConst 11 nu * K ^ (4 * 11 + 1)) with hB'
  have hB'0 : 0 ≤ B' := by
    have := tameRateConst_nonneg 11 hnu
    positivity
  set P := A ^ ((3 : ℝ) / 5) * B' ^ ((2 : ℝ) / 5) with hP
  have hP0 : 0 ≤ P := by positivity
  set T₀ := max 1 (((P + 1) / ε) ^ 5) with hT₀
  have hT₀1 : 1 ≤ T₀ := le_max_left _ _
  have hT₀0 : 0 < T₀ := by linarith
  refine ⟨T₀, hT₀1, fun F ↦ ?_⟩
  -- the two bounds at `T₀`
  have h1 : velocityEnergy 1 F (g.coefficients T₀) ≤ A / T₀ := by
    have h := velocityEnergy_one_le_div_of_planar (by norm_num) hnu hv (g.toTame (T₀ + 1)) hT₀0
      (by linarith) F
    have e : InfiniteConvectionEnergy.kineticEnergy v₀ / (2 * nu * T₀) / Real.pi ^ 2 = A / T₀ := by
      rw [hA]
      field_simp
    rw [e] at h
    exact h
  have h11 : velocityEnergy 11 F (g.coefficients T₀) ≤ B' * T₀ := by
    have h : velocityEnergy 11 F (g.coefficients T₀) ≤
        2 * (E₁₁ + tameRateConst 11 nu * K ^ (4 * 11 + 1) * T₀) :=
      velocityEnergy_eleven_le_of_planar hnu hv g hE hT₀0.le F
    have hC : 0 ≤ tameRateConst 11 nu * K ^ (4 * 11 + 1) := by
      have := tameRateConst_nonneg 11 hnu
      positivity
    rw [hB']
    nlinarith [mul_nonneg hE0 (sub_nonneg.mpr hT₀1), mul_nonneg hC (sub_nonneg.mpr hT₀1)]
  have h5 := velocityEnergy_five_le F (g.coefficients T₀)
  have hn1 := velocityEnergy_nonneg' 1 F (g.coefficients T₀)
  have hn11 := velocityEnergy_nonneg' 11 F (g.coefficients T₀)
  have hr1 : velocityEnergy 1 F (g.coefficients T₀) ^ ((3 : ℝ) / 5) ≤ (A / T₀) ^ ((3 : ℝ) / 5) :=
    Real.rpow_le_rpow hn1 h1 (by norm_num)
  have hr11 : velocityEnergy 11 F (g.coefficients T₀) ^ ((2 : ℝ) / 5) ≤ (B' * T₀) ^ ((2 : ℝ) / 5) :=
    Real.rpow_le_rpow hn11 h11 (by norm_num)
  have hprod : velocityEnergy 5 F (g.coefficients T₀) ≤
      (A / T₀) ^ ((3 : ℝ) / 5) * (B' * T₀) ^ ((2 : ℝ) / 5) :=
    h5.trans (mul_le_mul hr1 hr11 (by positivity) (by positivity))
  have hsplit : (A / T₀) ^ ((3 : ℝ) / 5) * (B' * T₀) ^ ((2 : ℝ) / 5) =
      P / T₀ ^ ((1 : ℝ) / 5) := by
    rw [Real.div_rpow hA0 hT₀0.le, Real.mul_rpow hB'0 hT₀0.le, hP]
    have hT : T₀ ^ ((3 : ℝ) / 5) = T₀ ^ ((2 : ℝ) / 5) * T₀ ^ ((1 : ℝ) / 5) := by
      rw [← Real.rpow_add hT₀0]
      norm_num
    rw [hT]
    have h2 : 0 < T₀ ^ ((2 : ℝ) / 5) := Real.rpow_pos_of_pos hT₀0 _
    have h3 : 0 < T₀ ^ ((1 : ℝ) / 5) := Real.rpow_pos_of_pos hT₀0 _
    field_simp
  have hroot : (P + 1) / ε ≤ T₀ ^ ((1 : ℝ) / 5) := by
    have hge : ((P + 1) / ε) ^ 5 ≤ T₀ := le_max_right _ _
    have hq : 0 ≤ (P + 1) / ε := by positivity
    have hmono := Real.rpow_le_rpow (pow_nonneg hq 5) hge (by norm_num : (0 : ℝ) ≤ 1 / 5)
    have e : (((P + 1) / ε) ^ 5) ^ ((1 : ℝ) / 5) = (P + 1) / ε := by
      rw [show ((1 : ℝ) / 5) = ((5 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.pow_rpow_inv_natCast hq (by norm_num)
    rw [e] at hmono
    exact hmono
  have h3 : 0 < T₀ ^ ((1 : ℝ) / 5) := Real.rpow_pos_of_pos hT₀0 _
  rw [hsplit] at hprod
  refine hprod.trans ?_
  rw [div_le_iff₀ h3]
  have hq : (P + 1) / ε * ε = P + 1 := by field_simp
  nlinarith [mul_le_mul_of_nonneg_right hroot hε.le]

end PlanarDecay

section Bootstrap

open LocalEnstrophyDiffusion FourierPlanarRegularity FourierGlobalSolution FourierSmallData

variable {nu : ℝ} {u₀ v₀ : FourierVelocity}

/-- The tame-rate bound at order `j ≤ 11` on `[0, s]`, `s ≤ T₀`, from an order-one bound. -/
def stabM (nu : ℝ) (j : ℕ) (K E T₀ : ℝ) : ℝ := 2 * (E + tameRateConst j nu * K ^ (4 * j + 1) * T₀)

/-- The total mass of the lattice decay weight. -/
def latticeMass : ℝ := ∑' k, latticeDecayWeight k

/-- The Grönwall rate of the energy difference, for order-seven bound `M₇` on both solutions. -/
def stabKappa (nu M₇ : ℝ) : ℝ :=
  9 / nu * ((Real.sqrt M₇ * latticeMass) ^ 2 + (Real.sqrt M₇ * latticeMass) ^ 2)

theorem stabKappa_nonneg (hnu : 0 < nu) (M₇ : ℝ) : 0 ≤ stabKappa nu M₇ := by
  unfold stabKappa
  positivity

theorem velocityEnergy_le_of_orderOne_bound (hnu : 0 < nu) {j : ℕ} (hj : 2 ≤ j) (hj11 : j ≤ 11)
    {w₀ : FourierVelocity} {T : ℝ} (c : TameSolutionOn nu 11 w₀ T) {s K E T₀ : ℝ}
    (hs : s ∈ Ico (0 : ℝ) T) (hsT₀ : s ≤ T₀) (hK0 : 0 ≤ K)
    (hK : ∀ τ ∈ Icc (0 : ℝ) s, ∀ F, velocityEnergy 1 F (c.coefficients τ) ≤ K)
    (hE : ∀ F, velocityEnergy j F w₀ ≤ E) :
    ∀ τ ∈ Icc (0 : ℝ) s, ∀ F, velocityEnergy j F (c.coefficients τ) ≤ stabM nu j K E T₀ := by
  intro τ hτ F
  have hτT : τ < T := hτ.2.trans_lt hs.2
  obtain ⟨B, hB⟩ := (c.ofLe hj11).order_local τ hτT
  obtain ⟨X, hX⟩ := (c.ofLe hj11).dissipation_local τ hτT
  have h := orderEnergy_le_of_orderOne j hj hnu (c.ofLe hj11).toSolutionOn hτ.1 hτT hB hX
    (fun τ' hτ' F ↦ hK τ' ⟨hτ'.1, hτ'.2.trans hτ.2⟩ F) hE F
  have hC := tameRateConst_nonneg j hnu
  have hmono : tameRateConst j nu * K ^ (4 * j + 1) * τ ≤
      tameRateConst j nu * K ^ (4 * j + 1) * T₀ :=
    mul_le_mul_of_nonneg_left (hτ.2.trans hsT₀) (mul_nonneg hC (pow_nonneg hK0 _))
  change velocityEnergy j F (c.coefficients τ) ≤
    2 * (E + tameRateConst j nu * K ^ (4 * j + 1) * τ) at h
  unfold stabM
  linarith

set_option maxHeartbeats 1000000 in
/-- **The bootstrap on `[0, T₀]`.** Let `v₀` be planar with global solution `g`, and
let the data `u₀` differ from `v₀` by at most `ε` in the order-eleven energy. With
`K = 2 Kv + 1`, where `Kv` bounds the order-one energy of `g`, every tame solution
from `u₀` keeps its order-one energy below `K` up to time `T₀`, and its difference
from `g` stays below `η₀` in the order-one energy, as long as `ε` is small against
the Grönwall rate of the energy difference over `[0, T₀]`. -/
theorem bootstrap (hnu : 0 < nu) (hv : IsPlanar v₀) (g : GlobalSolution nu 11 v₀)
    {T : ℝ} (c : TameSolutionOn nu 11 u₀ T) {E₁₁v T₀ η₀ ε : ℝ}
    (hEv : ∀ F, velocityEnergy 11 F v₀ ≤ E₁₁v) (hη₀0 : 0 < η₀) (hη₀ : η₀ ≤ 1 / 4)
    (hεη : ε ≤ η₀)
    (hεsmall : ε * Real.exp (stabKappa nu
        (stabM nu 7 (2 * (meanEnstrophy v₀ / Real.pi ^ 2) + 1) (2 * E₁₁v + 1) T₀) * T₀) *
        (4 * stabM nu 2 (2 * (meanEnstrophy v₀ / Real.pi ^ 2) + 1) (2 * E₁₁v + 1) T₀) ≤ η₀ ^ 2)
    (hw : ∀ F, velocityEnergy 11 F (FourierUniqueness.diff u₀ v₀) ≤ ε) :
    ∀ τ ∈ Ico (0 : ℝ) T, τ ≤ T₀ →
      (∀ F, velocityEnergy 1 F (c.coefficients τ) ≤ 2 * (meanEnstrophy v₀ / Real.pi ^ 2) + 1) ∧
      (∀ F, velocityEnergy 1 F
        (FourierUniqueness.diff (c.coefficients τ) (g.coefficients τ)) ≤ η₀) := by
  set Kv := meanEnstrophy v₀ / Real.pi ^ 2 with hKvdef
  set K := 2 * Kv + 1 with hKdef
  set Eu := 2 * E₁₁v + 1 with hEudef
  set M₂ := stabM nu 2 K Eu T₀ with hM₂
  set M₇ := stabM nu 7 K Eu T₀ with hM₇
  set κ := stabKappa nu M₇ with hκdef
  have hKv0 : 0 ≤ Kv := by
    have : 0 ≤ meanEnstrophy v₀ := integral_nonneg fun x ↦ by
      unfold LocalEnstrophyDiffusion.energy
      positivity
    positivity
  have hK0 : 0 ≤ K := by positivity
  have hEv0 : 0 ≤ E₁₁v := le_trans (velocityEnergy_nonneg' 11 ∅ _) (hEv ∅)
  have hε0 : 0 ≤ ε := le_trans (velocityEnergy_nonneg' 11 ∅ _) (hw ∅)
  have hκ0 : 0 ≤ κ := stabKappa_nonneg hnu M₇
  -- the planar solution's order-one bound
  have hvK : ∀ t, 0 ≤ t → ∀ F, velocityEnergy 1 F (g.coefficients t) ≤ Kv := fun t ht F ↦
    velocityEnergy_one_le_of_planar (by norm_num) hnu hv (g.toTame (t + 1)) ⟨ht, by linarith⟩ F
  -- data bounds up to order eleven
  have hdu : ∀ j, j ≤ 11 → ∀ F, velocityEnergy j F u₀ ≤ Eu := by
    intro j hj F
    have h1 := velocityEnergy_le_two_diff j F u₀ v₀
    have h2 := (velocityEnergy_le_of_order_le hj v₀ F).trans (hEv F)
    have h3 := (velocityEnergy_le_of_order_le hj _ F).trans (hw F)
    rw [hEudef]
    linarith
  have hdv : ∀ j, j ≤ 11 → ∀ F, velocityEnergy j F v₀ ≤ Eu := by
    intro j hj F
    have h2 := (velocityEnergy_le_of_order_le hj v₀ F).trans (hEv F)
    rw [hEudef]
    linarith
  have hD₀ : ∀ F, velocityEnergy 0 F (FourierUniqueness.diff u₀ v₀) ≤ ε := fun F ↦
    (velocityEnergy_le_of_order_le (by norm_num) _ F).trans (hw F)
  -- the step: an order-one bound on `[0, s]` improves itself at `s`
  have hstep : ∀ s ∈ Ico (0 : ℝ) T, s ≤ T₀ →
      (∀ τ ∈ Icc (0 : ℝ) s, ∀ F, velocityEnergy 1 F (c.coefficients τ) ≤ K) →
        (∀ F, velocityEnergy 1 F
          (FourierUniqueness.diff (c.coefficients s) (g.coefficients s)) ≤ η₀) ∧
        (∀ F, velocityEnergy 1 F (c.coefficients s) ≤ K - 1 / 2) := by
    intro s hs hsT₀ hK
    rcases hs.1.eq_or_lt with h0 | hpos
    · subst h0
      have hc0 : c.coefficients 0 = u₀ := c.initial
      have hg0 : g.coefficients 0 = v₀ := g.initial
      rw [hc0, hg0]
      have hd1 : ∀ F, velocityEnergy 1 F (FourierUniqueness.diff u₀ v₀) ≤ η₀ := fun F ↦
        ((velocityEnergy_le_of_order_le (by norm_num) _ F).trans (hw F)).trans hεη
      refine ⟨hd1, fun F ↦ ?_⟩
      have h1 := velocityEnergy_le_two_diff 1 F u₀ v₀
      have h2 := hvK 0 le_rfl F
      rw [hg0] at h2
      have h3 := hd1 F
      rw [hKdef]
      linarith
    · -- tame bounds for both solutions on `[0, s]`
      have hKg : ∀ τ ∈ Icc (0 : ℝ) s, ∀ F, velocityEnergy 1 F ((g.toTame T).coefficients τ) ≤ K :=
        fun τ hτ F ↦ (hvK τ hτ.1 F).trans (by rw [hKdef]; linarith)
      have hc2 := velocityEnergy_le_of_orderOne_bound hnu (j := 2) (by norm_num) (by norm_num) c hs
        hsT₀ hK0 hK (hdu 2 (by norm_num))
      have hc7 := velocityEnergy_le_of_orderOne_bound hnu (j := 7) (by norm_num) (by norm_num) c hs
        hsT₀ hK0 hK (hdu 7 (by norm_num))
      have hg2 := velocityEnergy_le_of_orderOne_bound hnu (j := 2) (by norm_num) (by norm_num)
        (g.toTame T) hs hsT₀ hK0 hKg (hdv 2 (by norm_num))
      have hg7 := velocityEnergy_le_of_orderOne_bound hnu (j := 7) (by norm_num) (by norm_num)
        (g.toTame T) hs hsT₀ hK0 hKg (hdv 7 (by norm_num))
      -- amplitude envelopes
      let env : Wavevector → ℝ := fun k ↦ Real.sqrt M₇ * latticeDecayWeight k
      have henv0 : ∀ k, 0 ≤ env k := fun k ↦
        mul_nonneg (Real.sqrt_nonneg _) (latticeDecayWeight_pos k).le
      have henvS : Summable env := summable_latticeDecayWeight.mul_left _
      have hac : ∀ τ ∈ Icc (0 : ℝ) s, ∀ k, amplitude (c.coefficients τ) k ≤ env k := fun τ hτ k ↦
        (amplitude_le_moment _ k).trans (orderMoment_le_latticeEnvelope 3 _ M₇ (hc7 τ hτ) k)
      have had : ∀ τ ∈ Icc (0 : ℝ) s, ∀ k, amplitude ((g.toTame T).coefficients τ) k ≤ env k :=
        fun τ hτ k ↦
          (amplitude_le_moment _ k).trans (orderMoment_le_latticeEnvelope 3 _ M₇ (hg7 τ hτ) k)
      have hsum : (∑' k, env k) = Real.sqrt M₇ * latticeMass := by
        simp only [env, latticeMass, tsum_mul_left]
      -- the energy difference
      have hL2 : ∀ F, velocityEnergy 0 F
          (FourierUniqueness.diff (c.coefficients s) (g.coefficients s)) ≤
            ε * Real.exp (κ * T₀) := by
        intro F
        have h := velocityEnergy_diff_le (m := 11) (by norm_num) hnu c (g.toTame T) hpos hs.2
          henv0 henv0 henvS henvS hac had hD₀ s ⟨hpos.le, le_rfl⟩ F
        rw [hsum] at h
        have hk : 9 / nu * ((Real.sqrt M₇ * latticeMass) ^ 2 + (Real.sqrt M₇ * latticeMass) ^ 2) * s ≤
            κ * T₀ := by
          rw [hκdef]
          exact mul_le_mul (le_refl _) hsT₀ hpos.le (stabKappa_nonneg hnu M₇)
        exact h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hk) hε0)
      have hE2 : ∀ F, velocityEnergy 2 F
          (FourierUniqueness.diff (c.coefficients s) (g.coefficients s)) ≤ 4 * M₂ := by
        intro F
        have h := velocityEnergy_diff_le_two 2 F (c.coefficients s) (g.coefficients s)
        have h1 := hc2 s ⟨hpos.le, le_rfl⟩ F
        have h2 := hg2 s ⟨hpos.le, le_rfl⟩ F
        change velocityEnergy 2 F (g.coefficients s) ≤ M₂ at h2
        linarith
      have hd1 : ∀ F, velocityEnergy 1 F
          (FourierUniqueness.diff (c.coefficients s) (g.coefficients s)) ≤ η₀ := by
        intro F
        have hcs := velocityEnergy_sq_le_mul 1 0 2 (by norm_num) F
          (FourierUniqueness.diff (c.coefficients s) (g.coefficients s))
        have hE0 := velocityEnergy_nonneg' 0 F
          (FourierUniqueness.diff (c.coefficients s) (g.coefficients s))
        have hE1 := velocityEnergy_nonneg' 1 F
          (FourierUniqueness.diff (c.coefficients s) (g.coefficients s))
        have hprod : velocityEnergy 0 F (FourierUniqueness.diff (c.coefficients s) (g.coefficients s)) *
            velocityEnergy 2 F (FourierUniqueness.diff (c.coefficients s) (g.coefficients s)) ≤
              ε * Real.exp (κ * T₀) * (4 * M₂) :=
          mul_le_mul (hL2 F) (hE2 F) (velocityEnergy_nonneg' 2 F _) (by positivity)
        have hsq : velocityEnergy 1 F
            (FourierUniqueness.diff (c.coefficients s) (g.coefficients s)) ^ 2 ≤ η₀ ^ 2 := by
          have : ε * Real.exp (κ * T₀) * (4 * M₂) ≤ η₀ ^ 2 := by
            simpa only [hκdef, hM₇, hM₂, hKdef, hKvdef, hEudef] using hεsmall
          linarith
        nlinarith [hη₀0]
      refine ⟨hd1, fun F ↦ ?_⟩
      have h1 := velocityEnergy_le_two_diff 1 F (c.coefficients s) (g.coefficients s)
      have h2 := hvK s hpos.le F
      have h3 := hd1 F
      rw [hKdef]
      linarith
  -- the continuity argument
  intro τ₁ hτ₁ hτ₁T₀
  set S' := (τ₁ + T) / 2 with hS'def
  have hτS' : τ₁ < S' := by linarith [hτ₁.2]
  have hS'T : S' < T := by linarith [hτ₁.2]
  have hec := continuousOn_fullEnergy (m := 1) (c.ofLe (by norm_num : 1 + 2 ≤ 11)) hS'T
  obtain ⟨B', hB'⟩ := (c.ofLe (by norm_num : 1 + 2 ≤ 11)).order_local S' hS'T
  set e : ℝ → ℝ := fun t ↦ fullEnergy 1 (c.coefficients t) with hedef
  have hsub : Icc (0 : ℝ) τ₁ ⊆ Icc 0 S' := Icc_subset_Icc le_rfl hτS'.le
  have hvel : ∀ t ∈ Icc (0 : ℝ) τ₁, ∀ F, velocityEnergy 1 F (c.coefficients t) ≤ e t :=
    fun t ht F ↦ velocityEnergy_le_fullEnergy 1 _ (hB' t (hsub ht)) F
  have hfull : ∀ s ∈ Icc (0 : ℝ) τ₁, (∀ τ ∈ Icc (0 : ℝ) s, e τ ≤ K) → e s ≤ K - 1 / 2 := by
    intro s hs h
    have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, hs.2.trans_lt hτ₁.2⟩
    refine fullEnergy_le_of_forall 1 _ (hstep s hsT (hs.2.trans hτ₁T₀) fun τ hτ F ↦ ?_).2
    exact (hvel τ ⟨hτ.1, hτ.2.trans hs.2⟩ F).trans (h τ hτ)
  have he0 : e 0 ≤ K - 1 / 2 := hfull 0 ⟨le_rfl, hτ₁.1⟩ fun τ hτ ↦ by
    have : τ = 0 := le_antisymm hτ.2 hτ.1
    subst this
    have h := (hstep 0 ⟨le_rfl, lt_of_le_of_lt hτ₁.1 hτ₁.2⟩ (le_trans hτ₁.1 hτ₁T₀)
      (fun τ' hτ' F ↦ by
        have : τ' = 0 := le_antisymm hτ'.2 hτ'.1
        subst this
        have hc0 : c.coefficients 0 = u₀ := c.initial
        rw [hc0]
        have h1 := velocityEnergy_le_two_diff 1 F u₀ v₀
        have h2 := hvK 0 le_rfl F
        rw [g.initial] at h2
        have h3 := (velocityEnergy_le_of_order_le (by norm_num : 1 ≤ 11) _ F).trans (hw F)
        rw [hKdef]
        linarith)).2
    exact (fullEnergy_le_of_forall 1 _ h).trans (by linarith)
  let U : Set ℝ := {t ∈ Icc (0 : ℝ) τ₁ | K - 1 / 4 ≤ e t}
  have hUempty : U = ∅ := by
    by_contra hne
    obtain ⟨t₀, ht₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hbdd : BddBelow U := ⟨0, fun t ht ↦ ht.1.1⟩
    set ts := sInf U with htsdef
    have hclosed : IsClosed U := by
      have h := (hec.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc
        (isClosed_Ici (a := K - 1 / 4))
      exact h
    have htsU : ts ∈ U := hclosed.csInf_mem ⟨t₀, ht₀⟩ hbdd
    have hts0 : 0 < ts := by
      rcases htsU.1.1.eq_or_lt with h | h
      · exfalso
        have hU0 := htsU.2
        rw [← h] at hU0
        linarith
      · exact h
    have hbelow : ∀ t ∈ Ico (0 : ℝ) ts, e t < K - 1 / 4 := by
      intro t ht
      by_contra hge
      have htU : t ∈ U := ⟨⟨ht.1, ht.2.le.trans htsU.1.2⟩, not_lt.mp hge⟩
      exact absurd (csInf_le hbdd htU) (not_le.mpr ht.2)
    have hhalf : ∀ t ∈ Ico (0 : ℝ) ts, e t ≤ K - 1 / 2 := by
      intro t ht
      refine hfull t ⟨ht.1, ht.2.le.trans htsU.1.2⟩ fun τ hτ ↦ ?_
      have h := hbelow τ ⟨hτ.1, hτ.2.trans_lt ht.2⟩
      linarith
    have hcl : ts ∈ closure (Ico (0 : ℝ) ts) := by
      rw [closure_Ico hts0.ne]
      exact ⟨hts0.le, le_rfl⟩
    have hcw : ContinuousWithinAt e (Ico (0 : ℝ) ts) ts :=
      (hec ts (hsub htsU.1)).mono fun t ht ↦ hsub ⟨ht.1, ht.2.le.trans htsU.1.2⟩
    have hle := ContinuousWithinAt.closure_le hcl hcw continuousWithinAt_const hhalf
    have hge := htsU.2
    linarith
  have hall : ∀ τ ∈ Icc (0 : ℝ) τ₁, e τ ≤ K := by
    intro τ hτ
    by_contra hgt
    have hU : τ ∈ U := ⟨hτ, by linarith [not_le.mp hgt]⟩
    rw [hUempty] at hU
    exact hU
  have hfin := hstep τ₁ hτ₁ hτ₁T₀ fun τ hτ F ↦ (hvel τ hτ F).trans (hall τ hτ)
  refine ⟨fun F ↦ (hfin.2 F).trans (by linarith), hfin.1⟩

end Bootstrap

section Assembly

open LocalEnstrophyDiffusion FourierPlanarRegularity FourierGlobalSolution FourierSmallData

variable {nu : ℝ}

set_option maxHeartbeats 1000000 in
/-- **Three-dimensional perturbations of planar flows are regular.** For every
planar admissible datum `v₀` of finite order-eleven energy there is `ε > 0` such
that every admissible datum within `ε` of `v₀` in the order-eleven energy has a
unique global solution, however large `v₀` is. -/
theorem exists_nhds_globalSolution_of_planar (hnu : 0 < nu) {v₀ : FourierVelocity}
    (hrv : ∀ q, v₀ (-q) = coefficientConjugate (v₀ q)) (hdv : ∀ q, modeDot q (v₀ q) = 0)
    (hzv : v₀ 0 = 0) {E₁₁v : ℝ} (hEv : ∀ F, velocityEnergy 11 F v₀ ≤ E₁₁v) (hv : IsPlanar v₀) :
    ∃ ε > 0, ∀ u₀ : FourierVelocity, (∀ q, u₀ (-q) = coefficientConjugate (u₀ q)) →
      (∀ q, modeDot q (u₀ q) = 0) → u₀ 0 = 0 →
      (∀ F, velocityEnergy 11 F (FourierUniqueness.diff u₀ v₀) ≤ ε) →
      Nonempty (GlobalSolution nu 11 u₀) := by
  have hEv0 : 0 ≤ E₁₁v := le_trans (velocityEnergy_nonneg' 11 ∅ _) (hEv ∅)
  obtain ⟨g⟩ := nonempty_globalSolution_of_planar 11 (by norm_num) hnu v₀ hrv hdv hzv hEv0 hEv hv
  set δ := smallRadius 5 nu with hδdef
  have hδ : 0 < δ := smallRadius_pos 5 hnu
  obtain ⟨T₀, hT₀1, hT₀small⟩ := exists_time_small_of_planar hnu hv g hEv
    (ε := δ ^ 2 / 32) (by positivity)
  have hT₀0 : 0 < T₀ := by linarith
  set Kv := meanEnstrophy v₀ / Real.pi ^ 2 with hKvdef
  set K := 2 * Kv + 1 with hKdef
  set Eu := 2 * E₁₁v + 1 with hEudef
  set M₂ := stabM nu 2 K Eu T₀ with hM₂
  set M₇ := stabM nu 7 K Eu T₀ with hM₇
  set M₁₁ := stabM nu 11 K Eu T₀ with hM₁₁
  set κ := stabKappa nu M₇ with hκdef
  have hKv0 : 0 ≤ Kv := by
    have : 0 ≤ meanEnstrophy v₀ := integral_nonneg fun x ↦ by
      unfold LocalEnstrophyDiffusion.energy
      positivity
    positivity
  have hK0 : 0 ≤ K := by positivity
  have hM₂0 : 0 ≤ M₂ := by
    have := tameRateConst_nonneg 2 hnu
    rw [hM₂]
    unfold stabM
    positivity
  have hM₁₁0 : 0 ≤ M₁₁ := by
    have := tameRateConst_nonneg 11 hnu
    rw [hM₁₁]
    unfold stabM
    positivity
  set η₀ := min (1 / 4) ((δ ^ 2 / 32) ^ 2 / (4 * M₁₁ + 1)) with hη₀def
  have hη₀0 : 0 < η₀ := lt_min (by norm_num) (by positivity)
  have hη₀ : η₀ ≤ 1 / 4 := min_le_left _ _
  have hη₀M : η₀ * (4 * M₁₁) ≤ (δ ^ 2 / 32) ^ 2 := by
    have h := min_le_right (1 / 4 : ℝ) ((δ ^ 2 / 32) ^ 2 / (4 * M₁₁ + 1))
    rw [← hη₀def] at h
    have h2 : η₀ * (4 * M₁₁ + 1) ≤ (δ ^ 2 / 32) ^ 2 := by
      rw [le_div_iff₀ (by positivity)] at h
      exact h
    nlinarith [hη₀0.le]
  set E := Real.exp (κ * T₀) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  set ε := min η₀ (η₀ ^ 2 / (E * (4 * M₂) + 1)) with hεdef
  have hε0 : 0 < ε := lt_min hη₀0 (by positivity)
  have hεη : ε ≤ η₀ := min_le_left _ _
  have hεsmall : ε * Real.exp (stabKappa nu
      (stabM nu 7 (2 * (meanEnstrophy v₀ / Real.pi ^ 2) + 1) (2 * E₁₁v + 1) T₀) * T₀) *
      (4 * stabM nu 2 (2 * (meanEnstrophy v₀ / Real.pi ^ 2) + 1) (2 * E₁₁v + 1) T₀) ≤ η₀ ^ 2 := by
    change ε * E * (4 * M₂) ≤ η₀ ^ 2
    have h := min_le_right η₀ (η₀ ^ 2 / (E * (4 * M₂) + 1))
    rw [← hεdef, le_div_iff₀ (by positivity)] at h
    nlinarith [hε0.le, mul_nonneg hE0.le hM₂0]
  refine ⟨ε, hε0, fun u₀ hr hd hz hw ↦ ?_⟩
  have hε0' : 0 ≤ ε := hε0.le
  have hEu0 : ∀ F, velocityEnergy 11 F u₀ ≤ 2 * E₁₁v + 2 * ε := fun F ↦ by
    have h1 := velocityEnergy_le_two_diff 11 F u₀ v₀
    have h2 := hEv F
    have h3 := hw F
    linarith
  refine nonempty_globalSolution (by norm_num) hnu ?_
  refine exists_tameSolutionOn_of_orderOne 11 (by norm_num) hnu u₀ hr hd hz
    (by positivity) hEu0 ?_
  intro H _
  refine ⟨max K (δ ^ 2 / 4), fun T _ c τ hτ F ↦ ?_⟩
  have hboot := bootstrap hnu hv g c hEv hη₀0 hη₀ hεη hεsmall hw
  rcases le_or_gt τ T₀ with hτT₀ | hτT₀
  · exact ((hboot τ hτ hτT₀).1 F).trans (le_max_left _ _)
  · -- after the planar flow has become small, the small-data theorem takes over
    have hT₀T : T₀ < T := hτT₀.trans hτ.2
    have hT₀mem : T₀ ∈ Ico (0 : ℝ) T := ⟨hT₀0.le, hT₀T⟩
    have hbT₀ := hboot T₀ hT₀mem le_rfl
    have hKc : ∀ t ∈ Icc (0 : ℝ) T₀, ∀ F, velocityEnergy 1 F (c.coefficients t) ≤ K :=
      fun t ht F ↦ (hboot t ⟨ht.1, ht.2.trans_lt hT₀T⟩ ht.2).1 F
    have hdu11 : ∀ F, velocityEnergy 11 F u₀ ≤ Eu := fun F ↦ by
      have := hEu0 F
      have : ε ≤ 1 / 4 := hεη.trans hη₀
      rw [hEudef]
      linarith
    have hdv11 : ∀ F, velocityEnergy 11 F v₀ ≤ Eu := fun F ↦ by
      have := hEv F
      rw [hEudef]
      linarith
    have hc11 := velocityEnergy_le_of_orderOne_bound hnu (j := 11) (by norm_num) le_rfl c hT₀mem
      le_rfl hK0 hKc hdu11
    have hKg : ∀ t ∈ Icc (0 : ℝ) T₀, ∀ F, velocityEnergy 1 F ((g.toTame T).coefficients t) ≤ K :=
      fun t ht F ↦ (velocityEnergy_one_le_of_planar (by norm_num) hnu hv (g.toTame (t + 1))
        ⟨ht.1, by linarith⟩ F).trans (by rw [hKdef]; linarith)
    have hg11 := velocityEnergy_le_of_orderOne_bound hnu (j := 11) (by norm_num) le_rfl
      (g.toTame T) hT₀mem le_rfl hK0 hKg hdv11
    -- the order-five energy of the difference at `T₀`
    have hw5 : ∀ F, velocityEnergy 5 F
        (FourierUniqueness.diff (c.coefficients T₀) (g.coefficients T₀)) ≤ δ ^ 2 / 32 := by
      intro F
      set wT := FourierUniqueness.diff (c.coefficients T₀) (g.coefficients T₀)
      have hcs := velocityEnergy_sq_le_mul 5 1 9 (by norm_num) F wT
      have h9 : velocityEnergy 9 F wT ≤ 4 * M₁₁ := by
        have h := (velocityEnergy_le_of_order_le (by norm_num : 9 ≤ 11) wT F).trans
          (velocityEnergy_diff_le_two 11 F (c.coefficients T₀) (g.coefficients T₀))
        have h1 := hc11 T₀ ⟨hT₀0.le, le_rfl⟩ F
        have h2 := hg11 T₀ ⟨hT₀0.le, le_rfl⟩ F
        change velocityEnergy 11 F (g.coefficients T₀) ≤ M₁₁ at h2
        linarith
      have h1 := hbT₀.2 F
      have hn1 := velocityEnergy_nonneg' 1 F wT
      have hn5 := velocityEnergy_nonneg' 5 F wT
      have hn9 := velocityEnergy_nonneg' 9 F wT
      have hprod : velocityEnergy 1 F wT * velocityEnergy 9 F wT ≤ η₀ * (4 * M₁₁) :=
        mul_le_mul h1 h9 hn9 hη₀0.le
      have hsq : velocityEnergy 5 F wT ^ 2 ≤ (δ ^ 2 / 32) ^ 2 := by linarith
      nlinarith [sq_nonneg δ]
    have hdata : ∀ F, velocityEnergy 5 F (c.coefficients T₀) ≤ δ ^ 2 / 8 := by
      intro F
      have h := velocityEnergy_le_two_diff 5 F (c.coefficients T₀) (g.coefficients T₀)
      have h1 := hT₀small F
      have h2 := hw5 F
      linarith
    have hκs : smallRateConst 5 * δ ≤ nu * (2 * Real.pi) ^ 2 :=
      (smallRateConst_mul_smallRadius 5 nu).le
    let c' := (c.shift hT₀0.le).ofLe (by norm_num : 5 + 2 ≤ 11)
    have hsmall := velocityEnergy_le_of_small (m := 5) (by norm_num) hnu c' hδ hκs hdata
      (τ - T₀) ⟨by linarith, by linarith [hτ.2]⟩ F
    have e : c'.coefficients (τ - T₀) = c.coefficients τ := by
      show c.coefficients (τ - T₀ + T₀) = c.coefficients τ
      rw [sub_add_cancel]
    rw [e] at hsmall
    exact ((velocityEnergy_le_of_order_le (by norm_num : 1 ≤ 5) _ F).trans hsmall).trans
      (le_max_right _ _)

end Assembly

section Official

open FourierOfficialTheorems FourierInitialData OfficialPeriodicProblem FourierRegularityEquivalence
open FourierPlanarRegularity FourierGlobalSolution

variable {nu : ℝ}

/-- **Three-dimensional perturbations of planar flows, official form.** For every
smooth, divergence-free, one-periodic planar initial velocity `v₀`, of any size,
there is `ε > 0` such that every smooth, divergence-free, one-periodic initial
velocity whose fluctuation lies within `ε` of that of `v₀` in the order-eleven
energy has a smooth periodic solution for all time. -/
theorem exists_official_near_planar (hnu : 0 < nu) {v₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hv₀ : InitialVelocityConditionPeriodic v₀) (hpl : IsPlanarVelocity v₀) :
    ∃ ε > 0, ∀ u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      InitialVelocityConditionPeriodic u₀ →
      (∀ F, velocityEnergy 11 F (FourierUniqueness.diff (fluctuation u₀) (fluctuation v₀)) ≤ ε) →
      ∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ (fun _ _ ↦ 0) v p := by
  obtain ⟨hr, hd, hz, E₀, hE₀⟩ := admissible_fluctuation hv₀ 11
  obtain ⟨ε, hε, h⟩ := exists_nhds_globalSolution_of_planar hnu hr hd hz hE₀
    (isPlanar_fluctuation hv₀ hpl)
  refine ⟨ε, hε, fun u₀ hu₀ hw ↦ ?_⟩
  obtain ⟨hr', hd', hz', -⟩ := admissible_fluctuation hu₀ 11
  obtain ⟨g⟩ := h (fluctuation u₀) hr' hd' hz' hw
  exact exists_official_of_globalSolution hnu hu₀ (by norm_num) g

end Official

end Mettapedia.FluidDynamics.NavierStokes.FourierStability
