import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierGalilean
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierAllOrders
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicFourierWeakDerivative
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpatialBottomProjector
import Mettapedia.Analysis.UnitTorusFourierReal

/-!
# Fourier data of a smooth periodic initial velocity

A smooth, one-periodic velocity on `ℝ³` descends to a continuous function on
the torus `ℝ³/ℤ³`, and its Fourier coefficients are those of the descended
function. Periodic integration by parts turns a coordinate derivative into the
multiplier `2π i kⱼ`, so the coefficients of a smooth function decay faster
than every power of `|k|`; the Fourier series then converges absolutely and
reconstructs the velocity pointwise. The coefficients of a real velocity are
real (`a₋ₖ = conj aₖ`), and those of a divergence-free velocity are transverse
(`k · aₖ = 0`). Removing the zero mode leaves Fourier data admissible of every
order, and the velocity is its mean plus the field of these data.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierInitialData

open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Set Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeLatticeDecayEnvelope PancakeFourierMaterialPaths
open PancakeDyadicDirectionEvolution PancakePeriodicVorticityEquation PancakePeriodicComplexStretch
open PancakeBlockReality PancakeTransverseEnergyFreezing PancakeHigherSobolevVelocityRate
open PancakeHaarTransportRate PancakeFourierTranslationCurve PancakeMeasurableMaterialRate
open PancakeHigherSobolevWeights
open FourierTimeRegularity FourierPhysicalFields FourierSpatialCalculus FourierOfficialEquation
open FourierGalilean FourierRegularityEquivalence OfficialPeriodicProblem

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

section Descent

variable {α : Type*} {u : ℝ³ → α}

theorem isOnePeriodic_add_int_smul (hu : IsOnePeriodic u) (i : Fin 3) (n : ℤ) :
    ∀ x : ℝ³, u (x + (n : ℝ) • EuclideanSpace.single i 1) = u x := by
  induction n with
  | zero => intro x; simp
  | succ n ih =>
    intro x
    have h := hu (x + ((n : ℤ) : ℝ) • EuclideanSpace.single i 1) i
    rw [← ih x, ← h, add_assoc]
    congr 2
    push_cast
    rw [add_smul, one_smul]
  | pred n ih =>
    intro x
    have h := hu (x + ((-(n : ℤ) - 1 : ℤ) : ℝ) • EuclideanSpace.single i 1) i
    rw [← ih x, ← h, add_assoc]
    congr 2
    push_cast
    rw [sub_smul, one_smul, sub_add_cancel]

theorem isOnePeriodic_add_int (hu : IsOnePeriodic u) (n : Fin 3 → ℤ) (x : ℝ³) :
    u (x + WithLp.toLp 2 (fun i ↦ (n i : ℝ))) = u x := by
  have e : WithLp.toLp 2 (fun i ↦ (n i : ℝ)) = ((n 0 : ℤ) : ℝ) • EuclideanSpace.single 0 (1 : ℝ) +
      ((n 1 : ℤ) : ℝ) • EuclideanSpace.single 1 (1 : ℝ) +
        ((n 2 : ℤ) : ℝ) • EuclideanSpace.single 2 (1 : ℝ) := by
    ext i
    fin_cases i <;> simp
  rw [e, ← add_assoc, ← add_assoc, isOnePeriodic_add_int_smul hu, isOnePeriodic_add_int_smul hu,
    isOnePeriodic_add_int_smul hu]

theorem exists_int_of_torusPoint_eq {r s : X3} (h : torusPoint s = torusPoint r) :
    ∃ n : Fin 3 → ℤ, s = r + fun i ↦ (n i : ℝ) := by
  have hi : ∀ i, ∃ k : ℤ, s i = r i + k := by
    intro i
    have h1 : ((s i : ℝ) : UnitAddCircle) = ((r i : ℝ) : UnitAddCircle) := congrFun h i
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq.mp h1)
    refine ⟨-k, ?_⟩
    rw [zsmul_eq_mul, mul_one] at hk
    push_cast
    linarith
  choose n hn using hi
  exact ⟨n, funext hn⟩

/-- The torus function of a one-periodic function on `ℝ³`. -/
def descend (u : ℝ³ → α) (y : T3) : α :=
  u (WithLp.toLp 2 (Function.surjInv torusPoint_surjective y))

theorem descend_torusPoint (hu : IsOnePeriodic u) (r : X3) :
    descend u (torusPoint r) = u (WithLp.toLp 2 r) := by
  unfold descend
  obtain ⟨n, hn⟩ := exists_int_of_torusPoint_eq
    (Function.surjInv_eq torusPoint_surjective (torusPoint r))
  rw [hn, WithLp.toLp_add, isOnePeriodic_add_int hu]

theorem continuous_descend [TopologicalSpace α] (hc : Continuous u) (hu : IsOnePeriodic u) :
    Continuous (descend u) := by
  have hq := IsOpenQuotientMap.piMap (fun _ : Fin 3 ↦
    (QuotientAddGroup.isOpenQuotientMap_mk (N := AddSubgroup.zmultiples (1 : ℝ))))
  apply hq.continuous_comp_iff.mp
  have he : descend u ∘ Pi.map (fun _ : Fin 3 ↦ (QuotientAddGroup.mk : ℝ → UnitAddCircle)) =
      fun r ↦ u (WithLp.toLp 2 r) :=
    funext fun r ↦ descend_torusPoint hu r
  rw [he]
  exact hc.comp (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous

theorem exists_bound {g : ℝ³ → ℝ} (hc : Continuous g) (hu : IsOnePeriodic g) :
    ∃ C, 0 ≤ C ∧ ∀ y, |descend g y| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_range (continuous_descend hc hu).abs).bddAbove
  exact ⟨max C 0, le_max_right _ _, fun y ↦ (hC ⟨y, rfl⟩).trans (le_max_left _ _)⟩

end Descent

section Coefficients

variable {g : ℝ³ → ℝ}

/-- The coordinate derivative `∂ⱼ g`. -/
def partialDeriv (j : Fin 3) (g : ℝ³ → ℝ) (x : ℝ³) : ℝ :=
  fderiv ℝ g x (EuclideanSpace.single j 1)

theorem isOnePeriodic_partialDeriv (hu : IsOnePeriodic g) (j : Fin 3) :
    IsOnePeriodic (partialDeriv j g) := by
  intro x i
  unfold partialDeriv
  have h : (fun y ↦ g (y + EuclideanSpace.single i 1)) = g := funext fun y ↦ hu y i
  rw [← fderiv_comp_add_right, h]

theorem contDiff_partialDeriv (hg : ContDiff ℝ ∞ g) (j : Fin 3) :
    ContDiff ℝ ∞ (partialDeriv j g) :=
  (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- The Fourier coefficients of a one-periodic scalar function. -/
def coeff (g : ℝ³ → ℝ) (k : Wavevector) : ℂ :=
  UnitAddTorus.mFourierCoeff (fun y ↦ ((descend g y : ℝ) : ℂ)) k

theorem shiftRate_descend (hg : ContDiff ℝ 1 g) (hu : IsOnePeriodic g) (j : Fin 3) :
    shiftRate (descend g) (coordinateShift j) = descend (partialDeriv j g) := by
  funext y
  obtain ⟨r, rfl⟩ := torusPoint_surjective y
  rw [descend_torusPoint (isOnePeriodic_partialDeriv hu j)]
  unfold shiftRate
  have e : (fun h ↦ descend g (torusPoint r + coordinateShift j h)) =
      fun h : ℝ ↦ g (WithLp.toLp 2 r + h • EuclideanSpace.single j 1) := by
    funext h
    rw [← LocalSpatialBottomProjector.torusPoint_add_single, descend_torusPoint hu]
    congr 1
  rw [e]
  have hd : HasDerivAt (fun h : ℝ ↦ WithLp.toLp 2 r + h • EuclideanSpace.single j (1 : ℝ))
      (EuclideanSpace.single j 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single j (1 : ℝ))).const_add
      (WithLp.toLp 2 r)
  have hg' : HasFDerivAt g (fderiv ℝ g (WithLp.toLp 2 r + (0 : ℝ) • EuclideanSpace.single j 1))
      (WithLp.toLp 2 r + (0 : ℝ) • EuclideanSpace.single j 1) :=
    (hg.differentiable one_ne_zero _).hasFDerivAt
  have h := (hg'.comp_hasDerivAt (0 : ℝ) hd).deriv
  simp only [zero_smul, add_zero] at h
  exact h

theorem locallyLipschitz_descend (hg : ContDiff ℝ 1 g) (hu : IsOnePeriodic g) :
    LocallyLipschitz (fun r : X3 ↦ descend g (torusPoint r)) := by
  have e : (fun r : X3 ↦ descend g (torusPoint r)) = fun r ↦ g (WithLp.toLp 2 r) :=
    funext fun r ↦ descend_torusPoint hu r
  rw [e]
  exact (hg.comp (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff).locallyLipschitz

/-- **Periodic integration by parts.** -/
theorem coeff_partialDeriv (hg : ContDiff ℝ ∞ g) (hu : IsOnePeriodic g) (j : Fin 3)
    (k : Wavevector) :
    coeff (partialDeriv j g) k = unitTorusDerivativePhase * (k j : ℂ) * coeff g k := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by simp)
  have h := PeriodicFourierWeakDerivative.mFourierCoeff_coordinateRate (descend g) j
    (continuous_descend hg.continuous hu) (locallyLipschitz_descend hg1 hu) k
  rw [shiftRate_descend hg1 hu j] at h
  exact h

theorem smooth_iterate (hg : ContDiff ℝ ∞ g) (hu : IsOnePeriodic g) (j : Fin 3) (n : ℕ) :
    ContDiff ℝ ∞ ((partialDeriv j)^[n] g) ∧ IsOnePeriodic ((partialDeriv j)^[n] g) := by
  induction n with
  | zero => exact ⟨hg, hu⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨contDiff_partialDeriv ih.1 j, isOnePeriodic_partialDeriv ih.2 j⟩

theorem coeff_iterate (hg : ContDiff ℝ ∞ g) (hu : IsOnePeriodic g) (j : Fin 3) (n : ℕ)
    (k : Wavevector) :
    coeff ((partialDeriv j)^[n] g) k = (unitTorusDerivativePhase * (k j : ℂ)) ^ n * coeff g k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := smooth_iterate hg hu j n
    rw [Function.iterate_succ_apply', coeff_partialDeriv hs.1 hs.2, ih, pow_succ]
    ring

theorem norm_coeff_le {C : ℝ} (hC : ∀ y, |descend g y| ≤ C) (k : Wavevector) :
    ‖coeff g k‖ ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := (volume : Measure T3))
    (f := fun y ↦ UnitAddTorus.mFourier (-k) y • ((descend g y : ℝ) : ℂ)) (C := C)
    (Eventually.of_forall fun y ↦ by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      calc ‖UnitAddTorus.mFourier (-k) y‖ * |descend g y| ≤ 1 * C :=
            mul_le_mul (((UnitAddTorus.mFourier (-k)).norm_coe_le_norm y).trans_eq
              UnitAddTorus.mFourier_norm) (hC y) (abs_nonneg _) zero_le_one
        _ = C := one_mul C)
  simpa [coeff, UnitAddTorus.mFourierCoeff] using h

theorem one_add_norm_pow_le (k : Wavevector) (N : ℕ) :
    ∃ j : Fin 3, (1 + ‖frequencyVec k‖) ^ N ≤ 3 ^ N * (1 + |(k j : ℝ)| ^ N) := by
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i ↦ |(k i : ℝ)|)
    Finset.univ_nonempty
  refine ⟨j, ?_⟩
  set a := |(k j : ℝ)| with ha
  have ha0 : 0 ≤ a := abs_nonneg _
  have hn : ‖frequencyVec k‖ ≤ 2 * a := by
    have hsq : ‖frequencyVec k‖ ^ 2 ≤ (2 * a) ^ 2 := by
      rw [norm_frequencyVec_sq, Fin.sum_univ_three]
      have h0 := hj 0 (Finset.mem_univ _)
      have h1 := hj 1 (Finset.mem_univ _)
      have h2 := hj 2 (Finset.mem_univ _)
      rw [← sq_abs (k 0 : ℝ), ← sq_abs (k 1 : ℝ), ← sq_abs (k 2 : ℝ)]
      have e0 := mul_le_mul h0 h0 (abs_nonneg _) ha0
      have e1 := mul_le_mul h1 h1 (abs_nonneg _) ha0
      have e2 := mul_le_mul h2 h2 (abs_nonneg _) ha0
      nlinarith [sq_nonneg a]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  calc (1 + ‖frequencyVec k‖) ^ N ≤ (1 + 2 * a) ^ N := by gcongr
    _ ≤ 3 ^ N * (1 + a ^ N) := by
      rcases le_total a 1 with h | h
      · calc (1 + 2 * a) ^ N ≤ 3 ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
          _ ≤ 3 ^ N * (1 + a ^ N) := le_mul_of_one_le_right (by positivity)
              (by linarith [pow_nonneg ha0 N])
      · calc (1 + 2 * a) ^ N ≤ (3 * a) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
          _ = 3 ^ N * a ^ N := mul_pow _ _ _
          _ ≤ 3 ^ N * (1 + a ^ N) := by gcongr; linarith

/-- **Rapid decay of the coefficients of a smooth periodic function.** -/
theorem coeff_decay (hg : ContDiff ℝ ∞ g) (hu : IsOnePeriodic g) (N : ℕ) :
    ∃ C, ∀ k, (1 + ‖frequencyVec k‖) ^ N * ‖coeff g k‖ ≤ C := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_bound hg.continuous hu
  have hb : ∀ j : Fin 3, ∃ C, 0 ≤ C ∧ ∀ k, |(k j : ℝ)| ^ N * ‖coeff g k‖ ≤ C := by
    intro j
    have hs := smooth_iterate hg hu j N
    obtain ⟨C, hC0, hC⟩ := exists_bound hs.1.continuous hs.2
    refine ⟨C, hC0, fun k ↦ ?_⟩
    have h := norm_coeff_le hC k
    rw [coeff_iterate hg hu j N k, norm_mul, norm_pow, norm_mul,
      PancakeIncomingLowSourceEnergy.norm_derivativePhase, Complex.norm_intCast] at h
    have h2 : (1 : ℝ) ≤ (2 * Real.pi) ^ N := one_le_pow₀ (by linarith [Real.pi_gt_three])
    calc |(k j : ℝ)| ^ N * ‖coeff g k‖ ≤ (2 * Real.pi) ^ N * (|(k j : ℝ)| ^ N * ‖coeff g k‖) :=
          le_mul_of_one_le_left (by positivity) h2
      _ = (2 * Real.pi * |(k j : ℝ)|) ^ N * ‖coeff g k‖ := by rw [mul_pow]; ring
      _ ≤ C := h
  choose C hC0 hC using hb
  refine ⟨3 ^ N * (C₀ + ∑ i, C i), fun k ↦ ?_⟩
  obtain ⟨j, hj⟩ := one_add_norm_pow_le k N
  have hg0 : ‖coeff g k‖ ≤ C₀ := norm_coeff_le hC₀ k
  have hCj : C j ≤ ∑ i, C i := Finset.single_le_sum (fun i _ ↦ hC0 i) (Finset.mem_univ j)
  calc (1 + ‖frequencyVec k‖) ^ N * ‖coeff g k‖
      ≤ 3 ^ N * (1 + |(k j : ℝ)| ^ N) * ‖coeff g k‖ :=
        mul_le_mul_of_nonneg_right hj (norm_nonneg _)
    _ = 3 ^ N * (‖coeff g k‖ + |(k j : ℝ)| ^ N * ‖coeff g k‖) := by ring
    _ ≤ 3 ^ N * (C₀ + ∑ i, C i) := by
        gcongr
        exact (hC j k).trans hCj

end Coefficients

section Vector

variable {u : ℝ³ → ℝ³}

theorem contDiff_component (hs : ContDiff ℝ ∞ u) (i : Fin 3) : ContDiff ℝ ∞ (fun x ↦ u x i) :=
  (EuclideanSpace.proj i : ℝ³ →L[ℝ] ℝ).contDiff.comp hs

theorem isOnePeriodic_component (hp : IsOnePeriodic u) (i : Fin 3) :
    IsOnePeriodic (fun x ↦ u x i) := fun x j ↦ by simp only [hp x j]

/-- The Fourier coefficients of a one-periodic velocity. -/
def coeffVec (u : ℝ³ → ℝ³) : FourierVelocity := fun k i ↦ coeff (fun x ↦ u x i) k

theorem rapid_coeffVec (hs : ContDiff ℝ ∞ u) (hp : IsOnePeriodic u) : Rapid (coeffVec u) := by
  intro N
  choose C hC using fun i : Fin 3 ↦
    coeff_decay (contDiff_component hs i) (isOnePeriodic_component hp i) N
  refine ⟨C 0 + C 1 + C 2, fun k ↦ ?_⟩
  unfold fourierMoment
  refine (mul_le_mul_of_nonneg_left (norm_le_sum_components _) (by positivity)).trans ?_
  rw [Finset.mul_sum, Fin.sum_univ_three]
  exact add_le_add (add_le_add (hC 0 k) (hC 1 k)) (hC 2 k)

theorem isReal_coeffVec : IsReal (coeffVec u) := by
  intro k
  ext i
  have h := Mettapedia.Analysis.UnitTorusFourierReal.mFourierCoeff_conj
    (fun y ↦ ((descend (fun x ↦ u x i) y : ℝ) : ℂ)) (-k)
  simp only [Complex.conj_ofReal, neg_neg] at h
  change coeff (fun x ↦ u x i) (-k) = conj (coeff (fun x ↦ u x i) k)
  exact h

theorem partialDeriv_component (hs : ContDiff ℝ ∞ u) (i j : Fin 3) (x : ℝ³) :
    partialDeriv j (fun y ↦ u y i) x = fderiv ℝ u x (EuclideanSpace.single j 1) i := by
  have hd : HasFDerivAt u (fderiv ℝ u x) x := (hs.differentiable (by simp) x).hasFDerivAt
  have h := ((EuclideanSpace.proj i : ℝ³ →L[ℝ] ℝ).hasFDerivAt.comp x hd).fderiv
  unfold partialDeriv
  change fderiv ℝ ((EuclideanSpace.proj i : ℝ³ →L[ℝ] ℝ) ∘ u) x _ = _
  rw [h]
  rfl

theorem coeff_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ³ → ℝ)
    (hc : ∀ i ∈ s, Continuous (f i)) (hp : ∀ i ∈ s, IsOnePeriodic (f i)) (k : Wavevector) :
    coeff (fun x ↦ ∑ i ∈ s, f i x) k = ∑ i ∈ s, coeff (f i) k := by
  unfold coeff UnitAddTorus.mFourierCoeff
  have he : ∀ y, ((descend (fun x ↦ ∑ i ∈ s, f i x) y : ℝ) : ℂ) = ∑ i ∈ s, ((descend (f i) y : ℝ) : ℂ) := by
    intro y
    simp [descend]
  simp only [he, Finset.smul_sum]
  exact integral_finsetSum s fun i hi ↦
    ((UnitAddTorus.mFourier (-k)).continuous.smul
      (Complex.continuous_ofReal.comp (continuous_descend (hc i hi) (hp i hi)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem coeff_zero_fun (k : Wavevector) : coeff (fun _ ↦ (0 : ℝ)) k = 0 := by
  simp [coeff, descend, UnitAddTorus.mFourierCoeff]

/-- **Divergence-free velocities have transverse coefficients.** -/
theorem transverse_coeffVec (hs : ContDiff ℝ ∞ u) (hp : IsOnePeriodic u)
    (hdiv : ∀ x, divergence u x = 0) (k : Wavevector) : modeDot k (coeffVec u k) = 0 := by
  have hsum : coeff (fun x ↦ ∑ i : Fin 3, partialDeriv i (fun y ↦ u y i) x) k = 0 := by
    have e : (fun x ↦ ∑ i : Fin 3, partialDeriv i (fun y ↦ u y i) x) = fun _ ↦ (0 : ℝ) := by
      funext x
      rw [← hdiv x, divergence_eq]
      exact Finset.sum_congr rfl fun i _ ↦ partialDeriv_component hs i i x
    rw [e, coeff_zero_fun]
  rw [coeff_sum _ _ (fun i _ ↦ (contDiff_partialDeriv (contDiff_component hs i) i).continuous)
    (fun i _ ↦ isOnePeriodic_partialDeriv (isOnePeriodic_component hp i) i)] at hsum
  have e3 : ∀ i : Fin 3, coeff (partialDeriv i (fun y ↦ u y i)) k =
      unitTorusDerivativePhase * (k i : ℂ) * coeff (fun x ↦ u x i) k := fun i ↦
    coeff_partialDeriv (contDiff_component hs i) (isOnePeriodic_component hp i) i k
  simp only [e3] at hsum
  have hph := unitTorusDerivativePhase_ne_zero
  rw [modeDot]
  have e2 : ∑ i : Fin 3, unitTorusDerivativePhase * (k i : ℂ) * coeff (fun x ↦ u x i) k =
      unitTorusDerivativePhase * ∑ i : Fin 3, (k i : ℂ) * coeffVec u k i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by simp only [coeffVec]; ring
  rw [e2] at hsum
  exact (mul_eq_zero.mp hsum).resolve_left hph

/-- **Fourier inversion.** A smooth one-periodic velocity is the real field of
its coefficients. -/
theorem realField_coeffVec (hs : ContDiff ℝ ∞ u) (hp : IsOnePeriodic u) (x : ℝ³) :
    realField (coeffVec u) x = u x := by
  have hr := rapid_coeffVec hs hp
  ext i
  rw [realField_apply, field_apply hr]
  let F : C(T3, ℂ) := ⟨fun y ↦ ((descend (fun z ↦ u z i) y : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (continuous_descend (contDiff_component hs i).continuous
      (isOnePeriodic_component hp i))⟩
  have hsum : Summable (UnitAddTorus.mFourierCoeff F) := by
    obtain ⟨C, hC⟩ := hr 4
    refine (summable_latticeDecayWeight.mul_left C).of_norm_bounded fun k ↦ ?_
    have h1 := (norm_le_moment (coeffVec u) 0 k).trans (fourierMoment_le_decay (n := 0) hC k)
    have h2 : ‖coeffVec u k i‖ ≤ ‖coeffVec u k‖ := norm_le_pi_norm _ i
    simp only [pow_zero, one_mul] at h1
    exact h2.trans h1
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsum
    (torusPoint (WithLp.ofLp x))
  have hF : F (torusPoint (WithLp.ofLp x)) = (u x i : ℂ) := by
    change ((descend (fun z ↦ u z i) (torusPoint (WithLp.ofLp x)) : ℝ) : ℂ) = _
    rw [descend_torusPoint (isOnePeriodic_component hp i)]
  rw [hF] at h
  have e : ∀ k, UnitAddTorus.mFourierCoeff F k • UnitAddTorus.mFourier k (torusPoint (WithLp.ofLp x)) =
      character k x * coeffVec u k i := by
    intro k
    rw [character_eq_mFourier, smul_eq_mul, mul_comm]
    rfl
  simp only [e] at h
  rw [h.tsum_eq, Complex.ofReal_re]

end Vector

section ZeroMean

variable {u : ℝ³ → ℝ³}

/-- The mean of a one-periodic velocity. -/
def meanOf (u : ℝ³ → ℝ³) : ℝ³ := complexRealPartEuclideanCLM (coeffVec u 0)

/-- The Fourier data of the fluctuation `u - mean`. -/
def fluctuation (u : ℝ³ → ℝ³) : FourierVelocity := coeffVec u - single0 (coeffVec u 0)

theorem fluctuation_zero : fluctuation u 0 = 0 := by
  simp [fluctuation]

theorem fluctuation_of_ne {q : Wavevector} (hq : q ≠ 0) : fluctuation u q = coeffVec u q := by
  simp [fluctuation, single0_of_ne _ hq]

theorem rapid_fluctuation (hs : ContDiff ℝ ∞ u) (hp : IsOnePeriodic u) : Rapid (fluctuation u) := by
  intro n
  obtain ⟨C, hC⟩ := rapid_coeffVec hs hp n
  refine ⟨C, fun k ↦ ?_⟩
  by_cases hk : k = 0
  · subst hk
    have h0 : fourierMoment n (fluctuation u) 0 = 0 := by
      simp [fourierMoment, fluctuation_zero, coefficientVec]
    rw [h0]
    exact (fourierMoment_nonneg n _ 0).trans (hC 0)
  · have e : fourierMoment n (fluctuation u) k = fourierMoment n (coeffVec u) k := by
      simp [fourierMoment, fluctuation_of_ne hk]
    rw [e]
    exact hC k

theorem isReal_fluctuation : IsReal (fluctuation u) := by
  intro k
  by_cases hk : k = 0
  · subst hk
    rw [neg_zero, fluctuation_zero]
    ext i
    simp [coefficientConjugate]
  · rw [fluctuation_of_ne (neg_ne_zero.mpr hk), fluctuation_of_ne hk, isReal_coeffVec k]

theorem transverse_fluctuation (hs : ContDiff ℝ ∞ u) (hp : IsOnePeriodic u)
    (hdiv : ∀ x, divergence u x = 0) (k : Wavevector) : modeDot k (fluctuation u k) = 0 := by
  by_cases hk : k = 0
  · subst hk
    simp [fluctuation_zero, modeDot]
  · rw [fluctuation_of_ne hk]
    exact transverse_coeffVec hs hp hdiv k

theorem latticeDecayWeight_le_one (k : Wavevector) : latticeDecayWeight k ≤ 1 := by
  unfold latticeDecayWeight
  rw [div_le_one (by positivity)]
  exact one_le_pow₀ (by linarith [norm_nonneg (frequencyVec k)])

/-- Rapid data have bounded Sobolev energies of every order. -/
theorem velocityEnergy_le_of_rapid {a : FourierVelocity} (ha : Rapid a) (n : ℕ) :
    ∃ E, ∀ F, velocityEnergy n F a ≤ E := by
  obtain ⟨C, hC⟩ := ha (n + 4)
  have hw : Summable (fun k ↦ C ^ 2 * latticeDecayWeight k) :=
    summable_latticeDecayWeight.mul_left _
  refine ⟨∑' k, C ^ 2 * latticeDecayWeight k, fun F ↦ ?_⟩
  rw [velocityEnergy_eq]
  refine le_trans (Finset.sum_le_sum fun k _ ↦ ?_) (hw.sum_le_tsum F fun k _ ↦ ?_)
  swap
  · have : 0 ≤ latticeDecayWeight k := by unfold latticeDecayWeight; positivity
    positivity
  have h1 := fourierMoment_le_decay hC k
  have h0 := fourierMoment_nonneg n a k
  have hC0 : 0 ≤ C := (fourierMoment_nonneg _ _ _).trans (hC k)
  have hw1 := latticeDecayWeight_le_one k
  have hw0 : 0 ≤ latticeDecayWeight k := by unfold latticeDecayWeight; positivity
  have e : orderWeight n k ^ 2 * coefficientEnergy (a k) = fourierMoment n a k ^ 2 := by
    rw [← norm_coefficientVec_sq]
    unfold fourierMoment PancakeHigherSobolevWeights.orderWeight
    ring
  rw [e]
  calc fourierMoment n a k ^ 2 ≤ (C * latticeDecayWeight k) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = C ^ 2 * (latticeDecayWeight k * latticeDecayWeight k) := by ring
    _ ≤ C ^ 2 * latticeDecayWeight k := by
        gcongr
        exact mul_le_of_le_one_left hw0 hw1

/-- **The fluctuation data are admissible of every order.** -/
theorem admissible_fluctuation (h : InitialVelocityConditionPeriodic u) (n : ℕ) :
    Admissible n (fluctuation u) :=
  ⟨isReal_fluctuation, transverse_fluctuation h.smooth h.isOnePeriodic h.div_free,
    fluctuation_zero, velocityEnergy_le_of_rapid (rapid_fluctuation h.smooth h.isOnePeriodic) n⟩

/-- **The velocity is its mean plus the field of the fluctuation.** -/
theorem eq_mean_add_realField (hs : ContDiff ℝ ∞ u) (hp : IsOnePeriodic u) (x : ℝ³) :
    u x = meanOf u + realField (fluctuation u) x := by
  have e : coeffVec u = fluctuation u + single0 (coeffVec u 0) := by
    simp [fluctuation]
  rw [← realField_coeffVec hs hp x, e]
  unfold realField meanOf
  rw [field_add (rapid_fluctuation hs hp) (rapid_single _), field_single, map_add, add_comm]

end ZeroMean

end Mettapedia.FluidDynamics.NavierStokes.FourierInitialData
