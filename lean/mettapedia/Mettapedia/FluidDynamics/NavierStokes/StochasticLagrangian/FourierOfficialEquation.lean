import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierSpatialCalculus
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfinitePressureCoefficients
import Mettapedia.FluidDynamics.NavierStokes.OfficialPeriodicProblem

/-!
# Fourier solutions solve the official periodic equations

A coefficient curve that is continuous, real, transverse, rapidly decaying on
bounded time intervals and solves the Fourier system at positive times defines
the physical velocity

```text
v(x, t) = Re ∑ₖ exp(2π i ⟨k, x⟩) cₖ(t)
```

and the physical pressure with coefficients `p̂_q = -(q · conv_q) / |q|²`.
This pair solves the Navier–Stokes equations pointwise on `ℝ³ × [0, ∞)` in the
form of the official statement: one-sided time derivative at `t = 0`, the
transport term `Dv(x) v(x)`, the Laplacian, the pressure gradient, zero force,
divergence-free velocity, smoothness up to the initial time, and
one-periodicity of velocity and pressure.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierOfficialEquation

open scoped BigOperators Topology ContDiff Laplacian ComplexConjugate Gradient
open Set Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeLatticeDecayEnvelope PancakeFourierMaterialPaths
open PancakeDyadicDirectionEvolution PancakePeriodicVorticityEquation PancakePeriodicComplexStretch
open PancakeBlockReality PancakeCoefficientLimitEquation PancakeSobolevFiberEnvelope
open PancakeInfinitePressureCoefficients
open FourierTimeRegularity FourierPhysicalFields FourierSpatialCalculus OfficialPeriodicProblem

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

section Time

theorem norm_le_decay_of_rapidOn {a : ℝ → FourierVelocity} {s : Set ℝ} (ha : RapidOn a s) :
    ∃ C, ∀ t ∈ s, ∀ k, ‖a t k‖ ≤ C * latticeDecayWeight k := by
  obtain ⟨C, hC⟩ := ha 4
  refine ⟨C, fun t ht k ↦ ?_⟩
  have h := (norm_le_moment (a t) 0 k).trans (fourierMoment_le_decay (n := 0)
    (fun k ↦ hC t ht k) k)
  simpa using h

/-- **Termwise time derivative of the field.** -/
theorem hasDerivWithinAt_field {S : ℝ} (hS : 0 < S) {a a' : ℝ → FourierVelocity}
    (ha : ContOn a (Icc 0 S) ∧ RapidOn a (Icc 0 S))
    (ha' : ContOn a' (Icc 0 S) ∧ RapidOn a' (Icc 0 S))
    (hd : ∀ t ∈ Icc (0 : ℝ) S, ∀ k i,
      HasDerivWithinAt (fun τ ↦ a τ k i) (a' t k i) (Icc 0 S) t)
    (x : ℝ³) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) :
    HasDerivWithinAt (fun τ ↦ field (a τ) x) (field (a' t) x) (Icc 0 S) t := by
  obtain ⟨C, hC⟩ := norm_le_decay_of_rapidOn ha.2
  obtain ⟨C', hC'⟩ := norm_le_decay_of_rapidOn ha'.2
  have h := hasDerivWithinAt_tsum_Icc hS (g := fun k τ ↦ character k x • a τ k)
    (g' := fun k τ ↦ character k x • a' τ k) (summable_latticeDecayWeight.mul_left C')
    (fun k τ hτ ↦ (hasDerivWithinAt_mode (hd τ hτ) k).const_smul (character k x))
    (fun k ↦ (continuousOn_pi.mpr fun i ↦ ha'.1 k i).const_smul (character k x))
    (fun k τ hτ ↦ by rw [norm_smul, norm_character, one_mul]; exact hC' τ hτ k)
    (continuousOn_tsum (fun k ↦ (continuousOn_pi.mpr fun i ↦ ha.1 k i).const_smul (character k x))
      (summable_latticeDecayWeight.mul_left C)
      (fun k τ hτ ↦ by rw [norm_smul, norm_character, one_mul]; exact hC τ hτ k))
    (fun τ hτ ↦ summable_term (rapid_of_rapidOn ha.2 hτ) x) ht
  exact h

/-- One-sided derivatives within `[0, S]` are one-sided derivatives within
`[0, ∞)` before `S`. -/
theorem hasDerivWithinAt_Ici_of_Icc {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {f' : F} {S t : ℝ} (h : HasDerivWithinAt f f' (Icc 0 S) t) (ht : t < S) :
    HasDerivWithinAt f f' (Ici 0) t := by
  refine h.mono_of_mem_nhdsWithin ?_
  have hI : Iic S ∈ 𝓝 t := Iic_mem_nhds ht
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hI] with τ h1 h2
  exact ⟨h1, h2⟩

end Time

section Hypotheses

variable {nu : ℝ} {c : ℝ → FourierVelocity}

/-- The hypotheses satisfied by the coefficient curve of a smooth global
Fourier solution. -/
structure FourierSolution (nu : ℝ) (c : ℝ → FourierVelocity) : Prop where
  continuous : ∀ k i, Continuous (fun t ↦ c t k i)
  rapid : ∀ S, 0 < S → RapidOn c (Icc 0 S)
  reality : ∀ t q, c t (-q) = coefficientConjugate (c t q)
  transverse : ∀ t q, modeDot q (c t q) = 0
  equation : ∀ t, 0 < t → ∀ q i,
    HasDerivAt (fun τ ↦ c τ q i) (infiniteVelocityRHS nu (c t) q i) t

theorem FourierSolution.smoothRapid (h : FourierSolution nu c) {S : ℝ} (hS : 0 < S) :
    ∀ j, SmoothRapid j c (Icc 0 S) :=
  smoothRapid_of_solution hS (lt_add_one S) h.continuous (h.rapid S hS)
    fun t ht q i ↦ h.equation t ht.1 q i

theorem FourierSolution.hasDerivWithinAt (h : FourierSolution nu c) {S : ℝ} (hS : 0 < S) :
    ∀ t ∈ Icc (0 : ℝ) S, ∀ q i, HasDerivWithinAt (fun τ ↦ c τ q i)
      (rhsCurve nu c t q i) (Icc 0 S) t :=
  hasDerivWithinAt_of_solution hS (lt_add_one S) h.continuous (h.rapid S hS)
    fun t ht q i ↦ h.equation t ht.1 q i

theorem FourierSolution.rapidAt (h : FourierSolution nu c) {t : ℝ} (ht : 0 ≤ t) :
    Rapid (c t) :=
  rapid_of_rapidOn (h.rapid (t + 1) (by linarith)) ⟨ht, by linarith⟩

theorem FourierSolution.isReal (h : FourierSolution nu c) (t : ℝ) : IsReal (c t) :=
  h.reality t

end Hypotheses

section Pressure

/-- The pressure symbol `v ↦ -(q · v) / |q|²`, stored in the first slot. -/
def pressureMap (q : Wavevector) : VelocityCoefficient →L[ℂ] VelocityCoefficient :=
  ((-(modeSquare q)⁻¹) • modeDotCLM q).smulRight (Pi.single 0 1)

theorem pressureMap_apply (q : Wavevector) (v : VelocityCoefficient) :
    pressureMap q v = Pi.single 0 (-modeDot q v / modeSquare q) := by
  ext i
  simp only [pressureMap, ContinuousLinearMap.smulRight_apply]
  by_cases hi : i = 0
  · subst hi
    simp [modeDotCLM_apply]
    ring
  · simp [hi]

theorem norm_pressureScalar_le (q : Wavevector) (v : VelocityCoefficient) :
    ‖-modeDot q v / modeSquare q‖ ≤ ‖coefficientVec v‖ := by
  by_cases hq : q = 0
  · subst q
    simp [modeSquare]
  · have h1 := one_le_norm_frequencyVec hq
    have hpos : 0 < ‖frequencyVec q‖ := by linarith
    rw [norm_div, norm_neg, FourierTimeRegularity.norm_modeSquare,
      div_le_iff₀ (by positivity)]
    have h := PancakeLowPressureBudget.norm_modeDot_le q v
    calc ‖modeDot q v‖ ≤ ‖frequencyVec q‖ * ‖coefficientVec v‖ := h
      _ = ‖coefficientVec v‖ * ‖frequencyVec q‖ * 1 := by ring
      _ ≤ ‖coefficientVec v‖ * ‖frequencyVec q‖ * ‖frequencyVec q‖ :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ‖coefficientVec v‖ * ‖frequencyVec q‖ ^ 2 := by ring

theorem norm_pressureMap_le (q : Wavevector) (v : VelocityCoefficient) :
    ‖coefficientVec (pressureMap q v)‖ ≤ 1 * (1 + ‖frequencyVec q‖) ^ 0 * ‖coefficientVec v‖ := by
  rw [pow_zero, one_mul, one_mul, pressureMap_apply]
  have h : coefficientVec (Pi.single 0 (-modeDot q v / modeSquare q)) =
      EuclideanSpace.single 0 (-modeDot q v / modeSquare q) := by
    ext i
    simp [coefficientVec]
  rw [h, PiLp.norm_single]
  exact norm_pressureScalar_le q v

/-- The pressure coefficient curve, in the first slot. -/
def pressureCurve (c : ℝ → FourierVelocity) : ℝ → FourierVelocity :=
  fun t q ↦ pressureMap q (convCurve c c t q)

theorem pressureCurve_apply (c : ℝ → FourierVelocity) (t : ℝ) (q : Wavevector) :
    pressureCurve c t q 0 = infinitePressureCoeff (c t) q := by
  simp [pressureCurve, pressureMap_apply, convCurve, conv_self, infinitePressureCoeff]

/-- The physical pressure. -/
def physPressure (c : ℝ → FourierVelocity) (x : ℝ³) (t : ℝ) : ℝ :=
  physVelocity (pressureCurve c) x t 0

theorem SmoothRapid.pressureCurve {S : ℝ} (hS : 0 < S) {c : ℝ → FourierVelocity} {j : ℕ}
    (hc : SmoothRapid j c (Icc 0 S)) : SmoothRapid j (pressureCurve c) (Icc 0 S) :=
  SmoothRapid.map_mode pressureMap zero_le_one norm_pressureMap_le
    (SmoothRapid.convCurve hS hc hc)

/-- **Smoothness of the pressure on `ℝ³ × [0, ∞)`.** -/
theorem contDiffOn_physPressure {c : ℝ → FourierVelocity}
    (hc : ∀ S, 0 < S → ∀ j, SmoothRapid j c (Icc 0 S)) :
    ContDiffOn ℝ ∞ (↿(physPressure c)) (univ ×ˢ Ici 0) := by
  have h := contDiffOn_physVelocity fun S hS j ↦ SmoothRapid.pressureCurve hS (hc S hS j)
  exact (EuclideanSpace.proj (0 : Fin 3) : ℝ³ →L[ℝ] ℝ).contDiff.comp_contDiffOn h

end Pressure

section Calculus

theorem gradient_apply (f : ℝ³ → ℝ) (x : ℝ³) (i : Fin 3) :
    ∇ f x i = fderiv ℝ f x (EuclideanSpace.single i 1) := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := ℝ³)
    (x := EuclideanSpace.single i 1) (y := fderiv ℝ f x)
  rw [EuclideanSpace.inner_single_right, one_mul] at h
  simpa [gradient] using h

theorem divergence_eq (v : ℝ³ → ℝ³) (x : ℝ³) :
    divergence v x = ∑ i, fderiv ℝ v x (EuclideanSpace.single i 1) i := by
  unfold divergence
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  simp [Matrix.trace, LinearMap.toMatrix_apply]

theorem re_tsum {f : Wavevector → ℂ} (hf : Summable f) : (∑' k, f k).re = ∑' k, (f k).re :=
  Complex.reCLM.map_tsum hf

end Calculus

section Equation

variable {nu : ℝ} {c : ℝ → FourierVelocity}

theorem physVelocity_slice (c : ℝ → FourierVelocity) (t : ℝ) :
    (fun x ↦ physVelocity c x t) = realField (c t) := rfl

/-- **The one-sided time derivative of the velocity.** -/
theorem derivWithin_physVelocity (h : FourierSolution nu c) (x : ℝ³) {t : ℝ} (ht : 0 ≤ t) :
    derivWithin (fun τ ↦ physVelocity c x τ) (Ici 0) t = realField (rhsCurve nu c t) x := by
  have hS : (0 : ℝ) < t + 1 := by linarith
  have hsr := h.smoothRapid hS
  have hrhs := SmoothRapid.rhsCurve hS nu (hsr 0)
  have hd := hasDerivWithinAt_field hS ⟨(hsr 0).1, (hsr 0).2⟩ ⟨hrhs.1, hrhs.2⟩
    (h.hasDerivWithinAt hS) x ⟨ht, by linarith⟩
  have hd' := hasDerivWithinAt_Ici_of_Icc
    (complexRealPartEuclideanCLM.hasFDerivAt.comp_hasDerivWithinAt t hd) (lt_add_one t)
  exact hd'.derivWithin (uniqueDiffOn_Ici 0 t ht)

/-- **The transport term.** -/
theorem transport_physVelocity (h : FourierSolution nu c) (x : ℝ³) {t : ℝ} (ht : 0 ≤ t) :
    fderiv ℝ (fun y ↦ physVelocity c y t) x (physVelocity c x t) =
      complexRealPartEuclideanCLM
        (unitTorusDerivativePhase • field (infiniteConvection (c t)) x) := by
  have ha := h.rapidAt ht
  rw [physVelocity_slice, fderiv_realField_apply ha, physVelocity_eq]
  have e : (fun k ↦ (unitTorusDerivativePhase *
      (modeFunctional k (realField (c t) x) : ℂ)) • c t k) =
      fun k ↦ (unitTorusDerivativePhase * modeDot k (field (c t) x)) • c t k := by
    funext k
    rw [modeFunctional_realField ha (h.isReal t)]
  rw [e, field_transport ha (h.transverse t) x]

/-- **The Laplacian of the velocity.** -/
theorem laplacian_physVelocity (h : FourierSolution nu c) (x : ℝ³) {t : ℝ} (ht : 0 ≤ t) :
    Δ (fun y ↦ physVelocity c y t) x = complexRealPartEuclideanCLM (field (lapCoeff (c t)) x) := by
  rw [physVelocity_slice, laplacian_realField (h.rapidAt ht)]

theorem FourierSolution.pressureRapid (h : FourierSolution nu c) {t : ℝ} (ht : 0 ≤ t) :
    Rapid (pressureCurve c t) := by
  have hS : (0 : ℝ) < t + 1 := by linarith
  exact rapid_of_rapidOn (SmoothRapid.pressureCurve hS (h.smoothRapid hS 0)).2 ⟨ht, by linarith⟩

/-- **The pressure gradient.** -/
theorem gradient_physPressure (h : FourierSolution nu c) (x : ℝ³) {t : ℝ} (ht : 0 ≤ t)
    (i : Fin 3) :
    ∇ (fun y ↦ physPressure c y t) x i =
      (∑' q, character q x * (unitTorusDerivativePhase * (q i : ℂ) *
        infinitePressureCoeff (c t) q)).re := by
  have hP := h.pressureRapid ht
  have e : (fun y ↦ physPressure c y t) =
      (EuclideanSpace.proj (0 : Fin 3) : ℝ³ →L[ℝ] ℝ) ∘ realField (pressureCurve c t) := rfl
  have hd : HasFDerivAt (realField (pressureCurve c t))
      (fderiv ℝ (realField (pressureCurve c t)) x) x :=
    ((contDiff_realField hP).differentiable (by simp) x).hasFDerivAt
  rw [gradient_apply, e, ((EuclideanSpace.proj (0 : Fin 3) : ℝ³ →L[ℝ] ℝ).hasFDerivAt.comp x
    hd).fderiv, ContinuousLinearMap.comp_apply, fderiv_realField_apply hP]
  change (complexRealPartEuclideanCLM _) 0 = _
  rw [realPart_apply, field_apply (hP.smul_poly (K := 2 * Real.pi) (d := 1) ?_)]
  · congr 1
    refine tsum_congr fun q ↦ ?_
    rw [Pi.smul_apply, pressureCurve_apply, modeFunctional_single, smul_eq_mul]
    push_cast
    ring
  · intro q
    rw [norm_mul, PancakeIncomingLowSourceEnergy.norm_derivativePhase, Complex.norm_real,
      Real.norm_eq_abs, modeFunctional_single, pow_one]
    exact mul_le_mul_of_nonneg_left ((abs_coord_le q i).trans (by linarith)) (by positivity)

/-- **The velocity is divergence free.** -/
theorem divergence_physVelocity (h : FourierSolution nu c) (x : ℝ³) {t : ℝ} (ht : 0 ≤ t) :
    divergence (fun y ↦ physVelocity c y t) x = 0 := by
  have ha := h.rapidAt ht
  have hr : ∀ i : Fin 3, Rapid (fun k ↦ (unitTorusDerivativePhase *
      (modeFunctional k (EuclideanSpace.single i 1) : ℂ)) • c t k) := fun i ↦
    ha.smul_poly (K := 2 * Real.pi) (d := 1) fun q ↦ by
      rw [norm_mul, PancakeIncomingLowSourceEnergy.norm_derivativePhase, Complex.norm_real,
        Real.norm_eq_abs, modeFunctional_single, pow_one]
      exact mul_le_mul_of_nonneg_left ((abs_coord_le q i).trans (by linarith)) (by positivity)
  rw [divergence_eq, physVelocity_slice]
  simp only [fderiv_realField_apply ha, realPart_apply, field_apply (hr _)]
  rw [← Complex.re_sum, ← Summable.tsum_finsetSum (f := fun i k ↦ character k x *
      ((unitTorusDerivativePhase * (modeFunctional k (EuclideanSpace.single i 1) : ℂ)) • c t k) i)
    fun i _ ↦ (Pi.summable.mp (summable_term (hr i) x) i).congr fun k ↦ rfl]
  have hz : ∀ k, ∑ i : Fin 3, character k x * ((unitTorusDerivativePhase *
      (modeFunctional k (EuclideanSpace.single i 1) : ℂ)) • c t k) i = 0 := by
    intro k
    have htr := h.transverse t k
    simp only [Pi.smul_apply, smul_eq_mul, modeFunctional_single]
    rw [modeDot] at htr
    simp only [Fin.sum_univ_three] at htr ⊢
    push_cast
    linear_combination character k x * unitTorusDerivativePhase * htr
  simp only [hz, tsum_zero, Complex.zero_re]

/-- Rapid decay transfers along pointwise bounds of polynomial growth. -/
theorem Rapid.of_le {a b : FourierVelocity} (ha : Rapid a) {K : ℝ} {d : ℕ}
    (hb : ∀ q, ‖coefficientVec (b q)‖ ≤ K * (1 + ‖frequencyVec q‖) ^ d * ‖coefficientVec (a q)‖) :
    Rapid b := by
  intro n
  obtain ⟨C, hC⟩ := ha (n + d)
  refine ⟨max K 0 * C, fun q ↦ ?_⟩
  have hK : K ≤ max K 0 := le_max_left _ _
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  have hC0 : 0 ≤ C := (fourierMoment_nonneg _ _ _).trans (hC 0)
  unfold fourierMoment
  have hq : (1 + ‖frequencyVec q‖) ^ (n + d) * ‖coefficientVec (a q)‖ ≤ C := hC q
  calc (1 + ‖frequencyVec q‖) ^ n * ‖coefficientVec (b q)‖
      ≤ (1 + ‖frequencyVec q‖) ^ n * (max K 0 * (1 + ‖frequencyVec q‖) ^ d *
          ‖coefficientVec (a q)‖) := by
        gcongr
        exact (hb q).trans (by gcongr)
    _ = max K 0 * ((1 + ‖frequencyVec q‖) ^ (n + d) * ‖coefficientVec (a q)‖) := by ring
    _ ≤ max K 0 * C := by gcongr

theorem field_sub {a b : FourierVelocity} (ha : Rapid a) (hb : Rapid b) (x : ℝ³) :
    field (a - b) x = field a x - field b x := by
  unfold field
  rw [← (summable_term ha x).tsum_sub (summable_term hb x)]
  simp only [Pi.sub_apply, smul_sub]

/-- The Fourier coefficients of the pressure gradient. -/
def gradCoeff (u : FourierVelocity) : FourierVelocity :=
  fun q j ↦ unitTorusDerivativePhase * (q j : ℂ) * infinitePressureCoeff u q

theorem rapid_gradCoeff {u : FourierVelocity} (hu : Rapid (infiniteConvection u)) :
    Rapid (gradCoeff u) := by
  refine Rapid.of_le hu (K := 2 * Real.pi) (d := 1) fun q ↦ ?_
  have e : coefficientVec (gradCoeff u q) =
      (unitTorusDerivativePhase * infinitePressureCoeff u q) • frequencyVec q := by
    ext j
    simp [gradCoeff, coefficientVec, frequencyVec, wavevectorCoefficient]
    ring
  rw [e, norm_smul, norm_mul, PancakeIncomingLowSourceEnergy.norm_derivativePhase, pow_one]
  have h1 := norm_infinitePressureCoeff_le u q
  have h2 : ‖frequencyVec q‖ ≤ 1 + ‖frequencyVec q‖ := by linarith
  calc 2 * Real.pi * ‖infinitePressureCoeff u q‖ * ‖frequencyVec q‖
      ≤ 2 * Real.pi * ‖coefficientVec (infiniteConvection u q)‖ * (1 + ‖frequencyVec q‖) := by
        gcongr
    _ = _ := by ring

theorem FourierSolution.convRapid (h : FourierSolution nu c) {t : ℝ} (ht : 0 ≤ t) :
    Rapid (infiniteConvection (c t)) := by
  have hS : (0 : ℝ) < t + 1 := by linarith
  exact rapid_of_rapidOn (SmoothRapid.convCurve hS (h.smoothRapid hS 0)
    (h.smoothRapid hS 0)).2 ⟨ht, by linarith⟩

theorem FourierSolution.rhsRapid (h : FourierSolution nu c) {t : ℝ} (ht : 0 ≤ t) :
    Rapid (rhsCurve nu c t) := by
  have hS : (0 : ℝ) < t + 1 := by linarith
  exact rapid_of_rapidOn (SmoothRapid.rhsCurve hS nu (h.smoothRapid hS 0)).2 ⟨ht, by linarith⟩

/-- **The pressure gradient as a real field.** -/
theorem gradient_physPressure_eq (h : FourierSolution nu c) (x : ℝ³) {t : ℝ} (ht : 0 ≤ t) :
    ∇ (fun y ↦ physPressure c y t) x = realField (gradCoeff (c t)) x := by
  ext j
  rw [gradient_physPressure h x ht, realField_apply,
    field_apply (rapid_gradCoeff (h.convRapid ht))]
  rfl

/-- **The coefficient identity.** The Fourier system is the equation
`∂ₜv + (v · ∇)v = ν Δv - ∇p` mode by mode, with the pressure coefficients
`p̂_q = -(q · conv_q) / |q|²`. -/
theorem rhs_add_convection (nu : ℝ) (u : FourierVelocity) (q : Wavevector) :
    infiniteVelocityRHS nu u q + unitTorusDerivativePhase • infiniteConvection u q =
      (nu : ℂ) • lapCoeff u q - gradCoeff u q := by
  ext j
  by_cases hq : modeSquare q = 0
  · have hl : lerayMode q ((-unitTorusDerivativePhase) • infiniteConvection u q) =
        (-unitTorusDerivativePhase) • infiniteConvection u q := by
      unfold lerayMode
      exact dite_eq_left hq
    simp only [infiniteVelocityRHS, hl, Pi.add_apply, unitTorusViscousVorticityCoeff,
      Pi.smul_apply, smul_eq_mul, lapCoeff, gradCoeff, infinitePressureCoeff, Pi.sub_apply, hq,
      div_zero]
    ring
  · have hl : lerayMode q ((-unitTorusDerivativePhase) • infiniteConvection u q) =
        fun i ↦ ((-unitTorusDerivativePhase) • infiniteConvection u q) i -
          (q i : ℂ) * modeDot q ((-unitTorusDerivativePhase) • infiniteConvection u q) /
            modeSquare q := by
      unfold lerayMode
      exact dite_eq_right hq
    simp only [infiniteVelocityRHS, hl, Pi.add_apply, unitTorusViscousVorticityCoeff,
      Pi.smul_apply, smul_eq_mul, lapCoeff, gradCoeff, infinitePressureCoeff, Pi.sub_apply,
      modeDot_smul]
    field_simp
    ring

/-- **The pointwise Navier–Stokes equations.** -/
theorem navierStokes_physVelocity (h : FourierSolution nu c) (x : ℝ³) {t : ℝ} (ht : 0 ≤ t) :
    derivWithin (fun τ ↦ physVelocity c x τ) (Ici 0) t +
      fderiv ℝ (fun y ↦ physVelocity c y t) x (physVelocity c x t) =
      nu • Δ (fun y ↦ physVelocity c y t) x - ∇ (fun y ↦ physPressure c y t) x := by
  have ha := h.rapidAt ht
  have hconv := h.convRapid ht
  have hlap : Rapid (fun q ↦ (nu : ℂ) • lapCoeff (c t) q) := by
    refine Rapid.of_le ha (K := |nu| * (2 * Real.pi) ^ 2) (d := 2) fun q ↦ ?_
    have e : coefficientVec ((nu : ℂ) • lapCoeff (c t) q) =
        ((nu : ℂ) * (unitTorusDerivativePhase ^ 2 * modeSquare q)) • coefficientVec (c t q) := by
      simp only [lapCoeff, smul_smul]
      rfl
    rw [e, norm_smul, norm_mul, norm_mul, norm_pow,
      PancakeIncomingLowSourceEnergy.norm_derivativePhase, Complex.norm_real, Real.norm_eq_abs,
      FourierTimeRegularity.norm_modeSquare]
    have hq : ‖frequencyVec q‖ ^ 2 ≤ (1 + ‖frequencyVec q‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
    calc |nu| * ((2 * Real.pi) ^ 2 * ‖frequencyVec q‖ ^ 2) * ‖coefficientVec (c t q)‖
        ≤ |nu| * ((2 * Real.pi) ^ 2 * (1 + ‖frequencyVec q‖) ^ 2) * ‖coefficientVec (c t q)‖ := by
          gcongr
      _ = _ := by ring
  have hph : Rapid (fun q ↦ unitTorusDerivativePhase • infiniteConvection (c t) q) :=
    hconv.smul_poly (K := 2 * Real.pi) (d := 0) fun q ↦ by
      rw [PancakeIncomingLowSourceEnergy.norm_derivativePhase, pow_zero, mul_one]
  have hgrad := rapid_gradCoeff hconv
  have key : field (rhsCurve nu c t) x +
      unitTorusDerivativePhase • field (infiniteConvection (c t)) x =
      (nu : ℂ) • field (lapCoeff (c t)) x - field (gradCoeff (c t)) x := by
    rw [← field_smul, ← field_smul, ← field_add (h.rhsRapid ht) hph, ← field_sub hlap hgrad]
    congr 1
    funext q
    exact rhs_add_convection nu (c t) q
  rw [derivWithin_physVelocity h x ht, transport_physVelocity h x ht,
    laplacian_physVelocity h x ht, gradient_physPressure_eq h x ht]
  unfold realField
  rw [← map_add, key, map_sub, Complex.coe_smul, map_smul]

/-- Velocities of Fourier curves are one-periodic. -/
theorem physVelocity_periodic (c : ℝ → FourierVelocity) (t : ℝ) :
    IsOnePeriodic (fun x ↦ physVelocity c x t) := by
  intro x i
  simp only [physVelocity, character_add_single]

theorem physPressure_periodic (c : ℝ → FourierVelocity) (t : ℝ) :
    IsOnePeriodic (fun x ↦ physPressure c x t) := by
  intro x i
  simp only [physPressure, physVelocity, character_add_single]

/-- **Fourier solutions are smooth periodic solutions in the official sense.**
The physical velocity and pressure of a continuous, real, transverse Fourier
solution that decays rapidly on bounded time intervals satisfy every clause of
the official periodic existence-and-smoothness statement with zero force, for
the initial velocity they define. -/
theorem navierStokesPeriodic_of_fourierSolution (h : FourierSolution nu c) :
    NavierStokesExistenceAndSmoothnessPeriodic nu (fun x ↦ physVelocity c x 0)
      (fun _ _ ↦ 0) (physVelocity c) (physPressure c) where
  navier_stokes x t ht := by
    rw [add_zero]
    exact navierStokes_physVelocity h x ht
  div_free x t ht := divergence_physVelocity h x ht
  initial_condition _ := rfl
  velocity_smooth := contDiffOn_physVelocity fun _ hS ↦ h.smoothRapid hS
  pressure_smooth := contDiffOn_physPressure fun _ hS ↦ h.smoothRapid hS
  isOnePeriodic_velocity t _ := physVelocity_periodic c t
  isOnePeriodic_pressure t _ := physPressure_periodic c t

end Equation

end Mettapedia.FluidDynamics.NavierStokes.FourierOfficialEquation
