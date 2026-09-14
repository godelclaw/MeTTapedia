import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.MisalignmentRefinedPin
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Order.IsLUB

/-!
# The spatial essential-supremum vorticity integrand

The conditional pancake route bounds vorticity at every spatial point by
one integrable time envelope.  Its BKM integrand must take the spatial
essential supremum before integrating in time.

For continuous spatial slices and a measure positive on nonempty open sets,
the essential supremum equals the supremum on any countable dense spatial
set.  Consequently the existing pointwise a.e. time-measurability hypotheses
suffice for time measurability of the spatial essential supremum.  There is
no interchange of an uncountable family of exceptional time sets.

We first use an extended nonnegative value, so an unbounded slice has value
infinity.  The real-valued representative is used only together with a
proved finite-envelope bound on the relevant time interval.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SpatialBKMIntegrand

open MeasureTheory Set TopologicalSpace
open MisalignmentRefinedPin
open scoped ENNReal NNReal

section General

variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E]

/-- Extended spatial essential supremum of the vorticity norm. -/
def spatialEssentialSupNorm (μ : Measure X) (omega : ℝ → X → E)
    (t : ℝ) : ℝ≥0∞ :=
  essSup (fun x ↦ ENNReal.ofReal ‖omega t x‖) μ

/-- Real-valued spatial BKM integrand.  Finiteness of the extended value
must be established when using this representative. -/
def spatialBKMIntegrand (μ : Measure X) (omega : ℝ → X → E)
    (t : ℝ) : ℝ := (spatialEssentialSupNorm μ omega t).toReal

/-- The constructed extended integrand is exactly mathlib's `L∞` seminorm. -/
theorem spatialEssentialSupNorm_eq_eLpNorm
    (μ : Measure X) (omega : ℝ → X → E) (t : ℝ) :
    spatialEssentialSupNorm μ omega t = eLpNorm (omega t) ⊤ μ := by
  simp [spatialEssentialSupNorm, eLpNorm_exponent_top, eLpNormEssSup]

theorem spatialEssentialSupNorm_le_of_bound
    (μ : Measure X) (omega : ℝ → X → E) (t b : ℝ)
    (hbound : ∀ x, ‖omega t x‖ ≤ b) :
    spatialEssentialSupNorm μ omega t ≤ ENNReal.ofReal b := by
  exact essSup_le_of_ae_le _
    (Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_le_ofReal (hbound x))

theorem spatialEssentialSupNorm_ne_top_of_bound
    (μ : Measure X) (omega : ℝ → X → E) (t b : ℝ)
    (hbound : ∀ x, ‖omega t x‖ ≤ b) :
    spatialEssentialSupNorm μ omega t ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (spatialEssentialSupNorm_le_of_bound μ omega t b hbound)

theorem spatialBKMIntegrand_nonneg
    (μ : Measure X) (omega : ℝ → X → E) (t : ℝ) :
    0 ≤ spatialBKMIntegrand μ omega t := ENNReal.toReal_nonneg

theorem spatialBKMIntegrand_le_of_bound
    (μ : Measure X) (omega : ℝ → X → E) (t b : ℝ)
    (hb : 0 ≤ b) (hbound : ∀ x, ‖omega t x‖ ≤ b) :
    spatialBKMIntegrand μ omega t ≤ b := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (spatialEssentialSupNorm_le_of_bound μ omega t b hbound)
  simpa [spatialBKMIntegrand, ENNReal.toReal_ofReal hb] using h

/-- With the envelope's finiteness proof, taking `toReal` loses no value. -/
theorem ofReal_spatialBKMIntegrand_of_bound
    (μ : Measure X) (omega : ℝ → X → E) (t b : ℝ)
    (hbound : ∀ x, ‖omega t x‖ ≤ b) :
    ENNReal.ofReal (spatialBKMIntegrand μ omega t) = spatialEssentialSupNorm μ omega t :=
  ENNReal.ofReal_toReal (spatialEssentialSupNorm_ne_top_of_bound μ omega t b hbound)

/-- The extended-valued time integral is controlled directly, before any
conversion to a real-valued representative. -/
theorem lintegral_spatialEssentialSupNorm_le_of_envelope
    (μ : Measure X) (omega : ℝ → X → E) (budget : ℝ → ℝ)
    {T : ℝ} (hT : 0 ≤ T)
    (hbudget : IntervalIntegrable budget volume 0 T)
    (hbudget_nonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ budget t)
    (hbound : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖omega t x‖ ≤ budget t) :
    (∫⁻ t in Ioc (0 : ℝ) T, spatialEssentialSupNorm μ omega t) ≤
      ENNReal.ofReal (∫ t in (0 : ℝ)..T, budget t) := by
  have hi : IntegrableOn budget (Ioc (0 : ℝ) T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hbudget
  have hn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) T)] budget := by
    refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
    exact Filter.Eventually.of_forall fun t ht ↦
      hbudget_nonneg t (Ioc_subset_Icc_self ht)
  calc
    _ ≤ ∫⁻ t in Ioc (0 : ℝ) T, ENNReal.ofReal (budget t) := by
      apply lintegral_mono_ae
      refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
      exact Filter.Eventually.of_forall fun t ht ↦
        spatialEssentialSupNorm_le_of_bound μ omega t (budget t)
          (hbound t (Ioc_subset_Icc_self ht))
    _ = ENNReal.ofReal (∫ t in Ioc (0 : ℝ) T, budget t) :=
      (ofReal_integral_eq_lintegral_ofReal hi hn).symm
    _ = _ := by rw [intervalIntegral.integral_of_le hT]

variable [TopologicalSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]

/-- Spatial continuity upgrades the a.e. essential-supremum bound to a
bound at every point, including points of spatial measure zero. -/
theorem pointwise_le_spatialEssentialSupNorm
    (omega : ℝ → X → E) (t : ℝ) (hcont : Continuous (omega t)) (x : X) :
    ENNReal.ofReal ‖omega t x‖ ≤ spatialEssentialSupNorm μ omega t := by
  have hd : Dense {y | ENNReal.ofReal ‖omega t y‖ ≤
      spatialEssentialSupNorm μ omega t} :=
    μ.dense_of_ae (ae_le_essSup (f := fun y ↦ ENNReal.ofReal ‖omega t y‖))
  have hc : IsClosed {y | ENNReal.ofReal ‖omega t y‖ ≤
      spatialEssentialSupNorm μ omega t} :=
    isClosed_le (ENNReal.continuous_ofReal.comp hcont.norm) continuous_const
  have hu := hd.closure_eq
  rw [hc.closure_eq] at hu
  exact Set.eq_univ_iff_forall.mp hu x

theorem norm_le_spatialBKMIntegrand
    (omega : ℝ → X → E) (t : ℝ) (hcont : Continuous (omega t))
    (hfinite : spatialEssentialSupNorm μ omega t ≠ ⊤) (x : X) :
    ‖omega t x‖ ≤ spatialBKMIntegrand μ omega t := by
  have h := ENNReal.toReal_mono hfinite
    (pointwise_le_spatialEssentialSupNorm μ omega t hcont x)
  simpa [spatialBKMIntegrand] using h

theorem spatialEssentialSupNorm_eq_iSup
    (omega : ℝ → X → E) (t : ℝ) (hcont : Continuous (omega t)) :
    spatialEssentialSupNorm μ omega t = ⨆ x, ENNReal.ofReal ‖omega t x‖ := by
  apply le_antisymm
  · exact essSup_le_of_ae_le _
      (Filter.Eventually.of_forall fun x ↦ le_iSup (fun y ↦ ENNReal.ofReal ‖omega t y‖) x)
  · exact iSup_le fun x ↦ pointwise_le_spatialEssentialSupNorm μ omega t hcont x

variable [SeparableSpace X]

theorem measurable_spatialEssentialSupNorm
    [MeasurableSpace E] [BorelSpace E]
    (omega : ℝ → X → E)
    (hcont : ∀ t, Continuous (omega t))
    (hmeas : ∀ x, Measurable (fun t ↦ omega t x)) :
    Measurable (spatialEssentialSupNorm μ omega) := by
  obtain ⟨s, hcount, hdense⟩ := TopologicalSpace.exists_countable_dense X
  letI : Countable s := hcount.to_subtype
  have heq (t : ℝ) : spatialEssentialSupNorm μ omega t =
      ⨆ x : s, ENNReal.ofReal ‖omega t x‖ := by
    rw [spatialEssentialSupNorm_eq_iSup μ omega t (hcont t)]
    exact (hdense.ciSup' (ENNReal.continuous_ofReal.comp (hcont t).norm)).symm
  simp_rw [show spatialEssentialSupNorm μ omega =
      (fun t ↦ ⨆ x : s, ENNReal.ofReal ‖omega t x‖) from funext heq]
  exact Measurable.iSup fun x ↦ (hmeas x).norm.ennreal_ofReal

/-- A countable dense set suffices; only pointwise a.e. time measurability
and spatial continuity are needed, with no joint-measurability premise. -/
theorem aemeasurable_spatialEssentialSupNorm
    (omega : ℝ → X → E)
    (hcont : ∀ t, Continuous (omega t))
    (hmeas : ∀ x, AEStronglyMeasurable (fun t ↦ omega t x) volume) :
    AEMeasurable (spatialEssentialSupNorm μ omega) volume := by
  obtain ⟨s, hcount, hdense⟩ := TopologicalSpace.exists_countable_dense X
  letI : Countable s := hcount.to_subtype
  have heq (t : ℝ) : spatialEssentialSupNorm μ omega t =
      ⨆ x : s, ENNReal.ofReal ‖omega t x‖ := by
    rw [spatialEssentialSupNorm_eq_iSup μ omega t (hcont t)]
    exact (hdense.ciSup' (ENNReal.continuous_ofReal.comp (hcont t).norm)).symm
  simp_rw [show spatialEssentialSupNorm μ omega =
      (fun t ↦ ⨆ x : s, ENNReal.ofReal ‖omega t x‖) from funext heq]
  exact AEMeasurable.iSup fun x ↦ (hmeas x).norm.aemeasurable.ennreal_ofReal

theorem aestronglyMeasurable_spatialBKMIntegrand
    (omega : ℝ → X → E)
    (hcont : ∀ t, Continuous (omega t))
    (hmeas : ∀ x, AEStronglyMeasurable (fun t ↦ omega t x) volume) :
    AEStronglyMeasurable (spatialBKMIntegrand μ omega) volume :=
  (aemeasurable_spatialEssentialSupNorm μ omega hcont hmeas).ennreal_toReal.aestronglyMeasurable

/-- A common nonnegative time envelope controls the spatial essential
supremum before time integration, with the same integral bound. -/
theorem intervalIntegrable_spatialBKMIntegrand_of_envelope
    (omega : ℝ → X → E) (budget : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hcont : ∀ t, Continuous (omega t))
    (hmeas : ∀ x, AEStronglyMeasurable (fun t ↦ omega t x) volume)
    (hbudget : IntervalIntegrable budget volume 0 T)
    (hbudget_nonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ budget t)
    (hbound : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖omega t x‖ ≤ budget t) :
    (∀ t ∈ Icc (0 : ℝ) T, spatialEssentialSupNorm μ omega t ≠ ⊤) ∧
      IntervalIntegrable (spatialBKMIntegrand μ omega) volume 0 T ∧
      (∫ t in (0 : ℝ)..T, spatialBKMIntegrand μ omega t) ≤
        ∫ t in (0 : ℝ)..T, budget t := by
  have hle (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      spatialBKMIntegrand μ omega t ≤ budget t :=
    spatialBKMIntegrand_le_of_bound μ omega t (budget t)
      (hbudget_nonneg t ht) (hbound t ht)
  have hint : IntervalIntegrable (spatialBKMIntegrand μ omega) volume 0 T := by
    apply hbudget.mono_fun
      ((aestronglyMeasurable_spatialBKMIntegrand μ omega hcont hmeas).restrict)
    refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
    refine Filter.Eventually.of_forall fun t ht ↦ ?_
    rw [uIoc_of_le hT] at ht
    have ht' : t ∈ Icc (0 : ℝ) T := Ioc_subset_Icc_self ht
    dsimp only
    rw [Real.norm_eq_abs, abs_of_nonneg (spatialBKMIntegrand_nonneg μ omega t),
      Real.norm_eq_abs, abs_of_nonneg (hbudget_nonneg t ht')]
    exact hle t ht'
  exact ⟨fun t ht ↦ spatialEssentialSupNorm_ne_top_of_bound μ omega t (budget t)
    (hbound t ht), hint, intervalIntegral.integral_mono_on hT hint hbudget hle⟩

end General

section HorizonLimit

/-- A uniform bound on all shorter time intervals controls the integral
up to a finite terminal time.  Merely knowing finiteness separately on each
shorter interval would not suffice. -/
theorem lintegral_Ioo_le_of_uniform_truncations
    (f : ℝ → ℝ≥0∞) {Tstar : ℝ} (hT : 0 < Tstar) (C : ℝ≥0∞)
    (hbound : ∀ T ∈ Ioo (0 : ℝ) Tstar, (∫⁻ t in Ioc (0 : ℝ) T, f t) ≤ C) :
    (∫⁻ t in Ioo (0 : ℝ) Tstar, f t) ≤ C := by
  obtain ⟨tau, hmono, hmem, hlim⟩ := exists_seq_strictMono_tendsto' hT
  have hunion : (⋃ n : ℕ, Ioc (0 : ℝ) (tau n)) = Ioo (0 : ℝ) Tstar := by
    ext t
    simp only [mem_iUnion, mem_Ioc, mem_Ioo]
    constructor
    · rintro ⟨n, ht0, htn⟩
      exact ⟨ht0, htn.trans_lt (hmem n).2⟩
    · intro ht
      obtain ⟨n, hn⟩ := (hlim.eventually (isOpen_Ioi.mem_nhds ht.2)).exists
      exact ⟨n, ht.1, hn.le⟩
  rw [← hunion, setLIntegral_iUnion_of_directed]
  · exact iSup_le fun n ↦ hbound (tau n) (hmem n)
  · exact (antitone_const.Ioc hmono.monotone).directed_le

/-- Uniformly bounded envelope integrals on shorter intervals give a finite
spatial BKM integral on the open interval ending at `Tstar`.  The envelope
may vary with the shorter horizon; its integral bound must be uniform. -/
theorem spatialBKM_before_terminalTime_of_uniform_envelopes
    {X E : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [SeparableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) [μ.IsOpenPosMeasure] (omega : ℝ → X → E)
    (hcont : ∀ t, Continuous (omega t))
    (hmeas : ∀ x, AEStronglyMeasurable (fun t ↦ omega t x) volume)
    {Tstar C : ℝ} (hT : 0 < Tstar)
    (henv : ∀ T ∈ Ioo (0 : ℝ) Tstar, ∃ budget : ℝ → ℝ,
      IntervalIntegrable budget volume 0 T ∧
        (∀ t ∈ Icc (0 : ℝ) T, 0 ≤ budget t) ∧
        (∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖omega t x‖ ≤ budget t) ∧
        (∫ t in (0 : ℝ)..T, budget t) ≤ C) :
    (∫⁻ t in Ioo (0 : ℝ) Tstar, spatialEssentialSupNorm μ omega t) ≤
        ENNReal.ofReal C ∧
      IntegrableOn (spatialBKMIntegrand μ omega) (Ioo (0 : ℝ) Tstar) volume := by
  have hb (T : ℝ) (ht : T ∈ Ioo (0 : ℝ) Tstar) :
      (∫⁻ t in Ioc (0 : ℝ) T, spatialEssentialSupNorm μ omega t) ≤
        ENNReal.ofReal C := by
    obtain ⟨b, hi, hn, hd, hc⟩ := henv T ht
    exact (lintegral_spatialEssentialSupNorm_le_of_envelope μ omega b ht.1.le
      hi hn hd).trans (ENNReal.ofReal_le_ofReal hc)
  have hlim := lintegral_Ioo_le_of_uniform_truncations
    (spatialEssentialSupNorm μ omega) hT (ENNReal.ofReal C) hb
  refine ⟨hlim, ?_⟩
  exact integrable_toReal_of_lintegral_ne_top
    ((aemeasurable_spatialEssentialSupNorm μ omega hcont hmeas).restrict)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlim)

end HorizonLimit

section PancakeRoute

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- The spatial continuity needed above follows from the velocity's
existing `C²` spatial regularity. -/
theorem continuous_curlField_of_contDiff {u : R3 → R3} (hu : ContDiff ℝ 2 u) :
    Continuous (curlField u) := by
  have hf : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  have hentry (i j : Fin 3) : Continuous
      (fun x ↦ fderiv ℝ u x (EuclideanSpace.single j 1) i) := by
    fun_prop
  apply continuous_induced_rng.2
  apply continuous_pi
  intro i
  fin_cases i
  · simpa [curlField, PiLp.single_apply, Function.comp_def] using
      continuous_sub.comp ((hentry 2 1).prodMk (hentry 1 2))
  · simpa [curlField, PiLp.single_apply, Function.comp_def] using
      continuous_sub.comp ((hentry 0 2).prodMk (hentry 2 0))
  · simpa [curlField, PiLp.single_apply, Function.comp_def] using
      continuous_sub.comp ((hentry 1 0).prodMk (hentry 0 1))

/-- Directional spatial derivatives are measurable in a parameter whenever
the values are measurable and the spatial derivative exists.  The proof
uses the explicit difference quotients at step sizes `1/n`. -/
theorem measurable_spatialDerivative_of_measurable_values
    {u : ℝ → R3 → R3} (x v : R3)
    (hmeas : ∀ y, Measurable (fun t ↦ u t y))
    (hdiff : ∀ t, DifferentiableAt ℝ (u t) x) :
    Measurable (fun t ↦ fderiv ℝ (u t) x v) := by
  let approx (n : ℕ) (t : ℝ) : R3 :=
    (n : ℝ) • (u t (x + (n : ℝ)⁻¹ • v) - u t x)
  have ha (n : ℕ) : Measurable (approx n) :=
    ((hmeas (x + (n : ℝ)⁻¹ • v)).sub (hmeas x)).const_smul (n : ℝ)
  have ht (t : ℝ) : Filter.Tendsto (fun n ↦ approx n t) Filter.atTop
      (nhds (fderiv ℝ (u t) x v)) := by
    apply (hdiff t).hasFDerivAt.lim v
    simpa using (tendsto_natCast_atTop_atTop :
      Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop)
  exact measurable_of_tendsto_metrizable ha (tendsto_pi_nhds.mpr ht)

/-- No additional time-measurability hypothesis on curl is needed for
transported momentum data: it follows from the time derivatives of velocity
and its existing spatial regularity. -/
theorem measurable_transportedCurl (M : TransportedMomentumData) (x : R3) :
    Measurable (fun t ↦ curlField (M.u t) x) := by
  have hu (y : R3) : Continuous (fun t ↦ M.u t y) :=
    continuous_iff_continuousAt.mpr fun t ↦ (M.u_hasTimeDeriv t y).continuousAt
  have hd (v : R3) : Measurable (fun t ↦ fderiv ℝ (M.u t) x v) :=
    measurable_spatialDerivative_of_measurable_values x v (fun y ↦ (hu y).measurable)
      (fun t ↦ ((M.u_contDiff t).differentiable (by norm_num)).differentiableAt)
  have he (i j : Fin 3) : Measurable
      (fun t ↦ fderiv ℝ (M.u t) x (EuclideanSpace.single j 1) i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) i).measurable.comp
      (hd (EuclideanSpace.single j 1))
  have hp : Measurable (fun t ↦ (curlField (M.u t) x).ofLp) := by
    apply measurable_pi_lambda
    intro i
    fin_cases i
    · simpa [curlField, PiLp.single_apply, Function.comp_def] using
        measurable_sub.comp ((he 2 1).prodMk (he 1 2))
    · simpa [curlField, PiLp.single_apply, Function.comp_def] using
        measurable_sub.comp ((he 0 2).prodMk (he 2 0))
    · simpa [curlField, PiLp.single_apply, Function.comp_def] using
        measurable_sub.comp ((he 1 0).prodMk (he 0 1))
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 ↦ ℝ)).measurable.comp hp

/-- The actual extended vorticity norm of the transported velocity field. -/
def transportedVorticityEssentialSup (M : TransportedMomentumData) (t : ℝ) : ℝ≥0∞ :=
  spatialEssentialSupNorm volume (fun tau x ↦ curlField (M.u tau) x) t

/-- The real representative of that spatial essential supremum. -/
def transportedVorticityBKMIntegrand (M : TransportedMomentumData) (t : ℝ) : ℝ :=
  spatialBKMIntegrand volume (fun tau x ↦ curlField (M.u tau) x) t

theorem measurable_transportedVorticityEssentialSup (M : TransportedMomentumData) :
    Measurable (transportedVorticityEssentialSup M) :=
  measurable_spatialEssentialSupNorm volume (fun t x ↦ curlField (M.u t) x)
    (fun t ↦ continuous_curlField_of_contDiff (M.u_contDiff t)) (measurable_transportedCurl M)

theorem measurable_transportedVorticityBKMIntegrand (M : TransportedMomentumData) :
    Measurable (transportedVorticityBKMIntegrand M) :=
  (measurable_transportedVorticityEssentialSup M).ennreal_toReal

/-- The conditional pancake route now controls the spatial essential
supremum before time integration.  This theorem constructs the integrand;
it does not discharge the sector hypotheses or invoke continuation. -/
theorem spatialBKM_of_pancakeBudget
    (M : TransportedMomentumData) (D : DyadicVorticityStretchingData)
    (lowFrequencyPart : ℝ → ℝ)
    (hlow_nonneg : ∀ t, 0 ≤ lowFrequencyPart t)
    (hlow_int : IntervalIntegrable lowFrequencyPart volume 0 D.T)
    (hdecomp : ∀ t ∈ Icc (0 : ℝ) D.T, ∀ x : R3,
      ‖curlField (M.u t) x‖ ≤ lowFrequencyPart t + D.highBlockSum t)
    {B εp Cc εc Cr εr : ℝ}
    (hbudget : ScaleLocalPancakeStrainBudget D B εp)
    (hcoh : CoerciveSectorEstimate D Cc εc)
    (hres : ResidualSectorEstimate D Cr εr)
    (hε : εp + εc + εr < 1) :
    (∀ t ∈ Icc (0 : ℝ) D.T, transportedVorticityEssentialSup M t ≠ ⊤) ∧
      IntervalIntegrable (transportedVorticityBKMIntegrand M) volume 0 D.T ∧
      (∫ t in (0 : ℝ)..D.T, transportedVorticityBKMIntegrand M t) ≤
        (∫ t in (0 : ℝ)..D.T, lowFrequencyPart t) +
          (D.relaxationConst + (B + Cc + Cr)) / (1 - (εp + εc + εr)) := by
  obtain ⟨hfinite, hint, hle⟩ := intervalIntegrable_spatialBKMIntegrand_of_envelope
    volume (fun t x ↦ curlField (M.u t) x)
    (fun t ↦ lowFrequencyPart t + D.highBlockSum t) D.T_nonneg
    (fun t ↦ continuous_curlField_of_contDiff (M.u_contDiff t))
    (fun x ↦ (measurable_transportedCurl M x).aestronglyMeasurable)
    (hlow_int.add D.highBlockSum_integrable)
    (fun t _ ↦ add_nonneg (hlow_nonneg t) (D.highBlockSum_nonneg t)) hdecomp
  refine ⟨hfinite, hint, hle.trans ?_⟩
  rw [intervalIntegral.integral_add hlow_int D.highBlockSum_integrable]
  exact add_le_add le_rfl
    (highBlockIntegral_le_of_sectorEstimates D
      (pancakeSectorEstimate_of_scaleLocalStrainBudget D hbudget) hcoh hres hε)

/-- The same spatial endpoint with the sharper misalignment budget. -/
theorem spatialBKM_of_misalignmentBudget
    (M : TransportedMomentumData) (D : DyadicVorticityStretchingData)
    (split : CoherentMisalignmentSplitData D)
    (lowFrequencyPart : ℝ → ℝ)
    (hlow_nonneg : ∀ t, 0 ≤ lowFrequencyPart t)
    (hlow_int : IntervalIntegrable lowFrequencyPart volume 0 D.T)
    (hdecomp : ∀ t ∈ Icc (0 : ℝ) D.T, ∀ x : R3,
      ‖curlField (M.u t) x‖ ≤ lowFrequencyPart t + D.highBlockSum t)
    {B ε Cc εc Cr εr : ℝ}
    (hbudget : MisalignmentStrainBudget D split B ε)
    (hcoh : CoerciveSectorEstimate D Cc εc)
    (hres : ResidualSectorEstimate D Cr εr)
    (hε : (split.coherentGain + ε) + εc + εr < 1) :
    (∀ t ∈ Icc (0 : ℝ) D.T, transportedVorticityEssentialSup M t ≠ ⊤) ∧
      IntervalIntegrable (transportedVorticityBKMIntegrand M) volume 0 D.T ∧
      (∫ t in (0 : ℝ)..D.T, transportedVorticityBKMIntegrand M t) ≤
        (∫ t in (0 : ℝ)..D.T, lowFrequencyPart t) +
          (D.relaxationConst + (B + Cc + Cr)) /
            (1 - ((split.coherentGain + ε) + εc + εr)) :=
  spatialBKM_of_pancakeBudget M D lowFrequencyPart hlow_nonneg hlow_int hdecomp
    (scaleLocalPancakeStrainBudget_of_misalignmentBudget D split hbudget) hcoh hres hε

end PancakeRoute

end Mettapedia.FluidDynamics.NavierStokes.SpatialBKMIntegrand
