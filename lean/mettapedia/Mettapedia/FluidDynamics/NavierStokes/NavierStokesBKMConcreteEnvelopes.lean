import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMUniformBridges

/-!
# Concrete BKM envelopes for constant, shear, heat-shear, and transported heat-shear fields.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BKMContinuation

/-- A constant velocity field carries the explicit zero BKM envelope on every
nonnegative slab. -/
theorem constantVelocityField_has_constantBKMEnvelope
    (c : NSSpace) (T : ℝ)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (constantVelocityField c) T (fun _ : NSTime => 0) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => 0) T 0 := by
  simpa using
    (uniformVorticityBoundUpTo_implies_constantBKMEnvelope
      (u := constantVelocityField c) (T := T) (B := 0) hT
      (uniformVorticityBoundUpTo_constantVelocityField c T))

/-- The steady linear shear field carries the explicit constant BKM envelope
`Ω(t) = |a|` on every nonnegative slab, with integral bound `T * |a|`. -/
theorem linearShearVelocityField_has_constantBKMEnvelope
    (a T : ℝ)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (linearShearVelocityField a) T (fun _ : NSTime => |a|) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => |a|) T (T * |a|) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := linearShearVelocityField a) (T := T) (B := |a|) hT
    (uniformVorticityBoundUpTo_linearShearVelocityField a T)

/-- The steady field `u(t,x) = (a * x₁, 0, b)` carries the same explicit
constant BKM envelope `Ω(t) = |a|` on every nonnegative slab. -/
theorem linearShearVerticalDriftVelocityField_has_constantBKMEnvelope
    (a b T : ℝ)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (linearShearVerticalDriftVelocityField a b) T
        (fun _ : NSTime => |a|) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => |a|) T (T * |a|) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := linearShearVerticalDriftVelocityField a b) (T := T) (B := |a|) hT
    (uniformVorticityBoundUpTo_linearShearVerticalDriftVelocityField a b T)

/-- The steady field `u(t,x) = (a * x₁, b, 0)` carries the same explicit
constant BKM envelope `Ω(t) = |a|` on every nonnegative slab. -/
theorem linearShearHorizontalDriftVelocityField_has_constantBKMEnvelope
    (a b T : ℝ)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (linearShearHorizontalDriftVelocityField a b) T
        (fun _ : NSTime => |a|) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => |a|) T (T * |a|) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := linearShearHorizontalDriftVelocityField a b) (T := T) (B := |a|) hT
    (uniformVorticityBoundUpTo_linearShearHorizontalDriftVelocityField a b T)

/-- The steady field `u(t,x) = (a * x₁, b, c)` carries the same explicit
constant BKM envelope `Ω(t) = |a|` on every nonnegative slab. -/
theorem linearShearFullDriftVelocityField_has_constantBKMEnvelope
    (a b c T : ℝ)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (linearShearFullDriftVelocityField a b c) T
        (fun _ : NSTime => |a|) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => |a|) T (T * |a|) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := linearShearFullDriftVelocityField a b c) (T := T) (B := |a|) hT
    (uniformVorticityBoundUpTo_linearShearFullDriftVelocityField a b c T)

/-- The natural damped heat-shear vorticity envelope.  It keeps the time
dependence that is lost when one immediately passes to the coarser constant
slab bound `|a * k|`. -/
def heatShearExpVorticityEnvelope (ν a k : ℝ) : NSTime → ℝ :=
  fun t : NSTime => |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * |k|

/-- Exact integral of the damped heat-shear vorticity envelope on `0 ≤ t ≤ T`.
For the nondegenerate damped branch (`ν > 0`, `k ≠ 0`) this is the sharp
scalar BKM budget instead of the coarser `T * |a * k|` budget. -/
def heatShearExpVorticityEnvelopeExactIntegralBound (ν a k T : ℝ) : ℝ :=
  |a| * |k| * ((1 - Real.exp (-(ν * k ^ (2 : ℕ)) * T)) / (ν * k ^ (2 : ℕ)))

/-- On a nonnegative-viscosity, nonnegative-time slab, the damped heat-shear
envelope is bounded by the older constant envelope `|a * k|`. -/
theorem heatShearExpVorticityEnvelope_le_const
    (ν a k T : ℝ)
    (hν : 0 ≤ ν) :
    ∀ t : NSTime, 0 ≤ t → t ≤ T →
      heatShearExpVorticityEnvelope ν a k t ≤ |a * k| := by
  intro t ht0 _htT
  have hexp_le : Real.exp (-(ν * k ^ (2 : ℕ)) * t) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hk2 : 0 ≤ k ^ (2 : ℕ) := by positivity
    have hprod : 0 ≤ ν * k ^ (2 : ℕ) := mul_nonneg hν hk2
    nlinarith
  calc
    heatShearExpVorticityEnvelope ν a k t
        ≤ |a| * 1 * |k| := by
          dsimp [heatShearExpVorticityEnvelope]
          gcongr
    _ = |a * k| := by
          rw [abs_mul]
          ring

private theorem integral_exp_neg_mul_interval
    (lam T : ℝ) (hlam : lam ≠ 0) :
    (∫ t in (0 : ℝ)..T, Real.exp (-(lam) * t)) =
      (1 - Real.exp (-(lam) * T)) / lam := by
  have hne : (-lam) ≠ 0 := by simpa using neg_ne_zero.mpr hlam
  have hcomp := intervalIntegral.integral_comp_mul_left
    (f := fun x : ℝ => Real.exp x) (a := (0 : ℝ)) (b := T) (c := -lam) hne
  rw [integral_exp] at hcomp
  change (∫ t in (0 : ℝ)..T, (fun x : ℝ => Real.exp x) (-lam * t)) =
    (1 - Real.exp (-lam * T)) / lam
  rw [hcomp]
  simp [smul_eq_mul, Real.exp_zero, div_eq_mul_inv]
  field_simp [hlam]
  ring

/-- The damped heat-shear envelope integrates exactly to its closed-form
exponential budget on every nonnegative slab in the nondegenerate damped case. -/
theorem integral_heatShearExpVorticityEnvelope_eq_exactIntegralBound
    (ν a k T : ℝ)
    (hT : 0 ≤ T)
    (hdecay : ν * k ^ (2 : ℕ) ≠ 0) :
    (∫ t in Set.Icc 0 T, heatShearExpVorticityEnvelope ν a k t
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
      heatShearExpVorticityEnvelopeExactIntegralBound ν a k T := by
  have hset_to_interval :
      (∫ t in Set.Icc 0 T, heatShearExpVorticityEnvelope ν a k t
          ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
        ∫ t in (0 : ℝ)..T, heatShearExpVorticityEnvelope ν a k t := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
  rw [hset_to_interval]
  dsimp [heatShearExpVorticityEnvelope, heatShearExpVorticityEnvelopeExactIntegralBound]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
  rw [integral_exp_neg_mul_interval (ν * k ^ (2 : ℕ)) T hdecay]
  ring

/-- The exact exponential BKM budget is an admissible integrability certificate
for the nondegenerate damped heat-shear envelope. -/
theorem integrableVorticityEnvelopeOn_heatShearExpVorticityEnvelope_exact
    (ν a k T : ℝ)
    (hν : 0 < ν)
    (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    integrableVorticityEnvelopeOn
      (heatShearExpVorticityEnvelope ν a k) T
      (heatShearExpVorticityEnvelopeExactIntegralBound ν a k T) := by
  have hk2pos : 0 < k ^ (2 : ℕ) := by
    nlinarith [sq_pos_of_ne_zero hk]
  have hdecay_pos : 0 < ν * k ^ (2 : ℕ) := mul_pos hν hk2pos
  have hdecay : ν * k ^ (2 : ℕ) ≠ 0 := ne_of_gt hdecay_pos
  have hΩint :
      MeasureTheory.IntegrableOn
        (heatShearExpVorticityEnvelope ν a k) (Set.Icc 0 T) := by
    have hcont : Continuous (heatShearExpVorticityEnvelope ν a k) := by
      change Continuous
        (fun t : NSTime => |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * |k|)
      continuity
    exact hcont.continuousOn.integrableOn_Icc
  have hint_eq :=
    integral_heatShearExpVorticityEnvelope_eq_exactIntegralBound ν a k T hT hdecay
  have hBnonneg : 0 ≤ heatShearExpVorticityEnvelopeExactIntegralBound ν a k T := by
    rw [← hint_eq]
    have hnonneg_ae :
        ∀ᵐ t ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc 0 T)),
          0 ≤ heatShearExpVorticityEnvelope ν a k t := by
      exact MeasureTheory.ae_of_all _ (fun t => by
        dsimp [heatShearExpVorticityEnvelope]
        positivity)
    exact MeasureTheory.integral_nonneg_of_ae hnonneg_ae
  refine ⟨hBnonneg, hΩint, ?_⟩
  rw [hint_eq]

/-- The damped heat-shear envelope is integrable on every nonnegative slab
when viscosity is nonnegative, with the same coarse scalar bound as the
constant envelope. -/
theorem integrableVorticityEnvelopeOn_heatShearExpVorticityEnvelope
    (ν a k T : ℝ)
    (hν : 0 ≤ ν)
    (hT : 0 ≤ T) :
    integrableVorticityEnvelopeOn
      (heatShearExpVorticityEnvelope ν a k) T (T * |a * k|) := by
  have hΩint :
      MeasureTheory.IntegrableOn
        (heatShearExpVorticityEnvelope ν a k) (Set.Icc 0 T) := by
    have hcont : Continuous (heatShearExpVorticityEnvelope ν a k) := by
      change Continuous
        (fun t : NSTime => |a| * Real.exp (-(ν * k ^ (2 : ℕ)) * t) * |k|)
      continuity
    exact hcont.continuousOn.integrableOn_Icc
  have hconstInt :
      MeasureTheory.IntegrableOn (fun _ : NSTime => |a * k|) (Set.Icc 0 T) := by
    have hs : (MeasureTheory.volume (Set.Icc 0 T)) ≠ (⊤ : ENNReal) := by
      rw [Real.volume_Icc]
      exact ne_of_lt ENNReal.ofReal_lt_top
    exact
      (MeasureTheory.integrableOn_const (s := Set.Icc 0 T)
        (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (C := |a * k|) (hs := hs))
  refine ⟨mul_nonneg hT (abs_nonneg (a * k)), hΩint, ?_⟩
  calc
    (∫ t in Set.Icc 0 T, heatShearExpVorticityEnvelope ν a k t
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ))
        ≤ ∫ t in Set.Icc 0 T, (fun _ : NSTime => |a * k|) t
            ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
          exact MeasureTheory.setIntegral_mono_on hΩint hconstInt measurableSet_Icc
            (fun t ht => heatShearExpVorticityEnvelope_le_const ν a k T hν t ht.1 ht.2)
    _ = T * |a * k| := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def,
            Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hT]

/-- The damped sinusoidal heat-shear field carries its sharper time-dependent
BKM envelope on every nonnegative slab when the viscosity is nonnegative. -/
theorem heatShearVelocityField_has_expBKMEnvelope
    (ν a k T : ℝ)
    (hν : 0 ≤ ν)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearVelocityField ν a k) T
        (heatShearExpVorticityEnvelope ν a k) ∧
      integrableVorticityEnvelopeOn
        (heatShearExpVorticityEnvelope ν a k) T (T * |a * k|) := by
  refine ⟨?_, integrableVorticityEnvelopeOn_heatShearExpVorticityEnvelope ν a k T hν hT⟩
  refine ⟨?_, ?_⟩
  · intro t ht0 _htT
    dsimp [heatShearExpVorticityEnvelope]
    positivity
  · intro t x _ht0 _htT
    exact norm_spatialVorticity_heatShearVelocityField_le_exp_abs ν a k t x

/-- In the nondegenerate damped case, the sinusoidal heat-shear field carries
the same time-dependent envelope with its exact closed-form BKM budget. -/
theorem heatShearVelocityField_has_exactExpBKMEnvelope
    (ν a k T : ℝ)
    (hν : 0 < ν)
    (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearVelocityField ν a k) T
        (heatShearExpVorticityEnvelope ν a k) ∧
      integrableVorticityEnvelopeOn
        (heatShearExpVorticityEnvelope ν a k) T
        (heatShearExpVorticityEnvelopeExactIntegralBound ν a k T) := by
  refine ⟨?_, integrableVorticityEnvelopeOn_heatShearExpVorticityEnvelope_exact
    ν a k T hν hk hT⟩
  exact (heatShearVelocityField_has_expBKMEnvelope ν a k T hν.le hT).1

/-- Transported heat shear carries the same sharper time-dependent BKM
envelope as the untransported heat-shear branch. -/
theorem heatShearTransportVelocityField_has_expBKMEnvelope
    (ν a k b T : ℝ)
    (hν : 0 ≤ ν)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearTransportVelocityField ν a k b) T
        (heatShearExpVorticityEnvelope ν a k) ∧
      integrableVorticityEnvelopeOn
        (heatShearExpVorticityEnvelope ν a k) T (T * |a * k|) := by
  refine ⟨?_, integrableVorticityEnvelopeOn_heatShearExpVorticityEnvelope ν a k T hν hT⟩
  refine ⟨?_, ?_⟩
  · intro t ht0 _htT
    dsimp [heatShearExpVorticityEnvelope]
    positivity
  · intro t x _ht0 _htT
    exact norm_spatialVorticity_heatShearTransportVelocityField_le_exp_abs ν a k b t x

/-- In the nondegenerate damped case, transported heat shear carries the exact
closed-form BKM budget for the same time-dependent envelope. -/
theorem heatShearTransportVelocityField_has_exactExpBKMEnvelope
    (ν a k b T : ℝ)
    (hν : 0 < ν)
    (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearTransportVelocityField ν a k b) T
        (heatShearExpVorticityEnvelope ν a k) ∧
      integrableVorticityEnvelopeOn
        (heatShearExpVorticityEnvelope ν a k) T
        (heatShearExpVorticityEnvelopeExactIntegralBound ν a k T) := by
  refine ⟨?_, integrableVorticityEnvelopeOn_heatShearExpVorticityEnvelope_exact
    ν a k T hν hk hT⟩
  exact (heatShearTransportVelocityField_has_expBKMEnvelope ν a k b T hν.le hT).1

/-- Transported full-drift heat shear carries the same sharper time-dependent
BKM envelope as the drift-free transported branch. -/
theorem heatShearTransportFullDriftVelocityField_has_expBKMEnvelope
    (ν a k b d c T : ℝ)
    (hν : 0 ≤ ν)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearTransportFullDriftVelocityField ν a k b d c) T
        (heatShearExpVorticityEnvelope ν a k) ∧
      integrableVorticityEnvelopeOn
        (heatShearExpVorticityEnvelope ν a k) T (T * |a * k|) := by
  refine ⟨?_, integrableVorticityEnvelopeOn_heatShearExpVorticityEnvelope ν a k T hν hT⟩
  refine ⟨?_, ?_⟩
  · intro t ht0 _htT
    dsimp [heatShearExpVorticityEnvelope]
    positivity
  · intro t x _ht0 _htT
    exact norm_spatialVorticity_heatShearTransportFullDriftVelocityField_le_exp_abs
      ν a k b d c t x

/-- In the nondegenerate damped case, transported full-drift heat shear carries
the exact closed-form BKM budget for the same time-dependent envelope. -/
theorem heatShearTransportFullDriftVelocityField_has_exactExpBKMEnvelope
    (ν a k b d c T : ℝ)
    (hν : 0 < ν)
    (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearTransportFullDriftVelocityField ν a k b d c) T
        (heatShearExpVorticityEnvelope ν a k) ∧
      integrableVorticityEnvelopeOn
        (heatShearExpVorticityEnvelope ν a k) T
        (heatShearExpVorticityEnvelopeExactIntegralBound ν a k T) := by
  refine ⟨?_, integrableVorticityEnvelopeOn_heatShearExpVorticityEnvelope_exact
    ν a k T hν hk hT⟩
  exact
    (heatShearTransportFullDriftVelocityField_has_expBKMEnvelope
      ν a k b d c T hν.le hT).1

/-- The damped sinusoidal heat-shear field carries the explicit constant BKM
envelope `Ω(t) = |a * k|` on every nonnegative slab when the viscosity is
nonnegative. -/
theorem heatShearVelocityField_has_constantBKMEnvelope
    (ν a k T : ℝ)
    (hν : 0 ≤ ν)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearVelocityField ν a k) T
        (fun _ : NSTime => |a * k|) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => |a * k|) T (T * |a * k|) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := heatShearVelocityField ν a k) (T := T) (B := |a * k|) hT
    (uniformVorticityBoundUpTo_heatShearVelocityField ν a k T hν)

/-- The heat-shear family with constant streamwise drift carries the same
explicit constant BKM envelope `Ω(t) = |a * k|` on every nonnegative slab when
the viscosity is nonnegative. -/
theorem heatShearStreamwiseDriftVelocityField_has_constantBKMEnvelope
    (ν a k d T : ℝ)
    (hν : 0 ≤ ν)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearStreamwiseDriftVelocityField ν a k d) T
        (fun _ : NSTime => |a * k|) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => |a * k|) T (T * |a * k|) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := heatShearStreamwiseDriftVelocityField ν a k d) (T := T) (B := |a * k|) hT
    (uniformVorticityBoundUpTo_heatShearStreamwiseDriftVelocityField ν a k d T hν)

/-- The heat-shear family with vertical drift carries the same explicit
constant BKM envelope `Ω(t) = |a * k|` on every nonnegative slab when the
viscosity is nonnegative. -/
theorem heatShearVerticalDriftVelocityField_has_constantBKMEnvelope
    (ν a k c T : ℝ)
    (hν : 0 ≤ ν)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearVerticalDriftVelocityField ν a k c) T
        (fun _ : NSTime => |a * k|) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => |a * k|) T (T * |a * k|) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := heatShearVerticalDriftVelocityField ν a k c) (T := T) (B := |a * k|) hT
    (uniformVorticityBoundUpTo_heatShearVerticalDriftVelocityField ν a k c T hν)

/-- The heat-shear family with full constant drift carries the same explicit
constant BKM envelope `Ω(t) = |a * k|` on every nonnegative slab when the
viscosity is nonnegative. -/
theorem heatShearFullDriftVelocityField_has_constantBKMEnvelope
    (ν a k d c T : ℝ)
    (hν : 0 ≤ ν)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearFullDriftVelocityField ν a k d c) T
        (fun _ : NSTime => |a * k|) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => |a * k|) T (T * |a * k|) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := heatShearFullDriftVelocityField ν a k d c) (T := T) (B := |a * k|) hT
    (uniformVorticityBoundUpTo_heatShearFullDriftVelocityField ν a k d c T hν)

/-- The transported heat-shear family carries the same explicit constant BKM
envelope `Ω(t) = |a * k|` on every nonnegative slab when the viscosity is
nonnegative. -/
theorem heatShearTransportVelocityField_has_constantBKMEnvelope
    (ν a k b T : ℝ)
    (hν : 0 ≤ ν)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearTransportVelocityField ν a k b) T
        (fun _ : NSTime => |a * k|) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => |a * k|) T (T * |a * k|) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := heatShearTransportVelocityField ν a k b) (T := T) (B := |a * k|) hT
    (uniformVorticityBoundUpTo_heatShearTransportVelocityField ν a k b T hν)

/-- The transported full-drift heat-shear family carries the same explicit
constant BKM envelope `Ω(t) = |a * k|` on every nonnegative slab when the
viscosity is nonnegative. -/
theorem heatShearTransportFullDriftVelocityField_has_constantBKMEnvelope
    (ν a k b d c T : ℝ)
    (hν : 0 ≤ ν)
    (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearTransportFullDriftVelocityField ν a k b d c) T
        (fun _ : NSTime => |a * k|) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => |a * k|) T (T * |a * k|) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := heatShearTransportFullDriftVelocityField ν a k b d c) (T := T) (B := |a * k|) hT
    (uniformVorticityBoundUpTo_heatShearTransportFullDriftVelocityField ν a k b d c T hν)

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
