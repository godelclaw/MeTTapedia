import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityContinuationSurface
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# BKM continuation core: vorticity envelopes, integrability, envelope algebra, and slab restriction.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BKMContinuation

def vorticityEnvelopeOn
    (u : NSVelocityField) (T : ℝ) (Ω : NSTime → ℝ) : Prop :=
  (∀ t, 0 ≤ t → t ≤ T → 0 ≤ Ω t) ∧
    ∀ t x, 0 ≤ t → t ≤ T → ‖spatialVorticity u t x‖ ≤ Ω t

/-- A BKM-style time-integrable envelope on `0 ≤ t ≤ T`. -/
def integrableVorticityEnvelopeOn
    (Ω : NSTime → ℝ) (T B : ℝ) : Prop :=
  0 ≤ B ∧
    MeasureTheory.IntegrableOn Ω (Set.Icc 0 T) ∧
    (∫ t in Set.Icc 0 T, Ω t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) ≤ B

/-- The BKM envelope data does not change the pointwise pressure-residual
necessary condition inherited from the underlying finite-time witness. -/
theorem BKMData_momentumPressureResidual_vorticity_zero_on
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    {W : ExplicitFiniteTimeRegularityWitness ν u₀ T}
    (_hBKM : ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn W.velocity T Ω ∧
        integrableVorticityEnvelopeOn Ω T B)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    spatialVorticity (momentumPressureResidual ν W.velocity) t x = 0 :=
  ExplicitFiniteTimeRegularityWitness.spatialVorticity_momentumPressureResidual_zero_on
    (ν := ν) (T := T) (u₀ := u₀) W (t := t) (x := x) ht0 htT

/-- The BKM residual-curl necessary condition can be transported across a
chosen velocity equality. -/
theorem BKMData_momentumPressureResidual_vorticity_of_velocity_eq_zero_on
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField}
    {W : ExplicitFiniteTimeRegularityWitness ν u₀ T}
    (hWvel : W.velocity = u)
    (_hBKM : ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn W.velocity T Ω ∧
        integrableVorticityEnvelopeOn Ω T B)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    spatialVorticity (momentumPressureResidual ν u) t x = 0 := by
  simpa [← hWvel] using
    (ExplicitFiniteTimeRegularityWitness.spatialVorticity_momentumPressureResidual_zero_on
      (ν := ν) (T := T) (u₀ := u₀) W (t := t) (x := x) ht0 htT)

/-- BKM packaging cannot hide a non-curl-free pressure residual on the certified
slab.  The envelope layer adds no escape hatch once the underlying finite-time
witness velocity is impossible. -/
theorem not_exists_BKMData_velocity_of_momentumPressureResidual_vorticity_ne_zero_on
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField}
    (hcurl : ∃ t : NSTime, ∃ x : NSSpace,
      0 ≤ t ∧ t ≤ T ∧
        spatialVorticity (momentumPressureResidual ν u) t x ≠ 0) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
      W.velocity = u ∧
        ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T B := by
  rintro ⟨W, hWvel, Ω, B, hEnv, hInt⟩
  rcases hcurl with ⟨t, x, ht0, htT, hne⟩
  exact hne
    (BKMData_momentumPressureResidual_vorticity_of_velocity_eq_zero_on
      (ν := ν) (T := T) (u₀ := u₀) (u := u) (W := W) hWvel
      ⟨Ω, B, hEnv, hInt⟩ (t := t) (x := x) ht0 htT)

/-- Explicit BKM-style continuation clause: a finite-time smooth witness with a
time-integrable vorticity envelope on `0 ≤ t ≤ T` extends to a global smooth
solution. -/
def ExplicitBKMContinuationClause
    (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ) : Prop :=
  0 < ν →
    smoothInitialVelocityData u₀ →
      (∀ x, initialSpatialDivergence u₀ x = 0) →
        ∀ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
          (∃ Ω : NSTime → ℝ, ∃ B : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T B) →
            ExplicitConcreteNavierStokesGlobalOutput ν u₀

/-- Global BKM-style continuation target built from the explicit continuation
clause above. -/
def ExplicitBKMContinuationTarget : Prop :=
  ∀ ν : ℝ, ∀ u₀ : NSInitialVelocity, ∀ T : ℝ,
    ExplicitBKMContinuationClause ν u₀ T

/-- Repaired BKM-style continuation clause: the input side is restricted to
smooth divergence-free initial data with finite initial kinetic energy. -/
def ExplicitFiniteEnergyBKMContinuationClause
    (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ) : Prop :=
  0 < ν →
    smoothInitialVelocityData u₀ →
      (∀ x, initialSpatialDivergence u₀ x = 0) →
        finiteInitialKineticEnergy u₀ →
          ∀ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
            (∃ Ω : NSTime → ℝ, ∃ B : ℝ,
              vorticityEnvelopeOn W.velocity T Ω ∧
                integrableVorticityEnvelopeOn Ω T B) →
              ExplicitConcreteNavierStokesGlobalOutput ν u₀

/-- Global repaired BKM-style continuation target built from the finite-energy
continuation clause. -/
def ExplicitFiniteEnergyBKMContinuationTarget : Prop :=
  ∀ ν : ℝ, ∀ u₀ : NSInitialVelocity, ∀ T : ℝ,
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T

/-- Corrected repaired BKM continuation target: only nonnegative horizons are
admissible. This removes the negative-horizon empty-slab loophole while keeping
the intended finite-energy BKM continuation surface. -/
def ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons : Prop :=
  ∀ ν : ℝ, ∀ u₀ : NSInitialVelocity, ∀ ⦃T : ℝ⦄,
    0 ≤ T → ExplicitFiniteEnergyBKMContinuationClause ν u₀ T

/-- Any explicit whole-space regularity clause immediately yields the
corresponding fixed-horizon BKM continuation clause on the same datum. -/
theorem ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitBKMContinuationClause
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (h : ExplicitConcreteNavierStokesRegularityClause ν u₀) :
    ExplicitBKMContinuationClause ν u₀ T := by
  intro hν hsmooth hdiv _W _hEnv
  exact h hν hsmooth hdiv

/-- The repaired explicit whole-space regularity clause likewise yields the
repaired fixed-horizon BKM continuation clause on the same datum. -/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyBKMContinuationClause
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀) :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  intro hν hsmooth hdiv hfinite _W _hEnv
  exact h hν hsmooth hdiv hfinite

/-- The same explicit whole-space regularity clause also yields the whole
fixed-datum family of BKM continuation clauses, one for each horizon. -/
theorem ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitBKMContinuationClause_allHorizons
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitConcreteNavierStokesRegularityClause ν u₀) :
    ∀ T : ℝ, ExplicitBKMContinuationClause ν u₀ T := by
  intro T
  exact
    ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitBKMContinuationClause
      (T := T) h

/-- Likewise, the repaired explicit whole-space regularity clause yields the
whole fixed-datum family of repaired BKM continuation clauses. -/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyBKMContinuationClause_allHorizons
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀) :
    ∀ T : ℝ, ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  intro T
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyBKMContinuationClause
      (T := T) h

/-- The repaired BKM continuation clause is vacuous outside the finite-energy
input domain: if `u₀` fails that hypothesis, the clause holds for purely
logical reasons. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_of_not_finiteInitialKineticEnergy
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    (hfinite : ¬ finiteInitialKineticEnergy u₀) :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ T := by
  intro _hν _hsmooth _hdiv hE _W _hEnv
  exact False.elim (hfinite hE)

/-- Direct zero-field envelope for BKM data on every slab. -/
theorem vorticityEnvelopeOn_zero
    (T : ℝ) :
    vorticityEnvelopeOn (0 : NSVelocityField) T (fun _ : NSTime => 0) := by
  refine ⟨?_, ?_⟩
  · intro t ht0 htT
    simp
  · intro t x ht0 htT
    change ‖spatialVorticity (0 : NSVelocityField) t x‖ ≤ 0
    simp [spatialVorticity_zero]

/-- Integrable zero envelope with zero integral bound on every slab. -/
theorem integrableVorticityEnvelopeOn_zero
    (T : ℝ) :
    integrableVorticityEnvelopeOn (fun _ : NSTime => 0) T 0 := by
  refine ⟨le_rfl, ?_, ?_⟩
  · have hs : (MeasureTheory.volume (Set.Icc 0 T)) ≠ (⊤ : ENNReal) := by
      rw [Real.volume_Icc]
      exact ne_of_lt ENNReal.ofReal_lt_top
    exact
      (MeasureTheory.integrableOn_const (s := Set.Icc 0 T)
        (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (C := (0 : ℝ)) (hs := hs))
  · simp

/-- A constant nonnegative envelope on a nonnegative slab `0 ≤ t ≤ T` is
integrable with the explicit linear bound `T * B`. -/
theorem integrableVorticityEnvelopeOn_const
    {T B : ℝ}
    (hT : 0 ≤ T)
    (hB : 0 ≤ B) :
    integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) := by
  refine ⟨mul_nonneg hT hB, ?_, ?_⟩
  · have hs : (MeasureTheory.volume (Set.Icc 0 T)) ≠ (⊤ : ENNReal) := by
      rw [Real.volume_Icc]
      exact ne_of_lt ENNReal.ofReal_lt_top
    exact
      (MeasureTheory.integrableOn_const (s := Set.Icc 0 T)
        (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (C := B) (hs := hs))
  · rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def,
      Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hT]

/-- Vorticity envelopes add on a fixed slab, provided both velocity fields have
pointwise differentiable spatial slices there. -/
theorem vorticityEnvelopeOn_add
    {u v : NSVelocityField} {T : ℝ} {Ω Ω' : NSTime → ℝ}
    (hu : ∀ t x, 0 ≤ t → t ≤ T → DifferentiableAt ℝ (fun y : NSSpace => u t y) x)
    (hv : ∀ t x, 0 ≤ t → t ≤ T → DifferentiableAt ℝ (fun y : NSSpace => v t y) x)
    (hΩ : vorticityEnvelopeOn u T Ω)
    (hΩ' : vorticityEnvelopeOn v T Ω') :
    vorticityEnvelopeOn (u + v) T (fun t => Ω t + Ω' t) := by
  rcases hΩ with ⟨hΩnonneg, hΩbound⟩
  rcases hΩ' with ⟨hΩ'nonneg, hΩ'bound⟩
  refine ⟨?_, ?_⟩
  · intro t ht0 htT
    exact add_nonneg (hΩnonneg t ht0 htT) (hΩ'nonneg t ht0 htT)
  · intro t x ht0 htT
    rw [spatialVorticity_add (u := u) (v := v) (t := t) (x := x)
      (hu t x ht0 htT) (hv t x ht0 htT)]
    calc
      ‖spatialVorticity u t x + spatialVorticity v t x‖ ≤
          ‖spatialVorticity u t x‖ + ‖spatialVorticity v t x‖ := norm_add_le _ _
      _ ≤ Ω t + Ω' t := add_le_add (hΩbound t x ht0 htT) (hΩ'bound t x ht0 htT)

/-- Vorticity envelopes are stable under constant velocity rescaling: if
`‖ω_u(t,x)‖ ≤ Ω(t)` on a slab, then
`‖ω_{a•u}(t,x)‖ ≤ |a| * Ω(t)` on the same slab. -/
theorem vorticityEnvelopeOn_const_smul
    {u : NSVelocityField} {T : ℝ} {Ω : NSTime → ℝ}
    (a : ℝ)
    (hΩ : vorticityEnvelopeOn u T Ω) :
    vorticityEnvelopeOn (a • u) T (fun t => |a| * Ω t) := by
  rcases hΩ with ⟨hΩnonneg, hΩbound⟩
  refine ⟨?_, ?_⟩
  · intro t ht0 htT
    exact mul_nonneg (abs_nonneg a) (hΩnonneg t ht0 htT)
  · intro t x ht0 htT
    have hsmul :
        spatialVorticity (a • u) t x = a • spatialVorticity u t x := by
      ext i
      fin_cases i <;>
        simp [spatialVorticity, spatialDerivativeComponent_const_smul, mul_sub]
    rw [hsmul]
    calc
      ‖a • spatialVorticity u t x‖ = |a| * ‖spatialVorticity u t x‖ := by
        simp [norm_smul, Real.norm_eq_abs]
      _ ≤ |a| * Ω t := mul_le_mul_of_nonneg_left (hΩbound t x ht0 htT) (abs_nonneg a)

/-- Vorticity envelopes are stable under sign flip of the velocity field. -/
theorem vorticityEnvelopeOn_neg
    {u : NSVelocityField} {T : ℝ} {Ω : NSTime → ℝ}
    (hΩ : vorticityEnvelopeOn u T Ω) :
    vorticityEnvelopeOn (-u) T Ω := by
  simpa using vorticityEnvelopeOn_const_smul (a := (-1 : ℝ)) (u := u) (T := T) (Ω := Ω) hΩ

/-- Vorticity envelope domination is monotone in the envelope function on a
fixed slab. -/
theorem vorticityEnvelopeOn_mono
    {u : NSVelocityField} {T : ℝ} {Ω Ω' : NSTime → ℝ}
    (hΩ : vorticityEnvelopeOn u T Ω)
    (hΩΩ' : ∀ t, 0 ≤ t → t ≤ T → Ω t ≤ Ω' t) :
    vorticityEnvelopeOn u T Ω' := by
  rcases hΩ with ⟨hnonneg, hbound⟩
  refine ⟨?_, ?_⟩
  · intro t ht0 htT
    exact le_trans (hnonneg t ht0 htT) (hΩΩ' t ht0 htT)
  · intro t x ht0 htT
    exact le_trans (hbound t x ht0 htT) (hΩΩ' t ht0 htT)

/-- Smooth space-time velocity fields satisfy the differentiability hypotheses
needed for envelope addition on each fixed time slice. -/
theorem vorticityEnvelopeOn_add_of_smooth
    {u v : NSVelocityField} {T : ℝ} {Ω Ω' : NSTime → ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hΩ : vorticityEnvelopeOn u T Ω)
    (hΩ' : vorticityEnvelopeOn v T Ω') :
    vorticityEnvelopeOn (u + v) T (fun t => Ω t + Ω' t) := by
  exact vorticityEnvelopeOn_add
    (hu := fun t x _ht0 _htT => smoothSpaceTimeVelocity_differentiableAt_spatialSlice hu t x)
    (hv := fun t x _ht0 _htT => smoothSpaceTimeVelocity_differentiableAt_spatialSlice hv t x)
    hΩ hΩ'

/-- Smooth slab envelopes are stable under subtraction, with the same additive
bound shape as for addition. -/
theorem vorticityEnvelopeOn_sub_of_smooth
    {u v : NSVelocityField} {T : ℝ} {Ω Ω' : NSTime → ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hΩ : vorticityEnvelopeOn u T Ω)
    (hΩ' : vorticityEnvelopeOn v T Ω') :
    vorticityEnvelopeOn (u - v) T (fun t => Ω t + Ω' t) := by
  simpa [sub_eq_add_neg] using
    (vorticityEnvelopeOn_add_of_smooth
      (u := u) (v := -v) (T := T) (Ω := Ω) (Ω' := Ω')
      hu (smoothSpaceTimeVelocity_neg hv) hΩ (vorticityEnvelopeOn_neg hΩ'))

/-- Integrable vorticity envelope bounds are monotone in the scalar integral
bound parameter. -/
theorem integrableVorticityEnvelopeOn_mono
    {Ω : NSTime → ℝ} {T B B' : ℝ}
    (hInt : integrableVorticityEnvelopeOn Ω T B)
    (hBB' : B ≤ B') :
    integrableVorticityEnvelopeOn Ω T B' := by
  rcases hInt with ⟨hB, hΩ, hI⟩
  refine ⟨le_trans hB hBB', hΩ, le_trans hI hBB'⟩

/-- Integrable vorticity envelopes are stable under multiplication by a
nonnegative constant. -/
theorem integrableVorticityEnvelopeOn_const_mul
    {Ω : NSTime → ℝ} {T B a : ℝ}
    (ha : 0 ≤ a)
    (hInt : integrableVorticityEnvelopeOn Ω T B) :
    integrableVorticityEnvelopeOn (fun t => a * Ω t) T (a * B) := by
  rcases hInt with ⟨hB, hΩ, hI⟩
  refine ⟨mul_nonneg ha hB, ?_, ?_⟩
  · simpa [MeasureTheory.IntegrableOn] using hΩ.const_mul a
  · rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hI ha

/-- Integrable vorticity envelopes are stable under constant velocity rescaling
via the absolute-value factor `|a|`. -/
theorem integrableVorticityEnvelopeOn_abs_const_smul
    {Ω : NSTime → ℝ} {T B a : ℝ}
    (hInt : integrableVorticityEnvelopeOn Ω T B) :
    integrableVorticityEnvelopeOn (fun t => |a| * Ω t) T (|a| * B) := by
  exact integrableVorticityEnvelopeOn_const_mul (a := |a|) (abs_nonneg a) hInt

/-- Integrable vorticity envelopes add, and the corresponding scalar integral
bound adds with them. -/
theorem integrableVorticityEnvelopeOn_add
    {Ω Ω' : NSTime → ℝ} {T B B' : ℝ}
    (hInt : integrableVorticityEnvelopeOn Ω T B)
    (hInt' : integrableVorticityEnvelopeOn Ω' T B') :
    integrableVorticityEnvelopeOn (fun t => Ω t + Ω' t) T (B + B') := by
  rcases hInt with ⟨hB, hΩ, hI⟩
  rcases hInt' with ⟨hB', hΩ', hI'⟩
  refine ⟨add_nonneg hB hB', hΩ.integrable.add hΩ'.integrable, ?_⟩
  calc
    (∫ t in Set.Icc 0 T, (Ω t + Ω' t) ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
        (∫ t in Set.Icc 0 T, Ω t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) +
          ∫ t in Set.Icc 0 T, Ω' t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
      simpa [MeasureTheory.IntegrableOn] using
        (MeasureTheory.integral_add hΩ.integrable hΩ'.integrable)
    _ ≤ B + B' := add_le_add hI hI'

/-- Smooth BKM envelope data package for the sum field `u + v`: the concrete
envelope functions add, and so do the corresponding finite integral bounds. -/
theorem BKMEnvelopeData_add_of_smooth
    {u v : NSVelocityField} {T B B' : ℝ} {Ω Ω' : NSTime → ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hΩ : vorticityEnvelopeOn u T Ω)
    (hInt : integrableVorticityEnvelopeOn Ω T B)
    (hΩ' : vorticityEnvelopeOn v T Ω')
    (hInt' : integrableVorticityEnvelopeOn Ω' T B') :
    vorticityEnvelopeOn (u + v) T (fun t => Ω t + Ω' t) ∧
      integrableVorticityEnvelopeOn (fun t => Ω t + Ω' t) T (B + B') := by
  exact ⟨vorticityEnvelopeOn_add_of_smooth hu hv hΩ hΩ',
    integrableVorticityEnvelopeOn_add hInt hInt'⟩

/-- Smooth BKM envelope data package for the difference field `u - v`: the
pointwise envelope remains the sum `Ω + Ω'`, and the finite integral bounds add
in the same way. -/
theorem BKMEnvelopeData_sub_of_smooth
    {u v : NSVelocityField} {T B B' : ℝ} {Ω Ω' : NSTime → ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hΩ : vorticityEnvelopeOn u T Ω)
    (hInt : integrableVorticityEnvelopeOn Ω T B)
    (hΩ' : vorticityEnvelopeOn v T Ω')
    (hInt' : integrableVorticityEnvelopeOn Ω' T B') :
    vorticityEnvelopeOn (u - v) T (fun t => Ω t + Ω' t) ∧
      integrableVorticityEnvelopeOn (fun t => Ω t + Ω' t) T (B + B') := by
  exact ⟨vorticityEnvelopeOn_sub_of_smooth hu hv hΩ hΩ',
    integrableVorticityEnvelopeOn_add hInt hInt'⟩

/-- Smooth BKM envelope data package for a linear combination `a • u + b • v`:
the pointwise envelope scales by `|a|` and `|b|`, and the finite integral
bound scales in the same way. -/
theorem BKMEnvelopeData_linearCombination_of_smooth
    {u v : NSVelocityField} {T B B' : ℝ} {Ω Ω' : NSTime → ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hΩ : vorticityEnvelopeOn u T Ω)
    (hInt : integrableVorticityEnvelopeOn Ω T B)
    (hΩ' : vorticityEnvelopeOn v T Ω')
    (hInt' : integrableVorticityEnvelopeOn Ω' T B')
    (a b : ℝ) :
    vorticityEnvelopeOn (a • u + b • v) T (fun t => |a| * Ω t + |b| * Ω' t) ∧
      integrableVorticityEnvelopeOn (fun t => |a| * Ω t + |b| * Ω' t) T
        (|a| * B + |b| * B') := by
  have hΩa : vorticityEnvelopeOn (a • u) T (fun t => |a| * Ω t) :=
    vorticityEnvelopeOn_const_smul (a := a) hΩ
  have hInta :
      integrableVorticityEnvelopeOn (fun t => |a| * Ω t) T (|a| * B) :=
    integrableVorticityEnvelopeOn_abs_const_smul (a := a) hInt
  have hΩb : vorticityEnvelopeOn (b • v) T (fun t => |b| * Ω' t) :=
    vorticityEnvelopeOn_const_smul (a := b) hΩ'
  have hIntb :
      integrableVorticityEnvelopeOn (fun t => |b| * Ω' t) T (|b| * B') :=
    integrableVorticityEnvelopeOn_abs_const_smul (a := b) hInt'
  simpa using
    (BKMEnvelopeData_add_of_smooth
      (u := a • u) (v := b • v) (T := T)
      (Ω := fun t => |a| * Ω t) (Ω' := fun t => |b| * Ω' t)
      (B := |a| * B) (B' := |b| * B')
      (smoothSpaceTimeVelocity_const_smul a hu)
      (smoothSpaceTimeVelocity_const_smul b hv)
      hΩa hInta hΩb hIntb)

/-- Integrable vorticity-envelope data restrict to any shorter slab
`0 ≤ t ≤ T'` with `T' ≤ T`; the restricted integral itself gives an explicit
admissible scalar bound. -/
theorem integrableVorticityEnvelopeOn_restrict
    {Ω : NSTime → ℝ} {T T' B : ℝ}
    (hInt : integrableVorticityEnvelopeOn Ω T B)
    (hT : T' ≤ T) :
    integrableVorticityEnvelopeOn Ω T'
      (|∫ t in Set.Icc 0 T', Ω t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)|) := by
  rcases hInt with ⟨_hB, hΩ, _hI⟩
  refine ⟨abs_nonneg _, ?_, ?_⟩
  · exact hΩ.mono_set (Set.Icc_subset_Icc le_rfl hT)
  · exact le_abs_self _

/-- If an envelope is nonnegative on the slab, then restricting to a shorter
slab admits the sharper restricted-integral bound, without an absolute value. -/
theorem vorticityEnvelopeOn.integrable_restrict
    {u : NSVelocityField} {T T' B : ℝ} {Ω : NSTime → ℝ}
    (hV : vorticityEnvelopeOn u T Ω)
    (hInt : integrableVorticityEnvelopeOn Ω T B)
    (hT : T' ≤ T) :
    integrableVorticityEnvelopeOn Ω T'
      (∫ t in Set.Icc 0 T', Ω t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  rcases hV with ⟨hnonneg, _hbound⟩
  rcases hInt with ⟨_hB, hΩInt, _hI⟩
  refine ⟨?_, ?_, le_rfl⟩
  · have hnonneg_ae :
      ∀ᵐ t ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc 0 T')),
        0 ≤ Ω t := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      exact MeasureTheory.ae_of_all _ (fun t ht => hnonneg t ht.1 (le_trans ht.2 hT))
    exact MeasureTheory.integral_nonneg_of_ae hnonneg_ae
  · exact hΩInt.mono_set (Set.Icc_subset_Icc le_rfl hT)

/-- A vorticity envelope valid on a slab `0 ≤ t ≤ T` restricts to any shorter
slab `0 ≤ t ≤ T'` with `T' ≤ T`. -/
theorem vorticityEnvelopeOn_restrict
    {u : NSVelocityField} {T T' : ℝ} {Ω : NSTime → ℝ}
    (hΩ : vorticityEnvelopeOn u T Ω)
    (hT : T' ≤ T) :
    vorticityEnvelopeOn u T' Ω := by
  rcases hΩ with ⟨hnonneg, hbound⟩
  refine ⟨?_, ?_⟩
  · intro t ht0 htT'
    exact hnonneg t ht0 (le_trans htT' hT)
  · intro t x ht0 htT'
    exact hbound t x ht0 (le_trans htT' hT)

/-- Combined restriction of concrete BKM envelope data to a shorter slab. -/
theorem BKMEnvelopeData_restrict
    {u : NSVelocityField} {T T' B : ℝ} {Ω : NSTime → ℝ}
    (hV : vorticityEnvelopeOn u T Ω)
    (hInt : integrableVorticityEnvelopeOn Ω T B)
    (hT : T' ≤ T) :
    vorticityEnvelopeOn u T' Ω ∧
      integrableVorticityEnvelopeOn Ω T'
        (∫ t in Set.Icc 0 T', Ω t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  exact ⟨vorticityEnvelopeOn_restrict hV hT, hV.integrable_restrict hInt hT⟩

/-- Smooth BKM envelope data for a linear combination restrict directly to any
shorter slab `0 ≤ t ≤ T' ≤ T`. -/
theorem BKMEnvelopeData_linearCombination_restrict_of_smooth
    {u v : NSVelocityField} {T T' B B' : ℝ} {Ω Ω' : NSTime → ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hΩ : vorticityEnvelopeOn u T Ω)
    (hInt : integrableVorticityEnvelopeOn Ω T B)
    (hΩ' : vorticityEnvelopeOn v T Ω')
    (hInt' : integrableVorticityEnvelopeOn Ω' T B')
    (a b : ℝ)
    (hT : T' ≤ T) :
    vorticityEnvelopeOn (a • u + b • v) T' (fun t => |a| * Ω t + |b| * Ω' t) ∧
      integrableVorticityEnvelopeOn (fun t => |a| * Ω t + |b| * Ω' t) T'
        (∫ t in Set.Icc 0 T', (|a| * Ω t + |b| * Ω' t)
          ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  have hData :
      vorticityEnvelopeOn (a • u + b • v) T (fun t => |a| * Ω t + |b| * Ω' t) ∧
        integrableVorticityEnvelopeOn (fun t => |a| * Ω t + |b| * Ω' t) T
          (|a| * B + |b| * B') := by
    exact BKMEnvelopeData_linearCombination_of_smooth hu hv hΩ hInt hΩ' hInt' a b
  exact BKMEnvelopeData_restrict hData.1 hData.2 hT

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
