import Euler.OrdinaryEulerVorticity
import Euler.OrdinaryEulerLogarithmicControl
import Euler.OrdinaryLogarithmicGradient
import Euler.OrdinaryTransportCancellation
import Euler.NonnegativeImproperIntegral
import MettapediaNS.WholeSpaceBKM
import MettapediaNS.WholeSpaceNSContinuation

/-!
# The vorticity blowup criterion for Navier–Stokes on `ℝ³`

Along every smooth Navier–Stokes evolution of `MettapediaNS.WholeSpaceViscousFlow` the
kinetic energy does not increase: transport and pressure do no work and viscosity
dissipates. The upstream whole-space logarithmic estimate bounds the gradient by the
vorticity supremum times the logarithm of the `H³` norm, and the gradient integral
controls that logarithm linearly, so a bounded vorticity integral bounds the gradient
integral (a Gronwall argument with an integrating factor).

With the continuation theorem of `MettapediaNS.WholeSpaceNSContinuation`, at a finite
maximal time the vorticity integrals are unbounded. The evolutions on shorter intervals
agree, by uniqueness, and define one smooth solution on the half-open maximal interval;
the route's spatial essential-supremum integrand of its curl, which is its vorticity
supremum, has infinite integral over that interval. Consequently either the data have a
smooth evolution on every finite interval, or that integral is infinite at a finite time;
and bounds on the vorticity integrals on every finite horizon imply global existence.
Nothing here provides such bounds.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceViscousFlow

open Set Filter MeasureTheory InnerProductSpace Real
open EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
  EulerMeanSolenoidal EulerMeanClassical EulerMeanSobolevBoundedField EulerVolterraConvolution
  EulerContinuousTimeIntegral EulerVectorCalculus EulerMeanCutoffCurl WholeSpaceViscousEnergy
  SpatialBKMIntegrand WholeSpaceBKM Finset
open scoped Topology ENNReal

namespace NSEvolution

variable {ν T : ℝ} {hT : 0 ≤ T}

/-! ## The energy inequality -/

/-- Transport and pressure do no work; the viscous term dissipates. -/
theorem velocity_derivative_inner (U : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) :
    ⟪(U.velocity t).toLp, (U.derivative t).toLp⟫_ℝ =
      -(ν * ∑ i : Fin 3, ‖((U.velocity t).directionalField (axis i)).toLp‖ ^ 2) := by
  have hd := solenoidal_representative_divergence _ (U.solenoidal t)
    (U.velocity t).field (U.velocity t).smooth (U.velocity t).toLp_ae
  have ha : ⟪(U.velocity t).toLp, (advectionField (U.velocity t) (U.velocity t)).toLp⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact advection_inner_zero (U.velocity t) (U.velocity t) hd
  have hp : ⟪(U.velocity t).toLp, (U.pressureForce t).toLp⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact pressure_pairing_zero (U.gradient t) (U.solenoidal t)
  rw [U.derivative_toLp_expand t, inner_add_right, inner_neg_right, inner_add_right, ha, hp,
    inner_smul_right, inner_laplacianField]
  ring

/-- The kinetic energy along the evolution, a continuous path. -/
def kineticPath (U : NSEvolution ν T hT) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun t ↦ ‖(U.velocity t).toLp‖ ^ 2,
    (continuous_toLp U.velocity (U.velocity_continuous 0)).norm.pow 2⟩

/-- **The energy inequality.** The `L²` norm of the velocity does not increase. -/
theorem l2_norm_le (hν : 0 ≤ ν) (U : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) :
    ‖(U.velocity t).toLp‖ ≤ ‖(U.velocity ⟨0, le_rfl, hT⟩).toLp‖ := by
  have hd (r : ℝ) (hr : r ∈ Ico 0 T) :
      HasDerivWithinAt (extendPath T hT U.kineticPath)
        (2 * ⟪(U.velocity (projIcc 0 T hT r)).toLp, (U.derivative (projIcc 0 T hT r)).toLp⟫_ℝ)
        (Icc 0 T) r := by
    have h := (U.velocity_hasDerivWithinAt ⟨r, hr.1, hr.2.le⟩).norm_sq
    change HasDerivWithinAt (fun x ↦ ‖(U.velocity (projIcc 0 T hT x)).toLp‖ ^ 2) _ (Icc 0 T) r
    simpa only [projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1, hr.2.le⟩)] using h
  have hb (r : ℝ) (_hr : r ∈ Ico 0 T) :
      2 * ⟪(U.velocity (projIcc 0 T hT r)).toLp, (U.derivative (projIcc 0 T hT r)).toLp⟫_ℝ ≤
        0 * extendPath T hT U.kineticPath r := by
    rw [U.velocity_derivative_inner, zero_mul]
    have hS : 0 ≤ ∑ i : Fin 3,
        ‖((U.velocity (projIcc 0 T hT r)).directionalField (axis i)).toLp‖ ^ 2 :=
      Finset.sum_nonneg fun i _ ↦ sq_nonneg _
    nlinarith [mul_nonneg hν hS]
  have h := linear_stability_within (extendPath T hT U.kineticPath)
    (fun r ↦ 2 * ⟪(U.velocity (projIcc 0 T hT r)).toLp,
      (U.derivative (projIcc 0 T hT r)).toLp⟫_ℝ) 0 T
    (U.kineticPath.continuous.comp continuous_projIcc).continuousOn hd hb t t.property
  have h2 : ‖(U.velocity t).toLp‖ ^ 2 ≤ ‖(U.velocity ⟨0, le_rfl, hT⟩).toLp‖ ^ 2 := by
    simpa only [extendPath, projIcc_of_mem hT t.property,
      projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩), kineticPath,
      ContinuousMap.coe_mk, zero_mul, Real.exp_zero, mul_one] using h
  nlinarith [norm_nonneg (U.velocity t).toLp, norm_nonneg (U.velocity ⟨0, le_rfl, hT⟩).toLp]

/-! ## Vorticity -/

/-- The vorticity supremum along the evolution, a continuous path. -/
def vorticityNormPath (U : NSEvolution ν T hT) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun t ↦ vorticityNorm (U.velocity t), vorticityNorm_continuous U.velocity U.velocity_continuous⟩

theorem vorticityNormPath_nonneg (U : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) :
    0 ≤ U.vorticityNormPath t :=
  vorticityNorm_nonneg _

theorem pointwise_vorticity_le (U : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) (x : Space) :
    ‖vectorCurl (U.velocity t).field x‖ ≤ U.vorticityNormPath t :=
  (vorticityNorm_le_iff (U.velocity t) _).mp le_rfl x

/-- The time integral of the vorticity supremum. -/
def vorticityIntegral (U : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) : ℝ :=
  realIntegral T hT U.vorticityNormPath t

theorem vorticityIntegral_nonneg (U : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) :
    0 ≤ U.vorticityIntegral t :=
  intervalIntegral.integral_nonneg_of_forall t.property.1
    (fun r ↦ U.vorticityNormPath_nonneg (projIcc 0 T hT r))

theorem vorticityIntegral_mono (U : NSEvolution ν T hT) (s t : Icc (0 : ℝ) T)
    (hst : (s : ℝ) ≤ t) : U.vorticityIntegral s ≤ U.vorticityIntegral t :=
  intervalIntegral.integral_mono_interval le_rfl s.property.1 hst
    (Eventually.of_forall (fun r ↦ U.vorticityNormPath_nonneg (projIcc 0 T hT r)))
    ((extendPath_continuous T hT U.vorticityNormPath).intervalIntegrable 0 t)

/-! ## Logarithmic control of the gradient integral -/

theorem logarithmic_h3_bound (hν : 0 ≤ ν) (U : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) :
    log (exp 1 + tensorNorm 3 (U.velocity t)) ≤
      logEnergyBase (U.velocity ⟨0, le_rfl, hT⟩) +
        gradientEnergyConstant * U.gradientIntegral t := by
  let a := gradientEnergyConstant * U.gradientIntegral t
  have ha : 0 ≤ a := mul_nonneg gradientEnergyConstant_nonneg (U.gradientIntegral_nonneg t)
  have hexp : 1 ≤ exp a := one_le_exp ha
  have hs : sqrt (exp a) ≤ exp a := sqrt_le_self_iff.mpr (Or.inr hexp)
  have hE0 := wordEnergy_nonneg 3 (U.velocity ⟨0, le_rfl, hT⟩)
  have hnorm : tensorNorm 3 (U.velocity t) ≤
      (wordCount 3 * sqrt (wordEnergy 3 (U.velocity ⟨0, le_rfl, hT⟩))) * exp a := by
    apply (tensorNorm_le_energy (U.velocity t) 3).trans
    calc
      wordCount 3 * sqrt (wordEnergy 3 (U.velocity t)) ≤
          wordCount 3 * sqrt (wordEnergy 3 (U.velocity ⟨0, le_rfl, hT⟩) * exp a) :=
        mul_le_mul_of_nonneg_left (sqrt_le_sqrt (U.h3_energy_gradientIntegral hν t))
          (wordCount_nonneg 3)
      _ = wordCount 3 * (sqrt (wordEnergy 3 (U.velocity ⟨0, le_rfl, hT⟩)) * sqrt (exp a)) := by
        rw [sqrt_mul hE0]
      _ ≤ wordCount 3 * (sqrt (wordEnergy 3 (U.velocity ⟨0, le_rfl, hT⟩)) * exp a) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (sqrt_nonneg _))
          (wordCount_nonneg 3)
      _ = _ := by ring
  have hexpone : exp 1 ≤ exp 1 * exp a := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp (exp_pos 1).le
  have harg : exp 1 + tensorNorm 3 (U.velocity t) ≤
      logEnergyBase (U.velocity ⟨0, le_rfl, hT⟩) * exp a := by
    calc
      _ ≤ exp 1 * exp a + (wordCount 3 * sqrt (wordEnergy 3 (U.velocity ⟨0, le_rfl, hT⟩))) *
            exp a :=
        add_le_add hexpone hnorm
      _ = _ := by unfold logEnergyBase; ring
  calc
    _ ≤ log (logEnergyBase (U.velocity ⟨0, le_rfl, hT⟩) * exp a) :=
      log_le_log (add_pos_of_pos_of_nonneg (exp_pos 1) (tensorNorm_nonneg 3 _)) harg
    _ = log (logEnergyBase (U.velocity ⟨0, le_rfl, hT⟩)) + a := by
      rw [log_mul (logEnergyBase_pos _).ne' (exp_pos a).ne', log_exp]
    _ ≤ logEnergyBase (U.velocity ⟨0, le_rfl, hT⟩) + a := by
      have h := log_le_sub_one_of_pos (logEnergyBase_pos (U.velocity ⟨0, le_rfl, hT⟩))
      linarith

section Logarithmic

variable (C : ℝ) (hC : 0 ≤ C) (W : C(Icc (0 : ℝ) T, ℝ)) (hW : ∀ t, 0 ≤ W t)

include hC hW

theorem gradient_logarithmic_envelope (hν : 0 ≤ ν) (U : NSEvolution ν T hT)
    (hlog : ∀ t, U.gradientNormPath t ≤
      C * (1 + ‖(U.velocity t).toLp‖ + W t * log (exp 1 + tensorNorm 3 (U.velocity t))))
    (t : Icc (0 : ℝ) T) :
    U.gradientNormPath t ≤ logarithmicGronwallConstant C (U.velocity ⟨0, le_rfl, hT⟩) *
      (1 + W t) * (1 + U.gradientIntegral t) := by
  let b := 1 + ‖(U.velocity ⟨0, le_rfl, hT⟩).toLp‖
  let e := logEnergyBase (U.velocity ⟨0, le_rfl, hT⟩)
  let d := b + e + gradientEnergyConstant
  let z := 1 + U.gradientIntegral t
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have he : 0 ≤ e := (logEnergyBase_pos _).le
  have hk := gradientEnergyConstant_nonneg
  have hg := U.gradientIntegral_nonneg t
  have hd : 0 ≤ d := add_nonneg (add_nonneg hb he) hk
  have hbd : b ≤ d := by dsimp [d]; linarith
  have hed : e ≤ d := by dsimp [d]; linarith
  have hkd : gradientEnergyConstant ≤ d := by dsimp [d]; linarith
  have hz : 1 ≤ z := by dsimp [z]; linarith
  have hbz : b ≤ d * z :=
    hbd.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hz hd)
  have hez : e + gradientEnergyConstant * U.gradientIntegral t ≤ d * z := by
    calc
      _ ≤ d + d * U.gradientIntegral t := add_le_add hed (mul_le_mul_of_nonneg_right hkd hg)
      _ = _ := by dsimp [z]; ring
  have hfirst : U.gradientNormPath t ≤
      C * (b + W t * (e + gradientEnergyConstant * U.gradientIntegral t)) := by
    apply (hlog t).trans
    apply mul_le_mul_of_nonneg_left _ hC
    exact add_le_add (add_le_add le_rfl (U.l2_norm_le hν t))
      (mul_le_mul_of_nonneg_left (U.logarithmic_h3_bound hν t) (hW t))
  apply hfirst.trans
  change C * (b + W t * (e + gradientEnergyConstant * U.gradientIntegral t)) ≤
    C * d * (1 + W t) * z
  calc
    _ ≤ C * (d * z + W t * (d * z)) :=
      mul_le_mul_of_nonneg_left (add_le_add hbz (mul_le_mul_of_nonneg_left hez (hW t))) hC
    _ = _ := by ring

theorem gradientIntegral_logarithmic_bound (hν : 0 ≤ ν) (U : NSEvolution ν T hT)
    (hlog : ∀ t, U.gradientNormPath t ≤
      C * (1 + ‖(U.velocity t).toLp‖ + W t * log (exp 1 + tensorNorm 3 (U.velocity t))))
    (t : Icc (0 : ℝ) T) :
    1 + U.gradientIntegral t ≤
      exp (logarithmicGronwallConstant C (U.velocity ⟨0, le_rfl, hT⟩) *
        ((t : ℝ) + realIntegral T hT W t)) := by
  let K : C(Icc (0 : ℝ) T, ℝ) := ⟨fun s ↦ 1 + W s, continuous_const.add W.continuous⟩
  let X := fun r ↦ 1 + realIntegral T hT U.gradientNormPath r
  let X' := extendPath T hT U.gradientNormPath
  have hIc : Continuous (realIntegral T hT U.gradientNormPath) :=
    (show Differentiable ℝ (realIntegral T hT U.gradientNormPath) from
      fun r ↦ (realIntegral_hasDerivAt T hT U.gradientNormPath r).differentiableAt).continuous
  have hc : ContinuousOn X (Icc (0 : ℝ) T) := (continuous_const.add hIc).continuousOn
  have hder (r : ℝ) (_hr : r ∈ Ico 0 T) : HasDerivWithinAt X (X' r) (Icc (0 : ℝ) T) r :=
    ((realIntegral_hasDerivAt T hT U.gradientNormPath r).const_add 1).hasDerivWithinAt
  have hi (r : ℝ) (hr : r ∈ Ico 0 T) :
      X' r ≤ logarithmicGronwallConstant C (U.velocity ⟨0, le_rfl, hT⟩) *
        extendPath T hT K r * X r := by
    have h := U.gradient_logarithmic_envelope C hC W hW hν hlog ⟨r, hr.1, hr.2.le⟩
    change U.gradientNormPath (projIcc 0 T hT r) ≤
      logarithmicGronwallConstant C (U.velocity ⟨0, le_rfl, hT⟩) *
        (1 + W (projIcc 0 T hT r)) * (1 + realIntegral T hT U.gradientNormPath r)
    simpa only [gradientIntegral,
      projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1, hr.2.le⟩)] using h
  have h := variable_linear_stability T hT X X'
    (logarithmicGronwallConstant C (U.velocity ⟨0, le_rfl, hT⟩)) K hc hder hi t
  have hX0 : X 0 = 1 := by simp only [X, realIntegral, intervalIntegral.integral_same, add_zero]
  have hK : realIntegral T hT K t = (t : ℝ) + realIntegral T hT W t := by
    change (∫ r in (0 : ℝ)..(t : ℝ), (1 + extendPath T hT W r)) = _
    rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable 0 t)
      ((extendPath_continuous T hT W).intervalIntegrable 0 t)]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
    rfl
  rw [hX0, one_mul, hK] at h
  exact h

end Logarithmic

/-- **A bounded vorticity integral bounds the gradient integral.** -/
theorem gradientIntegral_of_vorticity_bound (hν : 0 ≤ ν) (U : NSEvolution ν T hT)
    (Tmax G : ℝ) (hTmax : T ≤ Tmax) (hG : ∀ t, U.vorticityIntegral t ≤ G) (t : Icc (0 : ℝ) T) :
    U.gradientIntegral t ≤ exp (logarithmicGronwallConstant logarithmicGradientConstant
      (U.velocity ⟨0, le_rfl, hT⟩) * (Tmax + G)) := by
  have hlog : ∀ s, U.gradientNormPath s ≤ logarithmicGradientConstant *
      (1 + ‖(U.velocity s).toLp‖ +
        U.vorticityNormPath s * log (exp 1 + tensorNorm 3 (U.velocity s))) := fun s ↦
    (U.gradientNormPath_le_iff s _).mpr (logarithmic_gradient_bound_solenoidal (U.velocity s)
      (U.vorticityNormPath s) (U.solenoidal s) (U.pointwise_vorticity_le s))
  have hb := U.gradientIntegral_logarithmic_bound logarithmicGradientConstant
    logarithmicGradientConstant_nonneg U.vorticityNormPath U.vorticityNormPath_nonneg hν hlog t
  have he := exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (add_le_add (t.property.2.trans hTmax) (hG t))
    (logarithmicGronwallConstant_nonneg _ logarithmicGradientConstant_nonneg
      (U.velocity ⟨0, le_rfl, hT⟩)))
  have hvi : realIntegral T hT U.vorticityNormPath t = U.vorticityIntegral t := rfl
  rw [hvi] at hb
  linarith

end NSEvolution

namespace NSLifespan

variable {ν : ℝ} {A : SmoothL2Field Space} (L : NSLifespan ν A)

/-- **The vorticity integral blows up at a finite maximal time.** -/
theorem vorticityIntegral_unbounded (hν : 0 ≤ ν) (G : ℝ) :
    ∃ (S : ℝ) (hS : 0 < S) (hSL : S < L.duration) (t : Icc (0 : ℝ) S),
      G < (L.evolution S hS hSL).vorticityIntegral t := by
  by_contra hn
  push Not at hn
  apply L.not_gradientIntegral_bounded hν
    (exp (logarithmicGronwallConstant logarithmicGradientConstant A * (L.duration + G)))
  intro S hS hSL t
  have h := (L.evolution S hS hSL).gradientIntegral_of_vorticity_bound hν L.duration G hSL.le
    (hn S hS hSL) t
  simpa only [L.evolution_initial S hS hSL] using h

/-! ## The maximal solution -/

/-- The half-open maximal interval. -/
abbrev Time : Type := Ico (0 : ℝ) L.duration

def initialTime : L.Time := ⟨0, le_rfl, L.duration_pos⟩

def intermediateHorizon (t : L.Time) : ℝ := ((t : ℝ) + L.duration) / 2

theorem intermediateHorizon_pos (t : L.Time) : 0 < L.intermediateHorizon t := by
  have ht := t.property.1
  have hL := L.duration_pos
  dsimp [intermediateHorizon]
  linarith

theorem time_lt_intermediateHorizon (t : L.Time) : (t : ℝ) < L.intermediateHorizon t := by
  have ht := t.property.2
  dsimp [intermediateHorizon]
  linarith

theorem intermediateHorizon_lt (t : L.Time) : L.intermediateHorizon t < L.duration := by
  have ht := t.property.2
  dsimp [intermediateHorizon]
  linarith

def intermediateTime (t : L.Time) : Icc (0 : ℝ) (L.intermediateHorizon t) :=
  ⟨t, t.property.1, (L.time_lt_intermediateHorizon t).le⟩

def shorterTime (S : ℝ) (hSL : S < L.duration) (t : Icc (0 : ℝ) S) : L.Time :=
  ⟨t, t.property.1, t.property.2.trans_lt hSL⟩

/-- The velocity of the maximal solution. -/
def maximalField (t : L.Time) : SmoothL2Field Space :=
  (L.evolution (L.intermediateHorizon t) (L.intermediateHorizon_pos t)
    (L.intermediateHorizon_lt t)).velocity (L.intermediateTime t)

/-- The maximal solution restricts to every evolution on a shorter interval. -/
theorem maximalField_eq_evolution (hν : 0 ≤ ν) (S : ℝ) (hS : 0 < S) (hSL : S < L.duration)
    (t : Icc (0 : ℝ) S) :
    L.maximalField (L.shorterTime S hSL t) = (L.evolution S hS hSL).velocity t :=
  L.evolution_agrees_at hν (L.intermediateHorizon (L.shorterTime S hSL t)) S
    (L.intermediateHorizon_pos (L.shorterTime S hSL t)) hS
    (L.intermediateHorizon_lt (L.shorterTime S hSL t)) hSL t t.property.1
    (L.time_lt_intermediateHorizon (L.shorterTime S hSL t)).le t.property.2

theorem maximalField_initial : L.maximalField L.initialTime = A :=
  L.evolution_initial (L.intermediateHorizon L.initialTime)
    (L.intermediateHorizon_pos L.initialTime) (L.intermediateHorizon_lt L.initialTime)

theorem maximalField_solenoidal (t : L.Time) : (L.maximalField t).toLp ∈ solenoidalSpace :=
  (L.evolution (L.intermediateHorizon t) (L.intermediateHorizon_pos t)
    (L.intermediateHorizon_lt t)).solenoidal (L.intermediateTime t)

/-- Continuous restrictions on all shorter closed intervals give a continuous curve on
the half-open maximal interval. -/
theorem continuous_of_shorter_restrictions {E : Type*} [TopologicalSpace E] (f : L.Time → E)
    (hf : ∀ S (_hS : 0 < S) (hSL : S < L.duration),
      Continuous (fun t : Icc (0 : ℝ) S ↦ f (L.shorterTime S hSL t))) :
    Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hM : 0 < L.intermediateHorizon t := L.intermediateHorizon_pos t
  have hML : L.intermediateHorizon t < L.duration := L.intermediateHorizon_lt t
  have hg : Continuous (fun s : L.Time ↦
      f (L.shorterTime _ hML (projIcc 0 (L.intermediateHorizon t) hM.le (s : ℝ)))) :=
    (hf _ hM hML).comp (continuous_projIcc.comp continuous_subtype_val)
  apply hg.continuousAt.congr_of_eventuallyEq
  have hn : ∀ᶠ s : L.Time in 𝓝 t, (s : ℝ) < L.intermediateHorizon t :=
    continuous_subtype_val.continuousAt (Iio_mem_nhds (L.time_lt_intermediateHorizon t))
  filter_upwards [hn] with s hs
  rw [projIcc_of_mem hM.le ⟨s.property.1, hs.le⟩]
  rfl

theorem maximalField_jet_continuous (hν : 0 ≤ ν) (n : ℕ) :
    Continuous (fun t : L.Time ↦ (L.maximalField t).jetLp n) := by
  apply L.continuous_of_shorter_restrictions
  intro S hS hSL
  have he : (fun t : Icc (0 : ℝ) S ↦ (L.maximalField (L.shorterTime S hSL t)).jetLp n) =
      (fun t ↦ ((L.evolution S hS hSL).velocity t).jetLp n) := by
    funext t
    rw [L.maximalField_eq_evolution hν S hS hSL t]
  rw [he]
  exact (L.evolution S hS hSL).velocity_continuous n

/-- The maximal solution as a time-indexed family of fields; outside `[0, L)` it is set to
the datum, and only its values on `[0, L)` enter below. -/
def maximalVelocityPath (r : ℝ) : SmoothL2Field Space := by
  classical
  exact if hr : r ∈ Ico (0 : ℝ) L.duration then L.maximalField ⟨r, hr⟩ else A

theorem maximalVelocityPath_eq_evolution (hν : 0 ≤ ν) (S : ℝ) (hS : 0 < S)
    (hSL : S < L.duration) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) S) :
    L.maximalVelocityPath r = (L.evolution S hS hSL).velocity ⟨r, hr⟩ := by
  classical
  have hr' : r ∈ Ico (0 : ℝ) L.duration := ⟨hr.1, hr.2.trans_lt hSL⟩
  rw [maximalVelocityPath, dite_eq_left hr']
  exact L.maximalField_eq_evolution hν S hS hSL ⟨r, hr⟩

/-- The vorticity supremum of the maximal solution. -/
def vorticityDensity (r : ℝ) : ℝ := vorticityNorm (L.maximalVelocityPath r)

theorem vorticityDensity_nonneg (r : ℝ) : 0 ≤ L.vorticityDensity r := vorticityNorm_nonneg _

theorem vorticityDensity_eq_evolution (hν : 0 ≤ ν) (S : ℝ) (hS : 0 < S)
    (hSL : S < L.duration) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) S) :
    L.vorticityDensity r = (L.evolution S hS hSL).vorticityNormPath (projIcc 0 S hS.le r) := by
  rw [projIcc_of_mem hS.le hr]
  change vorticityNorm (L.maximalVelocityPath r) = vorticityNorm _
  rw [L.maximalVelocityPath_eq_evolution hν S hS hSL r hr]

theorem vorticityDensity_intervalIntegrable (hν : 0 ≤ ν) (S : ℝ) (hS : 0 < S)
    (hSL : S < L.duration) : IntervalIntegrable L.vorticityDensity volume 0 S := by
  have hc : Continuous (fun r : ℝ ↦
      (L.evolution S hS hSL).vorticityNormPath (projIcc 0 S hS.le r)) :=
    (L.evolution S hS hSL).vorticityNormPath.continuous.comp continuous_projIcc
  apply ContinuousOn.intervalIntegrable_of_Icc hS.le
  apply hc.continuousOn.congr
  intro r hr
  exact L.vorticityDensity_eq_evolution hν S hS hSL r hr

theorem vorticityDensity_integral_eq (hν : 0 ≤ ν) (S : ℝ) (hS : 0 < S)
    (hSL : S < L.duration) :
    (∫ r in (0 : ℝ)..S, L.vorticityDensity r) =
      (L.evolution S hS hSL).vorticityIntegral ⟨S, hS.le, le_rfl⟩ := by
  apply intervalIntegral.integral_congr
  intro r hr
  have hrS : r ∈ Icc (0 : ℝ) S := by simpa only [uIcc_of_le hS.le] using hr
  exact L.vorticityDensity_eq_evolution hν S hS hSL r hrS

/-- **The vorticity supremum of the maximal solution has infinite integral.** This is the
extended integral over the half-open maximal interval, not a totalized real integral. -/
theorem vorticityDensity_lintegral_eq_top (hν : 0 ≤ ν) :
    (∫⁻ r in Ico (0 : ℝ) L.duration, ENNReal.ofReal (L.vorticityDensity r)) = ⊤ := by
  apply EulerNonnegativeImproperIntegral.lintegral_eq_top_of_unbounded_partials
    L.vorticityDensity L.duration (L.vorticityDensity_intervalIntegrable hν)
    (fun r _ ↦ L.vorticityDensity_nonneg r)
  intro K
  obtain ⟨S, hS, hSL, t, hK⟩ := L.vorticityIntegral_unbounded hν K
  refine ⟨S, hS, hSL, ?_⟩
  rw [L.vorticityDensity_integral_eq hν S hS hSL]
  exact hK.trans_le ((L.evolution S hS hSL).vorticityIntegral_mono t ⟨S, hS.le, le_rfl⟩
    t.property.2)

/-- **The route's spatial essential-supremum integrand blows up.** The extended spatial
essential supremum of the curl of the maximal solution has infinite integral over the
half-open maximal interval. -/
theorem spatialEssentialSupNorm_lintegral_eq_top (hν : 0 ≤ ν) :
    (∫⁻ r in Ico (0 : ℝ) L.duration,
      spatialEssentialSupNorm volume (fun s ↦ curlField (L.maximalVelocityPath s).field) r) =
        ⊤ := by
  simp_rw [spatialEssentialSupNorm_curl_eq_ofReal_vorticityNorm]
  exact L.vorticityDensity_lintegral_eq_top hν

end NSLifespan

/-- **Global existence or vorticity blowup on `ℝ³`.** Smooth solenoidal data with all
derivatives in `L²` either have a smooth Navier–Stokes evolution on every finite interval,
or have a finite maximal lifespan at which the spatial essential supremum of the vorticity
of the maximal solution has infinite time integral. -/
theorem global_or_vorticity_blowup {ν : ℝ} (hν : 0 ≤ ν) (A : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) :
    (∀ T, 0 < T → HasNSEvolution ν A T) ∨
      ∃ L : NSLifespan ν A, (∫⁻ r in Ico (0 : ℝ) L.duration,
        spatialEssentialSupNorm volume (fun s ↦ curlField (L.maximalVelocityPath s).field) r) =
          ⊤ := by
  rcases global_or_lifespan hν A hA with h | hne
  · exact Or.inl h
  · exact Or.inr (hne.elim fun L ↦ ⟨L, L.spatialEssentialSupNorm_lintegral_eq_top hν⟩)

/-- **The Beale–Kato–Majda criterion on `ℝ³`.** If on every finite horizon the vorticity
integrals of all smooth evolutions from `A` are bounded, then `A` has a smooth evolution
on every finite interval. -/
theorem hasNSEvolution_of_vorticityIntegral_bound {ν : ℝ} (hν : 0 ≤ ν)
    (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace)
    (hbound : ∀ H, ∃ G, ∀ S (hS : 0 < S), S ≤ H → ∀ U : NSEvolution ν S hS.le,
      U.velocity ⟨0, le_rfl, hS.le⟩ = A → ∀ t, U.vorticityIntegral t ≤ G) :
    ∀ T, 0 < T → HasNSEvolution ν A T := by
  rcases global_or_lifespan hν A hA with h | hne
  · exact h
  · refine hne.elim fun L ↦ ?_
    exfalso
    obtain ⟨G, hG⟩ := hbound L.duration
    obtain ⟨S, hS, hSL, t, ht⟩ := L.vorticityIntegral_unbounded hν G
    exact (not_le_of_gt ht) (hG S hS hSL.le (L.evolution S hS hSL) (L.evolution_initial S hS hSL) t)

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceViscousFlow
