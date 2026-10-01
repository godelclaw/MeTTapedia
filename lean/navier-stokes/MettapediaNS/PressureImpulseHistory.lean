import MettapediaNS.WholeSpaceNSBlowup

/-!
# A paid signed pressure history on the actual unforced fluid drift

Transport and diffuse the original velocity using the actual NS velocity
as drift. Its difference from NS velocity satisfies the pressure-impulse
equation. The two literal PDE energy balances pay its terminal norm and
spacetime gradient by four times the original kinetic energy. Its signed
pressure work keeps the same original state across time boundaries.

Construction of the auxiliary passive history and its stochastic moment
identification are analytic in the companion lab. No energy bound is a
field of that history. This payment does not control positive variations,
pressure Hessians, the weighted geometric receiver or global regularity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureImpulseHistory

open Set MeasureTheory InnerProductSpace EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSolenoidal EulerMeanClassical
  EulerVolterraConvolution EulerContinuousTimeIntegral EulerSmoothFieldSobolevTime
  WholeSpaceViscousEnergy WholeSpaceViscousFlow
open scoped Topology

/-- The actual scalar advection-diffusion equation applied componentwise. -/
def passiveRhs (ν : ℝ) (u A : SmoothL2Field Space) : SmoothL2Field Space :=
  addField (fieldNeg (advectionField u A)) (scaleField ν (laplacianField A))

def impulse (u H : SmoothL2Field Space) : SmoothL2Field Space := fieldSub H u

def gradientCost (A : SmoothL2Field Space) : ℝ :=
  ∑ i : Fin 3, ‖(A.directionalField (axis i)).toLp‖ ^ 2

theorem gradientCost_nonneg (A : SmoothL2Field Space) : 0 ≤ gradientCost A :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem passiveRhs_toLp (ν : ℝ) (u A : SmoothL2Field Space) :
    (passiveRhs ν u A).toLp = -(advectionField u A).toLp +
      ν • (laplacianField A).toLp := by
  simp only [passiveRhs, toLp_addField, toLp_fieldNeg, scaleField_toLp]

private theorem directionalField_sub (A B : SmoothL2Field Space) (v : Space) :
    (fieldSub A B).directionalField v =
      fieldSub (A.directionalField v) (B.directionalField v) := by
  apply field_ext
  funext x
  have he : (fieldSub A B).field = A.field - B.field := funext (fieldSub_field A B)
  simp only [directionalField_field, fieldSub_field]
  rw [he, fderiv_sub (A.smooth.differentiable (by simp) x)
    (B.smooth.differentiable (by simp) x)]
  rfl

private theorem laplacianField_sub (A B : SmoothL2Field Space) :
    laplacianField (fieldSub A B) = fieldSub (laplacianField A) (laplacianField B) := by
  apply field_ext
  funext x
  simp only [laplacianField, directionalField_sub, sumField_field, fieldSub_field,
    Finset.sum_sub_distrib]

private theorem advectionField_sub (u A B : SmoothL2Field Space) :
    advectionField u (fieldSub A B) =
      fieldSub (advectionField u A) (advectionField u B) := by
  apply field_ext
  funext x
  have he : (fieldSub A B).field = A.field - B.field := funext (fieldSub_field A B)
  simp only [advectionField_field, fieldSub_field]
  rw [he, fderiv_sub (A.smooth.differentiable (by simp) x)
    (B.smooth.differentiable (by simp) x)]
  rfl

/-- The NS pressure sign is preserved: `D(H-u)=grad p`. -/
theorem impulse_rhs (ν : ℝ) (u H P : SmoothL2Field Space) :
    (passiveRhs ν u H).toLp - (navierStokesRhs ν u P).toLp =
      (passiveRhs ν u (impulse u H)).toLp + P.toLp := by
  simp only [passiveRhs_toLp, impulse, advectionField_sub, laplacianField_sub,
    toLp_fieldSub, navierStokesRhs, toLp_addField, eulerRhs, toLp_fieldNeg,
    scaleField_toLp, smul_sub]
  abel

/-- Incompressible transport does no passive work, without requiring
the passively transported vector itself to be solenoidal. -/
theorem passive_energy_rate (ν : ℝ) (u A : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) :
    ⟪A.toLp, (passiveRhs ν u A).toLp⟫_ℝ = -ν * gradientCost A := by
  have hd := solenoidal_representative_divergence _ hu u.field u.smooth u.toLp_ae
  have ha : ⟪A.toLp, (advectionField u A).toLp⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact advection_inner_zero u A hd
  rw [passiveRhs_toLp, inner_add_right, inner_neg_right, ha,
    real_inner_smul_right, inner_laplacianField]
  simp only [gradientCost]
  ring

private theorem norm_sub_sq_le (x y : L2) :
    ‖x-y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have hn := norm_sub_le x y
  have hs := (sq_le_sq₀ (norm_nonneg (x-y))
    (add_nonneg (norm_nonneg x) (norm_nonneg y))).2 hn
  nlinarith only [hs, sq_nonneg (‖x‖-‖y‖)]

theorem gradientCost_sub_le (H u : SmoothL2Field Space) :
    gradientCost (impulse u H) ≤ 2 * gradientCost H + 2 * gradientCost u := by
  simp only [gradientCost, impulse, directionalField_sub, toLp_fieldSub]
  have h := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦
    norm_sub_sq_le (H.directionalField (axis i)).toLp (u.directionalField (axis i)).toLp
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using h

theorem gradientCost_continuous {K : Type*} [TopologicalSpace K]
    (A : K → SmoothL2Field Space) (hA : ∀ n, Continuous (fun t ↦ (A t).jetLp n)) :
    Continuous (fun t ↦ gradientCost (A t)) := by
  apply continuous_finsetSum
  intro i _
  exact (continuous_toLp _ (continuous_jetLp_directionalField A hA (axis i) 0)).norm.pow 2

variable {ν T : ℝ} {hT : 0 ≤ T}

/-- The auxiliary history obeys its literal passive PDE on the actual
NS drift and starts from the original velocity. Construction is separate. -/
structure PassiveHistory (U : NSEvolution ν T hT) where
  field : Icc (0 : ℝ) T → SmoothL2Field Space
  jet_continuous : ∀ n, Continuous (fun t ↦ (field t).jetLp n)
  initial : field ⟨0, le_rfl, hT⟩ = U.velocity ⟨0, le_rfl, hT⟩
  time_law : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (fun r ↦ (field (projIcc 0 T hT r)).toLp)
      (passiveRhs ν (U.velocity t) (field t)).toLp (Icc (0 : ℝ) T) t

private theorem energy_balance (A R : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t ↦ (A t).jetLp n))
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (fun r ↦ (A (projIcc 0 T hT r)).toLp) (R t).toLp (Icc 0 T) t)
    (hi : ∀ t, ⟪(A t).toLp, (R t).toLp⟫_ℝ = -ν * gradientCost (A t))
    (t : Icc (0 : ℝ) T) :
    ‖(A t).toLp‖ ^ 2 + 2 * ν *
      (∫ s in (0 : ℝ)..(t : ℝ), gradientCost (A (projIcc 0 T hT s))) =
        ‖(A ⟨0, le_rfl, hT⟩).toLp‖ ^ 2 := by
  let rate : C(Icc (0 : ℝ) T, ℝ) :=
    ⟨fun s ↦ -2 * ν * gradientCost (A s),
      continuous_const.mul (gradientCost_continuous A hA)⟩
  have hh (s : Icc (0 : ℝ) T) :
      HasDerivWithinAt (fun r ↦ ‖(A (projIcc 0 T hT r)).toLp‖ ^ 2)
        (rate s) (Icc 0 T) s := by
    have h := (hd s).norm_sq
    simpa only [projIcc_of_mem hT s.property, hi, rate, ContinuousMap.coe_mk,
      mul_neg, neg_mul, ← mul_assoc] using h
  have he := eq_initial_add_integral T hT rate _ hh t
  simp only [projIcc_of_mem hT t.property,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩),
    integral_apply, realIntegral, extendPath, rate, ContinuousMap.coe_mk,
    intervalIntegral.integral_const_mul] at he
  linarith only [he]

namespace PassiveHistory

variable (U : NSEvolution ν T hT) (H : PassiveHistory U)

def impulseField (t : Icc (0 : ℝ) T) : SmoothL2Field Space :=
  impulse (U.velocity t) (H.field t)

theorem impulse_continuous (n : ℕ) :
    Continuous (fun t ↦ (H.impulseField U t).jetLp n) :=
  continuous_jet_fieldSub H.field U.velocity H.jet_continuous U.velocity_continuous n

theorem impulse_initial : (H.impulseField U ⟨0, le_rfl, hT⟩).toLp = 0 := by
  simp only [impulseField, impulse, toLp_fieldSub, H.initial, sub_self]

theorem impulse_hasDerivWithinAt (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun r ↦ (H.impulseField U (projIcc 0 T hT r)).toLp)
      ((passiveRhs ν (U.velocity t) (H.impulseField U t)).toLp +
        (U.pressureForce t).toLp) (Icc (0 : ℝ) T) t := by
  have h := (H.time_law t).sub (U.velocity_hasDerivWithinAt t)
  rw [U.derivative_eq_navierStokesRhs, impulse_rhs] at h
  convert! h using 1

theorem passive_balance (t : Icc (0 : ℝ) T) :
    ‖(H.field t).toLp‖ ^ 2 + 2 * ν *
      (∫ s in (0 : ℝ)..(t : ℝ), gradientCost (H.field (projIcc 0 T hT s))) =
        ‖(U.velocity ⟨0, le_rfl, hT⟩).toLp‖ ^ 2 := by
  simpa only [H.initial] using energy_balance H.field
    (fun s ↦ passiveRhs ν (U.velocity s) (H.field s)) H.jet_continuous H.time_law
    (fun s ↦ passive_energy_rate ν _ _ (U.solenoidal s)) t

theorem velocity_balance (t : Icc (0 : ℝ) T) :
    ‖(U.velocity t).toLp‖ ^ 2 + 2 * ν *
      (∫ s in (0 : ℝ)..(t : ℝ), gradientCost (U.velocity (projIcc 0 T hT s))) =
        ‖(U.velocity ⟨0, le_rfl, hT⟩).toLp‖ ^ 2 := by
  exact energy_balance U.velocity U.derivative U.velocity_continuous
    U.velocity_hasDerivWithinAt (fun s ↦ by
      simpa only [gradientCost, neg_mul] using U.velocity_derivative_inner s) t

/-- The complete original-datum payment includes both the terminal
impulse and its actual accumulated gradient cost. -/
theorem impulse_paid (hν : 0 ≤ ν) (t : Icc (0 : ℝ) T) :
    ‖(H.impulseField U t).toLp‖ ^ 2 + 2 * ν *
      (∫ s in (0 : ℝ)..(t : ℝ), gradientCost (H.impulseField U (projIcc 0 T hT s))) ≤
        4 * ‖(U.velocity ⟨0, le_rfl, hT⟩).toLp‖ ^ 2 := by
  have hi := (gradientCost_continuous (H.impulseField U) (H.impulse_continuous U)).comp
    (continuous_projIcc (h := hT))
  have hH := (gradientCost_continuous H.field H.jet_continuous).comp
    (continuous_projIcc (h := hT))
  have hu := (gradientCost_continuous U.velocity U.velocity_continuous).comp
    (continuous_projIcc (h := hT))
  have hcost := intervalIntegral.integral_mono_on (μ := volume) t.property.1
    (hi.intervalIntegrable 0 t)
    ((hH.const_mul 2 |>.add (hu.const_mul 2)).intervalIntegrable 0 t)
    (fun s _ ↦ gradientCost_sub_le (H.field (projIcc 0 T hT s))
      (U.velocity (projIcc 0 T hT s)))
  have hsum : (∫ s in (0 : ℝ)..(t : ℝ),
      2 * gradientCost (H.field (projIcc 0 T hT s)) +
      2 * gradientCost (U.velocity (projIcc 0 T hT s))) =
      2 * (∫ s in (0 : ℝ)..(t : ℝ), gradientCost (H.field (projIcc 0 T hT s))) +
      2 * (∫ s in (0 : ℝ)..(t : ℝ), gradientCost (U.velocity (projIcc 0 T hT s))) := by
    simpa only [Pi.add_apply, Function.comp_def, intervalIntegral.integral_const_mul] using
      intervalIntegral.integral_add (μ := volume) ((hH.const_mul 2).intervalIntegrable 0 t)
        ((hu.const_mul 2).intervalIntegrable 0 t)
  simp only [Pi.add_apply, Function.comp_def] at hcost
  rw [hsum] at hcost
  have hn : ‖(H.impulseField U t).toLp‖ ^ 2 ≤
      2 * ‖(H.field t).toLp‖ ^ 2 + 2 * ‖(U.velocity t).toLp‖ ^ 2 := by
    simpa only [impulseField, impulse, toLp_fieldSub] using
      norm_sub_sq_le (H.field t).toLp (U.velocity t).toLp
  have hm := mul_le_mul_of_nonneg_left hcost (show 0 ≤ 2 * ν by positivity)
  have hbH := H.passive_balance U t
  have hbu := velocity_balance U t
  linarith only [hn, hm, hbH, hbu]

/-- Signed pressure work against the identified impulse mean. This is
not work against an arbitrary or weighted geometric receiver. -/
def pressureWork (t : Icc (0 : ℝ) T) : ℝ :=
  ⟪(H.impulseField U t).toLp, (U.pressureForce t).toLp⟫_ℝ

theorem pressureWork_continuous : Continuous (H.pressureWork U) :=
  (continuous_toLp _ (H.impulse_continuous U 0)).inner
    (continuous_toLp _ (U.pressure_continuous 0))

theorem pressure_work_balance (t : Icc (0 : ℝ) T) :
    2 * (∫ s in (0 : ℝ)..(t : ℝ), H.pressureWork U (projIcc 0 T hT s)) =
      ‖(H.impulseField U t).toLp‖ ^ 2 + 2 * ν *
        (∫ s in (0 : ℝ)..(t : ℝ), gradientCost (H.impulseField U (projIcc 0 T hT s))) := by
  let rate : C(Icc (0 : ℝ) T, ℝ) :=
    ⟨fun s ↦ -2 * ν * gradientCost (H.impulseField U s) + 2 * H.pressureWork U s,
      (continuous_const.mul (gradientCost_continuous _ (H.impulse_continuous U))).add
        (continuous_const.mul (H.pressureWork_continuous U))⟩
  have hh (s : Icc (0 : ℝ) T) :
      HasDerivWithinAt (fun r ↦ ‖(H.impulseField U (projIcc 0 T hT r)).toLp‖ ^ 2)
        (rate s) (Icc 0 T) s := by
    have h := (H.impulse_hasDerivWithinAt U s).norm_sq
    simp only [projIcc_of_mem hT s.property, inner_add_right,
      passive_energy_rate ν _ _ (U.solenoidal s)] at h
    convert h using 1
    simp only [rate, ContinuousMap.coe_mk, pressureWork]
    ring
  have he := eq_initial_add_integral T hT rate _ hh t
  have hc := (gradientCost_continuous _ (H.impulse_continuous U)).comp
    (continuous_projIcc (h := hT))
  have hw := (H.pressureWork_continuous U).comp (continuous_projIcc (h := hT))
  simp only [projIcc_of_mem hT t.property,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩),
    H.impulse_initial U, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add,
    integral_apply, realIntegral, extendPath, rate, ContinuousMap.coe_mk] at he
  have hsum : (∫ s in (0 : ℝ)..(t : ℝ),
      -2 * ν * gradientCost (H.impulseField U (projIcc 0 T hT s)) +
        2 * H.pressureWork U (projIcc 0 T hT s)) =
      (-2 * ν) * (∫ s in (0 : ℝ)..(t : ℝ),
        gradientCost (H.impulseField U (projIcc 0 T hT s))) +
      2 * (∫ s in (0 : ℝ)..(t : ℝ), H.pressureWork U (projIcc 0 T hT s)) := by
    simpa only [Pi.add_apply, Function.comp_def, intervalIntegral.integral_const_mul] using
      intervalIntegral.integral_add (μ := volume)
        ((hc.const_mul (-2 * ν)).intervalIntegrable 0 t) ((hw.const_mul 2).intervalIntegrable 0 t)
  rw [hsum] at he
  linarith only [he]

theorem signed_pressure_work_paid (hν : 0 ≤ ν) (t : Icc (0 : ℝ) T) :
    0 ≤ 2 * (∫ s in (0 : ℝ)..(t : ℝ), H.pressureWork U (projIcc 0 T hT s)) ∧
    2 * (∫ s in (0 : ℝ)..(t : ℝ), H.pressureWork U (projIcc 0 T hT s)) ≤
      4 * ‖(U.velocity ⟨0, le_rfl, hT⟩).toLp‖ ^ 2 := by
  rw [H.pressure_work_balance U]
  constructor
  · have hi : 0 ≤ ∫ s in (0 : ℝ)..(t : ℝ),
        gradientCost (H.impulseField U (projIcc 0 T hT s)) :=
      intervalIntegral.integral_nonneg_of_forall t.property.1 (fun _ ↦ gradientCost_nonneg _)
    positivity
  · exact H.impulse_paid U hν t

/-- A signed cumulative payment, retaining the original initial label. -/
def spent (t : Icc (0 : ℝ) T) : ℝ :=
  ‖(H.impulseField U t).toLp‖ ^ 2 + 2 * ν *
    (∫ s in (0 : ℝ)..(t : ℝ), gradientCost (H.impulseField U (projIcc 0 T hT s)))

def reserve (t : Icc (0 : ℝ) T) : ℝ :=
  4 * ‖(U.velocity ⟨0, le_rfl, hT⟩).toLp‖ ^ 2 - H.spent U t

theorem spent_eq_pressureWork (t : Icc (0 : ℝ) T) :
    H.spent U t = 2 * (∫ s in (0 : ℝ)..(t : ℝ), H.pressureWork U (projIcc 0 T hT s)) :=
  (H.pressure_work_balance U t).symm

theorem spent_bounds (hν : 0 ≤ ν) (t : Icc (0 : ℝ) T) :
    0 ≤ H.spent U t ∧ H.spent U t ≤ 4 * ‖(U.velocity ⟨0, le_rfl, hT⟩).toLp‖ ^ 2 := by
  rw [H.spent_eq_pressureWork U]
  exact H.signed_pressure_work_paid U hν t

theorem reserve_nonneg (hν : 0 ≤ ν) (t : Icc (0 : ℝ) T) :
    0 ≤ H.reserve U t := by
  have h := (H.spent_bounds U hν t).2
  exact sub_nonneg.mpr h

theorem spent_initial : H.spent U ⟨0, le_rfl, hT⟩ = 0 := by
  simp only [spent, H.impulse_initial U, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    intervalIntegral.integral_same, mul_zero, zero_add]

/-- Composing actual segments carries the previous signed payment.
This does not bound the sum of positive variations of pressure work. -/
theorem pressure_work_between (s t : Icc (0 : ℝ) T) :
    H.spent U s + 2 * (∫ r in (s : ℝ)..(t : ℝ), H.pressureWork U (projIcc 0 T hT r)) =
      H.spent U t := by
  have hc := (H.pressureWork_continuous U).comp (continuous_projIcc (h := hT))
  have ha := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 s) (hc.intervalIntegrable s t)
  simp only [Function.comp_def] at ha
  rw [H.spent_eq_pressureWork U s, H.spent_eq_pressureWork U t]
  linarith only [ha]

theorem pressure_work_between_paid (hν : 0 ≤ ν) (s t : Icc (0 : ℝ) T) :
    2 * (∫ r in (s : ℝ)..(t : ℝ), H.pressureWork U (projIcc 0 T hT r)) ≤ H.reserve U s := by
  have he := H.pressure_work_between U s t
  have hb := (H.spent_bounds U hν t).2
  unfold reserve
  linarith only [he, hb]

end PassiveHistory

end Mettapedia.FluidDynamics.NavierStokes.PressureImpulseHistory
