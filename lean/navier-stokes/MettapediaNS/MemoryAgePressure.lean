import MettapediaNS.WholeSpacePressureReceiver
import MettapediaNS.ViscousMemoryPressure

/-!
# Pressure costs after splitting retained memory by age

An old positive memory tensor bounded by `L I` and a recent positive
tensor give a weighted pressure cost bounded by an unweighted receiver
cost and an explicit recent-memory remainder. The tensors need not
commute. The actual canonical pressure receiver supplies the unweighted
cost through its previously proved spatial diffusion payment.

The companion analytic argument obtains `L` from incompressible scalar
diffusion and the original memory-source mass. That propagator, the age
split, the space-time entropy pairing and the complete joint receiver
are not constructed by this module. No arbitrary-history bound on the
recent remainder or the full nonlinear production is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.MemoryAgePressure

open MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanClassical
  MiddleEigenvalueAlgebra WholeSpacePressureAugmentation WholeSpacePressureReceiver
  WholeSpaceViscousEnergy WholeSpaceBetchov EulerMeanSolenoidal

open scoped NNReal

abbrev Tensor := Fin 3 → Fin 3 → ℝ

def tensorTrace (C : Tensor) : ℝ := ∑ i, C i i

def vectorSquare (v : Fin 3 → ℝ) : ℝ := ∑ i, (v i) ^ 2

def quadratic (C : Tensor) (v : Fin 3 → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * C i j * v j

/-- This is `tr(ηI+C) v·(ηI+C)v`, written in a fixed orthonormal frame. -/
def memoryCost (η : ℝ) (C : Tensor) (v : Fin 3 → ℝ) : ℝ :=
  (3 * η + tensorTrace C) * (η * vectorSquare v + quadratic C v)

theorem vectorSquare_nonneg (v : Fin 3 → ℝ) : 0 ≤ vectorSquare v :=
  Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

theorem tensorTrace_add (A B : Tensor) :
    tensorTrace (A + B) = tensorTrace A + tensorTrace B := by
  simp [tensorTrace, Finset.sum_add_distrib]

theorem quadratic_add (A B : Tensor) (v : Fin 3 → ℝ) :
    quadratic (A + B) v = quadratic A v + quadratic B v := by
  simp [quadratic, mul_add, add_mul, Finset.sum_add_distrib]

theorem memoryCost_nonneg (η : ℝ) (C : Tensor) (v : Fin 3 → ℝ)
    (hη : 0 ≤ η) (hc : 0 ≤ tensorTrace C) (hq : 0 ≤ quadratic C v) :
    0 ≤ memoryCost η C v := by
  unfold memoryCost
  exact mul_nonneg (by positivity)
    (add_nonneg (mul_nonneg hη (vectorSquare_nonneg v)) hq)

/-- The fresh remainder retains the receiver's direction relative to
the generated tensor. The trace term is also retained. -/
def recentCost (K : ℝ) (recent : Tensor) (v : Fin 3 → ℝ) : ℝ :=
  K * tensorTrace recent * vectorSquare v +
    (3 * K + tensorTrace recent) * quadratic recent v

theorem recentCost_nonneg (K : ℝ) (recent : Tensor) (v : Fin 3 → ℝ)
    (hK : 0 ≤ K) (ht : 0 ≤ tensorTrace recent) (hq : 0 ≤ quadratic recent v) :
    0 ≤ recentCost K recent v := by
  unfold recentCost
  have hv := vectorSquare_nonneg v
  positivity

/-- The sharper comparison keeps anisotropic fresh memory; its tensors
may turn and need not commute with each other or with the receiver. -/
theorem memoryCost_anisotropic (η L : ℝ) (old recent : Tensor) (v : Fin 3 → ℝ)
    (hη : 0 ≤ η) (hL : 0 ≤ L)
    (htold : tensorTrace old ≤ 3 * L) (htrecent : 0 ≤ tensorTrace recent)
    (hqold : 0 ≤ quadratic old v)
    (hold : quadratic old v ≤ L * vectorSquare v)
    (hqrecent : 0 ≤ quadratic recent v) :
    memoryCost η (old + recent) v ≤
      3 * (η + L) ^ 2 * vectorSquare v + recentCost (η + L) recent v := by
  have hv := vectorSquare_nonneg v
  have hquad : η * vectorSquare v + quadratic old v + quadratic recent v ≤
      (η + L) * vectorSquare v + quadratic recent v := by nlinarith only [hold]
  have htrace : 3 * η + tensorTrace old + tensorTrace recent ≤
      3 * (η + L) + tensorTrace recent := by linarith only [htold]
  have hfirst := mul_le_mul_of_nonneg_right htrace
    (show 0 ≤ η * vectorSquare v + quadratic old v + quadratic recent v by positivity)
  have hsecond := mul_le_mul_of_nonneg_left hquad
    (show 0 ≤ 3 * (η + L) + tensorTrace recent by positivity)
  unfold memoryCost recentCost
  rw [tensorTrace_add, quadratic_add]
  nlinarith only [hfirst, hsecond]

theorem recentCost_trace_bound (K : ℝ) (recent : Tensor) (v : Fin 3 → ℝ)
    (hK : 0 ≤ K) (ht : 0 ≤ tensorTrace recent)
    (hq : quadratic recent v ≤ tensorTrace recent * vectorSquare v) :
    recentCost K recent v ≤
      2 * K ^ 2 * vectorSquare v + 3 * (tensorTrace recent) ^ 2 * vectorSquare v := by
  have hv := vectorSquare_nonneg v
  have hp := mul_le_mul_of_nonneg_left hq
    (show 0 ≤ 3 * K + tensorTrace recent by positivity)
  have hs := mul_nonneg (sq_nonneg (K - tensorTrace recent)) hv
  unfold recentCost
  nlinarith only [hp, hs]

/-- The recent tensor's trace is retained. The old bound and positivity
are explicit application hypotheses, supplied analytically by diffusion. -/
theorem memoryCost_split (η L : ℝ) (old recent : Tensor) (v : Fin 3 → ℝ)
    (hη : 0 ≤ η) (hL : 0 ≤ L)
    (htold : tensorTrace old ≤ 3 * L) (htrecent : 0 ≤ tensorTrace recent)
    (hqold : 0 ≤ quadratic old v)
    (hold : quadratic old v ≤ L * vectorSquare v)
    (hqrecent : 0 ≤ quadratic recent v)
    (hrecent : quadratic recent v ≤ tensorTrace recent * vectorSquare v) :
    memoryCost η (old + recent) v ≤
      5 * (η + L) ^ 2 * vectorSquare v +
        3 * (tensorTrace recent) ^ 2 * vectorSquare v := by
  have hv := vectorSquare_nonneg v
  have hK : 0 ≤ η + L := add_nonneg hη hL
  have hquad : η * vectorSquare v + quadratic old v + quadratic recent v ≤
      (η + L) * vectorSquare v + quadratic recent v := by nlinarith only [hold]
  have htrace : 3 * η + tensorTrace old + tensorTrace recent ≤
      3 * (η + L) + tensorTrace recent := by linarith only [htold]
  have hfirst := mul_le_mul_of_nonneg_right htrace
    (show 0 ≤ η * vectorSquare v + quadratic old v + quadratic recent v by positivity)
  have hsecond := mul_le_mul_of_nonneg_left hquad
    (show 0 ≤ 3 * (η + L) + tensorTrace recent by positivity)
  have hthird := mul_le_mul_of_nonneg_left hrecent
    (show 0 ≤ 3 * (η + L) + tensorTrace recent by positivity)
  have hcross := mul_nonneg (sq_nonneg (η + L - tensorTrace recent)) hv
  unfold memoryCost
  rw [tensorTrace_add, quadratic_add]
  nlinarith only [hfirst, hsecond, hthird, hcross]

/-- Integration does not assume a bound on the recent remainder. -/
theorem integral_memoryCost_split {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (η L : ℝ) (old recent : Ω → Tensor) (v : Ω → Fin 3 → ℝ)
    (hη : 0 ≤ η) (hL : 0 ≤ L)
    (hc : Integrable (fun x ↦ memoryCost η (old x + recent x) (v x)) μ)
    (hv : Integrable (fun x ↦ vectorSquare (v x)) μ)
    (hr : Integrable (fun x ↦ (tensorTrace (recent x)) ^ 2 * vectorSquare (v x)) μ)
    (htold : ∀ᵐ x ∂μ, tensorTrace (old x) ≤ 3 * L)
    (htrecent : ∀ᵐ x ∂μ, 0 ≤ tensorTrace (recent x))
    (hqold : ∀ᵐ x ∂μ, 0 ≤ quadratic (old x) (v x))
    (hold : ∀ᵐ x ∂μ, quadratic (old x) (v x) ≤ L * vectorSquare (v x))
    (hqrecent : ∀ᵐ x ∂μ, 0 ≤ quadratic (recent x) (v x))
    (hrecent : ∀ᵐ x ∂μ,
      quadratic (recent x) (v x) ≤ tensorTrace (recent x) * vectorSquare (v x)) :
    (∫ x, memoryCost η (old x + recent x) (v x) ∂μ) ≤
      5 * (η + L) ^ 2 * (∫ x, vectorSquare (v x) ∂μ) +
        3 * ∫ x, (tensorTrace (recent x)) ^ 2 * vectorSquare (v x) ∂μ := by
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    (hv.const_mul (5 * (η + L) ^ 2)) (hr.const_mul 3)]
  apply integral_mono_ae hc ((hv.const_mul (5 * (η + L) ^ 2)).add (hr.const_mul 3))
  filter_upwards [htold, htrecent, hqold, hold, hqrecent, hrecent]
    with x hto htr hqo ho hqr hrx
  simpa only [Pi.add_apply, mul_assoc] using
    memoryCost_split η L (old x) (recent x) (v x) hη hL hto htr hqo ho hqr hrx

/-- Given a finite recent remainder, the comparison establishes
integrability of the complete weighted cost, rather than assuming it. -/
theorem memoryCost_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (η L : ℝ) (old recent : Ω → Tensor) (v : Ω → Fin 3 → ℝ)
    (hη : 0 ≤ η) (hL : 0 ≤ L)
    (hm : AEStronglyMeasurable (fun x ↦ memoryCost η (old x + recent x) (v x)) μ)
    (hv : Integrable (fun x ↦ vectorSquare (v x)) μ)
    (hr : Integrable (fun x ↦ (tensorTrace (recent x)) ^ 2 * vectorSquare (v x)) μ)
    (htnonneg : ∀ᵐ x ∂μ, 0 ≤ tensorTrace (old x))
    (htold : ∀ᵐ x ∂μ, tensorTrace (old x) ≤ 3 * L)
    (htrecent : ∀ᵐ x ∂μ, 0 ≤ tensorTrace (recent x))
    (hqold : ∀ᵐ x ∂μ, 0 ≤ quadratic (old x) (v x))
    (hold : ∀ᵐ x ∂μ, quadratic (old x) (v x) ≤ L * vectorSquare (v x))
    (hqrecent : ∀ᵐ x ∂μ, 0 ≤ quadratic (recent x) (v x))
    (hrecent : ∀ᵐ x ∂μ,
      quadratic (recent x) (v x) ≤ tensorTrace (recent x) * vectorSquare (v x)) :
    Integrable (fun x ↦ memoryCost η (old x + recent x) (v x)) μ := by
  apply ((hv.const_mul (5 * (η + L) ^ 2)).add (hr.const_mul 3)).mono_nonneg hm
  · filter_upwards [htnonneg, htrecent, hqold, hqrecent] with x hto htr hqo hqr
    apply memoryCost_nonneg η (old x + recent x) (v x) hη
    · rw [tensorTrace_add]; exact add_nonneg hto htr
    · rw [quadratic_add]; exact add_nonneg hqo hqr
  · filter_upwards [htold, htrecent, hqold, hold, hqrecent, hrecent]
      with x hto htr hqo ho hqr hrx
    simpa only [Pi.add_apply, mul_assoc] using
      memoryCost_split η L (old x) (recent x) (v x) hη hL hto htr hqo ho hqr hrx

def pressureCoordinates (V : L2) (x : Space) : Fin 3 → ℝ := fun i ↦ V x i

theorem pressureCoordinates_square (V : L2) (x : Space) :
    vectorSquare (pressureCoordinates V x) = ‖V x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

theorem pressureCoordinates_square_integrable (V : L2) :
    Integrable (fun x ↦ vectorSquare (pressureCoordinates V x)) := by
  simp_rw [pressureCoordinates_square]
  exact (memLp_two_iff_integrable_sq_norm (Lp.memLp V).aestronglyMeasurable).1 (Lp.memLp V)

theorem integral_pressureCoordinates_square (V : L2) :
    (∫ x, vectorSquare (pressureCoordinates V x)) = ‖V‖ ^ 2 := by
  simp_rw [pressureCoordinates_square]
  exact (EulerLpBochnerRealization.norm_sq_eq_integral V).symm

/-- The two native diffusion costs that actually pay the canonical
receiver, before any matrix completion lower bound is applied. -/
def receiverNativeCost (u : SmoothL2Field Space) (ν b : ℝ)
    (h z : Space → ℝ) : ℝ :=
  ∑ k : Fin 3,
    (2 * ν * (∫ x, extendedWeight b (z x) *
      normSq (gradMatrix ((pressureField u).directionalField (axis k)) x)) +
      ∫ x, selectionDiffusion ν h z b k x)

/-- A literal consumer of the constructed negative Helmholtz projection.
The full augmented diffusion dominates the pressure part of this cost. -/
theorem actual_receiver_native_paid (u : SmoothL2Field Space) (ν b : ℝ)
    (hν : 0 < ν) (hb : 0 < b) (h z : Space → ℝ) (hh : ∀ x, 0 ≤ h x)
    {Kz : ℝ≥0} (hz : LipschitzWith Kz z)
    (hP : ∀ x, pressureSquare u x ≤ h x * z x)
    (hJ : ∀ k : Fin 3, Integrable (selectionDiffusion ν h z b k)) :
    ν * ‖receiverPressureGradient u b z
      (receiverDivergence_memLp u ν b hν hb h z hh hz hP hJ)‖ ^ 2 ≤
        48 * receiverNativeCost u ν b h z := by
  apply (receiverPressureGradient_paid u ν b hν hb h z hh hz hP hJ).trans
  rw [receiverNativeCost, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have hp : 0 ≤ ∫ x, extendedWeight b (z x) *
      normSq (gradMatrix ((pressureField u).directionalField (axis k)) x) := by
    apply integral_nonneg
    intro x
    exact mul_nonneg (extendedWeight_nonneg b (z x) hb)
      (by unfold normSq; positivity)
  nlinarith only [mul_nonneg hν.le hp]

/-- The weighted comparison applied to the actual canonical receiver.
Its age bound, positivity and recent integrability remain explicit. The
recent tensor is not discarded, reset or replaced by a future supremum. -/
theorem actual_receiver_age_split (u : SmoothL2Field Space) (ν b : ℝ)
    (hν : 0 < ν) (hb : 0 < b) (h z : Space → ℝ) (hh : ∀ x, 0 ≤ h x)
    {Kz : ℝ≥0} (hz : LipschitzWith Kz z)
    (hP : ∀ x, pressureSquare u x ≤ h x * z x)
    (hJ : ∀ k : Fin 3, Integrable (selectionDiffusion ν h z b k))
    (η L : ℝ) (hη : 0 ≤ η) (hL : 0 ≤ L) (old recent : Space → Tensor)
    (V : EulerMeanSolenoidal.L2)
    (hV : V = receiverPressureGradient u b z
      (receiverDivergence_memLp u ν b hν hb h z hh hz hP hJ))
    (hm : AEStronglyMeasurable
      (fun x ↦ memoryCost η (old x + recent x) (pressureCoordinates V x)))
    (hr : Integrable
      (fun x ↦ (tensorTrace (recent x)) ^ 2 * vectorSquare (pressureCoordinates V x)))
    (htnonneg : ∀ᵐ x, 0 ≤ tensorTrace (old x))
    (htold : ∀ᵐ x, tensorTrace (old x) ≤ 3 * L)
    (htrecent : ∀ᵐ x, 0 ≤ tensorTrace (recent x))
    (hqold : ∀ᵐ x, 0 ≤ quadratic (old x) (pressureCoordinates V x))
    (hold : ∀ᵐ x,
      quadratic (old x) (pressureCoordinates V x) ≤ L * vectorSquare (pressureCoordinates V x))
    (hqrecent : ∀ᵐ x, 0 ≤ quadratic (recent x) (pressureCoordinates V x))
    (hrecent : ∀ᵐ x, quadratic (recent x) (pressureCoordinates V x) ≤
      tensorTrace (recent x) * vectorSquare (pressureCoordinates V x)) :
    ν * (∫ x, memoryCost η (old x + recent x) (pressureCoordinates V x)) ≤
      240 * (η + L) ^ 2 * receiverNativeCost u ν b h z +
        3 * ν * ∫ x, (tensorTrace (recent x)) ^ 2 * vectorSquare (pressureCoordinates V x) := by
  have hv := pressureCoordinates_square_integrable V
  have hc := memoryCost_integrable volume η L old recent (pressureCoordinates V)
    hη hL hm hv hr htnonneg htold htrecent hqold hold hqrecent hrecent
  have hi := integral_memoryCost_split volume η L old recent (pressureCoordinates V)
    hη hL hc hv hr htold htrecent hqold hold hqrecent hrecent
  rw [integral_pressureCoordinates_square] at hi
  have hn := actual_receiver_native_paid u ν b hν hb h z hh hz hP hJ
  rw [← hV] at hn
  have h₁ := mul_le_mul_of_nonneg_left hi hν.le
  have h₂ := mul_le_mul_of_nonneg_left hn (show 0 ≤ 5 * (η + L) ^ 2 by positivity)
  nlinarith only [h₁, h₂]

/-- Combining a weighted split with a native receiver payment leaves
the full recent-memory cost as a named remainder. -/
theorem weighted_cost_native (ν K U Q R T : ℝ) (hν : 0 < ν)
    (hu : ν * U ≤ 48 * Q) (ht : T ≤ 5 * K ^ 2 * U + 3 * R) :
    T ≤ (240 * K ^ 2 / ν) * Q + 3 * R := by
  have hp := mul_le_mul_of_nonneg_left hu
    (show 0 ≤ 5 * K ^ 2 / ν by positivity)
  have he : (5 * K ^ 2 / ν) * (ν * U) = 5 * K ^ 2 * U := by field_simp
  have he₂ : (5 * K ^ 2 / ν) * (48 * Q) = (240 * K ^ 2 / ν) * Q := by ring
  rw [he, he₂] at hp
  linarith only [ht, hp]

/-- The original datum allowance is charged once for the entire prefix.
The entropy pairing is an explicit hypothesis; its physical time
identification and the recent cost are not proved by this scalar step. -/
theorem age_pressure_paid (ν η ε K E U Q R T I : ℝ)
    (hν : 0 < ν) (hη : 0 < η) (hε : 0 < ε) (hK : 0 < K)
    (hu : ν * U ≤ 48 * Q) (ht : T ≤ 5 * K ^ 2 * U + 3 * R)
    (hpair : |I| ≤ (60 * K ^ 2 / (ε * ν ^ 2 * η)) * E +
      T / (4 * (60 * K ^ 2 / (ε * ν ^ 2 * η)) * ν * η)) :
    |I| ≤ (60 * K ^ 2 * E / (ε * ν ^ 2 * η)) +
      ε * Q + (ε * ν / (80 * K ^ 2)) * R := by
  have hw := weighted_cost_native ν K U Q R T hν hu ht
  have hd : 0 < 4 * (60 * K ^ 2 / (ε * ν ^ 2 * η)) * ν * η := by positivity
  have hp := div_le_div_of_nonneg_right hw hd.le
  have he : (60 * K ^ 2 / (ε * ν ^ 2 * η)) * E +
      ((240 * K ^ 2 / ν) * Q + 3 * R) /
        (4 * (60 * K ^ 2 / (ε * ν ^ 2 * η)) * ν * η) =
      (60 * K ^ 2 * E / (ε * ν ^ 2 * η)) +
        ε * Q + (ε * ν / (80 * K ^ 2)) * R := by
    field_simp
    ring
  rw [← he]
  linarith only [hpair, hp]

/-- Native payment with the sharper anisotropic remainder. -/
theorem weighted_cost_anisotropic (ν K U Q R T : ℝ) (hν : 0 < ν)
    (hu : ν * U ≤ 48 * Q) (ht : T ≤ 3 * K ^ 2 * U + R) :
    T ≤ (144 * K ^ 2 / ν) * Q + R := by
  have hp := mul_le_mul_of_nonneg_left hu
    (show 0 ≤ 3 * K ^ 2 / ν by positivity)
  have he : (3 * K ^ 2 / ν) * (ν * U) = 3 * K ^ 2 * U := by field_simp
  have he₂ : (3 * K ^ 2 / ν) * (48 * Q) = (144 * K ^ 2 / ν) * Q := by ring
  rw [he, he₂] at hp
  linarith only [ht, hp]

/-- This payment retains both fresh directional work and its isotropic
trace term. The allowance comes from one original source budget. -/
theorem age_pressure_paid_anisotropic (ν η ε K E U Q R T I : ℝ)
    (hν : 0 < ν) (hη : 0 < η) (hε : 0 < ε) (hK : 0 < K)
    (hu : ν * U ≤ 48 * Q) (ht : T ≤ 3 * K ^ 2 * U + R)
    (hpair : |I| ≤ (36 * K ^ 2 / (ε * ν ^ 2 * η)) * E +
      T / (4 * (36 * K ^ 2 / (ε * ν ^ 2 * η)) * ν * η)) :
    |I| ≤ (36 * K ^ 2 * E / (ε * ν ^ 2 * η)) +
      ε * Q + (ε * ν / (144 * K ^ 2)) * R := by
  have hw := weighted_cost_anisotropic ν K U Q R T hν hu ht
  have hd : 0 < 4 * (36 * K ^ 2 / (ε * ν ^ 2 * η)) * ν * η := by positivity
  have hp := div_le_div_of_nonneg_right hw hd.le
  have he : (36 * K ^ 2 / (ε * ν ^ 2 * η)) * E +
      ((144 * K ^ 2 / ν) * Q + R) /
        (4 * (36 * K ^ 2 / (ε * ν ^ 2 * η)) * ν * η) =
      (36 * K ^ 2 * E / (ε * ν ^ 2 * η)) +
        ε * Q + (ε * ν / (144 * K ^ 2)) * R := by
    field_simp
    ring
  rw [← he]
  linarith only [hpair, hp]

/-- The low-frequency polynomial of the shear gradient square when
only frequencies up to three are retained; `x=cos y`. Its Fourier
identification is checked exactly in the companion lab. -/
def filteredShearSource (x : ℝ) : ℝ :=
  (3 / 2 : ℝ) + 2 * x + (3 / 2 : ℝ) * (2 * x ^ 2 - 1) + (4 * x ^ 3 - 3 * x)

theorem filteredShearSource_negative :
    filteredShearSource (1 / 10) = -(33 / 500 : ℝ) := by
  norm_num [filteredShearSource]

/-- The actual gradient square at the same point is strictly positive. -/
theorem unfilteredShearSource_positive :
    ((1 / 10 : ℝ) + (2 * (1 / 10 : ℝ) ^ 2 - 1) +
      (4 * (1 / 10 : ℝ) ^ 3 - 3 * (1 / 10 : ℝ))) ^ 2 = (21609 / 15625 : ℝ) := by
  norm_num

/-- Positive viscosity does not repair a nonpositive projected source.
This concerns truncated auxiliary memory, not the actual NS covariance. -/
theorem filteredShearMemory_rate_negative (ν : ℝ) (hν : 0 < ν) :
    2 * ν * filteredShearSource (1 / 10) < 0 := by
  rw [filteredShearSource_negative]
  nlinarith only [hν]

end Mettapedia.FluidDynamics.NavierStokes.MemoryAgePressure
