import MettapediaNS.JointSourceHistory
import MettapediaNS.WholeSpaceHistoryBridge

/-!
# Directional cubic renewal in the original history

The original two-index gradient packet and the actual curl have dual
strain rates. Their cubic observation cancels strain, retaining all
mixed spatial diffusion. The physical stretching additionally retains
the symmetric gradient compatibility defect. A same-path cubic label
is invariant before averaging; a product of three averaged fields is
not that same-path expectation.

The actual whole-space energy balance below makes a signed renewal
budget sufficient for the existing continuation theorem. The budget
is an explicit open hypothesis, not supplied by this module. Original
stochastic construction, the passive-scalar realization and its spatial
mass conservation remain analytic obligations.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.JointCubicRenewal

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSolenoidal
  EulerVolterraConvolution EulerContinuousTimeIntegral WholeSpaceOrderEnergy
  WholeSpaceViscousFlow WholeSpaceBetchov JointReceiverTensor JointTensorSymmetry
  WholeSpaceHistoryBridge
open scoped Matrix BigOperators

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ
local notation "Vec3" => Fin 3 → ℝ

def cubicObservation (A : Mat3) (w : Vec3) : ℝ := w ⬝ᵥ (A *ᵥ w)

def cubicDerivative (A R : Mat3) (w v : Vec3) : ℝ :=
  v ⬝ᵥ (A *ᵥ w) + w ⬝ᵥ (R *ᵥ w) + w ⬝ᵥ (A *ᵥ v)

def mixedDiffusion (A : Mat3) (w : Vec3)
    (dA : Fin 3 → Mat3) (dw : Fin 3 → Vec3) : ℝ :=
  ∑ k, (dw k ⬝ᵥ (A *ᵥ dw k) + dw k ⬝ᵥ (dA k *ᵥ w) +
    w ⬝ᵥ (dA k *ᵥ dw k))

def cubicProduction (ν : ℝ) (A R : Mat3) (w v : Vec3)
    (dA : Fin 3 → Mat3) (dw : Fin 3 → Vec3) : ℝ :=
  cubicDerivative A R w v - 2 * ν * mixedDiffusion A w dA dw

theorem dual_strain_cancellation (B A : Mat3) (w : Vec3) :
    cubicDerivative A (-B.transpose * A - A * B) w (B *ᵥ w) = 0 := by
  unfold cubicDerivative
  simp only [Matrix.sub_mulVec, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_sub, dotProduct_neg, Matrix.neg_mul, Matrix.dotProduct_transpose_mulVec,
    dotProduct_comm]
  ring

/-- All spatial derivatives remain; their mixed cost is signed. -/
theorem original_cubic_production (ν : ℝ) (B A : Mat3) (w : Vec3)
    (dA : Fin 3 → Mat3) (dw : Fin 3 → Vec3) :
    cubicProduction ν A (tensorRate B A 0 0) w (B *ᵥ w) dA dw =
      -2 * ν * mixedDiffusion A w dA dw := by
  simp only [cubicProduction, tensorRate, retainedSource, mul_zero,
    sub_zero, add_zero, dual_strain_cancellation, zero_sub]
  ring

/-- A physical curl source survives even when instantaneous kinetic
work is zero. No particular forcing construction is assumed here. -/
theorem forced_cubic_production (ν : ℝ) (B A : Mat3) (w g : Vec3)
    (dA : Fin 3 → Mat3) (dw : Fin 3 → Vec3) :
    cubicProduction ν A (tensorRate B A 0 0) w (B *ᵥ w + g) dA dw =
      -2 * ν * mixedDiffusion A w dA dw +
        g ⬝ᵥ (A *ᵥ w) + w ⬝ᵥ (A *ᵥ g) := by
  have hc := dual_strain_cancellation B A w
  simp only [cubicDerivative] at hc
  simp only [cubicProduction, tensorRate, retainedSource, mul_zero,
    sub_zero, add_zero, cubicDerivative, add_dotProduct, Matrix.mulVec_add,
    dotProduct_add]
  linarith

theorem physical_stretching_reconstruction (A B : Mat3) (w : Vec3) :
    cubicObservation B w = cubicObservation A w -
      cubicObservation (gradientDefect A B) w := by
  simp only [cubicObservation, gradientDefect, Matrix.sub_mulVec, dotProduct_sub]
  ring

def cubicCovariance (h : ℝ) (A : Mat3) (w : Vec3) : ℝ :=
  h - cubicObservation A w

theorem original_history_reconstruction (h : ℝ) (A B : Mat3) (w : Vec3) :
    cubicObservation B w = h - cubicCovariance h A w -
      cubicObservation (gradientDefect A B) w := by
  rw [physical_stretching_reconstruction A B w, cubicCovariance]
  ring

theorem mixed_diffusion_sub (A B : Mat3) (w : Vec3)
    (dA dB : Fin 3 → Mat3) (dw : Fin 3 → Vec3) :
    mixedDiffusion (A - B) w (fun k ↦ dA k - dB k) dw =
      mixedDiffusion A w dA dw - mixedDiffusion B w dB dw := by
  unfold mixedDiffusion
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Matrix.sub_mulVec, dotProduct_sub]
  ring

/-- Pressure remains in the directional compatibility work. -/
theorem defect_cubic_production (ν : ℝ) (B E P : Mat3) (w : Vec3)
    (dE : Fin 3 → Mat3) (dw : Fin 3 → Vec3) :
    cubicProduction ν E (-B.transpose * E - E * B + gradientDefectSource B P)
      w (B *ᵥ w) dE dw =
        cubicObservation (gradientDefectSource B P) w -
          2 * ν * mixedDiffusion E w dE dw := by
  have hc := dual_strain_cancellation B E w
  unfold cubicDerivative at hc
  simp only [cubicProduction, cubicDerivative, Matrix.add_mulVec, dotProduct_add,
    cubicObservation]
  linarith

/-- Combining the covariance and compatibility cancels their
original-packet derivatives, not the physical pressure or diffusion. -/
theorem compensated_renewal_production (ν : ℝ) (A B P : Mat3) (w : Vec3)
    (dA dB : Fin 3 → Mat3) (dw : Fin 3 → Vec3) :
    2 * ν * mixedDiffusion A w dA dw +
      cubicProduction ν (gradientDefect A B)
        (-B.transpose * gradientDefect A B - gradientDefect A B * B +
          gradientDefectSource B P) w (B *ᵥ w) (fun k ↦ dA k - dB k) dw =
      cubicObservation (gradientDefectSource B P) w +
        2 * ν * mixedDiffusion B w dB dw := by
  rw [defect_cubic_production]
  unfold gradientDefect
  rw [mixed_diffusion_sub]
  ring

theorem physical_cubic_rate (B P : Mat3) (w : Vec3) :
    cubicDerivative B (-B * B - P) w (B *ᵥ w) =
      cubicObservation (B.transpose * B - P) w := by
  simp only [cubicDerivative, cubicObservation, Matrix.sub_mulVec, Matrix.neg_mul,
    Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, dotProduct_sub, dotProduct_neg,
    Matrix.dotProduct_transpose_mulVec]
  ring

theorem actual_cubic_gradient_rate (ν : ℝ) (u : SmoothL2Field Space)
    (x : Space) (w : Vec3) :
    cubicDerivative (CovectorParentHistory.gradientMatrix u x)
      (JointCoframePressure.actualGradientRate ν u x) w
      (CovectorParentHistory.gradientMatrix u x *ᵥ w) =
        cubicObservation
          ((CovectorParentHistory.gradientMatrix u x).transpose *
            CovectorParentHistory.gradientMatrix u x -
              CovectorParentHistory.gradientMatrix (pressureField u) x) w := by
  have hg : JointCoframePressure.actualGradientRate ν u x =
      -(CovectorParentHistory.gradientMatrix u x *
        CovectorParentHistory.gradientMatrix u x) -
          CovectorParentHistory.gradientMatrix (pressureField u) x := by
    rw [JointCoframePressure.actual_gradient_rate,
      CovectorParentHistory.passive_gradient_rate]
    rfl
  rw [hg]
  simpa only [neg_mul] using physical_cubic_rate
    (CovectorParentHistory.gradientMatrix u x)
      (CovectorParentHistory.gradientMatrix (pressureField u) x) w

/-- Exact same-path transport, before multiplying independent means. -/
theorem same_path_cubic (F J V : Mat3) (w : Vec3) (hFJ : F * J = 1) :
    cubicObservation (F.transpose * V * F) (J *ᵥ w) = cubicObservation V w := by
  have hfw : F *ᵥ (J *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, hFJ, Matrix.one_mulVec]
  unfold cubicObservation
  simp only [← Matrix.mulVec_mulVec, hfw]
  rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm, hfw]

def stretchingMass (u : SmoothL2Field Space) : ℝ :=
  ∫ x, MiddleEigenvalueAlgebra.stretch (gradMatrix u x)

theorem actual_cubic_observation (B : Mat3) :
    cubicObservation B (JointCurlGeometry.tensorCurl B) =
      MiddleEigenvalueAlgebra.stretch B := by
  simp [cubicObservation, JointCurlGeometry.tensorCurl,
    MiddleEigenvalueAlgebra.stretch, MiddleEigenvalueAlgebra.vort,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

theorem stretching_integrable (u : SmoothL2Field Space)
    (hA : u.toLp ∈ solenoidalSpace) :
    Integrable (fun x ↦ MiddleEigenvalueAlgebra.stretch (gradMatrix u x)) := by
  apply ((trCube_integrable u hA).sub (cubicSelf_integrable u)).congr
  filter_upwards [] with x
  rw [Pi.sub_apply, cubicSelf_eq _ (gradMatrix_trace u hA x),
    MiddleEigenvalueAlgebra.trCube_eq _ (gradMatrix_trace u hA x)]
  ring

/-- An unsigned original label allowance need not vanish when the
signed cubic mass cancels. This alone does not pay recurrent renewal. -/
def originalLabelMass (u : SmoothL2Field Space) : ℝ :=
  ∫ x, |MiddleEigenvalueAlgebra.stretch (gradMatrix u x)|

theorem originalLabelMass_nonneg (u : SmoothL2Field Space) : 0 ≤ originalLabelMass u :=
  integral_nonneg fun _ ↦ abs_nonneg _

theorem signed_label_le_original (u : SmoothL2Field Space) :
    |stretchingMass u| ≤ originalLabelMass u := abs_integral_le_integral_abs

theorem stretching_mass_eq (u : SmoothL2Field Space)
    (hA : u.toLp ∈ solenoidalSpace) :
    stretchingMass u = -(∫ x, cubicSelf (gradMatrix u x)) := by
  have htr (x : Space) := gradMatrix_trace u hA x
  have hT := trCube_integrable u hA
  have hC := cubicSelf_integrable u
  have he : (fun x ↦ MiddleEigenvalueAlgebra.stretch (gradMatrix u x)) =
      fun x ↦ MiddleEigenvalueAlgebra.trCube (gradMatrix u x) -
        cubicSelf (gradMatrix u x) := by
    funext x
    rw [cubicSelf_eq _ (htr x), MiddleEigenvalueAlgebra.trCube_eq _ (htr x)]
    ring
  rw [stretchingMass, he, integral_sub hT hC, integral_trCube_eq_zero u hA, zero_sub]

variable {ν T : ℝ} {hT : 0 ≤ T}

/-- A continuous path of the literal physical cubic stretching mass. -/
def stretchingPath (U : NSEvolution ν T hT) : C(Icc (0 : ℝ) T, ℝ) :=
  (1 / 2 : ℝ) • productionPath U 1 + ν • U.orderEnergyPath 2

theorem stretchingPath_apply (U : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) :
    stretchingPath U t = stretchingMass (U.velocity t) := by
  change 1 / 2 * orderProduction 1 (U.velocity t) (U.derivative t) +
    ν * orderEnergy 2 (U.velocity t) = _
  rw [U.derivative_eq_navierStokesRhs, orderProduction_one_eq ν _ _
    (U.velocity_divergence t) (U.solenoidal t) (U.gradient t),
    stretching_mass_eq _ (U.solenoidal t)]
  ring

/-- The physical realization is mean(chi+omega^T E omega), retaining
the original passive label mass at every compatible seam. -/
def renewalPath (U : NSEvolution ν T hT) : C(Icc (0 : ℝ) T, ℝ) :=
  ContinuousMap.const _ (stretchingMass (U.velocity ⟨0, le_rfl, hT⟩)) - stretchingPath U

theorem renewalPath_apply (U : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) :
    renewalPath U t = stretchingMass (U.velocity ⟨0, le_rfl, hT⟩) -
      stretchingMass (U.velocity t) := by
  change _ - stretchingPath U t = _
  rw [stretchingPath_apply, ContinuousMap.const_apply]

theorem original_renewal_balance (U : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) :
    orderEnergy 1 (U.velocity t) + 2 * ν * realIntegral T hT (U.orderEnergyPath 2) t =
      orderEnergy 1 (U.velocity ⟨0, le_rfl, hT⟩) +
        2 * stretchingMass (U.velocity ⟨0, le_rfl, hT⟩) * t -
          2 * realIntegral T hT (renewalPath U) t := by
  have hp := production_integral U 1 t
  have he : productionPath U 1 =
      (2 : ℝ) • (ContinuousMap.const _
        (stretchingMass (U.velocity ⟨0, le_rfl, hT⟩)) - renewalPath U) -
          (2 * ν) • U.orderEnergyPath 2 := by
    ext r
    change orderProduction 1 (U.velocity r) (U.derivative r) = _
    dsimp [renewalPath, stretchingPath, productionPath, NSEvolution.orderEnergyPath]
    ring_nf
    rfl
  change integralLinear T hT (productionPath U 1) t = _ at hp
  rw [he, map_sub, map_smul, map_sub, map_smul] at hp
  change 2 * (realIntegral T hT (ContinuousMap.const _
    (stretchingMass (U.velocity ⟨0, le_rfl, hT⟩))) t -
      realIntegral T hT (renewalPath U) t) -
        2 * ν * realIntegral T hT (U.orderEnergyPath 2) t = _ at hp
  rw [realIntegral_const] at hp
  linarith

/-- The arbitrary-history inequality remains a hypothesis. The
remaining dissipation and original datum are visible in the conclusion. -/
theorem signed_renewal_energy_le (U : NSEvolution ν T hT) (t : Icc (0 : ℝ) T)
    (δ K : ℝ)
    (hbudget : -2 * realIntegral T hT (renewalPath U) t ≤
      (2 - δ) * ν * realIntegral T hT (U.orderEnergyPath 2) t + K) :
    orderEnergy 1 (U.velocity t) + δ * ν * realIntegral T hT (U.orderEnergyPath 2) t ≤
      orderEnergy 1 (U.velocity ⟨0, le_rfl, hT⟩) +
        2 * |stretchingMass (U.velocity ⟨0, le_rfl, hT⟩)| * t + K := by
  have he := original_renewal_balance U t
  have ht := t.property.1
  have hb := mul_le_mul_of_nonneg_right
    (le_abs_self (stretchingMass (U.velocity ⟨0, le_rfl, hT⟩))) ht
  nlinarith only [he, hbudget, hb]

/-- This explicitly quantified physical renewal budget is sufficient
for arbitrary-data whole-space continuation; it is not established here. -/
theorem hasNSEvolution_of_signed_renewal {ν : ℝ} (hν : 0 < ν)
    (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace)
    (hbudget : ∀ H, ∃ K, ∀ S (hS : 0 < S), S ≤ H → ∀ U : NSEvolution ν S hS.le,
      U.velocity ⟨0, le_rfl, hS.le⟩ = A → ∀ t,
        -2 * realIntegral S hS.le (renewalPath U) t ≤
          ν * realIntegral S hS.le (U.orderEnergyPath 2) t + K) :
    ∀ H, 0 < H → HasNSEvolution ν A H := by
  apply hasNSEvolution_of_orderOne_bound hν A hA
  intro H
  obtain ⟨K, hK⟩ := hbudget H
  refine ⟨orderEnergy 1 A + 2 * |stretchingMass A| * H + K, ?_⟩
  intro S hS hSH U hU t
  have hb := signed_renewal_energy_le U t 1 K (by
    norm_num
    simpa only [neg_mul] using hK S hS hSH U hU t)
  have hi : 0 ≤ realIntegral S hS.le (U.orderEnergyPath 2) t :=
    intervalIntegral.integral_nonneg (μ := volume) t.property.1
      (fun _ _ ↦ orderEnergy_nonneg 2 _)
  have htH : (t : ℝ) ≤ H := t.property.2.trans hSH
  have hm := mul_le_mul_of_nonneg_left htH (show 0 ≤ 2 * |stretchingMass A| by positivity)
  rw [hU] at hb
  have hn := mul_nonneg hν.le hi
  simp only [one_mul] at hb
  linarith

end Mettapedia.FluidDynamics.NavierStokes.JointCubicRenewal
