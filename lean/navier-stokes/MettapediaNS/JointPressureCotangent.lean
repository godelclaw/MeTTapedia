import MettapediaNS.JointTensorSymmetry

/-!
# Covariant diffusion and the complete pressure cotangent

The divergence of W vec(E) uses the complete covariant residual because
W_k=-W K_k. Its local cotangent is paid by that residual's quadratic
diffusion, but the pressure-gradient leg keeps the partial trace of W.
It is not an unweighted Helmholtz contraction or a history allowance.

Weak spatial integration by parts and the continuous stochastic metric
construction remain explicit analytic obligations. The companion lab
checks full physical metric/pressure jets and annular-swirl scalar
identities. Smooth sign passage and the stochastic Taylor--Green history
payment are analytic.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.JointPressureCotangent

open JointReceiverTensor TransportedFrameMetric
open scoped Matrix BigOperators Kronecker

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ
local notation "Vec3" => Fin 3 → ℝ
local notation "Pair3" => Fin 3 × Fin 3
local notation "Mat9" => Matrix Pair3 Pair3 ℝ

def slotLift (v : Vec3) (j : Fin 3) : Pair3 → ℝ :=
  fun il ↦ if il.2 = j then v il.1 else 0

def pressureReceiver (Q : Mat9) (r : Fin 3 → Pair3 → ℝ) : Vec3 :=
  fun i ↦ ∑ j, (Q *ᵥ r j) (i, j)

/-- The induced pressure metric retains every diagonal spatial slot. -/
def pressureMetric (Q : Mat9) : Mat3 := fun i l ↦ ∑ j : Fin 3, Q (i, j) (l, j)

def residualCost (Q : Mat9) (r : Fin 3 → Pair3 → ℝ) : ℝ :=
  ∑ j, pair Q (r j) (r j)

def pressureCost (Q : Mat9) (v : Vec3) : ℝ := pair (pressureMetric Q) v v

theorem receiver_work (Q : Mat9) (hQ : Q.IsSymm)
    (r : Fin 3 → Pair3 → ℝ) (v : Vec3) :
    (∑ j, pair Q (r j) (slotLift v j)) = v ⬝ᵥ pressureReceiver Q r := by
  simp_rw [pair_symm Q hQ (r _) (slotLift v _)]
  simp [pair, slotLift, pressureReceiver, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Fin.sum_univ_three]
  ring

theorem pressure_cost_eq_slots (Q : Mat9) (v : Vec3) :
    pressureCost Q v = ∑ j, pair Q (slotLift v j) (slotLift v j) := by
  simp [pressureCost, pressureMetric, slotLift, pair, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Fin.sum_univ_three]
  ring

theorem residualCost_nonneg (Q : Mat9) (hQ : Q.PosSemidef)
    (r : Fin 3 → Pair3 → ℝ) : 0 ≤ residualCost Q r :=
  Finset.sum_nonneg fun j _ ↦ hQ.dotProduct_mulVec_nonneg (r j)

theorem pressureCost_nonneg (Q : Mat9) (hQ : Q.PosSemidef) (v : Vec3) :
    0 ≤ pressureCost Q v := by
  rw [pressure_cost_eq_slots]
  exact Finset.sum_nonneg fun j _ ↦ hQ.dotProduct_mulVec_nonneg _

theorem pressureMetric_posSemidef (Q : Mat9) (hQ : Q.PosSemidef) :
    (pressureMetric Q).PosSemidef := by
  have hs : Q.IsSymm := Matrix.isHermitian_iff_isSymm.mp hQ.1
  have hr : (pressureMetric Q).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i l
    unfold pressureMetric
    apply Finset.sum_congr rfl
    intro j _
    exact hs.apply (i, j) (l, j)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_iff_isSymm.mpr hr)
  intro v
  simpa only [star_trivial, pressureCost, pair] using pressureCost_nonneg Q hQ v

private theorem scaled_square (Q : Mat9) (hQ : Q.IsSymm)
    (a b : Pair3 → ℝ) (t : ℝ) :
    pair Q (t • a - b) (t • a - b) =
      t ^ 2 * pair Q a a - 2 * t * pair Q a b + pair Q b b := by
  simp only [pair, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
    dotProduct_sub, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [show b ⬝ᵥ (Q *ᵥ a) = a ⬝ᵥ (Q *ᵥ b) from pair_symm Q hQ b a]
  ring

/-- The completed square keeps the pressure leg in its induced metric. -/
theorem scaled_pressure_young (Q : Mat9) (hQ : Q.PosSemidef)
    (r : Fin 3 → Pair3 → ℝ) (v : Vec3) (ν : ℝ) :
    2 * ν * (v ⬝ᵥ pressureReceiver Q r) ≤
      ν ^ 2 * residualCost Q r + pressureCost Q v := by
  have hs : Q.IsSymm := Matrix.isHermitian_iff_isSymm.mp hQ.1
  have hn := residualCost_nonneg Q hQ (fun j ↦ ν • r j - slotLift v j)
  unfold residualCost at hn
  simp_rw [scaled_square Q hs] at hn
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hn
  rw [receiver_work Q hs, ← pressure_cost_eq_slots] at hn
  change 0 ≤ ν ^ 2 * residualCost Q r -
    2 * ν * (v ⬝ᵥ pressureReceiver Q r) + pressureCost Q v at hn
  linarith only [hn]

/-- For v=-grad p, integration by parts pays half of the original
2nu diffusion while retaining nu^-1 times the induced pressure cost. -/
theorem pressure_absorption (Q : Mat9) (hQ : Q.PosSemidef)
    (r : Fin 3 → Pair3 → ℝ) (v : Vec3) (ν : ℝ) (hν : 0 < ν) :
    2 * (v ⬝ᵥ pressureReceiver Q r) ≤
      ν * residualCost Q r + pressureCost Q v / ν := by
  have hy := scaled_pressure_young Q hQ r v ν
  calc
    _ ≤ (ν ^ 2 * residualCost Q r + pressureCost Q v) / ν := by
      apply (le_div_iff₀ hν).2
      nlinarith only [hy]
    _ = _ := by field_simp

/-- A product-rule metric derivative produces precisely the retained
covariant residual, including its connection term. -/
theorem covariant_flux (Q K : Mat9) (e de : Pair3 → ℝ) :
    TransportedFrameMetric.gradient Q K *ᵥ e + Q *ᵥ de = Q *ᵥ (de - K *ᵥ e) := by
  simp only [TransportedFrameMetric.gradient, Matrix.neg_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
  abel

theorem defect_receiver (Q : Mat9) (K : Fin 3 → Mat9)
    (E : Mat3) (dE : Fin 3 → Mat3) :
    (fun i ↦ ∑ j : Fin 3,
      (TransportedFrameMetric.gradient Q (K j) *ᵥ flatten E +
        Q *ᵥ flatten (dE j)) (i, j)) =
      pressureReceiver Q (fun j ↦ flatten (dE j) - K j *ᵥ flatten E) := by
  simp only [covariant_flux]
  rfl

theorem slot_norm (v : Vec3) (j : Fin 3) :
    slotLift v j ⬝ᵥ slotLift v j = v ⬝ᵥ v := by
  simp [slotLift, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three]

/-- A supplied full metric bound controls the induced pressure metric.
For an evolving fluid, proving that bound from the original data is a
separate physical obligation. -/
theorem pressureCost_le_uniform (Q : Mat9) (κ : ℝ)
    (hκ : ∀ w : Pair3 → ℝ, pair Q w w ≤ κ * (w ⬝ᵥ w)) (v : Vec3) :
    pressureCost Q v ≤ 3 * κ * (v ⬝ᵥ v) := by
  rw [pressure_cost_eq_slots]
  calc
    _ ≤ ∑ j : Fin 3, κ * (slotLift v j ⬝ᵥ slotLift v j) :=
      Finset.sum_le_sum fun j _ ↦ hκ (slotLift v j)
    _ = _ := by simp only [slot_norm, Fin.sum_univ_three]; ring

theorem defect_diffusion_cost (Q : Mat9) (K : Fin 3 → Mat9)
    (E : Mat3) (dE : Fin 3 → Mat3) :
    residualCost Q (fun j ↦ flatten (dE j) - K j *ᵥ flatten E) =
      diffusionCost Q E K dE := rfl

/-- The one-frame case exposes the extra anisotropy factor explicitly.
It is not a uniform comparison to the one-index inverse metric. -/
theorem pressure_metric_kronecker (H : Mat3) :
    pressureMetric (H ⊗ₖ H) = H.trace • H := by
  ext i l
  simp only [pressureMetric, Matrix.kroneckerMap_apply, Matrix.trace, Matrix.diag_apply,
    Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

end Mettapedia.FluidDynamics.NavierStokes.JointPressureCotangent
