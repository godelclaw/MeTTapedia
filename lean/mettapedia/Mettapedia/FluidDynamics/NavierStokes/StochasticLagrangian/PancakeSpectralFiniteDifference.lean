import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeRegularizedDiffusion

/-!
# A collision-safe finite-difference replacement for the diffusion chain rule

The supporting Rayleigh functional and exact quadratic expansion give a
paid finite-increment inequality for the actual regularized spectral
energy. No spatial derivative of the largest eigenvalue is used. This is
an algebraic precursor to the weak spatial limit, not that limit itself.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeSpectralFiniteDifference

open scoped RealInnerProductSpace
open PancakeRegularizedDiffusion PancakeSpectralDefectEvolution PancakeStrainSpectralFrame
open PancakeTopEigenvalueDerivative PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def topVector (S : SymmetricStrain) : R3 := (orderedEigenframe S.1 S.2).eigenbasis 0

theorem topVector_norm (S : SymmetricStrain) : ‖topVector S‖ = 1 :=
  (orderedEigenframe S.1 S.2).eigenbasis.norm_eq_one 0

theorem topVector_rayleigh (S : SymmetricStrain) :
    ⟪topVector S, S.1 (topVector S)⟫ = topEigenvalue S := by
  rw [topVector, (orderedEigenframe S.1 S.2).apply_eigenbasis]
  simp [topEigenvalue, real_inner_smul_right, (orderedEigenframe S.1 S.2).eigenbasis.norm_eq_one]

def supportingRemainder (S T : SymmetricStrain) : ℝ :=
  topEigenvalue T - topEigenvalue S - ⟪topVector S, (T.1 - S.1) (topVector S)⟫

theorem supportingRemainder_nonneg (S T : SymmetricStrain) : 0 ≤ supportingRemainder S T := by
  have h := PancakeSpectralClusterDichotomy.rayleigh_le_topEigenvalue_mul_norm_sq T.1 T.2 (topVector S)
  rw [topVector_norm] at h
  norm_num at h
  simp only [supportingRemainder, sub_apply, inner_sub_right, topVector_rayleigh]
  change ⟪topVector S, T.1 (topVector S)⟫ ≤ topEigenvalue T at h
  linarith

theorem regularizedGap_symmetric (S : SymmetricStrain) (delta : ℝ) (v w : R3) :
    ⟪v, regularizedGap S delta w⟫ = ⟪regularizedGap S delta v, w⟫ := by
  simp only [regularizedGap, sub_apply, smul_apply, one_apply_eq_self, inner_sub_left,
    inner_sub_right, real_inner_smul_left, real_inner_smul_right, S.2]

theorem regularizedGap_sub_norm (S T : SymmetricStrain) (delta : ℝ) :
    ‖regularizedGap T delta - regularizedGap S delta‖ ≤ 2 * ‖T.1 - S.1‖ := by
  have hl := lipschitzWith_topEigenvalue.dist_le_mul T S
  simp only [NNReal.coe_one, one_mul, Subtype.dist_eq, dist_eq_norm, Real.norm_eq_abs] at hl
  have heq : regularizedGap T delta - regularizedGap S delta =
      (topEigenvalue T - topEigenvalue S) • (1 : R3 →L[ℝ] R3) - (T.1 - S.1) := by
    unfold regularizedGap
    module
  rw [heq]
  apply (norm_sub_le _ _).trans
  simp only [norm_smul, norm_one, Real.norm_eq_abs, mul_one]
  linarith

def regularizedEnergy (S : SymmetricStrain) (delta : ℝ) (w : R3) : ℝ :=
  ⟪w, regularizedGap S delta w⟫

def incrementRate (S T : SymmetricStrain) (delta : ℝ) (w v : R3) : ℝ :=
  remainderAnisotropy (T.1 - S.1) (topVector S) w + 2 * ⟪regularizedGap S delta w, v⟫

theorem regularizedEnergy_increment (S T : SymmetricStrain) (delta : ℝ) (w v : R3) :
    regularizedEnergy T delta (w + v) - regularizedEnergy S delta w - incrementRate S T delta w v =
      supportingRemainder S T * ‖w‖ ^ 2 +
        2 * ⟪v, (regularizedGap T delta - regularizedGap S delta) w⟫ +
        ⟪v, regularizedGap T delta v⟫ := by
  simp only [regularizedEnergy, incrementRate, supportingRemainder, remainderAnisotropy,
    regularizedGap, sub_apply, smul_apply, one_apply_eq_self, map_add, inner_add_left,
    inner_add_right, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_comm w v, T.2 w v, real_inner_comm (T.1 w) v, real_inner_comm (S.1 w) v]
  ring

/-- Exact finite-increment estimate, valid through every eigenvalue collision. -/
theorem incrementRate_paid (S T : SymmetricStrain) (delta : ℝ) (w v : R3) (hd : 0 < delta) :
    incrementRate S T delta w v + (delta / 2) * ‖v‖ ^ 2 ≤
      regularizedEnergy T delta (w + v) - regularizedEnergy S delta w +
        (8 / delta) * ‖T.1 - S.1‖ ^ 2 * ‖w‖ ^ 2 := by
  let G := regularizedGap T delta - regularizedGap S delta
  have hi := regularizedEnergy_increment S T delta w v
  have hy := spectralDefect_forcing_young v (-G w) (delta / 2) (by positivity)
  simp only [inner_neg_right, norm_neg] at hy
  have hc := regularizedGap_coercive T delta v
  have hr := mul_nonneg (supportingRemainder_nonneg S T) (sq_nonneg ‖w‖)
  have hG := regularizedGap_sub_norm S T delta
  have hop := G.le_opNorm w
  have hsq : ‖G w‖ ^ 2 ≤ 4 * ‖T.1 - S.1‖ ^ 2 * ‖w‖ ^ 2 := by
    calc
      _ ≤ (‖G‖ * ‖w‖) ^ 2 := by gcongr
      _ ≤ ((2 * ‖T.1 - S.1‖) * ‖w‖) ^ 2 := by gcongr
      _ = _ := by ring
  have hpay : ‖G w‖ ^ 2 / (delta / 2) ≤
      (8 / delta) * ‖T.1 - S.1‖ ^ 2 * ‖w‖ ^ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < delta / 2)).mpr
    field_simp
    nlinarith
  dsimp only [G] at hy hpay
  linarith

/-- Under a finite periodic reindexing the energy increments telescope.
No eigenframe regularity or continuum limiting argument is assumed. -/
theorem sum_incrementRate_paid {ι : Type*} [Fintype ι] (sigma : Equiv.Perm ι)
    (S : ι → SymmetricStrain) (w : ι → R3) (delta : ℝ) (hd : 0 < delta) :
    (∑ i, incrementRate (S i) (S (sigma i)) delta (w i) (w (sigma i) - w i)) +
      (delta / 2) * (∑ i, ‖w (sigma i) - w i‖ ^ 2) ≤
        (8 / delta) * ∑ i, ‖(S (sigma i)).1 - (S i).1‖ ^ 2 * ‖w i‖ ^ 2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
    incrementRate_paid (S i) (S (sigma i)) delta (w i) (w (sigma i) - w i) hd)
  have heq : (∑ i, regularizedEnergy (S (sigma i)) delta (w (sigma i))) =
      ∑ i, regularizedEnergy (S i) delta (w i) :=
    Equiv.sum_comp sigma (fun i ↦ regularizedEnergy (S i) delta (w i))
  have hw : ∀ i, w i + (w (sigma i) - w i) = w (sigma i) := fun i ↦ by abel
  simp only [hw, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum] at h
  rw [heq, sub_self, zero_add] at h
  simpa only [Finset.mul_sum, mul_assoc] using h

end Mettapedia.FluidDynamics.NavierStokes.PancakeSpectralFiniteDifference
