import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicGradientFluxSymbol
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFixedOutputVelocityBound
import Mettapedia.Analysis.UnitTorusGradientTransport

/-!
# Actual continuous jets of the gradient-projected Fourier tensor

Absolute summability of a tensor's coefficients and their first
derivatives constructs the corresponding projected translation jets.
The projection has a uniform coefficient bound and commutes with
constant spatial derivatives. Its curl symmetry is proved from its
symbol, not assumed. Repeated output frequencies are allowed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PeriodicProjectedTensorJet

open scoped RealInnerProductSpace
open Mettapedia.Analysis UnitTorusGradientProjection UnitTorusGradientTransport
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFourierTranslationCurve PancakeInfiniteFourierDerivative
open PancakeIndexedFourierMoments PancakeFixedOutputVelocityBound PancakePhysicalSixthDecay
open PancakeDyadicDirectionEvolution
open PeriodicGradientFluxSymbol

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem norm_projectedCoeff_le_sum (n : Wavevector) (J : Fin 3 → VelocityCoefficient) (j : Fin 3) :
    ‖projectedCoeff n J j‖ ≤ 4 * ∑ l, ‖J l‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  let a : VelocityCoefficient := fun l ↦ J l i
  have ha : ‖a‖ ≤ ∑ l, ‖J l‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro l
    exact (norm_le_pi_norm (J l) i).trans
      (Finset.single_le_sum (fun k _ ↦ norm_nonneg (J k)) (Finset.mem_univ l))
  have he : projectedCoeff n J j i = (a - lerayMode n a) j := by
    by_cases hn : modeSquare n = 0
    · simp [projectedCoeff, hn, lerayMode]
    · simp only [projectedCoeff, contraction, Pi.smul_apply, smul_eq_mul,
        Finset.sum_apply, Pi.sub_apply, lerayMode, hn, dite_false, sub_sub_cancel, modeDot, a]
      ring
  have hl : ‖lerayMode n a‖ ≤ 3 * ‖a‖ :=
    (norm_coefficient_sup_le_euclidean _).trans ((norm_lerayMode_le n a).trans
      (norm_coefficientVec_le_three a ‖a‖ (norm_nonneg _) (norm_le_pi_norm a)))
  rw [he]
  exact (norm_le_pi_norm _ j).trans ((norm_sub_le _ _).trans (by linarith))

def projectedFamily {ι : Type*} (freq : ι → Wavevector)
    (J : Fin 3 → ι → VelocityCoefficient) (j : Fin 3) (q : ι) : VelocityCoefficient :=
  projectedCoeff (freq q) (fun l ↦ J l q) j

theorem projectedCoeff_smul (n : Wavevector) (c : ℂ)
    (J : Fin 3 → VelocityCoefficient) (j : Fin 3) :
    projectedCoeff n (fun l ↦ c • J l) j = c • projectedCoeff n J j := by
  simp only [projectedCoeff, contraction, smul_comm (n _ : ℂ) c, ← Finset.smul_sum,
    smul_comm ((n j : ℂ) / modeSquare n) c]

theorem derivative_projectedFamily {ι : Type*} (freq : ι → Wavevector)
    (J : Fin 3 → ι → VelocityCoefficient) (j k : Fin 3) :
    indexedDerivativeCoeff freq k (projectedFamily freq J j) =
      projectedFamily freq (fun l ↦ indexedDerivativeCoeff freq k (J l)) j := by
  funext q
  exact (projectedCoeff_smul (freq q) _ _ j).symm

theorem summable_norm_projectedFamily {ι : Type*} (freq : ι → Wavevector)
    (J : Fin 3 → ι → VelocityCoefficient) (hJ : ∀ j, Summable (fun q ↦ ‖J j q‖)) (j : Fin 3) :
    Summable (fun q ↦ ‖projectedFamily freq J j q‖) :=
  ((summable_sum (fun l (_ : l ∈ (Finset.univ : Finset (Fin 3))) ↦ hJ l)).mul_left 4).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) (fun q ↦ norm_projectedCoeff_le_sum (freq q) _ j)

def indexedRealField {ι : Type*} (freq : ι → Wavevector) (a : ι → VelocityCoefficient) : C(T3, R3) :=
  (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3) (fullFourierField freq a)

def fieldJet {ι : Type*} (freq : ι → Wavevector) (a : ι → VelocityCoefficient)
    (ha : Summable (fun q ↦ ‖a q‖))
    (hd : ∀ k, Summable (fun q ↦ ‖indexedDerivativeCoeff freq k a q‖)) : TranslationJet (Fin 3) R3 where
  value := indexedRealField freq a
  gradient k := indexedRealField freq (indexedDerivativeCoeff freq k a)
  hasDerivAt k x h := by
    exact complexRealPartEuclideanCLM.hasFDerivAt.comp_hasDerivAt h
      (hasDerivAt_fullFourierField_shift freq a ha k (hd k) h x)

def projectedJet {ι : Type*} (freq : ι → Wavevector) (J : Fin 3 → ι → VelocityCoefficient)
    (hJ : ∀ j, Summable (fun q ↦ ‖J j q‖))
    (hdJ : ∀ j k, Summable (fun q ↦ ‖indexedDerivativeCoeff freq k (J j) q‖))
    (j : Fin 3) : TranslationJet (Fin 3) R3 :=
  fieldJet freq (projectedFamily freq J j) (summable_norm_projectedFamily freq J hJ j)
    (fun k ↦ by
      rw [derivative_projectedFamily]
      exact summable_norm_projectedFamily freq _ (fun l ↦ hdJ l k) j)

theorem projectedJet_curl {ι : Type*} (freq : ι → Wavevector) (J : Fin 3 → ι → VelocityCoefficient)
    (hJ : ∀ j, Summable (fun q ↦ ‖J j q‖))
    (hdJ : ∀ j k, Summable (fun q ↦ ‖indexedDerivativeCoeff freq k (J j) q‖)) (j k : Fin 3) :
    (projectedJet freq J hJ hdJ k).gradient j = (projectedJet freq J hJ hdJ j).gradient k := by
  change indexedRealField freq (indexedDerivativeCoeff freq j (projectedFamily freq J k)) =
    indexedRealField freq (indexedDerivativeCoeff freq k (projectedFamily freq J j))
  congr 1
  funext q
  simp only [indexedDerivativeCoeff, projectedFamily, projectedCoeff, smul_smul]
  congr 1
  ring

theorem indexedRealField_eq_tsum {ι : Type*} (freq : ι → Wavevector)
    (a : ι → VelocityCoefficient) (ha : Summable (fun q ↦ ‖a q‖)) :
    indexedRealField freq a = ∑' q, realMode (freq q) (a q) :=
  (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3).map_tsum (summable_modeField freq a ha)

theorem gradientProjection_eq_field {ι : Type*} (freq : ι → Wavevector)
    (J : Fin 3 → ι → VelocityCoefficient) (hJ : ∀ j, Summable (fun q ↦ ‖J j q‖)) :
    gradientProjection (toTensorL2 (fun j ↦ indexedRealField freq (J j))) =
      toTensorL2 (fun j ↦ indexedRealField freq (projectedFamily freq J j)) := by
  have hP := gradientProjection_indexedFourier freq J hJ
  change gradientProjection (toTensorL2 (fun j ↦ indexedRealField freq (J j))) = _ at hP
  rw [hP]
  have hs : Summable (fun q ↦ fun j ↦ realMode (freq q) (projectedFamily freq J j q)) := by
    apply Pi.summable.mpr
    intro j
    exact (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3).summable
      (summable_modeField freq _ (summable_norm_projectedFamily freq J hJ j))
  have he : (fun j ↦ indexedRealField freq (projectedFamily freq J j)) =
      ∑' q, fun j ↦ realMode (freq q) (projectedFamily freq J j q) := by
    funext j
    rw [tsum_apply hs, indexedRealField_eq_tsum freq _ (summable_norm_projectedFamily freq J hJ j)]
  rw [he]
  exact ((tensorEmbedding (d := Fin 3) (E := R3)).map_tsum hs).symm

theorem inner_projected_transport {ι : Type*} (freq : ι → Wavevector)
    (J : Fin 3 → ι → VelocityCoefficient)
    (hJ : ∀ j, Summable (fun q ↦ ‖J j q‖))
    (hdJ : ∀ j k, Summable (fun q ↦ ‖indexedDerivativeCoeff freq k (J j) q‖))
    (b : Fin 3 → TranslationJet (Fin 3) ℝ)
    (hb : ∀ x, ∑ k, (b k).gradient k x = 0) :
    ⟪gradientProjection (toTensorL2 (fun j ↦ indexedRealField freq (J j))),
      toTensorL2 (fun j ↦ transport b (fieldJet freq (J j) (hJ j) (hdJ j)))⟫ =
      ⟪toTensorL2 (deformation b (projectedJet freq J hJ hdJ)),
        toTensorL2 (fun j ↦ indexedRealField freq (J j)) -
          gradientProjection (toTensorL2 (fun j ↦ indexedRealField freq (J j)))⟫ := by
  rw [gradientProjection_eq_field freq J hJ]
  exact inner_projected_transport_eq_deformation b (projectedJet freq J hJ hdJ)
    (fun j ↦ fieldJet freq (J j) (hJ j) (hdJ j)) hb
    (projectedJet_curl freq J hJ hdJ) (gradientProjection_eq_field freq J hJ)

end Mettapedia.FluidDynamics.NavierStokes.PeriodicProjectedTensorJet
