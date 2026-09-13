import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierVorticityPairDynamics

/-!
# Dynamics of the amplitude-alignment factor in the exchanged flux

The squared outer vorticity amplitude is evolved together with the inner
cross-product energy. Their product is exactly the amplitude factor in
the exchanged triple-coefficient estimate. All three input heat rates
add, while the nonlinear source retains its sign and full frequency input.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierStretchingInteractionDynamics

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeGalerkinKineticEnergy PancakeGalerkinVorticityBridge
open PancakePeriodicVorticityEquation PancakeFrequencyProjectorCommutator
open PancakeCoefficientLimitEquation PancakeLocalInfiniteVelocity PancakeSignedTransportEnergy
open PeriodicGradientFluxTriple FourierVorticityPairDynamics

def modeEnergy (u : FourierVelocity) (k : Wavevector) : ℝ :=
  coefficientEnergy (fourierCurl u k)

def modeWork (u : FourierVelocity) (k : Wavevector) : ℝ :=
  2 * (coefficientHermitian (fourierCurl u k) (nonlinearCurl u k)).re

def interactionEnergy (u : FourierVelocity) (p : TripleIndex) : ℝ :=
  modeEnergy u p.1 * pairEnergy u p.2.1 p.2.2

def interactionWork (u : FourierVelocity) (p : TripleIndex) : ℝ :=
  modeWork u p.1 * pairEnergy u p.2.1 p.2.2 +
    modeEnergy u p.1 * pairWork u p.2.1 p.2.2

def interactionDamping (ν : ℝ) (p : TripleIndex) : ℝ :=
  modeDamping ν p.1 + pairDamping ν p.2.1 p.2.2

theorem interactionEnergy_nonneg (u : FourierVelocity) (p : TripleIndex) :
    0 ≤ interactionEnergy u p := by
  apply mul_nonneg _ (pairEnergy_nonneg u p.2.1 p.2.2)
  rw [modeEnergy, ← norm_coefficientVec_sq]
  positivity

theorem interactionDamping_pos {ν : ℝ} (hν : 0 < ν) (p : TripleIndex)
    (hl : p.2.1 ≠ 0) : 0 < interactionDamping ν p := by
  have hp := pairDamping_pos hν p.2.1 p.2.2 hl
  have hm : 0 ≤ modeDamping ν p.1 := by unfold modeDamping; positivity
  exact add_pos_of_nonneg_of_pos hm hp

variable {ν T B : ℝ} {u₀ : FourierVelocity}

theorem hasDerivAt_modeEnergy (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (k : Wavevector) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ modeEnergy (s.coefficients τ) k)
      (modeWork (s.coefficients t) k -
        2 * modeDamping ν k * modeEnergy (s.coefficients t) k) t := by
  have h := hasDerivAt_coefficientEnergy (fun τ ↦ fourierCurl (s.coefficients τ) k)
    _ t (hasDerivAt_fourierCurl s.coefficients _ t k (s.equation t ht k))
  rw [curlRHS_eq_nonlinear_add_damping] at h
  have hv := hermitian_real_smul_self (fourierCurl (s.coefficients t) k) (-modeDamping ν k)
  simp only [Complex.ofReal_neg] at hv
  simp only [hermitian_add_right, Complex.add_re, hv] at h
  apply h.congr_deriv
  dsimp [modeEnergy, modeWork]
  ring

theorem hasDerivAt_interactionEnergy (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (p : TripleIndex) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ interactionEnergy (s.coefficients τ) p)
      (interactionWork (s.coefficients t) p -
        2 * interactionDamping ν p * interactionEnergy (s.coefficients t) p) t := by
  have h := (hasDerivAt_modeEnergy s p.1 t ht).mul
    (hasDerivAt_pairEnergy s p.2.1 p.2.2 t ht)
  apply h.congr_deriv
  dsimp [interactionEnergy, interactionWork, interactionDamping]
  ring

section Continuity

variable {X : Type*} [TopologicalSpace X]

theorem continuous_cross_component (a b : X → VelocityCoefficient)
    (ha : ∀ i, Continuous (fun x ↦ a x i)) (hb : ∀ i, Continuous (fun x ↦ b x i))
    (i : Fin 3) : Continuous (fun x ↦ coefficientCross (a x) (b x) i) := by
  fin_cases i <;> simp only [coefficientCross] <;> fun_prop

theorem continuous_curl_component (u : X → FourierVelocity)
    (hu : ∀ q i, Continuous (fun x ↦ u x q i)) (q : Wavevector) (i : Fin 3) :
    Continuous (fun x ↦ fourierCurl (u x) q i) := by
  fin_cases i <;> simp only [fourierCurl, coefficientCross, Pi.smul_apply, smul_eq_mul] <;> fun_prop

theorem continuous_coefficientEnergy (a : X → VelocityCoefficient)
    (ha : ∀ i, Continuous (fun x ↦ a x i)) :
    Continuous (fun x ↦ coefficientEnergy (a x)) := by
  simp only [coefficientEnergy, Complex.normSq_eq_norm_sq]
  exact continuous_finsetSum Finset.univ (fun i _ ↦ (ha i).norm.pow 2)

theorem continuous_hermitian (a b : X → VelocityCoefficient)
    (ha : ∀ i, Continuous (fun x ↦ a x i)) (hb : ∀ i, Continuous (fun x ↦ b x i)) :
    Continuous (fun x ↦ coefficientHermitian (a x) (b x)) := by
  unfold coefficientHermitian
  exact continuous_finsetSum Finset.univ (fun i _ ↦ (ha i).star.mul (hb i))

theorem continuous_interactionEnergy (u : X → FourierVelocity)
    (hu : ∀ q i, Continuous (fun x ↦ u x q i)) (p : TripleIndex) :
    Continuous (fun x ↦ interactionEnergy (u x) p) :=
  (continuous_coefficientEnergy _ (continuous_curl_component u hu p.1)).mul
    (continuous_coefficientEnergy _ (continuous_cross_component _ _
      (continuous_curl_component u hu p.2.1) (continuous_curl_component u hu p.2.2)))

theorem continuous_interactionWork (u : X → FourierVelocity)
    (hu : ∀ q i, Continuous (fun x ↦ u x q i))
    (hN : ∀ q i, Continuous (fun x ↦ nonlinearCurl (u x) q i)) (p : TripleIndex) :
    Continuous (fun x ↦ interactionWork (u x) p) := by
  have hw := continuous_curl_component u hu
  have hc := continuous_cross_component _ _ (hw p.2.1) (hw p.2.2)
  have hsource (i : Fin 3) : Continuous (fun x ↦ pairSource (u x) p.2.1 p.2.2 i) :=
    (continuous_cross_component _ _ (hN p.2.1) (hw p.2.2) i).add
      (continuous_cross_component _ _ (hw p.2.1) (hN p.2.2) i)
  exact (((Complex.continuous_re.comp (continuous_hermitian _ _ (hw p.1) (hN p.1))).const_mul 2).mul
    (continuous_coefficientEnergy _ hc)).add
    ((continuous_coefficientEnergy _ (hw p.1)).mul
      ((Complex.continuous_re.comp (continuous_hermitian _ _ hc hsource)).const_mul 2))

end Continuity

theorem continuousOn_interactionWork (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (hB : 0 ≤ B) (p : TripleIndex) :
    ContinuousOn (fun t ↦ interactionWork (s.coefficients t) p) (Set.Icc (0 : ℝ) T) := by
  apply continuousOn_iff_continuous_restrict.mpr
  apply continuous_interactionWork _ (fun q i ↦ (s.continuous q i).comp continuous_subtype_val) ?_ p
  exact continuous_curl_component _ (FilteredAngularSourceIntegral.continuous_inviscidRHS_component s hB)

end Mettapedia.FluidDynamics.NavierStokes.FourierStretchingInteractionDynamics
