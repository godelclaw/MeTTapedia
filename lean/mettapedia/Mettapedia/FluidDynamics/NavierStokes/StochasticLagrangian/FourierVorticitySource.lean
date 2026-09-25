import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierRelaxation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeZeroModeCurlBridge
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierInfiniteTameRate

/-!
# The vorticity source is stretching plus transport, mode by mode

The vorticity source of the Fourier solutions, the curl of the Leray-projected
convection, is identified with the series of the physical stretching and
transport amplitudes of the route:

```text
curl N_k = ∑_p ( S(u_p) ω_{k-p} - (u_p · ∇) ω_{k-p} ),
```

in the unit-torus normalization of `unitTorusStrainStretchAmp` and
`unitTorusNegativeTransportAmp`. The proof has two steps. First the curl of the
convection is the curl of the Lamb vector `u × ω`: the pressure gradient is
killed by the curl, and after the exchange `p ↔ k - p` of the two modes of
each pair the identity is algebraic, using only the transversality of the
coefficients. Second the Lamb form is the limit of the finite identity already
checked on exhausting lattice boxes, where the stretching and transport
amplitudes appear.

The identity is what the sector estimates of the route split. With the
relaxation inequality, the sector estimates are now statements about the
stretching and transport series of actual solutions.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierVorticitySource

open scoped BigOperators Topology
open Set Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeLatticeDecayEnvelope PancakeLocalInfiniteVelocity
open PancakeCoefficientLimitEquation PancakeGalerkinKineticEnergy PancakeArbitraryDataBlocks
open PancakePeriodicVorticityEquation PancakePeriodicComplexStretch PancakeIndexedFourierMoments
open PancakeIncomingLowSourceEnergy PancakeExchangeSymmetricCurl PancakeZeroModeCurlBridge
open PancakeInfinitePressureCoefficients FourierInfiniteTameRate PancakeHigherDerivativeMoments
open FourierDyadicBlockContinuation LocalVorticityDiffusion
open FourierTimeRegularity FourierSpatialCalculus FourierRelaxation

section Algebra

theorem cross_sub_right (u v w : VelocityCoefficient) :
    coefficientCross u (v - w) = coefficientCross u v - coefficientCross u w := by
  ext i
  fin_cases i <;> simp [coefficientCross] <;> ring

theorem cross_self (u : VelocityCoefficient) : coefficientCross u u = 0 := by
  ext i
  fin_cases i <;> simp [coefficientCross] <;> ring

theorem curlMap_apply (k : Wavevector) (v : VelocityCoefficient) :
    curlMap k v = unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient k) v := rfl

/-- The curl kills the Leray correction. -/
theorem cross_wavevector_lerayMode (k : Wavevector) (v : VelocityCoefficient) :
    coefficientCross (wavevectorCoefficient k) (lerayMode k v) =
      coefficientCross (wavevectorCoefficient k) v := by
  unfold lerayMode
  split_ifs
  · rfl
  · have e : (fun i ↦ v i - (k i : ℂ) * modeDot k v / modeSquare k) =
        v - (modeDot k v / modeSquare k) • wavevectorCoefficient k := by
      ext i
      simp [wavevectorCoefficient]
      ring
    rw [e, cross_sub_right, coefficientCross_smul_right, cross_self, smul_zero, sub_zero]

theorem curlMap_lerayMode (k : Wavevector) (v : VelocityCoefficient) :
    curlMap k (lerayMode k v) = curlMap k v := by
  rw [curlMap_apply, curlMap_apply, cross_wavevector_lerayMode]

/-- The term of the convection seen by the curl. -/
def convCurlTerm (u : FourierVelocity) (k p : Wavevector) : VelocityCoefficient :=
  (-unitTorusDerivativePhase) • curlMap k (modeDot k (u p) • u (k - p))

/-- The Lamb-vector term `2πi k × (u_p × ω_{k-p})`. -/
def lambTerm (u : FourierVelocity) (k p : Wavevector) : VelocityCoefficient :=
  curlMap k (coefficientCross (u p) (fourierCurl u (k - p)))

/-- The stretching and transport term of the route. -/
def sourceTerm (u : FourierVelocity) (k p : Wavevector) : VelocityCoefficient :=
  unitTorusNegativeTransportAmp p (k - p) (fourierCurl u p) (fourierCurl u (k - p)) +
    unitTorusStrainStretchAmp p (fourierCurl u p) (fourierCurl u (k - p))

/-- **The pairwise identity.** For transverse coefficients `a` at `p` and `b` at
`k - p`, the two convection terms of the pair equal the two Lamb terms. -/
theorem pair_identity (k p : Wavevector) (a b : VelocityCoefficient) (hpa : modeDot p a = 0)
    (hrb : modeDot (k - p) b = 0) :
    (-unitTorusDerivativePhase) • curlMap k (modeDot k a • b) +
      (-unitTorusDerivativePhase) • curlMap k (modeDot k b • a) =
    curlMap k (coefficientCross a
        (unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient (k - p)) b)) +
      curlMap k (coefficientCross b
        (unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient p) a)) := by
  simp only [modeDot, Fin.sum_univ_three, Pi.sub_apply, Int.cast_sub] at hpa hrb
  ext i
  fin_cases i <;>
    simp [curlMap_apply, coefficientCross, modeDot, wavevectorCoefficient, Fin.sum_univ_three] <;>
    push_cast <;>
    first
    | linear_combination
        (-(unitTorusDerivativePhase ^ 2) * ((k 1 : ℂ) * b 2 - (k 2 : ℂ) * b 1)) * hpa +
        (-(unitTorusDerivativePhase ^ 2) * ((k 1 : ℂ) * a 2 - (k 2 : ℂ) * a 1)) * hrb
    | linear_combination
        (-(unitTorusDerivativePhase ^ 2) * ((k 2 : ℂ) * b 0 - (k 0 : ℂ) * b 2)) * hpa +
        (-(unitTorusDerivativePhase ^ 2) * ((k 2 : ℂ) * a 0 - (k 0 : ℂ) * a 2)) * hrb
    | linear_combination
        (-(unitTorusDerivativePhase ^ 2) * ((k 0 : ℂ) * b 1 - (k 1 : ℂ) * b 0)) * hpa +
        (-(unitTorusDerivativePhase ^ 2) * ((k 0 : ℂ) * a 1 - (k 1 : ℂ) * a 0)) * hrb

theorem pair_terms (u : FourierVelocity) (htr : ∀ p, modeDot p (u p) = 0) (k p : Wavevector) :
    convCurlTerm u k p + convCurlTerm u k (k - p) = lambTerm u k p + lambTerm u k (k - p) := by
  have h := pair_identity k p (u p) (u (k - p)) (htr p) (htr (k - p))
  simp only [convCurlTerm, lambTerm, sub_sub_cancel]
  exact h

end Algebra

section Norms

theorem norm_cv_cross_le (u v : VelocityCoefficient) :
    ‖coefficientVec (coefficientCross u v)‖ ≤ 6 * ‖coefficientVec u‖ * ‖coefficientVec v‖ := by
  have hu : ∀ i, ‖u i‖ ≤ ‖coefficientVec u‖ := fun i ↦ PiLp.norm_apply_le (coefficientVec u) i
  have hv : ∀ i, ‖v i‖ ≤ ‖coefficientVec v‖ := fun i ↦ PiLp.norm_apply_le (coefficientVec v) i
  have hc : ∀ i j l : Fin 3, ‖u i * v j - u j * v l‖ ≤ 2 * (‖coefficientVec u‖ * ‖coefficientVec v‖) := by
    intro i j l
    calc ‖u i * v j - u j * v l‖ ≤ ‖u i * v j‖ + ‖u j * v l‖ := norm_sub_le _ _
      _ = ‖u i‖ * ‖v j‖ + ‖u j‖ * ‖v l‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖coefficientVec u‖ * ‖coefficientVec v‖ + ‖coefficientVec u‖ * ‖coefficientVec v‖ :=
          add_le_add (mul_le_mul (hu i) (hv j) (norm_nonneg _) (norm_nonneg _))
            (mul_le_mul (hu j) (hv l) (norm_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  refine (norm_le_sum_components _).trans ?_
  rw [Fin.sum_univ_three]
  have e0 : coefficientCross u v 0 = u 1 * v 2 - u 2 * v 1 := rfl
  have e1 : coefficientCross u v 1 = u 2 * v 0 - u 0 * v 2 := rfl
  have e2 : coefficientCross u v 2 = u 0 * v 1 - u 1 * v 0 := rfl
  rw [e0, e1, e2]
  linarith [hc 1 2 1, hc 2 0 2, hc 0 1 0]

theorem norm_coefficientDot_le (u v : VelocityCoefficient) :
    ‖coefficientDot u v‖ ≤ 3 * ‖coefficientVec u‖ * ‖coefficientVec v‖ := by
  have hu : ∀ i, ‖u i‖ ≤ ‖coefficientVec u‖ := fun i ↦ PiLp.norm_apply_le (coefficientVec u) i
  have hv : ∀ i, ‖v i‖ ≤ ‖coefficientVec v‖ := fun i ↦ PiLp.norm_apply_le (coefficientVec v) i
  unfold coefficientDot
  refine (norm_sum_le _ _).trans ?_
  rw [Fin.sum_univ_three]
  have h : ∀ i : Fin 3, ‖u i * v i‖ ≤ ‖coefficientVec u‖ * ‖coefficientVec v‖ := fun i ↦ by
    rw [norm_mul]
    exact mul_le_mul (hu i) (hv i) (norm_nonneg _) (norm_nonneg _)
  linarith [h 0, h 1, h 2]

theorem norm_cv_smul (c : ℂ) (v : VelocityCoefficient) :
    ‖coefficientVec (c • v)‖ = ‖c‖ * ‖coefficientVec v‖ := by
  have e : coefficientVec (c • v) = c • coefficientVec v := rfl
  rw [e, norm_smul]

theorem norm_cv_add_le (v w : VelocityCoefficient) :
    ‖coefficientVec (v + w)‖ ≤ ‖coefficientVec v‖ + ‖coefficientVec w‖ := by
  have e : coefficientVec (v + w) = coefficientVec v + coefficientVec w := rfl
  rw [e]
  exact norm_add_le _ _

theorem norm_cv_curlMap_le (k : Wavevector) (v : VelocityCoefficient) :
    ‖coefficientVec (curlMap k v)‖ ≤ 2 * Real.pi * ‖frequencyVec k‖ * ‖coefficientVec v‖ := by
  rw [curlMap_apply, norm_cv_smul, PancakeIncomingLowSourceEnergy.norm_derivativePhase]
  have h := PancakeSameSectorDissipation.norm_cross_le k v
  calc 2 * Real.pi * ‖coefficientVec (coefficientCross (wavevectorCoefficient k) v)‖
      ≤ 2 * Real.pi * (‖frequencyVec k‖ * ‖coefficientVec v‖) := by gcongr
    _ = _ := by ring

theorem norm_cv_wavevector (k : Wavevector) :
    ‖coefficientVec (wavevectorCoefficient k)‖ = ‖frequencyVec k‖ := rfl

theorem norm_frequencyVec_le_one_add (k : Wavevector) :
    ‖frequencyVec k‖ ≤ 1 + ‖frequencyVec k‖ := by linarith

end Norms

section Envelope

/-- A summable envelope of the third Fourier moments. -/
structure MomentEnvelope (u : FourierVelocity) (g : Wavevector → ℝ) : Prop where
  nonneg : ∀ k, 0 ≤ g k
  summable : Summable g
  bound : ∀ k, fourierMoment 3 u k ≤ g k

variable {u : FourierVelocity} {g : Wavevector → ℝ}

theorem MomentEnvelope.moment_le (he : MomentEnvelope u g) {n : ℕ} (hn : n ≤ 3) (k : Wavevector) :
    fourierMoment n u k ≤ g k :=
  (fourierMoment_mono u hn k).trans (he.bound k)

theorem MomentEnvelope.norm_le (he : MomentEnvelope u g) (k : Wavevector) :
    ‖coefficientVec (u k)‖ ≤ g k := by
  have h := he.moment_le (n := 0) (by norm_num) k
  simpa [fourierMoment] using h

theorem MomentEnvelope.le_total (he : MomentEnvelope u g) (k : Wavevector) : g k ≤ ∑' p, g p :=
  he.summable.le_tsum k fun p _ ↦ he.nonneg p

theorem MomentEnvelope.total_nonneg (he : MomentEnvelope u g) : 0 ≤ ∑' p, g p :=
  tsum_nonneg he.nonneg

theorem MomentEnvelope.norm_curl_le (he : MomentEnvelope u g) (k : Wavevector) :
    ‖coefficientVec (fourierCurl u k)‖ ≤ 2 * Real.pi * g k :=
  (norm_coefficientVec_fourierCurl_le u k).trans
    (mul_le_mul_of_nonneg_left (he.moment_le (by norm_num) k) (by positivity))

theorem MomentEnvelope.norm_curl_le_total (he : MomentEnvelope u g) (k : Wavevector) :
    ‖coefficientVec (fourierCurl u k)‖ ≤ 2 * Real.pi * ∑' p, g p :=
  (he.norm_curl_le k).trans (mul_le_mul_of_nonneg_left (he.le_total k) (by positivity))

/-- Envelope of the vorticity coefficient with one power of the frequency. -/
theorem MomentEnvelope.weighted_norm_curl_le (he : MomentEnvelope u g) (k : Wavevector) :
    (1 + ‖frequencyVec k‖) * ‖coefficientVec (fourierCurl u k)‖ ≤ 2 * Real.pi * ∑' p, g p := by
  have h := (fourierMoment_curl_le 1 u k).trans
    (mul_le_mul_of_nonneg_left (he.moment_le (by norm_num) k) (by positivity))
  have e : fourierMoment 1 (fourierCurl u) k = (1 + ‖frequencyVec k‖) * ‖coefficientVec (fourierCurl u k)‖ := by
    unfold fourierMoment; ring
  rw [e] at h
  exact h.trans (mul_le_mul_of_nonneg_left (he.le_total k) (by positivity))

theorem MomentEnvelope.summable_convTerm (he : MomentEnvelope u g) (k : Wavevector) :
    Summable (fun p ↦ modeDot k (u p) • u (k - p)) := by
  have hb : ∀ p, ‖coefficientVec (modeDot k (u p) • u (k - p))‖ ≤
      (‖frequencyVec k‖ * ∑' q, g q) * g p := by
    intro p
    rw [norm_cv_smul]
    have h1 := PancakeLowPressureBudget.norm_modeDot_le k (u p)
    have h2 := (he.norm_le (k - p)).trans (he.le_total (k - p))
    have h3 := he.norm_le p
    have hgp := he.nonneg p
    calc ‖modeDot k (u p)‖ * ‖coefficientVec (u (k - p))‖
        ≤ (‖frequencyVec k‖ * g p) * ∑' q, g q :=
          mul_le_mul (h1.trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))) h2 (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) hgp)
      _ = _ := by ring
  exact (he.summable.mul_left _).of_norm_bounded fun p ↦
    (norm_coefficient_sup_le_euclidean _).trans (hb p)

theorem MomentEnvelope.summable_convCurlTerm (he : MomentEnvelope u g) (k : Wavevector) :
    Summable (fun p ↦ convCurlTerm u k p) := by
  have hb : ∀ p, ‖coefficientVec (convCurlTerm u k p)‖ ≤
      (2 * Real.pi * (2 * Real.pi * ‖frequencyVec k‖ * (‖frequencyVec k‖ * ∑' q, g q))) * g p := by
    intro p
    unfold convCurlTerm
    rw [norm_cv_smul, norm_neg, PancakeIncomingLowSourceEnergy.norm_derivativePhase]
    have h1 := norm_cv_curlMap_le k (modeDot k (u p) • u (k - p))
    rw [norm_cv_smul] at h1
    have h2 := PancakeLowPressureBudget.norm_modeDot_le k (u p)
    have h3 := he.norm_le p
    have h4 := (he.norm_le (k - p)).trans (he.le_total (k - p))
    have hgp := he.nonneg p
    have h5 : ‖modeDot k (u p)‖ * ‖coefficientVec (u (k - p))‖ ≤ (‖frequencyVec k‖ * g p) * ∑' q, g q :=
      mul_le_mul (h2.trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))) h4 (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) hgp)
    calc 2 * Real.pi * ‖coefficientVec (curlMap k (modeDot k (u p) • u (k - p)))‖
        ≤ 2 * Real.pi * (2 * Real.pi * ‖frequencyVec k‖ *
            (‖modeDot k (u p)‖ * ‖coefficientVec (u (k - p))‖)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 2 * Real.pi * (2 * Real.pi * ‖frequencyVec k‖ * ((‖frequencyVec k‖ * g p) * ∑' q, g q)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 (by positivity)) (by positivity)
      _ = _ := by ring
  exact (he.summable.mul_left _).of_norm_bounded fun p ↦
    (norm_coefficient_sup_le_euclidean _).trans (hb p)

theorem MomentEnvelope.summable_lambTerm (he : MomentEnvelope u g) (k : Wavevector) :
    Summable (fun p ↦ lambTerm u k p) := by
  have hb : ∀ p, ‖coefficientVec (lambTerm u k p)‖ ≤
      (2 * Real.pi * ‖frequencyVec k‖ * (6 * (2 * Real.pi * ∑' q, g q))) * g p := by
    intro p
    unfold lambTerm
    refine (norm_cv_curlMap_le k _).trans ?_
    have h1 := norm_cv_cross_le (u p) (fourierCurl u (k - p))
    have h3 := he.norm_le p
    have h4 := he.norm_curl_le_total (k - p)
    have hgp := he.nonneg p
    have h5 : 6 * ‖coefficientVec (u p)‖ * ‖coefficientVec (fourierCurl u (k - p))‖ ≤
        6 * g p * (2 * Real.pi * ∑' q, g q) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h3 (by norm_num)) h4 (norm_nonneg _)
        (mul_nonneg (by norm_num) hgp)
    calc 2 * Real.pi * ‖frequencyVec k‖ *
          ‖coefficientVec (coefficientCross (u p) (fourierCurl u (k - p)))‖
        ≤ 2 * Real.pi * ‖frequencyVec k‖ * (6 * g p * (2 * Real.pi * ∑' q, g q)) :=
          mul_le_mul_of_nonneg_left (h1.trans h5) (by positivity)
      _ = _ := by ring
  exact (he.summable.mul_left _).of_norm_bounded fun p ↦
    (norm_coefficient_sup_le_euclidean _).trans (hb p)

/-- **Envelope of the stretching and transport term**, after the Biot–Savart
inversion of the source velocity. -/
theorem MomentEnvelope.norm_sourceTerm_le (he : MomentEnvelope u g) (hu0 : u 0 = 0)
    (htr : ∀ p, modeDot p (u p) = 0) (k p : Wavevector) :
    ‖coefficientVec (sourceTerm u k p)‖ ≤ (2 * Real.pi) ^ 2 * (1 + 2) * (∑' q, g q) * g p := by
  have hbs : unitTorusBiotSavartAmp p (fourierCurl u p) = u p :=
    physicalBiotSavart_fourierCurl_meanZero u hu0 p (htr p)
  have hG := he.total_nonneg
  have hgp := he.nonneg p
  -- the transport term
  have ht : ‖coefficientVec (unitTorusNegativeTransportAmp p (k - p) (fourierCurl u p)
      (fourierCurl u (k - p)))‖ ≤ (2 * Real.pi) ^ 2 * (∑' q, g q) * g p := by
    unfold unitTorusNegativeTransportAmp
    rw [hbs, norm_cv_smul, norm_neg, norm_mul, PancakeIncomingLowSourceEnergy.norm_derivativePhase]
    have h1 := PancakeLowPressureBudget.norm_modeDot_le (k - p) (u p)
    have h2 := he.weighted_norm_curl_le (k - p)
    calc 2 * Real.pi * ‖modeDot (k - p) (u p)‖ * ‖coefficientVec (fourierCurl u (k - p))‖
        ≤ 2 * Real.pi * (‖frequencyVec (k - p)‖ * ‖coefficientVec (u p)‖) *
            ‖coefficientVec (fourierCurl u (k - p))‖ := by gcongr
      _ ≤ 2 * Real.pi * ((1 + ‖frequencyVec (k - p)‖) * g p) *
            ‖coefficientVec (fourierCurl u (k - p))‖ := by
          gcongr
          · exact norm_frequencyVec_le_one_add _
          · exact he.norm_le p
      _ = 2 * Real.pi * g p *
            ((1 + ‖frequencyVec (k - p)‖) * ‖coefficientVec (fourierCurl u (k - p))‖) := by ring
      _ ≤ 2 * Real.pi * g p * (2 * Real.pi * ∑' q, g q) := by gcongr
      _ = _ := by ring
  -- the stretching term
  have hs : ‖coefficientVec (unitTorusStrainStretchAmp p (fourierCurl u p) (fourierCurl u (k - p)))‖ ≤
      (2 * Real.pi) ^ 2 * 2 * (∑' q, g q) * g p := by
    unfold unitTorusStrainStretchAmp
    simp only [hbs]
    rw [norm_cv_smul, norm_mul, PancakeIncomingLowSourceEnergy.norm_derivativePhase]
    have hh : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [hh]
    have h1 := norm_coefficientDot_le (u p) (fourierCurl u (k - p))
    have h2 := PancakeLowPressureBudget.norm_modeDot_le p (fourierCurl u (k - p))
    have h3 := he.norm_curl_le_total (k - p)
    have hup := he.norm_le p
    have hp1 : ‖frequencyVec p‖ * ‖coefficientVec (u p)‖ ≤ g p := by
      have := he.moment_le (n := 1) (by norm_num) p
      unfold fourierMoment at this
      rw [pow_one] at this
      calc ‖frequencyVec p‖ * ‖coefficientVec (u p)‖
          ≤ (1 + ‖frequencyVec p‖) * ‖coefficientVec (u p)‖ := by
            gcongr; exact norm_frequencyVec_le_one_add p
        _ ≤ g p := this
    have hcv : ‖coefficientVec (coefficientDot (u p) (fourierCurl u (k - p)) • wavevectorCoefficient p +
        modeDot p (fourierCurl u (k - p)) • u p)‖ ≤
        3 * ‖coefficientVec (u p)‖ * ‖coefficientVec (fourierCurl u (k - p))‖ * ‖frequencyVec p‖ +
          ‖frequencyVec p‖ * ‖coefficientVec (fourierCurl u (k - p))‖ * ‖coefficientVec (u p)‖ := by
      refine (norm_cv_add_le _ _).trans ?_
      rw [norm_cv_smul, norm_cv_smul, norm_cv_wavevector]
      gcongr
    calc 1 / 2 * (2 * Real.pi) * ‖coefficientVec (coefficientDot (u p) (fourierCurl u (k - p)) •
          wavevectorCoefficient p + modeDot p (fourierCurl u (k - p)) • u p)‖
        ≤ 1 / 2 * (2 * Real.pi) * (3 * ‖coefficientVec (u p)‖ *
            ‖coefficientVec (fourierCurl u (k - p))‖ * ‖frequencyVec p‖ +
          ‖frequencyVec p‖ * ‖coefficientVec (fourierCurl u (k - p))‖ * ‖coefficientVec (u p)‖) := by
          gcongr
      _ = Real.pi * (4 * (‖frequencyVec p‖ * ‖coefficientVec (u p)‖) *
            ‖coefficientVec (fourierCurl u (k - p))‖) := by ring
      _ ≤ Real.pi * (4 * g p * (2 * Real.pi * ∑' q, g q)) := by gcongr
      _ = _ := by ring
  unfold sourceTerm
  refine (norm_cv_add_le _ _).trans ?_
  calc _ ≤ (2 * Real.pi) ^ 2 * (∑' q, g q) * g p + (2 * Real.pi) ^ 2 * 2 * (∑' q, g q) * g p :=
        add_le_add ht hs
    _ = _ := by ring

theorem MomentEnvelope.summable_sourceTerm (he : MomentEnvelope u g) (hu0 : u 0 = 0)
    (htr : ∀ p, modeDot p (u p) = 0) (k : Wavevector) :
    Summable (fun p ↦ sourceTerm u k p) :=
  (he.summable.mul_left _).of_norm_bounded fun p ↦
    (norm_coefficient_sup_le_euclidean _).trans (he.norm_sourceTerm_le hu0 htr k p)

end Envelope

section LambForm

variable {u : FourierVelocity} {g : Wavevector → ℝ}

/-- The vorticity source is the series of the convection terms seen by the curl. -/
theorem vorticitySource_eq_tsum_convCurlTerm (he : MomentEnvelope u g) (k : Wavevector) :
    vorticitySource u k = ∑' p, convCurlTerm u k p := by
  have hs := he.summable_convTerm k
  unfold vorticitySource nonlinear
  have e1 : nonlinearMap k (conv u u k) = lerayMode k ((-unitTorusDerivativePhase) • conv u u k) :=
    rfl
  rw [e1, curlMap_lerayMode, map_smul, conv_self, infiniteConvection_eq_of_summable hs,
    (curlMap k).map_tsum hs, ← tsum_const_smul'']
  rfl

/-- **The Lamb form of the vorticity source.** -/
theorem vorticitySource_eq_tsum_lambTerm (he : MomentEnvelope u g)
    (htr : ∀ p, modeDot p (u p) = 0) (k : Wavevector) :
    vorticitySource u k = ∑' p, lambTerm u k p := by
  rw [vorticitySource_eq_tsum_convCurlTerm he k]
  have hc := he.summable_convCurlTerm k
  have hl := he.summable_lambTerm k
  let σ : Wavevector ≃ Wavevector := Equiv.subLeft k
  have hcσ : Summable (fun p ↦ convCurlTerm u k (k - p)) := hc.comp_injective σ.injective
  have hlσ : Summable (fun p ↦ lambTerm u k (k - p)) := hl.comp_injective σ.injective
  have e1 : ∑' p, convCurlTerm u k (k - p) = ∑' p, convCurlTerm u k p :=
    σ.tsum_eq (fun p ↦ convCurlTerm u k p)
  have e2 : ∑' p, lambTerm u k (k - p) = ∑' p, lambTerm u k p :=
    σ.tsum_eq (fun p ↦ lambTerm u k p)
  have h : ∑' p, (convCurlTerm u k p + convCurlTerm u k (k - p)) =
      ∑' p, (lambTerm u k p + lambTerm u k (k - p)) :=
    tsum_congr fun p ↦ pair_terms u htr k p
  rw [hc.tsum_add hcσ, hl.tsum_add hlσ, e1, e2] at h
  have h2 : (2 : ℂ) • ∑' p, convCurlTerm u k p = (2 : ℂ) • ∑' p, lambTerm u k p := by
    rw [two_smul, two_smul]
    exact h
  exact smul_right_injective VelocityCoefficient (two_ne_zero) h2

end LambForm

section Exhaustion

/-- The modes `p` of a box whose partner `k - p` lies in the box. -/
def shellSet (N : ℕ) (k : Wavevector) : Finset Wavevector :=
  (wavevectorBox N).filter fun p ↦ k - p ∈ wavevectorBox N

theorem wavevectorBox_mono {M N : ℕ} (h : M ≤ N) : wavevectorBox M ⊆ wavevectorBox N := by
  intro p hp
  rw [mem_wavevectorBox_iff] at hp ⊢
  intro i
  exact (hp i).trans (by exact_mod_cast h)

theorem tendsto_shellSet (k : Wavevector) : Tendsto (fun N ↦ shellSet N k) atTop atTop := by
  refine Filter.tendsto_atTop_atTop.mpr fun F ↦ ?_
  obtain ⟨N₀, hN₀⟩ := Filter.tendsto_atTop_atTop.mp tendsto_wavevectorBox
    (F ∪ F.image fun p ↦ k - p)
  refine ⟨N₀, fun N hN p hp ↦ ?_⟩
  have hsub := hN₀ N hN
  refine Finset.mem_filter.mpr ⟨hsub (Finset.mem_union_left _ hp), hsub (Finset.mem_union_right _ ?_)⟩
  exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

/-- The pairs of a box with sum `k`, as the image of `shellSet`. -/
theorem pairs_eq_map (N : ℕ) (k : Wavevector) :
    (wavevectorBox N ×ˢ wavevectorBox N).filter (fun p ↦ p.1 + p.2 = k) =
      (shellSet N k).map ⟨fun p ↦ (p, k - p), fun _ _ h ↦ (Prod.ext_iff.mp h).1⟩ := by
  ext ⟨p₁, p₂⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_map, shellSet]
  constructor
  · rintro ⟨⟨h1, h2⟩, hsum⟩
    refine ⟨p₁, ⟨h1, ?_⟩, ?_⟩
    · rw [← hsum, add_sub_cancel_left]; exact h2
    · show (p₁, k - p₁) = (p₁, p₂)
      rw [← hsum, add_sub_cancel_left]
  · rintro ⟨a, ⟨ha, hka⟩, hae⟩
    have h1 : a = p₁ := (Prod.ext_iff.mp hae).1
    have h2 : k - a = p₂ := (Prod.ext_iff.mp hae).2
    subst h1
    subst h2
    exact ⟨⟨ha, hka⟩, by abel⟩

variable {u : FourierVelocity}

/-- **The finite identity on boxes**, from the exchange-symmetric curl. -/
theorem finite_lamb_eq_source (hu0 : u 0 = 0) (htr : ∀ p, modeDot p (u p) = 0) (N : ℕ)
    (k : Wavevector) :
    ∑ p ∈ shellSet N k, lambTerm u k p = ∑ p ∈ shellSet N k, sourceTerm u k p := by
  have h := incomingNonlinearCoeff_eq_curl_with_zero (wavevectorBox N) (fourierCurl u) k
    (fourierCurl_zero u) (fun q _ ↦ fourierCurl_transverse q u)
  rw [incomingNonlinearCoeff_eq_pairSum, curlConvolutionCoeff_eq_pairSum, pairs_eq_map,
    Finset.sum_map, Finset.sum_map] at h
  have hpv : ∀ p, physicalVelocity (fourierCurl u) p = u p := fun p ↦
    physicalBiotSavart_fourierCurl_meanZero u hu0 p (htr p)
  simp only [hpv] at h
  simp only [lambTerm, sourceTerm, curlMap_apply]
  exact h.symm

/-- **The vorticity source is the series of stretching and transport.** -/
theorem vorticitySource_eq_tsum_sourceTerm {g : Wavevector → ℝ} (he : MomentEnvelope u g)
    (hu0 : u 0 = 0) (htr : ∀ p, modeDot p (u p) = 0) (k : Wavevector) :
    vorticitySource u k = ∑' p, sourceTerm u k p := by
  rw [vorticitySource_eq_tsum_lambTerm he htr k]
  have hl := he.summable_lambTerm k
  have hs := he.summable_sourceTerm hu0 htr k
  have tl : Tendsto (fun s : Finset Wavevector ↦ ∑ p ∈ s, lambTerm u k p) atTop
      (𝓝 (∑' p, lambTerm u k p)) := by
    simpa only [HasSum, SummationFilter.unconditional] using hl.hasSum
  have ts : Tendsto (fun s : Finset Wavevector ↦ ∑ p ∈ s, sourceTerm u k p) atTop
      (𝓝 (∑' p, sourceTerm u k p)) := by
    simpa only [HasSum, SummationFilter.unconditional] using hs.hasSum
  have hl' := tl.comp (tendsto_shellSet k)
  have hs' := ts.comp (tendsto_shellSet k)
  refine tendsto_nhds_unique hl' (hs'.congr fun N ↦ ?_)
  exact (finite_lamb_eq_source hu0 htr N k).symm

/-- The stretching series. -/
def stretchingSeries (u : FourierVelocity) (k : Wavevector) : VelocityCoefficient :=
  ∑' p, unitTorusStrainStretchAmp p (fourierCurl u p) (fourierCurl u (k - p))

/-- The transport series. -/
def transportSeries (u : FourierVelocity) (k : Wavevector) : VelocityCoefficient :=
  ∑' p, unitTorusNegativeTransportAmp p (k - p) (fourierCurl u p) (fourierCurl u (k - p))

/-- **The Fourier vorticity equation.** Along any coefficient field with zero
mean, transverse coefficients and a summable envelope of the third moments,
the vorticity source is the stretching series plus the transport series. -/
theorem vorticitySource_eq_stretching_add_transport {g : Wavevector → ℝ}
    (he : MomentEnvelope u g) (hu0 : u 0 = 0) (htr : ∀ p, modeDot p (u p) = 0)
    (k : Wavevector) :
    vorticitySource u k = stretchingSeries u k + transportSeries u k := by
  rw [vorticitySource_eq_tsum_sourceTerm he hu0 htr k]
  have hs := he.summable_sourceTerm hu0 htr k
  -- both summands are summable: the transport is the difference of the source and the stretching
  have hst : Summable (fun p ↦ unitTorusStrainStretchAmp p (fourierCurl u p)
      (fourierCurl u (k - p))) := by
    refine (he.summable.mul_left ((2 * Real.pi) ^ 2 * 2 * ∑' q, g q)).of_norm_bounded fun p ↦
      (norm_coefficient_sup_le_euclidean _).trans ?_
    have hbs : unitTorusBiotSavartAmp p (fourierCurl u p) = u p :=
      physicalBiotSavart_fourierCurl_meanZero u hu0 p (htr p)
    have h := he.norm_sourceTerm_le hu0 htr k p
    -- reuse the stretching bound inside the source bound
    have hG := he.total_nonneg
    have hgp := he.nonneg p
    unfold unitTorusStrainStretchAmp
    simp only [hbs]
    rw [norm_cv_smul, norm_mul, PancakeIncomingLowSourceEnergy.norm_derivativePhase]
    have hh : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [hh]
    have h1 := norm_coefficientDot_le (u p) (fourierCurl u (k - p))
    have h2 := PancakeLowPressureBudget.norm_modeDot_le p (fourierCurl u (k - p))
    have h3 := he.norm_curl_le_total (k - p)
    have hup := he.norm_le p
    have hp1 : ‖frequencyVec p‖ * ‖coefficientVec (u p)‖ ≤ g p := by
      have := he.moment_le (n := 1) (by norm_num) p
      unfold fourierMoment at this
      rw [pow_one] at this
      calc ‖frequencyVec p‖ * ‖coefficientVec (u p)‖
          ≤ (1 + ‖frequencyVec p‖) * ‖coefficientVec (u p)‖ := by
            gcongr; exact norm_frequencyVec_le_one_add p
        _ ≤ g p := this
    have hcv : ‖coefficientVec (coefficientDot (u p) (fourierCurl u (k - p)) • wavevectorCoefficient p +
        modeDot p (fourierCurl u (k - p)) • u p)‖ ≤
        3 * ‖coefficientVec (u p)‖ * ‖coefficientVec (fourierCurl u (k - p))‖ * ‖frequencyVec p‖ +
          ‖frequencyVec p‖ * ‖coefficientVec (fourierCurl u (k - p))‖ * ‖coefficientVec (u p)‖ := by
      refine (norm_cv_add_le _ _).trans ?_
      rw [norm_cv_smul, norm_cv_smul, norm_cv_wavevector]
      gcongr
    calc 1 / 2 * (2 * Real.pi) * ‖coefficientVec (coefficientDot (u p) (fourierCurl u (k - p)) •
          wavevectorCoefficient p + modeDot p (fourierCurl u (k - p)) • u p)‖
        ≤ 1 / 2 * (2 * Real.pi) * (3 * ‖coefficientVec (u p)‖ *
            ‖coefficientVec (fourierCurl u (k - p))‖ * ‖frequencyVec p‖ +
          ‖frequencyVec p‖ * ‖coefficientVec (fourierCurl u (k - p))‖ * ‖coefficientVec (u p)‖) := by
          gcongr
      _ = Real.pi * (4 * (‖frequencyVec p‖ * ‖coefficientVec (u p)‖) *
            ‖coefficientVec (fourierCurl u (k - p))‖) := by ring
      _ ≤ Real.pi * (4 * g p * (2 * Real.pi * ∑' q, g q)) := by gcongr
      _ = _ := by ring
  have htr' : Summable (fun p ↦ unitTorusNegativeTransportAmp p (k - p) (fourierCurl u p)
      (fourierCurl u (k - p))) := by
    have e : (fun p ↦ unitTorusNegativeTransportAmp p (k - p) (fourierCurl u p)
        (fourierCurl u (k - p))) = fun p ↦ sourceTerm u k p -
          unitTorusStrainStretchAmp p (fourierCurl u p) (fourierCurl u (k - p)) := by
      funext p
      simp [sourceTerm]
    rw [e]
    exact hs.sub hst
  unfold stretchingSeries transportSeries sourceTerm
  rw [htr'.tsum_add hst, add_comm]

end Exhaustion

section Solutions

variable {nu T B : ℝ} {u₀ : FourierVelocity} {g : Wavevector → ℝ}

/-- Along a local solution with a moment envelope, the vorticity source is the
stretching series plus the transport series at every time. -/
theorem vorticitySource_eq_local (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (he : Envelope s g) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (k : Wavevector) :
    vorticitySource (s.coefficients t) k =
      stretchingSeries (s.coefficients t) k + transportSeries (s.coefficients t) k :=
  vorticitySource_eq_stretching_add_transport ⟨he.nonneg, he.summable, he.bound t ht⟩ (s.zero t)
    (s.transverse t) k

end Solutions

end Mettapedia.FluidDynamics.NavierStokes.FourierVorticitySource
