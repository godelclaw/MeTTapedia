import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFullStrainFrame

/-!
# From Fourier coherent-line remainder to strain alignment energy

For a divergence-free vector `xi` at frequency `k`, the coherent line is the
orthogonal projection of `e_x` into `k⊥`.  The distance from `xi` to this line
is no larger than its distance from the original line spanned by `e_x`.

After the full strain-frame construction, `e_x` is exactly the image of the
most expanding strain eigenvector.  Thus the real modewise Fourier
misalignment energy is bounded by the invariant expanding-eigenline alignment
energy used in `PancakeAlignmentDynamics`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeMisalignmentEnergyBridge

open PeriodicFourierTriad
open MeasureTheory
open scoped BigOperators ComplexConjugate RealInnerProductSpace
open PancakeRealCoherentPairEstimate
open PancakeFrameCovariance
open PancakeAxialFrameConstruction
open PancakeAlignmentDynamics
open PancakeStrainSpectralFrame
open PancakeStrainAxialFrame
open PancakeAnnularSectorProjector
open PancakeSquareDyadicSectorProjector
open PancakeDyadicKernelScaling
open PancakeFullStrainFrame
open PancakeSmoothCoherentSymbol
open PancakeFiniteFourierBilinearTransfer
open PancakePeriodicCoherentSplit
open PancakeComplexCoherentPDEIdentification
open PancakeFrozenFrameKernelTransfer
open PancakePhysicalFrameKernelTransfer
open PancakePhysicalMisalignmentSplit

local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Algebraic expansion of squared distance from a scalar multiple. -/
theorem normSq_sub_smul (u v : RealVec3) (c : ℝ) :
    normSq (sub u (smul c v)) =
      normSq u - 2 * c * dot v u + c ^ 2 * normSq v := by
  obtain ⟨ux, uy, uz⟩ := u
  obtain ⟨vx, vy, vz⟩ := v
  simp only [sub, smul, normSq, dot]
  ring

/-- Squared Euclidean length after subtracting an orthogonal rank-one
projection. -/
theorem normSq_sub_projection_eq (u v : RealVec3)
    (hv : normSq v ≠ 0) :
    normSq (sub u (smul (dot v u / normSq v) v)) =
      normSq u - dot v u ^ 2 / normSq v := by
  rw [normSq_sub_smul]
  field_simp [hv]
  ring

/-- A divergence-free vector sees the coherent direction through only its
`e_x` component. -/
theorem dot_coherentW_eq_normSq_mul_dot_ex_of_perp
    (k u : RealVec3) (hperp : dot k u = 0) :
    dot (coherentW k) u = normSq k * dot ex u := by
  obtain ⟨a, b, c⟩ := k
  obtain ⟨x, y, z⟩ := u
  simp only [coherentW, add, smul, normSq, dot, ex] at hperp ⊢
  linear_combination -(a : ℝ) * hperp

/-- A divergence-free real coefficient's squared coherent-line remainder is
bounded by its squared energy transverse to `e_x`. -/
theorem normSq_realMisalignment_le_transverseEnergy_ex
    (k xi : RealVec3) (hperp : dot k xi = 0)
    (hcoherent : 0 < normSq (coherentW k)) :
    normSq (sub xi (coherentProject k xi)) ≤
      normSq xi - dot ex xi ^ 2 := by
  have hKnonneg : 0 ≤ normSq k := normSq_nonneg k
  have hK : 0 < normSq k := by
    by_contra h
    push Not at h
    have hKzero : normSq k = 0 := le_antisymm h hKnonneg
    rw [normSq_coherentW, hKzero, zero_mul] at hcoherent
    exact (lt_irrefl 0) hcoherent
  have hB : 0 < normSq k - k.1 ^ 2 := by
    rw [normSq_coherentW] at hcoherent
    exact (mul_pos_iff.mp hcoherent).resolve_right (by
      intro hneg
      exact (not_lt_of_ge hKnonneg) hneg.1) |>.2
  have hfrac : dot ex xi ^ 2 ≤
      dot (coherentW k) xi ^ 2 / normSq (coherentW k) := by
    rw [dot_coherentW_eq_normSq_mul_dot_ex_of_perp k xi hperp,
      normSq_coherentW]
    rw [le_div_iff₀ (mul_pos hK hB)]
    have hBle : normSq k - k.1 ^ 2 ≤ normSq k := by
      nlinarith [sq_nonneg k.1]
    calc
      dot ex xi ^ 2 *
          (normSq k * (normSq k - k.1 ^ 2)) ≤
        dot ex xi ^ 2 * (normSq k * normSq k) := by
          gcongr
      _ = (normSq k * dot ex xi) ^ 2 := by ring
  have hexact :
      normSq (sub xi (coherentProject k xi)) =
        normSq xi -
          dot (coherentW k) xi ^ 2 / normSq (coherentW k) := by
    simpa [coherentProject, coherentCoeff] using
      normSq_sub_projection_eq xi (coherentW k) (ne_of_gt hcoherent)
  rw [hexact]
  exact sub_le_sub_left hfrac _

/-- **Unit modewise alignment bridge.**  For a unit divergence-free real
coefficient, its squared coherent-line remainder is bounded by its invariant
line-misalignment energy relative to `e_x`. -/
theorem normSq_realMisalignment_le_alignmentEnergy_ex
    (k xi : RealVec3)
    (hxi : normSq xi = 1) (hperp : dot k xi = 0)
    (hcoherent : 0 < normSq (coherentW k)) :
    normSq (sub xi (coherentProject k xi)) ≤
      1 - dot ex xi ^ 2 := by
  rw [← hxi]
  exact normSq_realMisalignment_le_transverseEnergy_ex
    k xi hperp hcoherent

/-! ## Complex Fourier coefficients -/

/-- Coordinatewise real part of a complex Fourier coefficient. -/
def complexRealPartVec (u : ComplexVec3) : RealVec3 :=
  ((u 0).re, (u 1).re, (u 2).re)

/-- Coordinatewise imaginary part of a complex Fourier coefficient. -/
def complexImagPartVec (u : ComplexVec3) : RealVec3 :=
  ((u 0).im, (u 1).im, (u 2).im)

/-- Hermitian Euclidean energy of a complex three-vector. -/
def complexEuclideanNormSq (u : ComplexVec3) : ℝ :=
  Complex.normSq (u 0) + Complex.normSq (u 1) + Complex.normSq (u 2)

/-- Hermitian energy transverse to the fixed coherent reference `e_x`. -/
def complexTransverseEnergyEx (u : ComplexVec3) : ℝ :=
  Complex.normSq (u 1) + Complex.normSq (u 2)

/-- Scalar trigonometric polynomial with prescribed finite Fourier
coefficients. -/
def finiteScalarFourierReconstruction (s : Finset Wavevector)
    (a : Wavevector → ℂ) (x : UnitAddTorus (Fin 3)) : ℂ :=
  ∑ k ∈ s, UnitAddTorus.mFourier k x * a k

theorem continuous_finiteScalarFourierReconstruction
    (s : Finset Wavevector) (a : Wavevector → ℂ) :
    Continuous (finiteScalarFourierReconstruction s a) := by
  unfold finiteScalarFourierReconstruction
  fun_prop

/-- Orthogonality of two multivariate unit-torus Fourier characters, in a
form convenient for finite Parseval expansion. -/
theorem integral_mFourier_mul_conj_mFourier (k l : Wavevector) :
    (∫ x : UnitAddTorus (Fin 3),
        UnitAddTorus.mFourier l x *
          conj (UnitAddTorus.mFourier k x)) =
      if k = l then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp
    (UnitAddTorus.orthonormal_mFourier (d := Fin 3))) k l
  simpa only [ContinuousMap.inner_toLp] using h

/-- Exact finite Parseval identity in the normalization of the unit-torus
characters used throughout the periodic pancake development. -/
theorem integral_normSq_finiteScalarFourierReconstruction
    (s : Finset Wavevector) (a : Wavevector → ℂ) :
    (∫ x : UnitAddTorus (Fin 3),
        Complex.normSq (finiteScalarFourierReconstruction s a x)) =
      ∑ k ∈ s, Complex.normSq (a k) := by
  apply Complex.ofReal_injective
  calc
    ((∫ x : UnitAddTorus (Fin 3),
        Complex.normSq (finiteScalarFourierReconstruction s a x) : ℝ) : ℂ) =
        ∫ x : UnitAddTorus (Fin 3),
          (Complex.normSq
            (finiteScalarFourierReconstruction s a x) : ℂ) := by
      exact integral_ofReal.symm
    _ = ∫ x : UnitAddTorus (Fin 3),
        ∑ k ∈ s, ∑ l ∈ s,
          (conj (a k) * a l) *
            (UnitAddTorus.mFourier l x *
              conj (UnitAddTorus.mFourier k x)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [Complex.normSq_eq_conj_mul_self]
      simp_rw [finiteScalarFourierReconstruction, map_sum, map_mul,
        Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ = ∑ k ∈ s, ∑ l ∈ s,
        ∫ x : UnitAddTorus (Fin 3),
          (conj (a k) * a l) *
            (UnitAddTorus.mFourier l x *
              conj (UnitAddTorus.mFourier k x)) := by
      rw [integral_finsetSum s]
      · apply Finset.sum_congr rfl
        intro k hk
        rw [integral_finsetSum s]
        intro l hl
        have hcont : Continuous (fun x : UnitAddTorus (Fin 3) ↦
            (conj (a k) * a l) *
              (UnitAddTorus.mFourier l x *
                conj (UnitAddTorus.mFourier k x))) := by
          fun_prop
        simpa only [integrableOn_univ] using
          hcont.continuousOn.integrableOn_compact
            (isCompact_univ : IsCompact
              (Set.univ : Set (UnitAddTorus (Fin 3))))
      · intro k hk
        apply integrable_finsetSum s
        intro l hl
        have hcont : Continuous (fun x : UnitAddTorus (Fin 3) ↦
            (conj (a k) * a l) *
              (UnitAddTorus.mFourier l x *
                conj (UnitAddTorus.mFourier k x))) := by
          fun_prop
        simpa only [integrableOn_univ] using
          hcont.continuousOn.integrableOn_compact
            (isCompact_univ : IsCompact
              (Set.univ : Set (UnitAddTorus (Fin 3))))
    _ = ∑ k ∈ s, ∑ l ∈ s,
        (conj (a k) * a l) * (if k = l then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      rw [integral_const_mul, integral_mFourier_mul_conj_mFourier]
    _ = ((∑ k ∈ s, Complex.normSq (a k) : ℝ) : ℂ) := by
      simp [Complex.normSq_eq_conj_mul_self]

theorem finiteFourierReconstruction_component
    (s : Finset Wavevector) (omega : FourierVelocity)
    (i : Fin 3) (x : UnitAddTorus (Fin 3)) :
    finiteFourierReconstruction s omega x i =
      finiteScalarFourierReconstruction s (fun k ↦ omega k i) x := by
  simp [finiteFourierReconstruction, finiteScalarFourierReconstruction,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Parseval turns the summed transverse coefficient energy into the
physical-space `L²` transverse energy of the finite reconstruction. -/
theorem integral_transverseEnergyEx_finiteFourierReconstruction
    (s : Finset Wavevector) (omega : FourierVelocity) :
    (∫ x : UnitAddTorus (Fin 3),
        complexTransverseEnergyEx
          (finiteFourierReconstruction s omega x)) =
      ∑ k ∈ s, complexTransverseEnergyEx (omega k) := by
  have hint (i : Fin 3) : Integrable (fun x : UnitAddTorus (Fin 3) ↦
      Complex.normSq (finiteFourierReconstruction s omega x i)) := by
    have hcomponent : Continuous (fun x : UnitAddTorus (Fin 3) ↦
        finiteFourierReconstruction s omega x i) :=
      (continuous_apply i).comp
        (continuous_finiteFourierReconstruction s omega)
    have hcont : Continuous (fun x : UnitAddTorus (Fin 3) ↦
        Complex.normSq (finiteFourierReconstruction s omega x i)) :=
      Complex.continuous_normSq.comp hcomponent
    simpa only [integrableOn_univ] using
      hcont.continuousOn.integrableOn_compact
        (isCompact_univ : IsCompact (Set.univ : Set (UnitAddTorus (Fin 3))))
  rw [show (fun x : UnitAddTorus (Fin 3) ↦
      complexTransverseEnergyEx (finiteFourierReconstruction s omega x)) =
      (fun x ↦
        Complex.normSq (finiteFourierReconstruction s omega x 1) +
        Complex.normSq (finiteFourierReconstruction s omega x 2)) by
          funext x
          rfl]
  rw [integral_add (hint 1) (hint 2)]
  rw [show (∫ x : UnitAddTorus (Fin 3),
      Complex.normSq (finiteFourierReconstruction s omega x 1)) =
      ∑ k ∈ s, Complex.normSq (omega k 1) by
        simpa only [finiteFourierReconstruction_component] using
          integral_normSq_finiteScalarFourierReconstruction s
            (fun k ↦ omega k 1)]
  rw [show (∫ x : UnitAddTorus (Fin 3),
      Complex.normSq (finiteFourierReconstruction s omega x 2)) =
      ∑ k ∈ s, Complex.normSq (omega k 2) by
        simpa only [finiteFourierReconstruction_component] using
          integral_normSq_finiteScalarFourierReconstruction s
            (fun k ↦ omega k 2)]
  rw [← Finset.sum_add_distrib]
  rfl

theorem complexEuclideanNormSq_eq_real_add_imag (u : ComplexVec3) :
    complexEuclideanNormSq u =
      normSq (complexRealPartVec u) + normSq (complexImagPartVec u) := by
  simp [complexEuclideanNormSq, complexRealPartVec, complexImagPartVec,
    Complex.normSq_apply, normSq, dot]
  ring

theorem complexTransverseEnergyEx_eq_real_add_imag (u : ComplexVec3) :
    complexTransverseEnergyEx u =
      (normSq (complexRealPartVec u) - dot ex (complexRealPartVec u) ^ 2) +
      (normSq (complexImagPartVec u) - dot ex (complexImagPartVec u) ^ 2) := by
  simp [complexTransverseEnergyEx, complexRealPartVec, complexImagPartVec,
    Complex.normSq_apply, normSq, dot, ex]
  ring

theorem dot_complexRealPartVec_eq_zero_of_perp
    (k : RealVec3) (u : ComplexVec3)
    (hperp : complexBilinearDot (complexFrequency k) u = 0) :
    dot k (complexRealPartVec u) = 0 := by
  have h := congrArg Complex.re hperp
  obtain ⟨a, b, c⟩ := k
  simpa [complexBilinearDot, complexFrequency, realVec3ToComplexVec3,
    complexRealPartVec, dot, Fin.sum_univ_three] using h

theorem dot_complexImagPartVec_eq_zero_of_perp
    (k : RealVec3) (u : ComplexVec3)
    (hperp : complexBilinearDot (complexFrequency k) u = 0) :
    dot k (complexImagPartVec u) = 0 := by
  have h := congrArg Complex.im hperp
  obtain ⟨a, b, c⟩ := k
  simpa [complexBilinearDot, complexFrequency, realVec3ToComplexVec3,
    complexImagPartVec, dot, Fin.sum_univ_three] using h

/-- A complex vector is the sum of its real part and `i` times its imaginary
part, expressed in the real coordinate model. -/
theorem complexVec3_eq_real_add_I_imag (u : ComplexVec3) :
    u = realVec3ToComplexVec3 (complexRealPartVec u) +
      Complex.I • realVec3ToComplexVec3 (complexImagPartVec u) := by
  ext i
  fin_cases i <;>
    simp [complexRealPartVec, complexImagPartVec, realVec3ToComplexVec3,
      Complex.ext_iff]

/-- Complexifying a real frame transports coordinatewise real parts by the
original real frame. -/
theorem complexRealPartVec_complexifyRealLinearEquiv
    (L : RealVec3 ≃ₗ[ℝ] RealVec3) (u : ComplexVec3) :
    complexRealPartVec (complexifyRealLinearEquiv L u) =
      L (complexRealPartVec u) := by
  rw [complexVec3_eq_real_add_I_imag u, map_add, map_smul,
    complexifyRealLinearEquiv_realVec3ToComplexVec3,
    complexifyRealLinearEquiv_realVec3ToComplexVec3]
  apply Prod.ext
  · simp [complexRealPartVec, realVec3ToComplexVec3]
  · apply Prod.ext <;> simp [complexRealPartVec, realVec3ToComplexVec3]

/-- Complexifying a real frame transports coordinatewise imaginary parts by
the original real frame. -/
theorem complexImagPartVec_complexifyRealLinearEquiv
    (L : RealVec3 ≃ₗ[ℝ] RealVec3) (u : ComplexVec3) :
    complexImagPartVec (complexifyRealLinearEquiv L u) =
      L (complexImagPartVec u) := by
  rw [complexVec3_eq_real_add_I_imag u, map_add, map_smul,
    complexifyRealLinearEquiv_realVec3ToComplexVec3,
    complexifyRealLinearEquiv_realVec3ToComplexVec3]
  apply Prod.ext
  · simp [complexImagPartVec, realVec3ToComplexVec3]
  · apply Prod.ext <;> simp [complexImagPartVec, realVec3ToComplexVec3]

theorem complexBilinearDot_complexFrequency_re
    (k : RealVec3) (u : ComplexVec3) :
    (complexBilinearDot (complexFrequency k) u).re =
      dot k (complexRealPartVec u) := by
  obtain ⟨a, b, c⟩ := k
  simp [complexBilinearDot, complexFrequency, realVec3ToComplexVec3,
    complexRealPartVec, dot, Fin.sum_univ_three]

theorem complexBilinearDot_complexFrequency_im
    (k : RealVec3) (u : ComplexVec3) :
    (complexBilinearDot (complexFrequency k) u).im =
      dot k (complexImagPartVec u) := by
  obtain ⟨a, b, c⟩ := k
  simp [complexBilinearDot, complexFrequency, realVec3ToComplexVec3,
    complexImagPartVec, dot, Fin.sum_univ_three]

/-- A real orthogonal frame preserves the complex-bilinear divergence
pairing between a real frequency and a complex Fourier amplitude. -/
theorem complexBilinearDot_orientedFrame_covariant
    (F : OrientedFrameEquiv) (k : RealVec3) (u : ComplexVec3) :
    complexBilinearDot
        (complexFrequency (F.toFun k))
        (orientedFrameComplexLinearMap F u) =
      complexBilinearDot (complexFrequency k) u := by
  apply Complex.ext
  · rw [complexBilinearDot_complexFrequency_re,
      complexBilinearDot_complexFrequency_re]
    simp only [orientedFrameComplexLinearMap,
      complexRealPartVec_complexifyRealLinearEquiv]
    exact F.map_dot k (complexRealPartVec u)
  · rw [complexBilinearDot_complexFrequency_im,
      complexBilinearDot_complexFrequency_im]
    simp only [orientedFrameComplexLinearMap,
      complexImagPartVec_complexifyRealLinearEquiv]
    exact F.map_dot k (complexImagPartVec u)

/-- The real-frequency complex divergence pairing is exactly the periodic
Fourier `modeDot` after embedding an integer wavevector into `RealVec3`. -/
theorem complexBilinearDot_realWavevector_eq_modeDot
    (k : Wavevector) (u : VelocityCoefficient) :
    complexBilinearDot (complexFrequency (realWavevector k)) u =
      modeDot k u := by
  simp [complexBilinearDot, complexFrequency, realWavevector,
    realVec3ToComplexVec3, modeDot, Fin.sum_univ_three]

/-- The Euclidean coordinate implementation used by the sector projector is
the same oriented-frame map used by the complex amplitude transport. -/
theorem orientedFrameWavevectorCoordinates_eq_toFun_realWavevector
    (F : OrientedFrameEquiv) (k : Wavevector) :
    orientedFrameWavevectorCoordinates F k = F.toFun (realWavevector k) := by
  have h := orientedFrameEuclideanLinearIsometryEquiv_coordinates F
    (euclideanWavevectorOfWavevector k)
  simpa [orientedFrameWavevectorCoordinates, euclideanWavevectorOfWavevector,
    euclideanToRealVec3LinearEquiv, realWavevector] using h

theorem complexCoherentChartCoeff_re
    (k : RealVec3) (u : ComplexVec3) :
    (complexCoherentChartCoeff k u).re =
      coherentCoeff k (complexRealPartVec u) := by
  unfold complexCoherentChartCoeff coherentCoeff
  rw [Fin.sum_univ_three]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  simp only [complexRealPartVec, dot, coordinate_zero, coordinate_one,
    coordinate_two]
  ring

theorem complexCoherentChartCoeff_im
    (k : RealVec3) (u : ComplexVec3) :
    (complexCoherentChartCoeff k u).im =
      coherentCoeff k (complexImagPartVec u) := by
  unfold complexCoherentChartCoeff coherentCoeff
  rw [Fin.sum_univ_three]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul]
  simp only [complexImagPartVec, dot, coordinate_zero, coordinate_one,
    coordinate_two]
  ring

theorem complexRealPartVec_sub (u v : ComplexVec3) :
    complexRealPartVec (u - v) =
      sub (complexRealPartVec u) (complexRealPartVec v) := by
  apply Prod.ext
  · simp [complexRealPartVec, sub]
  · apply Prod.ext <;> simp [complexRealPartVec, sub]

theorem complexImagPartVec_sub (u v : ComplexVec3) :
    complexImagPartVec (u - v) =
      sub (complexImagPartVec u) (complexImagPartVec v) := by
  apply Prod.ext
  · simp [complexImagPartVec, sub]
  · apply Prod.ext <;> simp [complexImagPartVec, sub]

theorem complexRealPartVec_project
    (k : RealVec3) (u : ComplexVec3) :
    complexRealPartVec (complexCoherentChartProject k u) =
      coherentProject k (complexRealPartVec u) := by
  apply Prod.ext
  · simp [complexRealPartVec, complexCoherentChartProject,
      coherentProject, smul, realVec3ToComplexVec3,
      complexCoherentChartCoeff_re]
  · apply Prod.ext <;>
      simp [complexRealPartVec, complexCoherentChartProject,
        coherentProject, smul, realVec3ToComplexVec3,
        complexCoherentChartCoeff_re]

theorem complexImagPartVec_project
    (k : RealVec3) (u : ComplexVec3) :
    complexImagPartVec (complexCoherentChartProject k u) =
      coherentProject k (complexImagPartVec u) := by
  apply Prod.ext
  · simp [complexImagPartVec, complexCoherentChartProject,
      coherentProject, smul, realVec3ToComplexVec3,
      complexCoherentChartCoeff_im]
  · apply Prod.ext <;>
      simp [complexImagPartVec, complexCoherentChartProject,
        coherentProject, smul, realVec3ToComplexVec3,
        complexCoherentChartCoeff_im]

/-- The real part of the complex coherent-line remainder is the real
coherent-line remainder of the real part. -/
theorem complexRealPartVec_misalignment
    (k : RealVec3) (u : ComplexVec3) :
    complexRealPartVec (complexMisalignmentChartComponent k u) =
      sub (complexRealPartVec u)
        (coherentProject k (complexRealPartVec u)) := by
  rw [complexMisalignmentChartComponent, complexRealPartVec_sub,
    complexRealPartVec_project]

/-- The imaginary part of the complex coherent-line remainder is the real
coherent-line remainder of the imaginary part. -/
theorem complexImagPartVec_misalignment
    (k : RealVec3) (u : ComplexVec3) :
    complexImagPartVec (complexMisalignmentChartComponent k u) =
      sub (complexImagPartVec u)
        (coherentProject k (complexImagPartVec u)) := by
  rw [complexMisalignmentChartComponent, complexImagPartVec_sub,
    complexImagPartVec_project]

/-- **Complex modewise alignment bridge.**  For an arbitrary complex
divergence-free Fourier coefficient, the Hermitian energy of the exact
three-term split's coefficient remainder is bounded by its energy transverse
to the coherent reference line. -/
theorem complexEuclideanNormSq_misalignment_le_transverseEnergyEx
    (k : RealVec3) (u : ComplexVec3)
    (hperp : complexBilinearDot (complexFrequency k) u = 0)
    (hcoherent : 0 < normSq (coherentW k)) :
    complexEuclideanNormSq (complexMisalignmentChartComponent k u) ≤
      complexTransverseEnergyEx u := by
  rw [complexEuclideanNormSq_eq_real_add_imag,
    complexRealPartVec_misalignment, complexImagPartVec_misalignment,
    complexTransverseEnergyEx_eq_real_add_imag]
  exact add_le_add
    (normSq_realMisalignment_le_transverseEnergy_ex k
      (complexRealPartVec u)
      (dot_complexRealPartVec_eq_zero_of_perp k u hperp) hcoherent)
    (normSq_realMisalignment_le_transverseEnergy_ex k
      (complexImagPartVec u)
      (dot_complexImagPartVec_eq_zero_of_perp k u hperp) hcoherent)

/-- The chart `e_x` component of a physical direction in the full strain
frame is its inner product with the most expanding strain eigenvector. -/
theorem dot_ex_fullStrainFrame_eq_inner_expanding
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v)
    (xi : R3) :
    dot ex ((fullStrainFrame S hSsymm).toFun
      (realVec3OfEuclidean xi)) =
      inner ℝ xi ((orderedEigenframe S hSsymm).eigenbasis 0) := by
  calc
    dot ex ((fullStrainFrame S hSsymm).toFun
        (realVec3OfEuclidean xi)) =
        dot ((fullStrainFrame S hSsymm).toFun
          (expandingDirection S hSsymm))
          ((fullStrainFrame S hSsymm).toFun
            (realVec3OfEuclidean xi)) := by
      rw [fullStrainFrame_maps_expandingDirection_to_ex]
    _ = dot (expandingDirection S hSsymm)
          (realVec3OfEuclidean xi) :=
      (fullStrainFrame S hSsymm).map_dot _ _
    _ = inner ℝ ((orderedEigenframe S hSsymm).eigenbasis 0) xi := by
      rw [expandingDirection, dot_realVec3OfEuclidean]
    _ = inner ℝ xi ((orderedEigenframe S hSsymm).eigenbasis 0) :=
      real_inner_comm _ _

/-- **Strain-frame alignment bridge.**  A unit physical direction which is
perpendicular to a physical frequency has no more coherent-line remainder in
the full strain frame than its invariant misalignment from the most expanding
strain eigenline. -/
theorem fullStrainFrame_realMisalignment_le_alignmentEnergy
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v)
    (k : RealVec3) (xi : R3) (hxi : ‖xi‖ = 1)
    (hperp : dot k (realVec3OfEuclidean xi) = 0)
    (hcoherent : 0 < normSq (coherentW
      ((fullStrainFrame S hSsymm).toFun k))) :
    normSq (sub
      ((fullStrainFrame S hSsymm).toFun (realVec3OfEuclidean xi))
      (coherentProject ((fullStrainFrame S hSsymm).toFun k)
        ((fullStrainFrame S hSsymm).toFun
          (realVec3OfEuclidean xi)))) ≤
      alignmentEnergy xi ((orderedEigenframe S hSsymm).eigenbasis 0) := by
  have hxiChart : normSq
      ((fullStrainFrame S hSsymm).toFun
        (realVec3OfEuclidean xi)) = 1 := by
    rw [(fullStrainFrame S hSsymm).map_normSq,
      normSq_realVec3OfEuclidean, hxi]
    norm_num
  have hperpChart : dot
      ((fullStrainFrame S hSsymm).toFun k)
      ((fullStrainFrame S hSsymm).toFun
        (realVec3OfEuclidean xi)) = 0 := by
    rw [(fullStrainFrame S hSsymm).map_dot, hperp]
  have h := normSq_realMisalignment_le_alignmentEnergy_ex
    ((fullStrainFrame S hSsymm).toFun k)
    ((fullStrainFrame S hSsymm).toFun (realVec3OfEuclidean xi))
    hxiChart hperpChart hcoherent
  rw [dot_ex_fullStrainFrame_eq_inner_expanding] at h
  exact h

/-- On the genuine square-dyadic pancake sector the coherent denominator
needed by the strain-frame alignment bridge is automatically positive. -/
theorem normSq_coherentW_fullStrainFrame_pos_of_sector
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v)
    {N : ℕ} (hN : 2 ≤ N) (k : RealVec3)
    (hk : InRealSquarePancakeConeAnnulus N
      ((fullStrainFrame S hSsymm).toFun k)) :
    0 < normSq (coherentW ((fullStrainFrame S hSsymm).toFun k)) := by
  let q := (fullStrainFrame S hSsymm).toFun k
  have hqnorm : normSq q ≠ 0 := ne_of_gt hk.2.1
  have hN2 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by
    have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have htrans : 0 ≤ q.1 ^ 2 + q.2.1 ^ 2 := by positivity
  have hcone : q.1 ^ 2 + q.2.1 ^ 2 ≤ (1 / 4 : ℝ) * normSq q := by
    have hscaled : 4 * (q.1 ^ 2 + q.2.1 ^ 2) ≤ normSq q := by
      calc
        4 * (q.1 ^ 2 + q.2.1 ^ 2) ≤
            (N : ℝ) ^ 2 * (q.1 ^ 2 + q.2.1 ^ 2) := by gcongr
        _ ≤ normSq q := hk.2.2.2.2
    nlinarith
  exact normSq_coherentW_pos hqnorm hcone (le_refl (1 / 4 : ℝ))

/-- Sector form of the strain-frame alignment bridge, with no independent
nondegeneracy premise. -/
theorem fullStrainFrame_sector_realMisalignment_le_alignmentEnergy
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v)
    {N : ℕ} (hN : 2 ≤ N) (k : RealVec3) (xi : R3)
    (hsector : InRealSquarePancakeConeAnnulus N
      ((fullStrainFrame S hSsymm).toFun k))
    (hxi : ‖xi‖ = 1)
    (hperp : dot k (realVec3OfEuclidean xi) = 0) :
    normSq (sub
      ((fullStrainFrame S hSsymm).toFun (realVec3OfEuclidean xi))
      (coherentProject ((fullStrainFrame S hSsymm).toFun k)
        ((fullStrainFrame S hSsymm).toFun
          (realVec3OfEuclidean xi)))) ≤
      alignmentEnergy xi ((orderedEigenframe S hSsymm).eigenbasis 0) :=
  fullStrainFrame_realMisalignment_le_alignmentEnergy S hSsymm k xi hxi
    hperp
    (normSq_coherentW_fullStrainFrame_pos_of_sector
      S hSsymm hN k hsector)

/-- Complex Fourier form of the full-strain-frame bridge.  Physical
divergence-freeness is transported into the chart rather than assumed again
after rotation. -/
theorem fullStrainFrame_sector_complexMisalignment_le_transverseEnergyEx
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v)
    {N : ℕ} (hN : 2 ≤ N) (k : RealVec3) (u : ComplexVec3)
    (hsector : InRealSquarePancakeConeAnnulus N
      ((fullStrainFrame S hSsymm).toFun k))
    (hperp : complexBilinearDot (complexFrequency k) u = 0) :
    complexEuclideanNormSq
        (complexMisalignmentChartComponent
          ((fullStrainFrame S hSsymm).toFun k)
          (orientedFrameComplexLinearMap
            (fullStrainFrame S hSsymm) u)) ≤
      complexTransverseEnergyEx
        (orientedFrameComplexLinearMap
          (fullStrainFrame S hSsymm) u) := by
  apply complexEuclideanNormSq_misalignment_le_transverseEnergyEx
  · rw [complexBilinearDot_orientedFrame_covariant, hperp]
  · exact normSq_coherentW_fullStrainFrame_pos_of_sector
      S hSsymm hN k hsector

/-- **Finite-sector energy bridge.**  For a divergence-free periodic Fourier
field, the total exact coefficient-remainder energy on a genuine physical
square-dyadic pancake sector is bounded by the total chart energy transverse
to the expanding strain eigenline. -/
theorem fullStrainFrame_sectorModes_sum_complexMisalignment_le
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v)
    {N : ℕ} (hN : 2 ≤ N) (support : Finset Wavevector)
    (omega : FourierVelocity)
    (hdiv : ∀ k, modeDot k (omega k) = 0) :
    (∑ k ∈ squareDyadicPancakeSectorModes
          (fullStrainFrame S hSsymm) N support,
        complexEuclideanNormSq
          (complexMisalignmentChartComponent
            (orientedFrameWavevectorCoordinates
              (fullStrainFrame S hSsymm) k)
            (orientedFrameComplexLinearMap
              (fullStrainFrame S hSsymm) (omega k)))) ≤
      ∑ k ∈ squareDyadicPancakeSectorModes
          (fullStrainFrame S hSsymm) N support,
        complexTransverseEnergyEx
          (orientedFrameComplexLinearMap
            (fullStrainFrame S hSsymm) (omega k)) := by
  apply Finset.sum_le_sum
  intro k hk
  have hksector : InOrientedSquarePancakeConeAnnulus
      (fullStrainFrame S hSsymm) N k :=
    (mem_squareDyadicPancakeSectorModes_iff
      (fullStrainFrame S hSsymm) N support k).mp hk |>.2
  have hsector : InRealSquarePancakeConeAnnulus N
      ((fullStrainFrame S hSsymm).toFun (realWavevector k)) := by
    rw [← orientedFrameWavevectorCoordinates_eq_toFun_realWavevector]
    exact hksector
  have hperp : complexBilinearDot
      (complexFrequency (realWavevector k)) (omega k) = 0 := by
    rw [complexBilinearDot_realWavevector_eq_modeDot, hdiv]
  simpa [orientedFrameWavevectorCoordinates_eq_toFun_realWavevector] using
    fullStrainFrame_sector_complexMisalignment_le_transverseEnergyEx
      S hSsymm hN (realWavevector k) (omega k) hsector hperp

/-- **Physical-space finite-sector bridge.**  The total coefficient energy of
the exact coherent-line remainder is controlled by the physical `L²` energy
in the two chart components transverse to the expanding strain eigenline.
The frame is frozen at the supplied symmetric strain tensor `S`; no
cardinality loss occurs. -/
theorem fullStrainFrame_sectorModes_sum_complexMisalignment_le_integral
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v)
    {N : ℕ} (hN : 2 ≤ N) (support : Finset Wavevector)
    (omega : FourierVelocity)
    (hdiv : ∀ k, modeDot k (omega k) = 0) :
    (∑ k ∈ squareDyadicPancakeSectorModes
          (fullStrainFrame S hSsymm) N support,
        complexEuclideanNormSq
          (complexMisalignmentChartComponent
            (orientedFrameWavevectorCoordinates
              (fullStrainFrame S hSsymm) k)
            (orientedFrameComplexLinearMap
              (fullStrainFrame S hSsymm) (omega k)))) ≤
      ∫ x : UnitAddTorus (Fin 3),
        complexTransverseEnergyEx
          (finiteFourierReconstruction
            (squareDyadicPancakeSectorModes
              (fullStrainFrame S hSsymm) N support)
            (fun k ↦ orientedFrameComplexLinearMap
              (fullStrainFrame S hSsymm) (omega k)) x) := by
  calc
    (∑ k ∈ squareDyadicPancakeSectorModes
          (fullStrainFrame S hSsymm) N support,
        complexEuclideanNormSq
          (complexMisalignmentChartComponent
            (orientedFrameWavevectorCoordinates
              (fullStrainFrame S hSsymm) k)
            (orientedFrameComplexLinearMap
              (fullStrainFrame S hSsymm) (omega k)))) ≤
        ∑ k ∈ squareDyadicPancakeSectorModes
          (fullStrainFrame S hSsymm) N support,
          complexTransverseEnergyEx
            (orientedFrameComplexLinearMap
              (fullStrainFrame S hSsymm) (omega k)) :=
      fullStrainFrame_sectorModes_sum_complexMisalignment_le
        S hSsymm hN support omega hdiv
    _ = ∫ x : UnitAddTorus (Fin 3),
        complexTransverseEnergyEx
          (finiteFourierReconstruction
            (squareDyadicPancakeSectorModes
              (fullStrainFrame S hSsymm) N support)
            (fun k ↦ orientedFrameComplexLinearMap
              (fullStrainFrame S hSsymm) (omega k)) x) :=
      (integral_transverseEnergyEx_finiteFourierReconstruction
        (squareDyadicPancakeSectorModes
          (fullStrainFrame S hSsymm) N support)
        (fun k ↦ orientedFrameComplexLinearMap
          (fullStrainFrame S hSsymm) (omega k))).symm

end PancakeMisalignmentEnergyBridge
end NavierStokes
end FluidDynamics
end Mettapedia
