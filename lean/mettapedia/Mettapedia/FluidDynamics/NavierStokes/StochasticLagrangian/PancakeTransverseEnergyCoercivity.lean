import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeTransverseEnergyFreezing

/-!
# Coercivity of frozen transverse energy by the strain defect

On the branch where the top strain eigenvalue is separated from the other
two, energy transverse to the top eigenline is controlled by the Rayleigh
defect.  The estimate is homogeneous, so it applies at vorticity zeros without
normalizing the field.

The complex statement applies the real estimate to the coordinatewise real
and imaginary parts.  It is then integrated over a finite Fourier
reconstruction and composed with the exact pancake-remainder freezing bound.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeTransverseEnergyCoercivity

open scoped BigOperators RealInnerProductSpace
open MeasureTheory
open PeriodicFourierTriad
open PancakeAlignmentDynamics
open PancakeComplexMisalignmentExpansion
open PancakeFiniteFourierBilinearTransfer
open PancakeFullStrainFrame
open PancakeMisalignmentEnergyBridge
open PancakePeriodicCoherentSplit
open PancakePhysicalFrameKernelTransfer
open PancakePhysicalMisalignmentSplit
open PancakeSmoothCoherentSymbol
open PancakeSquareDyadicSectorProjector
open PancakeStrainSpectralFrame
open PancakeTransverseEnergyFreezing

local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Parseval in a three-dimensional real orthonormal basis, without unit
normalization of the vector. -/
theorem parseval_three_norm_sq
    (b : OrthonormalBasis (Fin 3) ℝ R3) (u : R3) :
    (inner ℝ u (b 0)) ^ 2 + (inner ℝ u (b 1)) ^ 2 +
      (inner ℝ u (b 2)) ^ 2 = ‖u‖ ^ 2 := by
  have h := b.sum_inner_mul_inner u u
  simpa [Fin.sum_univ_succ, real_inner_comm, pow_two,
    real_inner_self_eq_norm_sq, add_assoc] using h

/-- Homogeneous spectral-gap coercivity: transverse energy relative to the
top eigenline is bounded by the top Rayleigh defect. -/
theorem gap_mul_transverseLineEnergy_le_strainDefect
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v)
    (u : R3) (gap : ℝ)
    (hgap₁ : gap ≤
      (orderedEigenframe S hSsymm).eigenvalue 0 -
        (orderedEigenframe S hSsymm).eigenvalue 1)
    (hgap₂ : gap ≤
      (orderedEigenframe S hSsymm).eigenvalue 0 -
        (orderedEigenframe S hSsymm).eigenvalue 2) :
    gap * transverseLineEnergy
        ((orderedEigenframe S hSsymm).eigenbasis 0) u ≤
      (orderedEigenframe S hSsymm).eigenvalue 0 * ‖u‖ ^ 2 -
        inner ℝ u (S u) := by
  let F := orderedEigenframe S hSsymm
  have hparse := parseval_three_norm_sq F.eigenbasis u
  have hray := rayleigh_three S hSsymm F.eigenvalue F.eigenbasis
    F.apply_eigenbasis u
  change gap ≤ F.eigenvalue 0 - F.eigenvalue 1 at hgap₁
  change gap ≤ F.eigenvalue 0 - F.eigenvalue 2 at hgap₂
  change gap * transverseLineEnergy (F.eigenbasis 0) u ≤
    F.eigenvalue 0 * ‖u‖ ^ 2 - inner ℝ u (S u)
  calc
    gap * transverseLineEnergy (F.eigenbasis 0) u =
        gap * ((inner ℝ u (F.eigenbasis 1)) ^ 2 +
          (inner ℝ u (F.eigenbasis 2)) ^ 2) := by
      unfold transverseLineEnergy
      rw [← hparse]
      ring
    _ ≤ (F.eigenvalue 0 - F.eigenvalue 1) *
          (inner ℝ u (F.eigenbasis 1)) ^ 2 +
        (F.eigenvalue 0 - F.eigenvalue 2) *
          (inner ℝ u (F.eigenbasis 2)) ^ 2 := by
      rw [mul_add]
      exact add_le_add
        (mul_le_mul_of_nonneg_right hgap₁ (sq_nonneg _))
        (mul_le_mul_of_nonneg_right hgap₂ (sq_nonneg _))
    _ = F.eigenvalue 0 * ‖u‖ ^ 2 - inner ℝ u (S u) := by
      rw [← hparse, hray]
      ring

/-- Complex Rayleigh defect, obtained by adding the real- and imaginary-part
defects. -/
def complexStrainDefect
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v)
    (u : ComplexVec3) : ℝ :=
  (orderedEigenframe S hSsymm).eigenvalue 0 *
      complexEuclideanNormSq u -
    (inner ℝ (complexRealPartEuclidean u)
        (S (complexRealPartEuclidean u)) +
      inner ℝ (complexImagPartEuclidean u)
        (S (complexImagPartEuclidean u)))

/-- Complex homogeneous spectral-gap coercivity. -/
theorem gap_mul_complexTransverseLineEnergy_le_complexStrainDefect
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v)
    (u : ComplexVec3) (gap : ℝ)
    (hgap₁ : gap ≤
      (orderedEigenframe S hSsymm).eigenvalue 0 -
        (orderedEigenframe S hSsymm).eigenvalue 1)
    (hgap₂ : gap ≤
      (orderedEigenframe S hSsymm).eigenvalue 0 -
        (orderedEigenframe S hSsymm).eigenvalue 2) :
    gap * complexTransverseLineEnergy
        ((orderedEigenframe S hSsymm).eigenbasis 0) u ≤
      complexStrainDefect S hSsymm u := by
  have hre := gap_mul_transverseLineEnergy_le_strainDefect
    S hSsymm (complexRealPartEuclidean u) gap hgap₁ hgap₂
  have him := gap_mul_transverseLineEnergy_le_strainDefect
    S hSsymm (complexImagPartEuclidean u) gap hgap₁ hgap₂
  unfold complexTransverseLineEnergy complexStrainDefect
  rw [complexEuclideanNormSq_eq_parts]
  linarith [hre, him]

theorem continuous_complexStrainDefect_comp
    {X : Type*} [TopologicalSpace X]
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v)
    {u : X → ComplexVec3} (hu : Continuous u) :
    Continuous (fun x ↦ complexStrainDefect S hSsymm (u x)) := by
  have hre : Continuous (fun x ↦ complexRealPartEuclidean (u x)) := by
    unfold complexRealPartEuclidean
    fun_prop
  have him : Continuous (fun x ↦ complexImagPartEuclidean (u x)) := by
    unfold complexImagPartEuclidean
    fun_prop
  have hnorm : Continuous (fun x ↦ complexEuclideanNormSq (u x)) :=
    continuous_complexEuclideanNormSq_comp hu
  have hSre : Continuous (fun x ↦ S (complexRealPartEuclidean (u x))) :=
    S.continuous.comp hre
  have hSim : Continuous (fun x ↦ S (complexImagPartEuclidean (u x))) :=
    S.continuous.comp him
  unfold complexStrainDefect
  exact (continuous_const.mul hnorm).sub
    ((hre.inner hSre).add (him.inner hSim))

/-- Integrated coercivity for a finite Fourier reconstruction in the full
frozen strain frame. -/
theorem gap_mul_integral_fullStrainFrame_transverseEnergy_le_defect
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v)
    (s : Finset Wavevector) (omega : FourierVelocity) (gap : ℝ)
    (hgap₁ : gap ≤
      (orderedEigenframe S hSsymm).eigenvalue 0 -
        (orderedEigenframe S hSsymm).eigenvalue 1)
    (hgap₂ : gap ≤
      (orderedEigenframe S hSsymm).eigenvalue 0 -
        (orderedEigenframe S hSsymm).eigenvalue 2) :
    gap * (∫ x : UnitAddTorus (Fin 3),
      complexTransverseEnergyEx
        (finiteFourierReconstruction s
          (fun k ↦ orientedFrameComplexLinearMap
            (fullStrainFrame S hSsymm) (omega k)) x)) ≤
      ∫ x : UnitAddTorus (Fin 3),
        complexStrainDefect S hSsymm
          (finiteFourierReconstruction s omega x) := by
  let field : UnitAddTorus (Fin 3) → ComplexVec3 :=
    finiteFourierReconstruction s omega
  let frameField : UnitAddTorus (Fin 3) → ComplexVec3 :=
    finiteFourierReconstruction s
      (fun k ↦ orientedFrameComplexLinearMap
        (fullStrainFrame S hSsymm) (omega k))
  have hfield : Continuous field :=
    continuous_finiteFourierReconstruction s omega
  have hframeField : Continuous frameField :=
    continuous_finiteFourierReconstruction s _
  have htransInt : Integrable
      (fun x ↦ complexTransverseEnergyEx (frameField x)) := by
    have hcont := continuous_complexTransverseEnergyEx_comp hframeField
    simpa only [integrableOn_univ] using
      hcont.continuousOn.integrableOn_compact
        (isCompact_univ : IsCompact
          (Set.univ : Set (UnitAddTorus (Fin 3))))
  have hdefectInt : Integrable
      (fun x ↦ complexStrainDefect S hSsymm (field x)) := by
    have hcont := continuous_complexStrainDefect_comp S hSsymm hfield
    simpa only [integrableOn_univ] using
      hcont.continuousOn.integrableOn_compact
        (isCompact_univ : IsCompact
          (Set.univ : Set (UnitAddTorus (Fin 3))))
  have hpoint : ∀ x,
      gap * complexTransverseEnergyEx (frameField x) ≤
        complexStrainDefect S hSsymm (field x) := by
    intro x
    rw [show complexTransverseEnergyEx (frameField x) =
        complexTransverseLineEnergy
          ((orderedEigenframe S hSsymm).eigenbasis 0) (field x) by
      exact fullStrainFrame_transverseEnergy_finiteReconstruction_eq
        S hSsymm s omega x]
    exact gap_mul_complexTransverseLineEnergy_le_complexStrainDefect
      S hSsymm (field x) gap hgap₁ hgap₂
  change gap * (∫ x, complexTransverseEnergyEx (frameField x)) ≤
    ∫ x, complexStrainDefect S hSsymm (field x)
  calc
    gap * (∫ x, complexTransverseEnergyEx (frameField x)) =
        ∫ x, gap * complexTransverseEnergyEx (frameField x) := by
      rw [integral_const_mul]
    _ ≤ ∫ x, complexStrainDefect S hSsymm (field x) :=
      integral_mono (htransInt.const_mul gap) hdefectInt hpoint

/-- **Separated-cell coercive remainder estimate.**  If the two frozen top
gaps dominate `threshold + epsilon`, the collision branches are excluded and
the exact sector remainder is controlled by the integrated strain defect plus
the explicit frame-oscillation energy error. -/
theorem gap_mul_sectorMisalignment_le_defect_add_freezingError
    (A B : R3 →L[ℝ] R3)
    (hAsymm : ∀ (u v : R3), inner ℝ u (A v) = inner ℝ (A u) v)
    (hBsymm : ∀ (u v : R3), inner ℝ u (B v) = inner ℝ (B u) v)
    (epsilon threshold : ℝ) (hthreshold : 0 < threshold)
    (hepsilon : 0 ≤ epsilon) (hAB : ‖A - B‖ ≤ epsilon)
    (hgap₁ : threshold + epsilon ≤
      (orderedEigenframe B hBsymm).eigenvalue 0 -
        (orderedEigenframe B hBsymm).eigenvalue 1)
    (hgap₂ : threshold + epsilon ≤
      (orderedEigenframe B hBsymm).eigenvalue 0 -
        (orderedEigenframe B hBsymm).eigenvalue 2)
    {N : ℕ} (hN : 2 ≤ N) (support : Finset Wavevector)
    (omega : FourierVelocity) (hdiv : ∀ k, modeDot k (omega k) = 0) :
    (threshold + epsilon) *
      (∑ k ∈ squareDyadicPancakeSectorModes
            (fullStrainFrame A hAsymm) N support,
          complexEuclideanNormSq
            (complexMisalignmentChartComponent
              (orientedFrameWavevectorCoordinates
                (fullStrainFrame A hAsymm) k)
              (orientedFrameComplexLinearMap
                (fullStrainFrame A hAsymm) (omega k)))) ≤
      (∫ x : UnitAddTorus (Fin 3),
        complexStrainDefect B hBsymm
          (finiteFourierReconstruction
            (squareDyadicPancakeSectorModes
              (fullStrainFrame A hAsymm) N support)
            omega x)) +
      (threshold + epsilon) * (4 * (epsilon / threshold)) *
        ∫ x : UnitAddTorus (Fin 3),
          complexEuclideanNormSq
            (finiteFourierReconstruction
              (squareDyadicPancakeSectorModes
                (fullStrainFrame A hAsymm) N support)
              omega x) := by
  let sA := squareDyadicPancakeSectorModes
    (fullStrainFrame A hAsymm) N support
  let remainderEnergy :=
    ∑ k ∈ sA,
      complexEuclideanNormSq
        (complexMisalignmentChartComponent
          (orientedFrameWavevectorCoordinates
            (fullStrainFrame A hAsymm) k)
          (orientedFrameComplexLinearMap
            (fullStrainFrame A hAsymm) (omega k)))
  let transverseIntegral :=
    ∫ x : UnitAddTorus (Fin 3),
      complexTransverseEnergyEx
        (finiteFourierReconstruction sA
          (fun k ↦ orientedFrameComplexLinearMap
            (fullStrainFrame B hBsymm) (omega k)) x)
  let defectIntegral :=
    ∫ x : UnitAddTorus (Fin 3),
      complexStrainDefect B hBsymm
        (finiteFourierReconstruction sA omega x)
  let fullEnergyIntegral :=
    ∫ x : UnitAddTorus (Fin 3),
      complexEuclideanNormSq (finiteFourierReconstruction sA omega x)
  have hfreeze := sectorMisalignment_smallFrozenGap_or_le_frozenIntegral
    A B hAsymm hBsymm epsilon threshold hthreshold hepsilon hAB
      hN support omega hdiv
  have hfar : remainderEnergy ≤ transverseIntegral +
      (4 * (epsilon / threshold)) * fullEnergyIntegral := by
    rcases hfreeze with hsmall₁ | hsmall₂ | hfar
    · exact False.elim ((not_lt_of_ge hgap₁) hsmall₁)
    · exact False.elim ((not_lt_of_ge hgap₂) hsmall₂)
    · simpa [remainderEnergy, transverseIntegral, fullEnergyIntegral, sA]
        using hfar
  have hcoercive : (threshold + epsilon) * transverseIntegral ≤
      defectIntegral := by
    simpa [transverseIntegral, defectIntegral, sA] using
      gap_mul_integral_fullStrainFrame_transverseEnergy_le_defect
        B hBsymm sA omega (threshold + epsilon) hgap₁ hgap₂
  have hgapNonneg : 0 ≤ threshold + epsilon := by linarith
  change (threshold + epsilon) * remainderEnergy ≤
    defectIntegral +
      (threshold + epsilon) * (4 * (epsilon / threshold)) *
        fullEnergyIntegral
  calc
    (threshold + epsilon) * remainderEnergy ≤
        (threshold + epsilon) *
          (transverseIntegral +
            (4 * (epsilon / threshold)) * fullEnergyIntegral) :=
      mul_le_mul_of_nonneg_left hfar hgapNonneg
    _ = (threshold + epsilon) * transverseIntegral +
        (threshold + epsilon) * (4 * (epsilon / threshold)) *
          fullEnergyIntegral := by ring
    _ ≤ defectIntegral +
        (threshold + epsilon) * (4 * (epsilon / threshold)) *
          fullEnergyIntegral :=
      add_le_add hcoercive (le_refl _)

/-- Final cellwise dichotomy: either the frozen top strain gap is small, or
the exact sector remainder satisfies the coercive strain-defect estimate with
the explicit frame-freezing error. -/
theorem smallFrozenGap_or_gap_mul_sectorMisalignment_le_defect
    (A B : R3 →L[ℝ] R3)
    (hAsymm : ∀ (u v : R3), inner ℝ u (A v) = inner ℝ (A u) v)
    (hBsymm : ∀ (u v : R3), inner ℝ u (B v) = inner ℝ (B u) v)
    (epsilon threshold : ℝ) (hthreshold : 0 < threshold)
    (hepsilon : 0 ≤ epsilon) (hAB : ‖A - B‖ ≤ epsilon)
    {N : ℕ} (hN : 2 ≤ N) (support : Finset Wavevector)
    (omega : FourierVelocity) (hdiv : ∀ k, modeDot k (omega k) = 0) :
    (orderedEigenframe B hBsymm).eigenvalue 0 -
        (orderedEigenframe B hBsymm).eigenvalue 1 <
          threshold + epsilon ∨
      (orderedEigenframe B hBsymm).eigenvalue 0 -
        (orderedEigenframe B hBsymm).eigenvalue 2 <
          threshold + epsilon ∨
      (threshold + epsilon) *
        (∑ k ∈ squareDyadicPancakeSectorModes
              (fullStrainFrame A hAsymm) N support,
            complexEuclideanNormSq
              (complexMisalignmentChartComponent
                (orientedFrameWavevectorCoordinates
                  (fullStrainFrame A hAsymm) k)
                (orientedFrameComplexLinearMap
                  (fullStrainFrame A hAsymm) (omega k)))) ≤
        (∫ x : UnitAddTorus (Fin 3),
          complexStrainDefect B hBsymm
            (finiteFourierReconstruction
              (squareDyadicPancakeSectorModes
                (fullStrainFrame A hAsymm) N support)
              omega x)) +
        (threshold + epsilon) * (4 * (epsilon / threshold)) *
          ∫ x : UnitAddTorus (Fin 3),
            complexEuclideanNormSq
              (finiteFourierReconstruction
                (squareDyadicPancakeSectorModes
                  (fullStrainFrame A hAsymm) N support)
                omega x) := by
  by_cases hgap₁ : threshold + epsilon ≤
      (orderedEigenframe B hBsymm).eigenvalue 0 -
        (orderedEigenframe B hBsymm).eigenvalue 1
  · by_cases hgap₂ : threshold + epsilon ≤
        (orderedEigenframe B hBsymm).eigenvalue 0 -
          (orderedEigenframe B hBsymm).eigenvalue 2
    · exact Or.inr (Or.inr
        (gap_mul_sectorMisalignment_le_defect_add_freezingError
          A B hAsymm hBsymm epsilon threshold hthreshold hepsilon hAB
          hgap₁ hgap₂ hN support omega hdiv))
    · exact Or.inr (Or.inl (lt_of_not_ge hgap₂))
  · exact Or.inl (lt_of_not_ge hgap₁)

end PancakeTransverseEnergyCoercivity
end NavierStokes
end FluidDynamics
end Mettapedia
