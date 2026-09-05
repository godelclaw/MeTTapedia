import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpectralProjectorRegularity

/-!
# Spectral-cluster resolution of the top-gap collision branch

When the two largest strain eigenvalues collide, a distinguished expanding
line need not vary continuously.  In three dimensions the corresponding
expanding two-plane can still be stable: it is the orthogonal complement of
the bottom eigenline.  Only when the bottom gap collapses as well is that
plane no longer distinguished; for a trace-free strain, simultaneous collapse
of both adjacent gaps forces the entire spectrum to be small.

This module formalizes that trichotomy.  It proves bottom-eigenvalue Weyl
stability, a quantitative local Lipschitz theorem for the bottom-line and
expanding-plane projectors, the exact two-gap decomposition of the complex
Rayleigh defect, and the trace-free triple-cluster estimate.  These statements
identify precisely what remains to be controlled on the collision branch;
they do not choose an eigenvector inside a degenerate expanding plane.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeSpectralClusterDichotomy

open scoped RealInnerProductSpace
open PeriodicFourierTriad
open PancakeAlignmentDynamics
open PancakeEigenframePerturbation
open PancakeMisalignmentEnergyBridge
open PancakePeriodicCoherentSplit
open PancakeSmoothCoherentSymbol
open PancakeStrainSpectralFrame
open PancakeTransverseEnergyCoercivity
open PancakeTransverseEnergyFreezing
open PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain

local notation "R3" => EuclideanSpace ℝ (Fin 3)

namespace SymmetricStrain

/-- Gap between the middle and bottom eigenvalues. -/
def bottomGap (S : SymmetricStrain) : ℝ :=
  secondEigenvalue S - thirdEigenvalue S

/-- Full spectral width. -/
def spectralWidth (S : SymmetricStrain) : ℝ :=
  topEigenvalue S - thirdEigenvalue S

/-- Sign-invariant projector onto the most contracting eigendirection. -/
def bottomEigenlineProjector (S : SymmetricStrain) : R3 →L[ℝ] R3 :=
  lineProjector ((orderedEigenframe S.1 S.2).eigenbasis 2)

/-- Projector onto the two-plane complementary to the bottom eigenline. -/
def expandingPlaneProjector (S : SymmetricStrain) : R3 →L[ℝ] R3 :=
  ContinuousLinearMap.id ℝ R3 - bottomEigenlineProjector S

theorem bottomGap_nonneg (S : SymmetricStrain) : 0 ≤ bottomGap S := by
  exact sub_nonneg.mpr
    ((orderedEigenframe S.1 S.2).antitone_eigenvalue (by decide))

theorem spectralWidth_eq_topGap_add_bottomGap (S : SymmetricStrain) :
    spectralWidth S = topGap S + bottomGap S := by
  unfold spectralWidth topGap bottomGap topEigenvalue secondEigenvalue
    thirdEigenvalue
  ring

theorem topGap_le_spectralWidth (S : SymmetricStrain) :
    topGap S ≤ spectralWidth S := by
  rw [spectralWidth_eq_topGap_add_bottomGap]
  exact le_add_of_nonneg_right (bottomGap_nonneg S)

theorem bottomGap_le_spectralWidth (S : SymmetricStrain) :
    bottomGap S ≤ spectralWidth S := by
  rw [spectralWidth_eq_topGap_add_bottomGap]
  exact le_add_of_nonneg_left (topGap_nonneg S)

end SymmetricStrain

open SymmetricStrain

/-! ## Bottom eigenvalue and bottom-projector perturbation -/

/-- The bottom eigenvalue of the constructed ordered frame is below every
unit Rayleigh quotient. -/
theorem constructedBottomEigenvalue_le_rayleigh
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v)
    (u : R3) (hu : ‖u‖ = 1) :
    (orderedEigenframe S hSsymm).eigenvalue 2 ≤ inner ℝ u (S u) := by
  let F := orderedEigenframe S hSsymm
  have hparse := parseval_three F.eigenbasis u hu
  have hray := rayleigh_three S hSsymm F.eigenvalue F.eigenbasis
    F.apply_eigenbasis u
  have h20 : F.eigenvalue 2 ≤ F.eigenvalue 0 :=
    F.antitone_eigenvalue (by decide)
  have h21 : F.eigenvalue 2 ≤ F.eigenvalue 1 :=
    F.antitone_eigenvalue (by decide)
  change F.eigenvalue 2 ≤ inner ℝ u (S u)
  calc
    F.eigenvalue 2 =
        F.eigenvalue 2 * (inner ℝ u (F.eigenbasis 0)) ^ 2 +
          F.eigenvalue 2 * (inner ℝ u (F.eigenbasis 1)) ^ 2 +
          F.eigenvalue 2 * (inner ℝ u (F.eigenbasis 2)) ^ 2 := by
      rw [← mul_add, ← mul_add, hparse, mul_one]
    _ ≤ F.eigenvalue 0 * (inner ℝ u (F.eigenbasis 0)) ^ 2 +
          F.eigenvalue 1 * (inner ℝ u (F.eigenbasis 1)) ^ 2 +
          F.eigenvalue 2 * (inner ℝ u (F.eigenbasis 2)) ^ 2 := by
      gcongr
    _ = inner ℝ u (S u) := hray.symm

/-- Weyl estimate for the bottom eigenvalues of two symmetric strains. -/
theorem abs_constructedBottomEigenvalue_sub_le
    (A B : R3 →L[ℝ] R3)
    (hAsymm : ∀ (u v : R3), inner ℝ u (A v) = inner ℝ (A u) v)
    (hBsymm : ∀ (u v : R3), inner ℝ u (B v) = inner ℝ (B u) v) :
    |(orderedEigenframe A hAsymm).eigenvalue 2 -
        (orderedEigenframe B hBsymm).eigenvalue 2| ≤ ‖A - B‖ := by
  let eA := (orderedEigenframe A hAsymm).eigenbasis 2
  let eB := (orderedEigenframe B hBsymm).eigenbasis 2
  have heA : ‖eA‖ = 1 :=
    (orderedEigenframe A hAsymm).eigenbasis.norm_eq_one 2
  have heB : ‖eB‖ = 1 :=
    (orderedEigenframe B hBsymm).eigenbasis.norm_eq_one 2
  have hAeA : inner ℝ eA (A eA) =
      (orderedEigenframe A hAsymm).eigenvalue 2 := by
    rw [(orderedEigenframe A hAsymm).apply_eigenbasis,
      real_inner_smul_right, real_inner_self_eq_norm_sq, heA]
    norm_num
  have hBeB : inner ℝ eB (B eB) =
      (orderedEigenframe B hBsymm).eigenvalue 2 := by
    rw [(orderedEigenframe B hBsymm).apply_eigenbasis,
      real_inner_smul_right, real_inner_self_eq_norm_sq, heB]
    norm_num
  have hB_at_eA := constructedBottomEigenvalue_le_rayleigh B hBsymm eA heA
  have hA_at_eB := constructedBottomEigenvalue_le_rayleigh A hAsymm eB heB
  have hpertA := abs_inner_clm_apply_le_opNorm (A - B) eB heB
  have hpertB := abs_inner_clm_apply_le_opNorm (B - A) eA heA
  have hBA : ‖B - A‖ = ‖A - B‖ := norm_sub_rev B A
  have hsplitA : inner ℝ eB ((A - B) eB) =
      inner ℝ eB (A eB) - inner ℝ eB (B eB) := by
    rw [sub_apply, inner_sub_right]
  have hsplitB : inner ℝ eA ((B - A) eA) =
      inner ℝ eA (B eA) - inner ℝ eA (A eA) := by
    rw [sub_apply, inner_sub_right]
  rw [abs_le]
  constructor
  · rw [hBA, hsplitB, hAeA] at hpertB
    have hp := (abs_le.mp hpertB).2
    linarith [hp, hB_at_eA]
  · rw [hsplitA, hBeB] at hpertA
    have hp := (abs_le.mp hpertA).2
    linarith [hp, hA_at_eB]

/-- Generic matched-eigenline perturbation specialized to the bottom lines
of the two constructed ordered frames. -/
theorem constructedContractingLine_nearCollision_or_projectorClose
    (A B : R3 →L[ℝ] R3)
    (hAsymm : ∀ (u v : R3), inner ℝ u (A v) = inner ℝ (A u) v)
    (hBsymm : ∀ (u v : R3), inner ℝ u (B v) = inner ℝ (B u) v)
    (epsilon threshold : ℝ) (hthreshold : 0 < threshold)
    (hepsilon : 0 ≤ epsilon) (hAB : ‖A - B‖ ≤ epsilon) :
    |(orderedEigenframe A hAsymm).eigenvalue 2 -
        (orderedEigenframe B hBsymm).eigenvalue 0| < threshold ∨
      |(orderedEigenframe A hAsymm).eigenvalue 2 -
        (orderedEigenframe B hBsymm).eigenvalue 1| < threshold ∨
      ‖lineProjector ((orderedEigenframe A hAsymm).eigenbasis 2) -
          lineProjector ((orderedEigenframe B hBsymm).eigenbasis 2)‖ ≤
        4 * (epsilon / threshold) := by
  apply nearDegenerate_or_norm_matchedEigenline_sub_le
    A B
    ((orderedEigenframe A hAsymm).eigenbasis 2)
    ((orderedEigenframe B hBsymm).eigenbasis 2)
    ((orderedEigenframe B hBsymm).eigenbasis 0)
    ((orderedEigenframe B hBsymm).eigenbasis 1)
    ((orderedEigenframe A hAsymm).eigenvalue 2)
    ((orderedEigenframe B hBsymm).eigenvalue 0)
    ((orderedEigenframe B hBsymm).eigenvalue 1)
    epsilon threshold hBsymm
  · exact (orderedEigenframe A hAsymm).apply_eigenbasis 2
  · exact (orderedEigenframe B hBsymm).apply_eigenbasis 0
  · exact (orderedEigenframe B hBsymm).apply_eigenbasis 1
  · exact (orderedEigenframe A hAsymm).eigenbasis.norm_eq_one 2
  · exact (orderedEigenframe B hBsymm).eigenbasis.norm_eq_one 2
  · exact (orderedEigenframe B hBsymm).eigenbasis.norm_eq_one 0
  · exact (orderedEigenframe B hBsymm).eigenbasis.norm_eq_one 1
  · have hparse := parseval_three
        (orderedEigenframe B hBsymm).eigenbasis
        ((orderedEigenframe A hAsymm).eigenbasis 2)
        ((orderedEigenframe A hAsymm).eigenbasis.norm_eq_one 2)
    nlinarith [hparse]
  · exact hthreshold
  · exact hepsilon
  · exact hAB

/-- Either the frozen bottom gap is small, or the contracting-line projector
is close.  This is the bottom-cluster analogue of the existing top-line
alternative. -/
theorem constructedContractingLine_smallFrozenGap_or_projectorClose
    (A B : R3 →L[ℝ] R3)
    (hAsymm : ∀ (u v : R3), inner ℝ u (A v) = inner ℝ (A u) v)
    (hBsymm : ∀ (u v : R3), inner ℝ u (B v) = inner ℝ (B u) v)
    (epsilon threshold : ℝ) (hthreshold : 0 < threshold)
    (hepsilon : 0 ≤ epsilon) (hAB : ‖A - B‖ ≤ epsilon) :
    (orderedEigenframe B hBsymm).eigenvalue 1 -
        (orderedEigenframe B hBsymm).eigenvalue 2 <
          threshold + epsilon ∨
      ‖lineProjector ((orderedEigenframe A hAsymm).eigenbasis 2) -
          lineProjector ((orderedEigenframe B hBsymm).eigenbasis 2)‖ ≤
        4 * (epsilon / threshold) := by
  have hbottom : |(orderedEigenframe A hAsymm).eigenvalue 2 -
      (orderedEigenframe B hBsymm).eigenvalue 2| ≤ epsilon :=
    (abs_constructedBottomEigenvalue_sub_le A B hAsymm hBsymm).trans hAB
  rcases constructedContractingLine_nearCollision_or_projectorClose
      A B hAsymm hBsymm epsilon threshold hthreshold hepsilon hAB with
    hnear₀ | hnear₁ | hfar
  · apply Or.inl
    have horder : (orderedEigenframe B hBsymm).eigenvalue 1 ≤
        (orderedEigenframe B hBsymm).eigenvalue 0 :=
      (orderedEigenframe B hBsymm).antitone_eigenvalue (by decide)
    have hfull : (orderedEigenframe B hBsymm).eigenvalue 0 -
        (orderedEigenframe B hBsymm).eigenvalue 2 <
          threshold + epsilon := by
      calc
        (orderedEigenframe B hBsymm).eigenvalue 0 -
            (orderedEigenframe B hBsymm).eigenvalue 2 =
          ((orderedEigenframe B hBsymm).eigenvalue 0 -
            (orderedEigenframe A hAsymm).eigenvalue 2) +
          ((orderedEigenframe A hAsymm).eigenvalue 2 -
            (orderedEigenframe B hBsymm).eigenvalue 2) := by ring
        _ ≤ |(orderedEigenframe A hAsymm).eigenvalue 2 -
              (orderedEigenframe B hBsymm).eigenvalue 0| +
            |(orderedEigenframe A hAsymm).eigenvalue 2 -
              (orderedEigenframe B hBsymm).eigenvalue 2| := by
          calc
            (orderedEigenframe B hBsymm).eigenvalue 0 -
                (orderedEigenframe A hAsymm).eigenvalue 2 +
              ((orderedEigenframe A hAsymm).eigenvalue 2 -
                (orderedEigenframe B hBsymm).eigenvalue 2) ≤
              |(orderedEigenframe B hBsymm).eigenvalue 0 -
                (orderedEigenframe A hAsymm).eigenvalue 2| +
              |(orderedEigenframe A hAsymm).eigenvalue 2 -
                (orderedEigenframe B hBsymm).eigenvalue 2| :=
              add_le_add (le_abs_self _) (le_abs_self _)
            _ = _ := by rw [abs_sub_comm]
        _ < threshold + epsilon := add_lt_add_of_lt_of_le hnear₀ hbottom
    linarith
  · apply Or.inl
    calc
      (orderedEigenframe B hBsymm).eigenvalue 1 -
          (orderedEigenframe B hBsymm).eigenvalue 2 =
        ((orderedEigenframe B hBsymm).eigenvalue 1 -
          (orderedEigenframe A hAsymm).eigenvalue 2) +
        ((orderedEigenframe A hAsymm).eigenvalue 2 -
          (orderedEigenframe B hBsymm).eigenvalue 2) := by ring
      _ ≤ |(orderedEigenframe A hAsymm).eigenvalue 2 -
            (orderedEigenframe B hBsymm).eigenvalue 1| +
          |(orderedEigenframe A hAsymm).eigenvalue 2 -
            (orderedEigenframe B hBsymm).eigenvalue 2| := by
        calc
          (orderedEigenframe B hBsymm).eigenvalue 1 -
              (orderedEigenframe A hAsymm).eigenvalue 2 +
            ((orderedEigenframe A hAsymm).eigenvalue 2 -
              (orderedEigenframe B hBsymm).eigenvalue 2) ≤
            |(orderedEigenframe B hBsymm).eigenvalue 1 -
              (orderedEigenframe A hAsymm).eigenvalue 2| +
            |(orderedEigenframe A hAsymm).eigenvalue 2 -
              (orderedEigenframe B hBsymm).eigenvalue 2| :=
            add_le_add (le_abs_self _) (le_abs_self _)
          _ = _ := by rw [abs_sub_comm]
      _ < threshold + epsilon := add_lt_add_of_lt_of_le hnear₁ hbottom
  · exact Or.inr hfar

namespace SymmetricStrain

/-- Quantitative local Lipschitz estimate for the contracting-line
projector, based on the frozen bottom gap. -/
theorem norm_bottomEigenlineProjector_sub_le_of_norm_sub_lt_half_bottomGap
    (A B : SymmetricStrain) (hgap : 0 < bottomGap B)
    (hAB : ‖A.1 - B.1‖ < bottomGap B / 2) :
    ‖bottomEigenlineProjector A - bottomEigenlineProjector B‖ ≤
      (8 / bottomGap B) * ‖A.1 - B.1‖ := by
  have hthreshold : 0 < bottomGap B / 2 := by positivity
  rcases constructedContractingLine_smallFrozenGap_or_projectorClose
      A.1 B.1 A.2 B.2 ‖A.1 - B.1‖ (bottomGap B / 2)
      hthreshold (norm_nonneg _) le_rfl with hsmall | hprojector
  · exfalso
    simp only [bottomGap, secondEigenvalue, thirdEigenvalue] at hsmall hAB
    linarith
  · change ‖bottomEigenlineProjector A - bottomEigenlineProjector B‖ ≤
      (8 / bottomGap B) * ‖A.1 - B.1‖
    refine hprojector.trans_eq ?_
    field_simp [ne_of_gt hgap]
    ring

/-- The complementary expanding two-plane has the same local Lipschitz
bound as the contracting line. -/
theorem norm_expandingPlaneProjector_sub_le_of_norm_sub_lt_half_bottomGap
    (A B : SymmetricStrain) (hgap : 0 < bottomGap B)
    (hAB : ‖A.1 - B.1‖ < bottomGap B / 2) :
    ‖expandingPlaneProjector A - expandingPlaneProjector B‖ ≤
      (8 / bottomGap B) * ‖A.1 - B.1‖ := by
  have hbottom :=
    norm_bottomEigenlineProjector_sub_le_of_norm_sub_lt_half_bottomGap
      A B hgap hAB
  calc
    ‖expandingPlaneProjector A - expandingPlaneProjector B‖ =
        ‖bottomEigenlineProjector A - bottomEigenlineProjector B‖ := by
      unfold expandingPlaneProjector
      rw [sub_sub_sub_cancel_left, norm_sub_rev]
    _ ≤ (8 / bottomGap B) * ‖A.1 - B.1‖ := hbottom

/-- The expanding-plane projector is continuous at every strain whose bottom
eigenvalue is separated from the other two. -/
theorem continuousAt_expandingPlaneProjector_of_bottomGap_pos
    (B : SymmetricStrain) (hgap : 0 < bottomGap B) :
    ContinuousAt expandingPlaneProjector B := by
  rw [Metric.continuousAt_iff]
  intro epsilon hepsilon
  let delta := min (bottomGap B / 2) (epsilon * bottomGap B / 8)
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (by positivity) (by positivity)
  refine ⟨delta, hdelta, ?_⟩
  intro A hdist
  have hnorm : ‖A.1 - B.1‖ < delta := by
    simpa [Subtype.dist_eq, dist_eq_norm] using hdist
  have hhalf : ‖A.1 - B.1‖ < bottomGap B / 2 :=
    hnorm.trans_le (min_le_left _ _)
  have hepsilonBound : ‖A.1 - B.1‖ < epsilon * bottomGap B / 8 :=
    hnorm.trans_le (min_le_right _ _)
  have hprojector :=
    norm_expandingPlaneProjector_sub_le_of_norm_sub_lt_half_bottomGap
      A B hgap hhalf
  have hscale : 0 < 8 / bottomGap B := by positivity
  calc
    dist (expandingPlaneProjector A) (expandingPlaneProjector B) =
        ‖expandingPlaneProjector A - expandingPlaneProjector B‖ :=
      dist_eq_norm _ _
    _ ≤ (8 / bottomGap B) * ‖A.1 - B.1‖ := hprojector
    _ < (8 / bottomGap B) * (epsilon * bottomGap B / 8) :=
      mul_lt_mul_of_pos_left hepsilonBound hscale
    _ = epsilon := by
      field_simp [ne_of_gt hgap]

/-- A continuous strain field with positive bottom gap has a continuous
expanding-plane projector. -/
theorem continuous_expandingPlaneProjector_comp_of_bottomGap_pos
    {X : Type*} [TopologicalSpace X] (S : X → SymmetricStrain)
    (hS : Continuous S) (hgap : ∀ x, 0 < bottomGap (S x)) :
    Continuous (fun x ↦ expandingPlaneProjector (S x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (continuousAt_expandingPlaneProjector_of_bottomGap_pos
    (S x) (hgap x)).comp hS.continuousAt

/-- On a bottom-gap-separated region, the expanding-plane projector is
measurable without choosing a basis inside that plane. -/
theorem measurable_expandingPlaneProjector_restrict_of_bottomGap_pos
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] (S : X → SymmetricStrain)
    (hS : Continuous S) (region : Set X)
    (hgap : ∀ x ∈ region, 0 < bottomGap (S x)) :
    Measurable (fun x : region ↦ expandingPlaneProjector (S x.1)) := by
  have hSrestrict : Continuous (fun x : region ↦ S x.1) :=
    hS.comp continuous_subtype_val
  exact (continuous_expandingPlaneProjector_comp_of_bottomGap_pos
    (fun x : region ↦ S x.1) hSrestrict (fun x ↦ hgap x.1 x.2)).measurable

end SymmetricStrain

/-! ## Exact defect decomposition and trace-free triple collision -/

/-- Complex squared coordinate energy along a real unit direction. -/
def complexLineCoordinateEnergy (e : R3) (u : ComplexVec3) : ℝ :=
  (inner ℝ (complexRealPartEuclidean u) e) ^ 2 +
    (inner ℝ (complexImagPartEuclidean u) e) ^ 2

theorem complexLineCoordinateEnergy_nonneg (e : R3) (u : ComplexVec3) :
    0 ≤ complexLineCoordinateEnergy e u := by
  unfold complexLineCoordinateEnergy
  positivity

/-- Exact two-gap spectral decomposition of the complex top Rayleigh defect.
The top-gap collision only removes coercivity inside the expanding plane; the
bottom-direction component retains the full spectral-width coefficient. -/
theorem complexStrainDefect_eq_topGap_mul_middle_add_width_mul_bottom
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v)
    (u : ComplexVec3) :
    complexStrainDefect S hSsymm u =
      ((orderedEigenframe S hSsymm).eigenvalue 0 -
        (orderedEigenframe S hSsymm).eigenvalue 1) *
          complexLineCoordinateEnergy
            ((orderedEigenframe S hSsymm).eigenbasis 1) u +
      ((orderedEigenframe S hSsymm).eigenvalue 0 -
        (orderedEigenframe S hSsymm).eigenvalue 2) *
          complexLineCoordinateEnergy
            ((orderedEigenframe S hSsymm).eigenbasis 2) u := by
  let F := orderedEigenframe S hSsymm
  let ur := complexRealPartEuclidean u
  let ui := complexImagPartEuclidean u
  have hparseR := parseval_three_norm_sq F.eigenbasis ur
  have hparseI := parseval_three_norm_sq F.eigenbasis ui
  have hrayR := rayleigh_three S hSsymm F.eigenvalue F.eigenbasis
    F.apply_eigenbasis ur
  have hrayI := rayleigh_three S hSsymm F.eigenvalue F.eigenbasis
    F.apply_eigenbasis ui
  change F.eigenvalue 0 * complexEuclideanNormSq u -
      (inner ℝ ur (S ur) + inner ℝ ui (S ui)) = _
  rw [complexEuclideanNormSq_eq_parts]
  unfold complexLineCoordinateEnergy
  change F.eigenvalue 0 * (‖ur‖ ^ 2 + ‖ui‖ ^ 2) -
      (inner ℝ ur (S ur) + inner ℝ ui (S ui)) = _
  rw [← hparseR, ← hparseI, hrayR, hrayI]
  ring

/-- If both adjacent gaps of an ordered trace-free spectrum are smaller than
`threshold`, then every eigenvalue has magnitude below `2 * threshold`. -/
theorem traceFree_bothGapsSmall_eigenvalues_abs_lt
    (S : SymmetricStrain) (threshold : ℝ) (hthreshold : 0 < threshold)
    (htrace : topEigenvalue S + secondEigenvalue S + thirdEigenvalue S = 0)
    (htop : topGap S < threshold) (hbottom : bottomGap S < threshold) :
    |topEigenvalue S| < 2 * threshold ∧
      |secondEigenvalue S| < 2 * threshold ∧
      |thirdEigenvalue S| < 2 * threshold := by
  have h01 : secondEigenvalue S ≤ topEigenvalue S := by
    exact (orderedEigenframe S.1 S.2).antitone_eigenvalue (by decide)
  have h12 : thirdEigenvalue S ≤ secondEigenvalue S := by
    exact (orderedEigenframe S.1 S.2).antitone_eigenvalue (by decide)
  have htopNonneg : 0 ≤ topEigenvalue S := by
    by_contra h
    have hneg : topEigenvalue S < 0 := lt_of_not_ge h
    linarith
  have hbottomNonpos : thirdEigenvalue S ≤ 0 := by
    by_contra h
    have hpos : 0 < thirdEigenvalue S := lt_of_not_ge h
    linarith
  simp only [topGap, bottomGap] at htop hbottom
  rw [abs_lt, abs_lt, abs_lt]
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  · constructor <;> linarith

/-- Homogeneous Rayleigh upper bound by the largest constructed eigenvalue. -/
theorem rayleigh_le_topEigenvalue_mul_norm_sq
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v)
    (u : R3) :
    inner ℝ u (S u) ≤
      (orderedEigenframe S hSsymm).eigenvalue 0 * ‖u‖ ^ 2 := by
  let F := orderedEigenframe S hSsymm
  have hparse := parseval_three_norm_sq F.eigenbasis u
  have hray := rayleigh_three S hSsymm F.eigenvalue F.eigenbasis
    F.apply_eigenbasis u
  have h01 : F.eigenvalue 1 ≤ F.eigenvalue 0 :=
    F.antitone_eigenvalue (by decide)
  have h02 : F.eigenvalue 2 ≤ F.eigenvalue 0 :=
    F.antitone_eigenvalue (by decide)
  calc
    inner ℝ u (S u) =
        F.eigenvalue 0 * (inner ℝ u (F.eigenbasis 0)) ^ 2 +
          F.eigenvalue 1 * (inner ℝ u (F.eigenbasis 1)) ^ 2 +
          F.eigenvalue 2 * (inner ℝ u (F.eigenbasis 2)) ^ 2 := hray
    _ ≤ F.eigenvalue 0 * (inner ℝ u (F.eigenbasis 0)) ^ 2 +
          F.eigenvalue 0 * (inner ℝ u (F.eigenbasis 1)) ^ 2 +
          F.eigenvalue 0 * (inner ℝ u (F.eigenbasis 2)) ^ 2 := by
      gcongr
    _ = F.eigenvalue 0 * ‖u‖ ^ 2 := by
      rw [← mul_add, ← mul_add, hparse]

/-- On the trace-free triple-collision branch, real stretching is bounded by
the small collision threshold times energy. -/
theorem traceFree_bothGapsSmall_rayleigh_le
    (S : SymmetricStrain) (threshold : ℝ) (hthreshold : 0 < threshold)
    (htrace : topEigenvalue S + secondEigenvalue S + thirdEigenvalue S = 0)
    (htop : topGap S < threshold) (hbottom : bottomGap S < threshold)
    (u : R3) :
    inner ℝ u (S.1 u) ≤ 2 * threshold * ‖u‖ ^ 2 := by
  have hspectrum := traceFree_bothGapsSmall_eigenvalues_abs_lt
    S threshold hthreshold htrace htop hbottom
  have htopSmall : topEigenvalue S < 2 * threshold :=
    (le_abs_self (topEigenvalue S)).trans_lt hspectrum.1
  exact (rayleigh_le_topEigenvalue_mul_norm_sq S.1 S.2 u).trans
    (mul_le_mul_of_nonneg_right htopSmall.le (sq_nonneg ‖u‖))

/-- Complex version of the harmless triple-collision stretching bound. -/
theorem traceFree_bothGapsSmall_complexRayleigh_le
    (S : SymmetricStrain) (threshold : ℝ) (hthreshold : 0 < threshold)
    (htrace : topEigenvalue S + secondEigenvalue S + thirdEigenvalue S = 0)
    (htop : topGap S < threshold) (hbottom : bottomGap S < threshold)
    (u : ComplexVec3) :
    inner ℝ (complexRealPartEuclidean u) (S.1 (complexRealPartEuclidean u)) +
        inner ℝ (complexImagPartEuclidean u)
          (S.1 (complexImagPartEuclidean u)) ≤
      2 * threshold * complexEuclideanNormSq u := by
  have hre := traceFree_bothGapsSmall_rayleigh_le
    S threshold hthreshold htrace htop hbottom
      (complexRealPartEuclidean u)
  have him := traceFree_bothGapsSmall_rayleigh_le
    S threshold hthreshold htrace htop hbottom
      (complexImagPartEuclidean u)
  rw [complexEuclideanNormSq_eq_parts]
  linarith

/-- **Trace-free collision trichotomy.**  On the small top-gap branch, either
the bottom gap is still separated (so the expanding plane is the stable
object), or the whole ordered spectrum is small. -/
theorem traceFree_smallTopGap_bottomSeparated_or_spectrumSmall
    (S : SymmetricStrain) (threshold : ℝ) (hthreshold : 0 < threshold)
    (htrace : topEigenvalue S + secondEigenvalue S + thirdEigenvalue S = 0)
    (htop : topGap S < threshold) :
    threshold ≤ bottomGap S ∨
      (|topEigenvalue S| < 2 * threshold ∧
        |secondEigenvalue S| < 2 * threshold ∧
        |thirdEigenvalue S| < 2 * threshold) := by
  by_cases hbottom : threshold ≤ bottomGap S
  · exact Or.inl hbottom
  · exact Or.inr (traceFree_bothGapsSmall_eigenvalues_abs_lt
      S threshold hthreshold htrace htop (lt_of_not_ge hbottom))

/-- Route-facing form of the collision trichotomy: a small top gap leaves
either a separated, stable expanding plane or a uniform small-rate bound on
all complex stretching vectors. -/
theorem traceFree_smallTopGap_bottomSeparated_or_complexRayleigh_le
    (S : SymmetricStrain) (threshold : ℝ) (hthreshold : 0 < threshold)
    (htrace : topEigenvalue S + secondEigenvalue S + thirdEigenvalue S = 0)
    (htop : topGap S < threshold) :
    threshold ≤ bottomGap S ∨
      ∀ u : ComplexVec3,
        inner ℝ (complexRealPartEuclidean u)
            (S.1 (complexRealPartEuclidean u)) +
          inner ℝ (complexImagPartEuclidean u)
            (S.1 (complexImagPartEuclidean u)) ≤
          2 * threshold * complexEuclideanNormSq u := by
  by_cases hbottom : threshold ≤ bottomGap S
  · exact Or.inl hbottom
  · apply Or.inr
    intro u
    exact traceFree_bothGapsSmall_complexRayleigh_le
      S threshold hthreshold htrace htop (lt_of_not_ge hbottom) u

end PancakeSpectralClusterDichotomy
end NavierStokes
end FluidDynamics
end Mettapedia
