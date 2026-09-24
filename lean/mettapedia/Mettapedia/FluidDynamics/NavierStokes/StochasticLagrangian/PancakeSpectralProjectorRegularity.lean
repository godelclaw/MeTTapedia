import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeConcreteWeightedFreezing

/-!
# Regularity of the expanding-line spectral projector

An ordered eigenvector cannot be chosen continuously through eigenvalue
collisions, and its sign is intrinsically arbitrary.  The pancake estimates
only need the rank-one projector onto the expanding line.  This module puts
symmetric three-dimensional strains in their natural metric space and proves
that this sign-invariant projector is locally Lipschitz, hence continuous,
wherever the top eigenvalue is simple.

The estimate is quantitative: in a ball of radius half the frozen top gap,
the projector changes by at most `8 / gap` times the strain-operator change.
Thus a continuous strain field has a continuous (and therefore measurable)
expanding-line projector on every separated-gap branch.  Collisions remain an
explicit alternative rather than being hidden in a discontinuous eigenvector
choice.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeSpectralProjectorRegularity

open scoped RealInnerProductSpace
open MeasureTheory
open PeriodicFourierTriad
open PancakeAlignmentDynamics
open PancakeEigenframePerturbation
open PancakeSmoothCoherentSymbol
open PancakeStrainSpectralFrame
open PancakeTransverseEnergyFreezing

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- The metric space of symmetric continuous linear operators on physical
three-space. -/
abbrev SymmetricStrain :=
  {S : R3 →L[ℝ] R3 //
    ∀ u v : R3, inner ℝ u (S v) = inner ℝ (S u) v}

namespace SymmetricStrain

/-- Largest eigenvalue selected by the constructed ordered spectral frame. -/
def topEigenvalue (S : SymmetricStrain) : ℝ :=
  (orderedEigenframe S.1 S.2).eigenvalue 0

/-- Second eigenvalue selected by the constructed ordered spectral frame. -/
def secondEigenvalue (S : SymmetricStrain) : ℝ :=
  (orderedEigenframe S.1 S.2).eigenvalue 1

/-- Third eigenvalue selected by the constructed ordered spectral frame. -/
def thirdEigenvalue (S : SymmetricStrain) : ℝ :=
  (orderedEigenframe S.1 S.2).eigenvalue 2

/-- Spectral separation between the expanding eigenvalue and the rest. -/
def topGap (S : SymmetricStrain) : ℝ :=
  topEigenvalue S - secondEigenvalue S

/-- Sign-invariant projector onto the most expanding eigendirection. -/
def topEigenlineProjector (S : SymmetricStrain) : R3 →L[ℝ] R3 :=
  lineProjector ((orderedEigenframe S.1 S.2).eigenbasis 0)

/-- Quadratic energy transverse to a projector.  Unlike an eigenvector
formula, this expression is intrinsically sign invariant. -/
def transverseProjectorEnergy (P : R3 →L[ℝ] R3) (u : R3) : ℝ :=
  ‖u‖ ^ 2 - inner ℝ u (P u)

/-- Complex transverse energy obtained by applying the projector formula to
the coordinatewise real and imaginary parts. -/
def complexTransverseProjectorEnergy
    (P : R3 →L[ℝ] R3) (u : ComplexVec3) : ℝ :=
  transverseProjectorEnergy P (complexRealPartEuclidean u) +
    transverseProjectorEnergy P (complexImagPartEuclidean u)

theorem transverseProjectorEnergy_lineProjector (e u : R3) :
    transverseProjectorEnergy (lineProjector e) u =
      transverseLineEnergy e u := by
  unfold transverseProjectorEnergy transverseLineEnergy lineProjector
  simp only [InnerProductSpace.rankOne_apply, real_inner_smul_right]
  rw [real_inner_comm e u]
  ring

theorem complexTransverseProjectorEnergy_topEigenlineProjector
    (S : SymmetricStrain) (u : ComplexVec3) :
    complexTransverseProjectorEnergy (topEigenlineProjector S) u =
      complexTransverseLineEnergy
        ((orderedEigenframe S.1 S.2).eigenbasis 0) u := by
  unfold complexTransverseProjectorEnergy complexTransverseLineEnergy
  unfold topEigenlineProjector
  rw [transverseProjectorEnergy_lineProjector,
    transverseProjectorEnergy_lineProjector]

/-- Projector transverse energy is jointly continuous in the projector and
the complex vector. -/
theorem continuous_complexTransverseProjectorEnergy_comp
    {X : Type*} [TopologicalSpace X]
    (P : X → R3 →L[ℝ] R3) (u : X → ComplexVec3)
    (hP : Continuous P) (hu : Continuous u) :
    Continuous (fun x ↦ complexTransverseProjectorEnergy (P x) (u x)) := by
  have hre : Continuous (fun x ↦ complexRealPartEuclidean (u x)) := by
    unfold complexRealPartEuclidean
    fun_prop
  have him : Continuous (fun x ↦ complexImagPartEuclidean (u x)) := by
    unfold complexImagPartEuclidean
    fun_prop
  have hPre : Continuous
      (fun x ↦ P x (complexRealPartEuclidean (u x))) := by
    fun_prop
  have hPim : Continuous
      (fun x ↦ P x (complexImagPartEuclidean (u x))) := by
    fun_prop
  unfold complexTransverseProjectorEnergy transverseProjectorEnergy
  exact ((hre.norm.pow 2).sub (hre.inner hPre)).add
    ((him.norm.pow 2).sub (him.inner hPim))

theorem topGap_nonneg (S : SymmetricStrain) : 0 ≤ topGap S := by
  exact sub_nonneg.mpr
    ((orderedEigenframe S.1 S.2).antitone_eigenvalue (by decide))

theorem topGap_le_top_sub_third (S : SymmetricStrain) :
    topGap S ≤ topEigenvalue S - thirdEigenvalue S := by
  have h12 : (orderedEigenframe S.1 S.2).eigenvalue 2 ≤
      (orderedEigenframe S.1 S.2).eigenvalue 1 :=
    (orderedEigenframe S.1 S.2).antitone_eigenvalue (by decide)
  unfold topGap topEigenvalue secondEigenvalue thirdEigenvalue
  linarith

/-- Quantitative local Lipschitz estimate for the expanding-line projector.
The frozen strain `B` supplies the reference gap. -/
theorem norm_topEigenlineProjector_sub_le_of_norm_sub_lt_half_topGap
    (A B : SymmetricStrain) (hgap : 0 < topGap B)
    (hAB : ‖A.1 - B.1‖ < topGap B / 2) :
    ‖topEigenlineProjector A - topEigenlineProjector B‖ ≤
      (8 / topGap B) * ‖A.1 - B.1‖ := by
  have hthreshold : 0 < topGap B / 2 := by positivity
  have hepsilon : 0 ≤ ‖A.1 - B.1‖ := norm_nonneg _
  have hclose : ‖A.1 - B.1‖ ≤ ‖A.1 - B.1‖ := le_rfl
  rcases constructedExpandingLine_smallFrozenGap_or_projectorClose
      A.1 B.1 A.2 B.2 ‖A.1 - B.1‖ (topGap B / 2)
      hthreshold hepsilon hclose with hsmall₁ | hsmall₂ | hprojector
  · exfalso
    simp only [topGap, topEigenvalue, secondEigenvalue] at hsmall₁ hAB
    linarith
  · exfalso
    have h13 := topGap_le_top_sub_third B
    simp only [topGap, topEigenvalue, secondEigenvalue, thirdEigenvalue]
      at h13 hsmall₂ hAB
    linarith
  · change ‖topEigenlineProjector A - topEigenlineProjector B‖ ≤
      (8 / topGap B) * ‖A.1 - B.1‖
    refine hprojector.trans_eq ?_
    field_simp [ne_of_gt hgap]
    ring

/-- The expanding-line projector is continuous at every strain with a simple
top eigenvalue. -/
theorem continuousAt_topEigenlineProjector_of_topGap_pos
    (B : SymmetricStrain) (hgap : 0 < topGap B) :
    ContinuousAt topEigenlineProjector B := by
  rw [Metric.continuousAt_iff]
  intro epsilon hepsilon
  let delta := min (topGap B / 2) (epsilon * topGap B / 8)
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (by positivity) (by positivity)
  refine ⟨delta, hdelta, ?_⟩
  intro A hdist
  have hnorm : ‖A.1 - B.1‖ < delta := by
    simpa [Subtype.dist_eq, dist_eq_norm] using hdist
  have hhalf : ‖A.1 - B.1‖ < topGap B / 2 :=
    hnorm.trans_le (min_le_left _ _)
  have hepsilonBound : ‖A.1 - B.1‖ < epsilon * topGap B / 8 :=
    hnorm.trans_le (min_le_right _ _)
  have hprojector :=
    norm_topEigenlineProjector_sub_le_of_norm_sub_lt_half_topGap
      A B hgap hhalf
  have hscale : 0 < 8 / topGap B := by positivity
  calc
    dist (topEigenlineProjector A) (topEigenlineProjector B) =
        ‖topEigenlineProjector A - topEigenlineProjector B‖ :=
      dist_eq_norm _ _
    _ ≤ (8 / topGap B) * ‖A.1 - B.1‖ := hprojector
    _ < (8 / topGap B) * (epsilon * topGap B / 8) :=
      mul_lt_mul_of_pos_left hepsilonBound hscale
    _ = epsilon := by
      field_simp [ne_of_gt hgap]

/-- Along a continuous strain field, the expanding-line projector is
continuous at every point where the top gap is positive. -/
theorem continuousAt_topEigenlineProjector_comp_of_topGap_pos
    {X : Type*} [TopologicalSpace X] (S : X → SymmetricStrain) (x : X)
    (hS : ContinuousAt S x) (hgap : 0 < topGap (S x)) :
    ContinuousAt (fun y ↦ topEigenlineProjector (S y)) x :=
  (continuousAt_topEigenlineProjector_of_topGap_pos (S x) hgap).comp hS

/-- A continuous strain field whose top gap is everywhere positive has a
continuous sign-invariant expanding-line projector. -/
theorem continuous_topEigenlineProjector_comp_of_topGap_pos
    {X : Type*} [TopologicalSpace X] (S : X → SymmetricStrain)
    (hS : Continuous S) (hgap : ∀ x, 0 < topGap (S x)) :
    Continuous (fun x ↦ topEigenlineProjector (S x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact continuousAt_topEigenlineProjector_comp_of_topGap_pos
    S x (hS.continuousAt) (hgap x)

/-- Set-local form: continuity holds on any region on which the top gap stays
strictly positive, with no assertion made on the collision set. -/
theorem continuousOn_topEigenlineProjector_comp_of_topGap_pos
    {X : Type*} [TopologicalSpace X] (S : X → SymmetricStrain)
    (hS : Continuous S) (region : Set X)
    (hgap : ∀ x ∈ region, 0 < topGap (S x)) :
    ContinuousOn (fun x ↦ topEigenlineProjector (S x)) region := by
  intro x hx
  exact (continuousAt_topEigenlineProjector_comp_of_topGap_pos
    S x hS.continuousAt (hgap x hx)).continuousWithinAt

/-- The projector restricted to a separated-gap region is continuous as a
map on the subtype representing that region. -/
theorem continuous_topEigenlineProjector_restrict_of_topGap_pos
    {X : Type*} [TopologicalSpace X] (S : X → SymmetricStrain)
    (hS : Continuous S) (region : Set X)
    (hgap : ∀ x ∈ region, 0 < topGap (S x)) :
    Continuous (fun x : region ↦ topEigenlineProjector (S x.1)) := by
  apply continuous_topEigenlineProjector_comp_of_topGap_pos
    (fun x : region ↦ S x.1)
  · exact hS.comp continuous_subtype_val
  · intro x
    exact hgap x.1 x.2

/-- In particular the separated-gap expanding-line projector is measurable
for continuous strain fields on Borel spaces. -/
theorem measurable_topEigenlineProjector_comp_of_topGap_pos
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] (S : X → SymmetricStrain)
    (hS : Continuous S) (hgap : ∀ x, 0 < topGap (S x)) :
    Measurable (fun x ↦ topEigenlineProjector (S x)) :=
  (continuous_topEigenlineProjector_comp_of_topGap_pos S hS hgap).measurable

/-- Measurability on a separated region, expressed on the region subtype so
that collisions outside it need no artificial projector choice. -/
theorem measurable_topEigenlineProjector_restrict_of_topGap_pos
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] (S : X → SymmetricStrain)
    (hS : Continuous S) (region : Set X)
    (hgap : ∀ x ∈ region, 0 < topGap (S x)) :
    Measurable (fun x : region ↦ topEigenlineProjector (S x.1)) :=
  (continuous_topEigenlineProjector_restrict_of_topGap_pos
    S hS region hgap).measurable

/-- The physical complex transverse-energy density is continuous for a
continuous vector field on an everywhere separated strain branch.  The
conclusion is stated using the constructed eigenvector, but the proof factors
through the sign-invariant projector. -/
theorem continuous_complexTopTransverseEnergy_comp_of_topGap_pos
    {X : Type*} [TopologicalSpace X]
    (S : X → SymmetricStrain) (u : X → ComplexVec3)
    (hS : Continuous S) (hu : Continuous u)
    (hgap : ∀ x, 0 < topGap (S x)) :
    Continuous (fun x ↦
      complexTransverseLineEnergy
        ((orderedEigenframe (S x).1 (S x).2).eigenbasis 0) (u x)) := by
  have hprojector :=
    continuous_topEigenlineProjector_comp_of_topGap_pos S hS hgap
  have henergy := continuous_complexTransverseProjectorEnergy_comp
    (fun x ↦ topEigenlineProjector (S x)) u hprojector hu
  simpa only [complexTransverseProjectorEnergy_topEigenlineProjector] using henergy

/-- The separated moving-frame transverse-energy profile is integrable on
every finite time interval. -/
theorem intervalIntegrable_complexTopTransverseEnergy_of_topGap_pos
    (S : ℝ → SymmetricStrain) (u : ℝ → ComplexVec3)
    (hS : Continuous S) (hu : Continuous u)
    (hgap : ∀ t, 0 < topGap (S t)) (a b : ℝ) :
    IntervalIntegrable (fun t ↦
      complexTransverseLineEnergy
        ((orderedEigenframe (S t).1 (S t).2).eigenbasis 0) (u t))
      volume a b :=
  (continuous_complexTopTransverseEnergy_comp_of_topGap_pos
    S u hS hu hgap).intervalIntegrable a b

/-- On a separated-gap region, the actual transverse-energy density is
measurable without choosing a measurable eigenvector sign. -/
theorem measurable_complexTopTransverseEnergy_restrict_of_topGap_pos
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X]
    (S : X → SymmetricStrain) (u : X → ComplexVec3)
    (hS : Continuous S) (hu : Continuous u) (region : Set X)
    (hgap : ∀ x ∈ region, 0 < topGap (S x)) :
    Measurable (fun x : region ↦
      complexTransverseLineEnergy
        ((orderedEigenframe (S x.1).1 (S x.1).2).eigenbasis 0) (u x.1)) := by
  have hSrestrict : Continuous (fun x : region ↦ S x.1) :=
    hS.comp continuous_subtype_val
  have hurestrict : Continuous (fun x : region ↦ u x.1) :=
    hu.comp continuous_subtype_val
  exact (continuous_complexTopTransverseEnergy_comp_of_topGap_pos
    (fun x : region ↦ S x.1) (fun x : region ↦ u x.1)
    hSrestrict hurestrict (fun x ↦ hgap x.1 x.2)).measurable

end SymmetricStrain

end PancakeSpectralProjectorRegularity
end NavierStokes
end FluidDynamics
end Mettapedia
