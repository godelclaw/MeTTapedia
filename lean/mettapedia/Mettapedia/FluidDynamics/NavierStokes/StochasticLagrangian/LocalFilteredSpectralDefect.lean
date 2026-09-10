import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalFilteredStrain
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpectralResidual
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalDefectODEBudget

/-!
# Filtered strain against the full actual vorticity

Both fields are evaluated along the same trajectory of the full infinite
solution. The discarded strain acts on the full vorticity as an explicit
mismatch term; the filtered strain equation retains pressure-corrected
subgrid feedback and unresolved transport. Their gap-weighted spectral
defect has a signed balance across eigenvalue collisions.

The common local moment envelope justifies regularity, not a uniform
high-frequency or terminal-time estimate for the displayed sources.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalFilteredSpectralDefect

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeLocalInfiniteVelocity
open PancakeLocalMaterialTrajectories PancakeLocalSpatialVelocity PancakeFourierMaterialPaths
open PancakeCurlOutputTail PancakeFrequencyProjectorCommutator PancakeFilteredStrainDynamics
open PancakeInfiniteFourierTime PancakeCoefficientLimitEquation PancakePhysicalDefectODEBudget
open PancakePhysicalSpectralDefect PancakeSpectralDefectEvolution PancakeSpectralDefectBudget
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open LocalMaterialVorticity LocalMaterialStrain

local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

variable {nu T B : ℝ} {u₀ : FourierVelocity}

/-- Each actual Fourier coefficient is continuously differentiable on a
compact interior interval. No derivative at the lifespan endpoints is used. -/
theorem contDiffOn_coefficients (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (hB : 0 ≤ B) {a b : ℝ} (hI : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) T)
    (q : Wavevector) (i : Fin 3) :
    ContDiffOn ℝ 1 (fun t ↦ s.coefficients t q i) (Set.uIcc a b) := by
  have hc : ContinuousOn (fun t ↦ infiniteVelocityRHS nu (s.coefficients t) q i)
      (Set.Icc (0 : ℝ) T) :=
    continuousOn_iff_continuous_restrict.mpr (continuous_velocityRHS_component s hB q i)
  exact contDiffOn_one_of_hasDerivAt_interval _ _ a b
    (hc.mono (hI.trans Set.Ioo_subset_Icc_self)) (fun t ht ↦ s.equation t (hI ht) q i)

/-- Joint continuity of the actual velocity makes its material trajectory
`C¹`; path regularity is not a separate geometric hypothesis. -/
theorem contDiffOn_materialPath (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (X : ℝ → X3)
    (hX : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s t (X t)) t)
    {a b : ℝ} (hI : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) T) :
    ContDiffOn ℝ 1 X (Set.uIcc a b) := by
  have hc := continuousOn_material_eval s (fun t x ↦ spatialField s t x)
    (spatialField_joint_continuous s) X hX hI
  have hd : ContinuousOn (fun t ↦ liftedVelocity s t (X t)) (Set.uIcc a b) := by
    apply continuousOn_pi.mpr
    intro i
    exact Complex.continuous_re.comp_continuousOn
      ((continuous_apply i).comp_continuousOn hc)
  exact contDiffOn_one_of_hasDerivAt_interval _ _ a b hd (fun t ht ↦ hX t (hI ht))

theorem contDiffOn_filteredStrainAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (hB : 0 ≤ B) (chi : Wavevector → ℂ) (modes : Finset Wavevector) (X : ℝ → X3)
    (hX : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s t (X t)) t)
    {a b : ℝ} (hI : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) T) :
    ContDiffOn ℝ 1 (fun t ↦ (LocalFilteredStrain.strainAlong s chi modes X t).1)
      (Set.uIcc a b) :=
  contDiffOn_physicalStrainPath chi modes s.coefficients X _
    (fun q _ i ↦ contDiffOn_coefficients s hB hI q i)
    (fun i ↦ contDiffOn_pi.mp (contDiffOn_materialPath s X hX hI) i)

/-- Discarded strain continues to stretch the actual vorticity. It is
neither a viscosity term nor an externally prescribed forcing. -/
def strainMismatchAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (X : ℝ → X3) (t : ℝ) : R3 :=
  (LocalMaterialVorticity.strainAlong s X t -
    (LocalFilteredStrain.strainAlong s chi modes X t).1) (vorticityAlong s X t)

def forcingAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (X : ℝ → X3) (t : ℝ) : R3 :=
  strainMismatchAlong s chi modes X t + diffusionAlong s X t

def defectAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (X : ℝ → X3) (t : ℝ) : ℝ :=
  topSpectralDefect (LocalFilteredStrain.strainAlong s chi modes X t) (vorticityAlong s X t)

def residualAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (X : ℝ → X3) (t : ℝ) : R3 :=
  let S := LocalFilteredStrain.strainAlong s chi modes X t
  spectralResidual S.1 (topEigenvalue S) (vorticityAlong s X t)

def anisotropyAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector) (X : ℝ → X3) (t : ℝ) : ℝ :=
  topRemainderAnisotropy (LocalFilteredStrain.strainAlong s chi modes X t)
    (LocalFilteredStrain.remainderAlong s chi modes outputs X t) (vorticityAlong s X t)

theorem hasDerivAt_fullVorticity_filteredStrain
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (vorticityAlong s X)
      ((LocalFilteredStrain.strainAlong s chi modes X t).1 (vorticityAlong s X t) +
        forcingAlong s chi modes X t) t := by
  apply (hasDerivAt_vorticityAlong s g hg hSum hu X hX t ht).congr_deriv
  simp only [forcingAlong, strainMismatchAlong, sub_apply]
  abel

variable (s : LocalInfiniteVelocitySolution nu u₀ T B) (hB : 0 ≤ B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
  (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
  (modes outputs : Finset Wavevector) (hcut : ∀ q, q ∉ modes → chi q = 0)
  (hchir : ∀ q, chi (-q) = conj (chi q))
  (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs)
  (hs : ∀ k, -k ∈ modes ↔ k ∈ modes) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
  (X : ℝ → X3)
  (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)

include hB hg hSum hu hX

theorem continuousOn_forcingAlong {a b : ℝ} (hI : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) T) :
    ContinuousOn (forcingAlong s chi modes X) (Set.uIcc a b) :=
  continuousOn_forcing_of_evolution
    (fun t ↦ (LocalFilteredStrain.strainAlong s chi modes X t).1)
    (vorticityAlong s X) (forcingAlong s chi modes X) a b
    (contDiffOn_filteredStrainAlong s hB chi modes X hX hI).continuousOn
    ((contDiffOn_vorticityAlong s g hg hSum hu X hX).mono hI)
    (fun t ht ↦ hasDerivAt_fullVorticity_filteredStrain s g hg hSum hu chi modes X hX t (hI ht))

include hchi hcut hchir hsub hout hs hk

/-- A spectral-defect identity for filtered strain and full vorticity.
The remainder contains the actual filtered stress and material-transport
correction. Eigenvalue collisions require no spectral gap assumption. -/
theorem integrated_defectAlong_identity {a b : ℝ}
    (hI : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) T) :
    IntervalIntegrable (anisotropyAlong s chi modes outputs X) volume a b ∧
      defectAlong s chi modes X b + (∫ t in a..b, ‖residualAlong s chi modes X t‖ ^ 2) =
        defectAlong s chi modes X a + (∫ t in a..b, anisotropyAlong s chi modes outputs X t) +
          ∫ t in a..b, 2 * ⟪residualAlong s chi modes X t, forcingAlong s chi modes X t⟫ :=
  integrated_topSpectralDefect_identity (LocalFilteredStrain.strainAlong s chi modes X)
    (vorticityAlong s X) (LocalFilteredStrain.remainderAlong s chi modes outputs X)
    (forcingAlong s chi modes X) a b
    (contDiffOn_filteredStrainAlong s hB chi modes X hX hI)
    ((contDiffOn_vorticityAlong s g hg hSum hu X hX).mono hI)
    (continuousOn_forcingAlong s hB g hg hSum hu chi modes X hX hI)
    (fun t ht ↦ LocalFilteredStrain.hasDerivAt_strainAlong s chi C hchi modes outputs
      hcut hchir hsub hout hs hk X t (hI ht) (hX t (hI ht)))
    (fun t ht ↦ hasDerivAt_fullVorticity_filteredStrain s g hg hSum hu chi modes X hX t (hI ht))

/-- The corresponding almost-everywhere identity is available before
integrating, with no chosen-eigenvector differentiability hypothesis. -/
theorem ae_hasDerivAt_defectAlong {a b : ℝ}
    (hI : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) T) :
    ∀ᵐ t, t ∈ Set.uIcc a b → HasDerivAt (defectAlong s chi modes X)
      (-‖residualAlong s chi modes X t‖ ^ 2 + anisotropyAlong s chi modes outputs X t +
        2 * ⟪residualAlong s chi modes X t, forcingAlong s chi modes X t⟫) t :=
  ae_hasDerivAt_topSpectralDefect (LocalFilteredStrain.strainAlong s chi modes X)
    (vorticityAlong s X) (LocalFilteredStrain.remainderAlong s chi modes outputs X)
    (forcingAlong s chi modes X) a b
    (contDiffOn_filteredStrainAlong s hB chi modes X hX hI)
    (fun t ht ↦ LocalFilteredStrain.hasDerivAt_strainAlong s chi C hchi modes outputs
      hcut hchir hsub hout hs hk X t (hI ht) (hX t (hI ht)))
    (fun t ht ↦ hasDerivAt_fullVorticity_filteredStrain s g hg hSum hu chi modes X hX t (hI ht))

end Mettapedia.FluidDynamics.NavierStokes.LocalFilteredSpectralDefect
