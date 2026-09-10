import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalMaterialStrain

/-!
# Spectral-defect balance for the actual local solution

The collision-compatible spectral identity is applied to the strain and
vorticity of the constructed infinite Fourier solution on a material path.
The differential equations and regularity are proved, not additional
hypotheses. Pressure, spin and viscosity remain in the remainder.

This is a local exact balance, not a uniform misalignment-strain budget.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSpectralDefect

open scoped RealInnerProductSpace
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeLocalInfiniteVelocity
open PancakeLocalMaterialTrajectories PancakeCurlOutputTail LocalMaterialVorticity
open LocalVorticityDiffusion LocalMaterialStrain PancakeSpectralDefectEvolution
open PancakeSpectralDefectBudget PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain

local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

variable {nu T B : ℝ} {u₀ : FourierVelocity}

/-- Gap-weighted misalignment of actual vorticity and actual strain. -/
def defectAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (X : ℝ → X3) (t : ℝ) : ℝ :=
  topSpectralDefect (symmetricStrainAlong s X t) (vorticityAlong s X t)

/-- The gap-weighted vector whose squared norm is the damping term. -/
def residualAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (X : ℝ → X3) (t : ℝ) : R3 :=
  spectralResidual (strainAlong s X t) (topEigenvalue (symmetricStrainAlong s X t))
    (vorticityAlong s X t)

/-- Signed anisotropy of the full physical remainder. -/
def anisotropyAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (X : ℝ → X3) (t : ℝ) : ℝ :=
  topRemainderAnisotropy (symmetricStrainAlong s X t) (strainRemainderAlong s X t)
    (vorticityAlong s X t)

variable (s : LocalInfiniteVelocitySolution nu u₀ T B) (hB : 0 ≤ B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
  (X : ℝ → X3)
  (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)

include hB hg hSum hu hX

/-- Exact, collision-safe balance on any compact subinterval of local
existence. Integrability of the selected-frame anisotropy is a conclusion. -/
theorem integrated_defectAlong_identity {a b : ℝ}
    (hI : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) T) :
    IntervalIntegrable (anisotropyAlong s X) volume a b ∧
      defectAlong s X b + (∫ t in a..b, ‖residualAlong s X t‖ ^ 2) =
        defectAlong s X a + (∫ t in a..b, anisotropyAlong s X t) +
          ∫ t in a..b, 2 * ⟪residualAlong s X t, diffusionAlong s X t⟫ := by
  have hS := (contDiffOn_strainAlong s g hg hSum hu hB X hX).mono hI
  have hw := (contDiffOn_vorticityAlong s g hg hSum hu X hX).mono hI
  have hf := continuousOn_diffusionAlong s g hSum hu X hX hI
  exact integrated_topSpectralDefect_identity (symmetricStrainAlong s X)
    (vorticityAlong s X) (strainRemainderAlong s X) (diffusionAlong s X) a b hS hw hf
    (fun t ht ↦ hasDerivAt_strainAlong s g hg hSum hu X hX t (hI ht))
    (fun t ht ↦ hasDerivAt_vorticityAlong s g hg hSum hu X hX t (hI ht))

/-- Spending a positive share of residual damping bounds the viscous
cross term, but leaves the pressure/spin/strain-diffusion anisotropy signed
and explicit. No estimate depending only on initial energy is inferred. -/
theorem integrated_defectAlong_budget {a b : ℝ}
    (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (theta : ℝ) (htheta : 0 < theta) :
    defectAlong s X b + (1 - theta) * (∫ t in a..b, ‖residualAlong s X t‖ ^ 2) ≤
      defectAlong s X a + (∫ t in a..b, anisotropyAlong s X t) +
        (∫ t in a..b, ‖diffusionAlong s X t‖ ^ 2) / theta := by
  have hI' : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) T := by rwa [Set.uIcc_of_le hab]
  have hS := (contDiffOn_strainAlong s g hg hSum hu hB X hX).mono hI'
  have hw := (contDiffOn_vorticityAlong s g hg hSum hu X hX).mono hI'
  have hf : ContinuousOn (diffusionAlong s X) (Set.uIcc a b) :=
    continuousOn_diffusionAlong s g hSum hu X hX hI'
  exact integrated_topSpectralDefect_budget (symmetricStrainAlong s X)
    (vorticityAlong s X) (strainRemainderAlong s X) (diffusionAlong s X) a b theta hab htheta
    hS hw hf (fun t ht ↦ hasDerivAt_strainAlong s g hg hSum hu X hX t (hI' ht))
    (fun t ht ↦ hasDerivAt_vorticityAlong s g hg hSum hu X hX t (hI' ht))

end Mettapedia.FluidDynamics.NavierStokes.LocalSpectralDefect
