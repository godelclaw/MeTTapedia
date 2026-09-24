import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.BottomProjectedEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalFrozenVorticity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalProjectorMotion

/-!
# Actual bottom-projected vorticity energy and signed viscous forcing

The frozen energy derivative uses the actual full vorticity and the
actual material projector. Incompressibility supplies the bottom-gap
damping. Only frame transfer is absorbed; viscosity remains in its signed
pairing. The differential estimate is restricted to positive bottom gap.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalBottomEnergy

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakeFilteredStrainDynamics PancakeLocalInfiniteVelocity
open PancakeFourierMaterialPaths PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakeSpectralClusterDichotomy.SymmetricStrain
open LocalClusterAnisotropy LocalFrozenVorticity LocalProjectorMotion LocalTopPlaneRate
open LocalLowDiffusionBudget LocalJointDiffusionBudget LocalAlignmentForcing
open BottomProjectorMotion FilteredStrainTrace
open LocalMeanAlignmentBalance PancakeMeasurableMaterialRate

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def energy (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity) (x : T3) : ℝ :=
  BottomProjectedEnergy.energy (spatialStrain modes (filteredVelocity chi u) x) (fullVorticity u x)

def frozenEnergy (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (t : ℝ) (x : T3) (h : ℝ) : ℝ :=
  BottomProjectedEnergy.energy (frozenStrain chi modes u t x h) (frozenVorticity u t x h)

def materialRate (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu t : ℝ) (x : T3) : ℝ :=
  BottomProjectedEnergy.rate (spatialStrain modes (filteredVelocity chi (u t)) x) (fullVorticity (u t) x)
    (strainMismatch chi modes (u t) x + nu • fullVorticityLaplacian (u t) x) (-planeRate chi modes u t x)

def source (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (nu : ℝ) (x : T3) : ℝ :=
  let S := spatialStrain modes (filteredVelocity chi u) x
  let w := fullVorticity u x
  let K := bottomCoupling S (jointRemainder chi modes outputs u nu x)
  2 * ⟪bottomEigenlineProjector S w, strainMismatch chi modes u x + nu • fullVorticityLaplacian u x⟫ +
    4 * ‖K‖ ^ 2 / bottomGap S ^ 3 * ‖expandingPlaneProjector S w‖ ^ 2

theorem frozenEnergy_eq_materialShift (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (t : ℝ) (x : T3) (h : ℝ) :
    frozenEnergy chi modes u t x h =
      energy chi modes (u (t + h)) (x + materialShift (velocity (u t) x) h) := rfl

theorem source_viscous_split (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) (nu : ℝ) (x : T3) :
    let S := spatialStrain modes (filteredVelocity chi u) x
    let w := fullVorticity u x
    let K := bottomCoupling S (jointRemainder chi modes outputs u nu x)
    source chi modes outputs u nu x =
      2 * ⟪bottomEigenlineProjector S w, strainMismatch chi modes u x⟫ +
        2 * nu * ⟪bottomEigenlineProjector S w, fullVorticityLaplacian u x⟫ +
        4 * ‖K‖ ^ 2 / bottomGap S ^ 3 * ‖expandingPlaneProjector S w‖ ^ 2 := by
  simp only [source, inner_add_right, real_inner_smul_right]
  ring

theorem frozenEnergy_zero (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (t : ℝ) (x : T3) :
    frozenEnergy chi modes u t x 0 = energy chi modes (u t) x := by
  simp only [frozenEnergy, frozenStrain_zero, frozenVorticity_zero, energy]

variable {nu T B : ℝ} {u₀ : FourierVelocity}

theorem hasDerivAt_frozenEnergy (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (t : ℝ) (ht : t ∈ Set.Ioo a b) (x : T3)
    (hP : DifferentiableAt ℝ
      (fun h ↦ bottomEigenlineProjector (frozenStrain chi modes s.coefficients t x h)) 0) :
    HasDerivAt (fun h ↦ frozenEnergy chi modes s.coefficients t x h)
      (materialRate chi modes s.coefficients nu t x) 0 := by
  let f := strainMismatch chi modes (s.coefficients t) x + nu • fullVorticityLaplacian (s.coefficients t) x
  have hw := hasDerivAt_frozenVorticity s g hg hSum hu a b hab hI t ht x
  have hw' : HasDerivAt (fun h ↦ frozenVorticity s.coefficients t x h)
      ((frozenStrain chi modes s.coefficients t x 0).1 (frozenVorticity s.coefficients t x 0) + f) 0 := by
    apply hw.congr_deriv
    simp only [frozenStrain_zero, frozenVorticity_zero, f, strainMismatch, sub_apply]
    module
  have hd := deriv_expandingPlaneProjector_eq_neg (frozenStrain chi modes s.coefficients t x) 0 hP
  have hD : deriv (fun h ↦ bottomEigenlineProjector (frozenStrain chi modes s.coefficients t x h)) 0 =
      -planeRate chi modes s.coefficients t x := by
    unfold planeRate
    rw [hd, neg_neg]
  have hP' := hP.hasDerivAt
  rw [hD] at hP'
  have h := BottomProjectedEnergy.hasDerivAt_energy_of_strainEquation
    (frozenStrain chi modes s.coefficients t x) (fun h ↦ frozenVorticity s.coefficients t x h)
    _ f 0 hP' hw'
  simpa only [frozenStrain_zero, frozenVorticity_zero, frozenEnergy, materialRate, f] using h

variable (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
  (modes outputs : Finset Wavevector) (hcut : ∀ q, q ∉ modes → chi q = 0)
  (hchir : ∀ q, chi (-q) = conj (chi q))
  (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs)
  (hs : ∀ k, -k ∈ modes ↔ k ∈ modes) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
  (hB : 0 ≤ B) (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)

include hchi hcut hchir hsub hout hs hk hB hab hI

theorem ae_ae_hasDerivAt_frozenEnergy
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b), ∀ᵐ x : T3,
      0 < bottomGap (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x) →
      HasDerivAt (fun h ↦ frozenEnergy chi modes s.coefficients t x h)
        (materialRate chi modes s.coefficients nu t x) 0 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_ae_differentiableAt_frozenProjectors s chi C hchi modes outputs hcut hchir hsub hout hs hk
      hB a b hab hI] with t ht hx
  exact hx.mono (fun x h hg' ↦ hasDerivAt_frozenEnergy s g hg hSum hu chi modes a b hab hI t ht x (h hg').1)

theorem ae_ae_materialRate_add_damping_le :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b), ∀ᵐ x : T3,
      0 < bottomGap (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x) →
      materialRate chi modes s.coefficients nu t x +
        (bottomGap (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x) / 3) *
          energy chi modes (s.coefficients t) x ≤ source chi modes outputs (s.coefficients t) nu x := by
  filter_upwards [ae_ae_planeRate_gap_absorption s chi C hchi modes outputs hcut hchir hsub hout hs hk
    hB a b hab hI] with t ht
  exact ht.mono (fun x hx hg ↦ by
    have hquad := hx hg (fullVorticity (s.coefficients t) x)
    have htrace := trace_filteredStrain_eq_zero chi modes (s.coefficients t) (s.transverse t) x
    apply BottomProjectedEnergy.rate_add_gap_damping_le _ _ _ _ _ htrace
    simpa only [neg_apply, inner_neg_right, abs_neg, BottomProjectedEnergy.energy] using hquad)

theorem ae_ae_deriv_frozenEnergy_add_damping_le
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b), ∀ᵐ x : T3,
      0 < bottomGap (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x) →
      deriv (fun h ↦ frozenEnergy chi modes s.coefficients t x h) 0 +
        (bottomGap (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x) / 3) *
          energy chi modes (s.coefficients t) x ≤ source chi modes outputs (s.coefficients t) nu x := by
  filter_upwards [ae_ae_hasDerivAt_frozenEnergy s chi C hchi modes outputs hcut hchir hsub hout hs hk
    hB a b hab hI g hg hSum hu,
    ae_ae_materialRate_add_damping_le s chi C hchi modes outputs hcut hchir hsub hout hs hk hB a b hab hI]
    with t hderiv hbound
  filter_upwards [hderiv, hbound] with x hx hy hg'
  rw [(hx hg').deriv]
  exact hy hg'

end Mettapedia.FluidDynamics.NavierStokes.LocalBottomEnergy
