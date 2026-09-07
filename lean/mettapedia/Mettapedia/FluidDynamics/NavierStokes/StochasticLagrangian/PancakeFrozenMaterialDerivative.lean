import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeMeasurableMaterialRate

/-!
# The constructed material derivative agrees with the finite NS equation

The comparison uses a straight path with the actual instantaneous fluid
velocity. Its tangent satisfies the material equation at the evaluation
time, which is all the chain rule requires. Differentiability of the actual
top-eigenvalue path remains explicit; no assigned spectral rate replaces it.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeFrozenMaterialDerivative

open scoped Topology ComplexConjugate RealInnerProductSpace Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicVorticityEquation PancakePeriodicCoherentSplit
open PancakeFourierMaterialPaths PancakePhysicalSpectralDefect PancakeDyadicDirectionEvolution
open PancakeFilteredStrainDynamics PancakeGalerkinKineticEnergy PancakeSpatialStrainEvolution
open PancakePhysicalViscousSplit PancakeMaterialDiffusionBudget PancakeMeasurableMaterialRate
open PancakeRegularizedMaterialRate PancakeRegularizedDiffusion PancakeSpectralFiniteDifference
open PancakeFrequencyProjectorCommutator PancakeSpectralProjectorRegularity.SymmetricStrain
open MeasureTheory PancakeFourierStrainGradient PancakeSpectralDefectEvolution

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem hasDerivAt_frozenMaterialEnergy
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector) (u : ℝ → FourierVelocity)
    (delta nu t : ℝ) (x : T3)
    (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs)
    (hchi : ∀ q, q ∉ modes → chi q = 0) (hchir : ∀ q, chi (-q) = conj (chi q))
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ q, u t (-q) = PancakeBlockReality.coefficientConjugate (u t q))
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0) (hu : ∀ k ∈ modes, modeDot k (u t k) = 0)
    (hd : ∀ p ∈ modes, ∀ k : Fin 3,
      HasDerivAt (fun tau ↦ u tau p k) (velocityRHS modes (u t) nu p k) t)
    (hlambda : DifferentiableAt ℝ (fun h ↦ topEigenvalue
      (spatialStrain modes (filteredVelocity chi (u (t + h)))
        (x + materialShift (spatialVelocity chi modes (u t) x) h))) 0) :
    HasDerivAt (frozenMaterialEnergy chi modes u delta t x)
      (physicalMaterialRate chi modes outputs (u t) delta nu x) 0 := by
  obtain ⟨r, rfl⟩ := torusPoint_surjective x
  let v := spatialVelocity chi modes (u t) (torusPoint r)
  let uu := fun h ↦ u (t + h)
  let X := fun h i ↦ r i + h * v i
  have hu0 : uu 0 = u t := by simp [uu]
  have hX0 : X 0 = r := by funext i; simp [X]
  have hd' : ∀ p ∈ modes, ∀ k : Fin 3,
      HasDerivAt (fun h ↦ uu h p k) (velocityRHS modes (uu 0) nu p k) 0 := by
    intro p hp k
    have hd0 : HasDerivAt (fun tau ↦ u tau p k) (velocityRHS modes (u t) nu p k) (t + id 0) := by
      simpa only [id_eq, add_zero] using hd p hp k
    have h := hd0.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_add t)
    simpa only [uu, add_zero, one_smul, mul_one, Function.comp_def] using h
  have hX : ∀ i, HasDerivAt (fun h ↦ X h i)
      (finiteFourierReconstruction modes (filteredVelocity chi (uu 0)) (torusPoint (X 0)) i).re 0 := by
    intro i
    have hi := ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (r i)
    have hi' : HasDerivAt (fun h ↦ X h i) (v i) 0 := by
      simpa only [X, id_eq, one_mul] using hi
    simpa only [hu0, hX0, v, spatialVelocity, complexRealPartEuclideanCLM_apply,
      PancakeTransverseEnergyFreezing.complexRealPartEuclidean, PiLp.toLp_apply] using hi'
  have hr' : ∀ q, uu 0 (-q) = PancakeBlockReality.coefficientConjugate (uu 0 q) := by
    simpa only [hu0] using hr
  have hu' : ∀ k ∈ modes, modeDot k (uu 0 k) = 0 := by simpa only [hu0] using hu
  have hS := hasDerivAt_spatialStrain_material chi modes outputs uu X nu 0
    hsub hout hchi hchir hs hr' hk hu' hd' hX
  have hw := hasDerivAt_spatialVorticity_material chi modes uu X nu 0 hchir hs hr' hk hu' hd' hX
  have hL : DifferentiableAt ℝ (fun h ↦ topEigenvalue (physicalStrainPath chi modes uu X h)) 0 := by
    simpa only [physicalStrainPath, uu, X, torusPoint_line, v] using hlambda
  have he := hasDerivAt_regularizedEnergy (physicalStrainPath chi modes uu X)
    (physicalVorticityPath modes uu X) _ _ delta 0 hS hw hL
  have hfun : (fun h ↦ regularizedEnergy (physicalStrainPath chi modes uu X h) delta
      (physicalVorticityPath modes uu X h)) = frozenMaterialEnergy chi modes u delta t (torusPoint r) := by
    funext h
    simp only [physicalStrainPath, physicalVorticityPath, uu, X, torusPoint_line, v,
      frozenMaterialEnergy, physicalRegularizedEnergy]
  rw [hfun] at he
  apply he.congr_deriv
  simp only [physicalStrainPath, physicalVorticityPath, hu0, hX0, physicalMaterialRate]

/-- Agreement with the physical rate supplies a continuous absolute
envelope, so integrability is a conclusion rather than an extra budget. -/
theorem integrable_frozenMaterialRate_of_agreement
    (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector) (u : ℝ → FourierVelocity)
    (delta nu t : ℝ)
    (hc : ∀ q ∈ modes, ∀ i, Continuous (fun s ↦ u s q i))
    (heq : ∀ᵐ x : T3, frozenMaterialRate chi modes u delta t x =
      physicalMaterialRate chi modes outputs (u t) delta nu x) :
    Integrable (frozenMaterialRate chi modes u delta t) := by
  have hinc : Measurable (fun x : T3 ↦ (t, x)) := measurable_const.prodMk measurable_id
  have hm0 := (measurable_frozenMaterialRate chi modes u delta hc).comp hinc
  have hm : Measurable (frozenMaterialRate chi modes u delta t) := hm0
  have hi : Integrable (physicalMaterialAbsEnvelope chi modes outputs (u t) delta nu) :=
    (continuous_physicalMaterialAbsEnvelope chi modes outputs (u t) delta nu).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [heq] with x hx
  rw [Real.norm_eq_abs, hx]
  exact abs_physicalMaterialRate_le chi modes outputs (u t) delta nu x

/-- The rate in this spatial balance is a constructed, jointly measurable
derivative. Its identification and integrability are derived from the
physical equation and the stated AE spectral differentiability. -/
theorem integral_frozenMaterialRate_paid
    (chi : Wavevector → ℂ) (low modes outputs : Finset Wavevector) (u : ℝ → FourierVelocity)
    (delta nu t : ℝ) (hdelt : 0 < delta) (hnu : 0 ≤ nu)
    (hlow : low ⊆ modes) (hsub : modes ⊆ outputs)
    (hout : ∀ k ∈ modes, ∀ l ∈ modes, k + l ∈ outputs)
    (hchi : ∀ q, q ∉ low → chi q = 0) (hchir : ∀ q, chi (-q) = conj (chi q))
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ q, u t (-q) = PancakeBlockReality.coefficientConjugate (u t q))
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0) (hu : ∀ k ∈ modes, modeDot k (u t k) = 0)
    (hc : ∀ q ∈ modes, ∀ i, Continuous (fun s ↦ u s q i))
    (hd : ∀ p ∈ modes, ∀ k : Fin 3,
      HasDerivAt (fun tau ↦ u tau p k) (velocityRHS modes (u t) nu p k) t)
    (hL : ∀ᵐ x : T3, MaterialSpectralDifferentiable chi modes u t x) :
    (∫ x : T3, frozenMaterialRate chi modes u delta t x) + (1 / 2 : ℝ) * (∫ x : T3,
      ‖spectralResidual (spatialStrain modes (filteredVelocity chi (u t)) x).1
        (topEigenvalue (spatialStrain modes (filteredVelocity chi (u t)) x)) (spatialVorticity modes (u t) x)‖ ^ 2) ≤
      (16 * nu / delta) * strainGradientCutoffWeight low chi *
        PancakeViscousMisalignmentAbsorption.fullEnergy modes (u t) *
        PancakeViscousMisalignmentAbsorption.fullEnergy modes (fourierCurl (u t)) +
      ∫ x : T3, physicalNonviscousEnvelope chi modes outputs (u t) delta x := by
  have hchim : ∀ q, q ∉ modes → chi q = 0 := fun q hq ↦ hchi q (fun hql ↦ hq (hlow hql))
  have heq : ∀ᵐ x : T3, frozenMaterialRate chi modes u delta t x =
      physicalMaterialRate chi modes outputs (u t) delta nu x := by
    filter_upwards [hL] with x hx
    exact (hasDerivAt_frozenMaterialEnergy chi modes outputs u delta nu t x hsub hout hchim hchir
      hs hr hk hu hd hx).deriv
  exact integral_materialRate_paid chi low modes outputs (u t) delta nu
    (frozenMaterialRate chi modes u delta t) hdelt hnu hlow hsub hchi
    (integrable_frozenMaterialRate_of_agreement chi modes outputs u delta nu t hc heq)
    (heq.mono (fun _ hx ↦ hx.le))

end Mettapedia.FluidDynamics.NavierStokes.PancakeFrozenMaterialDerivative
