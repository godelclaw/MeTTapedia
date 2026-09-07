import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpacetimeSpectralDifferentiability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Almost-everywhere material differentiability on the periodic domain

The real-spacetime Rademacher result is transported through the measured
fundamental cube and then sliced in time. Spectral differentiability is
a conclusion for C¹ finite Fourier fields, not a gap hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeAEMaterialRate

open scoped Topology
open MeasureTheory Measure Set
open PeriodicFourierTriad PancakePeriodicVorticityEquation PancakeFourierMaterialPaths
open PancakeFilteredStrainDynamics PancakeMeasurableMaterialRate PancakeTopEigenvalueDerivative
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakeSpacetimeSpectralDifferentiability

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def frozenMaterialEigenvalue (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (t : ℝ) (x : T3) (h : ℝ) : ℝ :=
  topEigenvalue (spatialStrain modes (filteredVelocity chi (u (t + h)))
    (x + materialShift (spatialVelocity chi modes (u t) x) h))

theorem continuous_frozenParameter
    {Y : Type*} [TopologicalSpace Y]
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : ℝ → FourierVelocity)
    (hu : ∀ q ∈ modes, ∀ i, Continuous (fun t ↦ u t q i))
    (f : ℝ × T3 → Y) (hf : Continuous f) :
    Continuous (fun z : (ℝ × T3) × ℝ ↦ f (z.1.1 + z.2,
      z.1.2 + materialShift (spatialVelocity chi modes (u z.1.1) z.1.2) z.2)) := by
  have hv : Continuous (fun z : (ℝ × T3) × ℝ ↦ spatialVelocity chi modes (u z.1.1) z.1.2) :=
    (continuous_parametric_spatialVelocity chi modes u hu).comp
    (continuous_fst : Continuous (fun z : (ℝ × T3) × ℝ ↦ z.1))
  have hs : Continuous (fun z : (ℝ × T3) × ℝ ↦
      z.1.2 + materialShift (spatialVelocity chi modes (u z.1.1) z.1.2) z.2) := by
    apply Continuous.add continuous_fst.snd
    apply continuous_pi
    intro i
    change Continuous (fun z : (ℝ × T3) × ℝ ↦
      ((z.2 * spatialVelocity chi modes (u z.1.1) z.1.2 i : ℝ) : UnitAddCircle))
    have hvi := (PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) i).comp hv
    exact continuous_quot_mk.comp (continuous_snd.mul hvi)
  have ht : Continuous (fun z : (ℝ × T3) × ℝ ↦ z.1.1 + z.2) := continuous_fst.fst.add continuous_snd
  exact hf.comp (ht.prodMk hs)

theorem continuous_frozenMaterialEigenvalue
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : ℝ → FourierVelocity)
    (hu : ∀ q ∈ modes, ∀ i, Continuous (fun t ↦ u t q i)) :
    Continuous (fun z : (ℝ × T3) × ℝ ↦ frozenMaterialEigenvalue chi modes u z.1.1 z.1.2 z.2) := by
  have hS := continuous_parametric_strain modes chi u hu
  have hL := lipschitzWith_topEigenvalue.continuous.comp hS
  exact continuous_frozenParameter chi modes u hu _ hL

theorem measurableSet_differentiableAt_zero
    {P : Type*} [TopologicalSpace P] [MeasurableSpace P] [OpensMeasurableSpace P]
    (f : P → ℝ → ℝ) (hf : Continuous f.uncurry) :
    MeasurableSet {p | DifferentiableAt ℝ (f p) 0} := by
  have hm := measurableSet_of_differentiableAt_with_param ℝ hf
  exact hm.preimage (show Measurable (fun p : P ↦ (p, (0 : ℝ))) from
    measurable_id.prodMk measurable_const)

theorem measurableSet_materialSpectralDifferentiable
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : ℝ → FourierVelocity)
    (hu : ∀ q ∈ modes, ∀ i, Continuous (fun t ↦ u t q i)) :
    MeasurableSet {z : ℝ × T3 | MaterialSpectralDifferentiable chi modes u z.1 z.2} := by
  exact measurableSet_differentiableAt_zero
    (fun z : ℝ × T3 ↦ frozenMaterialEigenvalue chi modes u z.1 z.2)
    (continuous_frozenMaterialEigenvalue chi modes u hu)

theorem measurePreserving_torusPoint :
    MeasurePreserving torusPoint
      (Measure.pi (fun _ : Fin 3 ↦ (volume : Measure ℝ).restrict (Ioc 0 1)))
      (volume : Measure T3) := by
  have hcircle : MeasurePreserving (fun r : ℝ ↦ (r : UnitAddCircle))
      ((volume : Measure ℝ).restrict (Ioc 0 1)) AddCircle.haarAddCircle := by
    simpa only [zero_add, AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]
      using UnitAddCircle.measurePreserving_mk 0
  exact measurePreserving_pi _ _ (fun _ : Fin 3 ↦ hcircle)

/-- Transfer an AE statement from all real representatives to normalized
periodic Haar measure, through an explicit measured fundamental cube. -/
theorem ae_torus_of_ae_real (P : T3 → Prop) (hP : MeasurableSet {x | P x})
    (h : ∀ᵐ r : X3, P (torusPoint r)) : ∀ᵐ x : T3, P x := by
  have hc : ∀ᵐ r ∂Measure.pi (fun _ : Fin 3 ↦ (volume : Measure ℝ).restrict (Ioc 0 1)),
      P (torusPoint r) := by
    rw [← Measure.restrict_pi_pi]
    exact ae_restrict_of_ae h
  rw [← measurePreserving_torusPoint.map_eq]
  exact (ae_map_iff measurePreserving_torusPoint.aemeasurable hP).mpr hc

theorem ae_ae_torus_of_ae_real (P : ℝ → T3 → Prop)
    (hP : MeasurableSet {z : ℝ × T3 | P z.1 z.2})
    (h : ∀ᵐ z : ℝ × X3, P z.1 (torusPoint z.2)) :
    ∀ᵐ t : ℝ, ∀ᵐ x : T3, P t x := by
  have hreal : ∀ᵐ t : ℝ, ∀ᵐ r : X3, P t (torusPoint r) :=
    ae_ae_of_ae_prod h
  filter_upwards [hreal] with t ht
  have hinc : Measurable (fun x : T3 ↦ (t, x)) := measurable_const.prodMk measurable_id
  exact ae_torus_of_ae_real (P t) (hP.preimage hinc) ht

/-- Actual spectral differentiability holds for almost every space point
at almost every time. No eigenvalue separation or eigenframe regularity
is assumed. -/
theorem ae_ae_materialSpectralDifferentiable
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : ℝ → FourierVelocity)
    (hu : ∀ q ∈ modes, ∀ i, ContDiff ℝ 1 (fun t ↦ u t q i)) :
    ∀ᵐ t : ℝ, ∀ᵐ x : T3, MaterialSpectralDifferentiable chi modes u t x := by
  have hm := measurableSet_materialSpectralDifferentiable chi modes u
    (fun q hq i ↦ (hu q hq i).continuous)
  exact ae_ae_torus_of_ae_real (MaterialSpectralDifferentiable chi modes u) hm
    (ae_real_materialSpectralDifferentiable chi modes u hu)

end Mettapedia.FluidDynamics.NavierStokes.PancakeAEMaterialRate
