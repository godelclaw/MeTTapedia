import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpatialCoefficientRecovery

/-!
# A reconstructed local physical velocity with its actual Fourier equation

The constructed coefficient evolution gives a jointly continuous real
spatial field. Fourier integration recovers exactly the evolved coefficients,
and the field agrees with the initial physical input. Its Fourier equation
is proved using these integrals; higher spatial differentiability is not
asserted here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeLocalSpatialVelocity

open scoped ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeArbitraryDataBlocks
open PancakeLocalInfiniteVelocity PancakeGalerkinCoefficientLimit PancakeCoefficientLimitProperties
open PancakeSobolevSpaceTime PancakeSobolevAbsoluteTail PancakeSpatialCoefficientRecovery
open PancakeInfiniteFourierDerivative PancakeInfiniteRealCurl PancakePhysicalFieldReconstruction
open PancakeCoefficientLimitEquation PancakeContinuousCoordinateJet

local notation "T3" => UnitAddTorus (Fin 3)

def infiniteSolutionPaths {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) : CoefficientLimit T :=
  fun q i ↦ BoundedContinuousFunction.mkOfCompact
    ⟨fun t ↦ s.coefficients t q i, (s.continuous q i).comp continuous_subtype_val⟩

def spatialField {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (t : ℝ) : C(T3, VelocityCoefficient) :=
  fullFourierField id (s.coefficients t)

theorem spatialField_joint_continuous {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) :
    Continuous (fun z : SpaceTime T ↦ spatialField s z.1 z.2) :=
  continuous_fullFourierField (infiniteSolutionPaths s) B
    (fun t F ↦ s.sobolev_bound t t.2 F)

theorem spatialField_coefficients {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    torusFourierVelocity (spatialField s t) = s.coefficients t :=
  torusFourierVelocity_fullFourierField _ (summable_norm_coefficients _ B (s.sobolev_bound t ht))

theorem spatialField_reality {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T)
    (x : T3) (i : Fin 3) :
    conj (spatialField s t x i) = spatialField s t x i :=
  fullFourierField_conj _ (summable_norm_coefficients _ B (s.sobolev_bound t ht))
    (s.reality t) x i

theorem spatialField_initial {nu T B : ℝ} (hT : 0 ≤ T) (f : T3 → VelocityCoefficient)
    (hc : ∀ i, Continuous (fun x ↦ f x i))
    (s : LocalInfiniteVelocitySolution nu (torusFourierVelocity f) T B) :
    ⇑(spatialField s 0) = f := by
  have hs := summable_norm_coefficients _ B (s.sobolev_bound 0 ⟨le_rfl, hT⟩)
  rw [s.initial] at hs
  change ⇑(fullFourierField id (s.coefficients 0)) = f
  rw [s.initial]
  exact fullFourierField_torusFourierVelocity f hc hs

theorem spatialField_transverse {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T)
    (q : Wavevector) :
    modeDot q (torusFourierVelocity (spatialField s t) q) = 0 := by
  rw [spatialField_coefficients s t ht]
  exact s.transverse t q

theorem spatialField_zero_mean {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    torusFourierVelocity (spatialField s t) 0 = 0 := by
  rw [spatialField_coefficients s t ht]
  exact s.zero t

/-- The evolving coefficients here are the actual Fourier integrals of the reconstructed field. -/
theorem spatialField_fourier_equation {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (q : Wavevector) (i : Fin 3) :
    HasDerivAt (fun τ ↦ torusFourierVelocity (spatialField s τ) q i)
      (infiniteVelocityRHS nu (torusFourierVelocity (spatialField s t)) q i) t := by
  rw [spatialField_coefficients s t ⟨ht.1.le, ht.2.le⟩]
  apply (s.equation t ht q i).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with τ hτ
  rw [spatialField_coefficients s τ ⟨hτ.1.le, hτ.2.le⟩]

theorem exists_physical_localSpatialVelocity (nu : ℝ) (hnu : 0 < nu)
    (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 6 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ k, modeDot k (torusFourierVelocity f k) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution nu (torusFourierVelocity f) T B,
        Continuous (fun z : SpaceTime T ↦ spatialField s z.1 z.2) ∧
        ⇑(spatialField s 0) = f ∧
        (∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ x i,
          conj (spatialField s t x i) = spatialField s t x i) ∧
        (∀ t, t ∈ Set.Icc (0 : ℝ) T →
          torusFourierVelocity (spatialField s t) = s.coefficients t) := by
  obtain ⟨T, hT, B, hB, ⟨s⟩⟩ :=
    exists_physical_localInfiniteVelocitySolution nu hnu f hf hr hd hzero
  have hc (i : Fin 3) : Continuous (fun x ↦ f x i) := by
    simpa only [coordinateJet_zero] using (hf i).1 0 0 (by omega)
  exact ⟨T, hT, B, hB, s, spatialField_joint_continuous s,
    spatialField_initial hT.le f hc s, spatialField_reality s, spatialField_coefficients s⟩

end Mettapedia.FluidDynamics.NavierStokes.PancakeLocalSpatialVelocity
