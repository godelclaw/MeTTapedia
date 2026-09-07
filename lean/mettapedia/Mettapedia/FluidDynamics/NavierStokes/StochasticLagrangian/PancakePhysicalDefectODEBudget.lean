import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalSpectralDefect

/-!
# Physical spectral-defect budget with regularity derived from the ODE

The finite velocity RHS is continuous in its retained coefficients.
Consequently the velocity and real material trajectory equations supply
the C1 regularity used by the collision-safe integral theorem.
No separate strain equation, phase equation, C1 field hypothesis, or
forcing-integrability budget is assumed by the final theorem.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalDefectODEBudget

open scoped BigOperators ComplexConjugate RealInnerProductSpace Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicVorticityEquation
open PancakePeriodicComplexStretch PancakeFourierPressureStrain PancakeFilteredStrainDynamics
open PancakeBlockReality PancakeFrequencyProjectorCommutator PancakeFourierMaterialPaths
open PancakeSpatialStrainEvolution PancakeGalerkinKineticEnergy PancakeLowPressureBudget
open PancakePhysicalSpectralDefect PancakeSpectralDefectEvolution
open PancakeSpectralProjectorRegularity.SymmetricStrain

local notation "T3" => UnitAddTorus (Fin 3)

theorem continuousOn_convectionConvolution (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (domain : Set ℝ)
    (hu : ∀ q ∈ modes, ∀ i, ContinuousOn (fun t ↦ u t q i) domain)
    (q : Wavevector) (i : Fin 3) :
    ContinuousOn (fun t ↦ convectionConvolution modes (u t) q i) domain := by
  simp only [convectionConvolution, Finset.sum_apply]
  apply continuousOn_finsetSum
  intro k hk
  apply continuousOn_finsetSum
  intro l hl
  by_cases hkl : k + l = q
  · simp only [hkl, ite_true, orderedConvection, Pi.smul_apply, smul_eq_mul]
    apply ContinuousOn.mul _ (hu l hl i)
    unfold modeDot
    apply continuousOn_finsetSum
    intro j _
    exact continuousOn_const.mul (hu k hk j)
  · simp only [hkl, ite_false, Pi.zero_apply]
    exact continuousOn_const

theorem continuousOn_velocityRHS (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu : ℝ) (domain : Set ℝ)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ t ∈ domain, ∀ k ∈ modes, modeDot k (u t k) = 0)
    (hc : ∀ q ∈ modes, ∀ i, ContinuousOn (fun t ↦ u t q i) domain)
    (q : Wavevector) (hq : q ∈ modes) (i : Fin 3) :
    ContinuousOn (fun t ↦ velocityRHS modes (u t) nu q i) domain := by
  have hC := continuousOn_convectionConvolution modes u domain hc q i
  have hP := continuousOn_pressureCoeff modes u q domain hc
  have he : ContinuousOn (fun t ↦
      (-unitTorusDerivativePhase) * convectionConvolution modes (u t) q i -
        unitTorusDerivativePhase * (q i : ℂ) * pressureCoeff modes (u t) q +
        ((nu : ℂ) * unitTorusDerivativePhase ^ 2 * modeSquare q) * u t q i) domain :=
    ((continuousOn_const.mul hC).sub (continuousOn_const.mul hP)).add
      (continuousOn_const.mul (hc q hq i))
  apply he.congr
  intro t ht
  simpa only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    pressureGradientCoeff, unitTorusViscousVorticityCoeff] using
      congrFun (velocityRHS_eq_negativeConvection_pressure_viscosity modes (u t) nu hk (hu t ht) q) i

theorem contDiffOn_one_of_hasDerivAt_interval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : ℝ → E) (a b : ℝ)
    (hg : ContinuousOn g (Set.uIcc a b))
    (hd : ∀ t ∈ Set.uIcc a b, HasDerivAt f (g t) t) :
    ContDiffOn ℝ 1 f (Set.uIcc a b) := by
  by_cases hab : a = b
  · subst b
    simp only [Set.uIcc_self]
    intro t ht
    have : t = a := Set.mem_singleton_iff.mp ht
    subst t
    exact contDiffWithinAt_singleton
  · have huniq : UniqueDiffOn ℝ (Set.uIcc a b) := uniqueDiffOn_Icc (min_lt_max.mpr hab)
    apply (contDiffOn_one_iff_derivWithin huniq).mpr
    refine ⟨fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt, ?_⟩
    apply hg.congr
    intro t ht
    exact (hd t ht).hasDerivWithinAt.derivWithin (huniq t ht)

/-- The C1 input for physical Fourier fields is a consequence of the
retained velocity ODE and the explicit continuity of its RHS. -/
theorem contDiffOn_coefficients_of_velocityRHS
    (modes : Finset Wavevector) (u : ℝ → FourierVelocity) (nu a b : ℝ)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ t ∈ Set.uIcc a b, ∀ k ∈ modes, modeDot k (u t k) = 0)
    (hd : ∀ t ∈ Set.uIcc a b, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun tau ↦ u tau q i) (velocityRHS modes (u t) nu q i) t) :
    ∀ q ∈ modes, ∀ i, ContDiffOn ℝ 1 (fun t ↦ u t q i) (Set.uIcc a b) := by
  have hc := continuousOn_coefficients_of_velocityRHS modes u nu (Set.uIcc a b) hd
  intro q hq i
  exact contDiffOn_one_of_hasDerivAt_interval _ _ a b
    (continuousOn_velocityRHS modes u nu (Set.uIcc a b) hk hu hc q hq i)
    (fun t ht ↦ hd t ht q hq i)

theorem continuousOn_characterPath (q : Wavevector) (X : ℝ → Fin 3 → ℝ)
    (domain : Set ℝ) (hX : ∀ i, ContinuousOn (fun t ↦ X t i) domain) :
    ContinuousOn (fun t ↦ UnitAddTorus.mFourier q (torusPoint (X t))) domain := by
  simp_rw [mFourier_torusPoint]
  unfold realModeDot
  fun_prop

theorem continuousOn_filteredVelocity_observation
    (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (X : ℝ → Fin 3 → ℝ) (domain : Set ℝ)
    (hu : ∀ q ∈ modes, ∀ i, ContinuousOn (fun t ↦ u t q i) domain)
    (hX : ∀ i, ContinuousOn (fun t ↦ X t i) domain) (i : Fin 3) :
    ContinuousOn (fun t ↦ (finiteFourierReconstruction modes
      (filteredVelocity chi (u t)) (torusPoint (X t)) i).re) domain := by
  apply Complex.continuous_re.comp_continuousOn
  simp only [finiteFourierReconstruction, filteredVelocity, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  apply continuousOn_finsetSum
  intro q hq
  exact (continuousOn_characterPath q X domain hX).mul (continuousOn_const.mul (hu q hq i))

/-- The real trajectory ODE supplies its own C1 regularity as well. -/
theorem contDiffOn_materialPath_of_ODE
    (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (X : ℝ → Fin 3 → ℝ) (a b : ℝ)
    (hu : ∀ q ∈ modes, ∀ i, ContinuousOn (fun t ↦ u t q i) (Set.uIcc a b))
    (hX : ∀ t ∈ Set.uIcc a b, ∀ i, HasDerivAt (fun tau ↦ X tau i)
      (finiteFourierReconstruction modes (filteredVelocity chi (u t)) (torusPoint (X t)) i).re t) :
    ∀ i, ContDiffOn ℝ 1 (fun t ↦ X t i) (Set.uIcc a b) := by
  have hXc : ∀ i, ContinuousOn (fun t ↦ X t i) (Set.uIcc a b) :=
    fun i t ht ↦ (hX t ht i).continuousAt.continuousWithinAt
  intro i
  exact contDiffOn_one_of_hasDerivAt_interval _ _ a b
    (continuousOn_filteredVelocity_observation chi modes u X _ hu hXc i) (fun t ht ↦ hX t ht i)

/-- The full physical signed defect budget needs only the retained
velocity equation, the real trajectory equation, and the algebraic
reality/support/incompressibility conditions. Its forcing integrals are
not yet bounded uniformly from arbitrary initial data. -/
theorem physicalSpectralDefect_budget_of_velocityODE
    (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (X : ℝ → Fin 3 → ℝ) (nu a b theta : ℝ)
    (hab : a ≤ b) (htheta : 0 < theta)
    (hchi : ∀ q, q ∉ modes → chi q = 0)
    (hchir : ∀ q, chi (-q) = conj (chi q))
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hr : ∀ t ∈ Set.uIcc a b, ∀ q, u t (-q) = coefficientConjugate (u t q))
    (hu : ∀ t ∈ Set.uIcc a b, ∀ k ∈ modes, modeDot k (u t k) = 0)
    (hd : ∀ t ∈ Set.uIcc a b, ∀ p ∈ modes, ∀ k : Fin 3,
      HasDerivAt (fun tau ↦ u tau p k) (velocityRHS modes (u t) nu p k) t)
    (hX : ∀ t ∈ Set.uIcc a b, ∀ i, HasDerivAt (fun tau ↦ X tau i)
      (finiteFourierReconstruction modes (filteredVelocity chi (u t)) (torusPoint (X t)) i).re t) :
    let S := physicalStrainPath chi modes u X
    let w := physicalVorticityPath modes u X
    let R := fun t ↦ spatialStrainRemainder chi modes (materialOutputModes modes)
      (u t) nu (torusPoint (X t))
    let f := fun t ↦ spatialVorticityForcing chi modes (u t) nu (torusPoint (X t))
    let z := fun t ↦ spectralResidual (S t).1 (topEigenvalue (S t)) (w t)
    physicalSpectralDefect chi modes (u b) (torusPoint (X b)) +
      (1 - theta) * (∫ t in a..b, ‖z t‖ ^ 2) ≤
        physicalSpectralDefect chi modes (u a) (torusPoint (X a)) +
          (∫ t in a..b, PancakeSpectralDefectBudget.topRemainderAnisotropy (S t) (R t) (w t)) +
          (∫ t in a..b, ‖f t‖ ^ 2) / theta := by
  exact integrated_physicalSpectralDefect_budget chi modes (materialOutputModes modes) u X nu a b theta
    hab htheta (subset_materialOutputModes modes) (add_mem_materialOutputModes modes)
    hchi hchir hs hk (contDiffOn_coefficients_of_velocityRHS modes u nu a b hk hu hd)
    (contDiffOn_materialPath_of_ODE chi modes u X a b
      (continuousOn_coefficients_of_velocityRHS modes u nu _ hd) hX) hr hu hd hX

/-- The exact physical identity retains the signed viscous and transport
pairing. It is the appropriate starting point before a Young estimate
would charge the square of the entire vorticity forcing. -/
theorem physicalSpectralDefect_identity_of_velocityODE
    (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (X : ℝ → Fin 3 → ℝ) (nu a b : ℝ)
    (hchi : ∀ q, q ∉ modes → chi q = 0)
    (hchir : ∀ q, chi (-q) = conj (chi q))
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hr : ∀ t ∈ Set.uIcc a b, ∀ q, u t (-q) = coefficientConjugate (u t q))
    (hu : ∀ t ∈ Set.uIcc a b, ∀ k ∈ modes, modeDot k (u t k) = 0)
    (hd : ∀ t ∈ Set.uIcc a b, ∀ p ∈ modes, ∀ k : Fin 3,
      HasDerivAt (fun tau ↦ u tau p k) (velocityRHS modes (u t) nu p k) t)
    (hX : ∀ t ∈ Set.uIcc a b, ∀ i, HasDerivAt (fun tau ↦ X tau i)
      (finiteFourierReconstruction modes (filteredVelocity chi (u t)) (torusPoint (X t)) i).re t) :
    let S := physicalStrainPath chi modes u X
    let w := physicalVorticityPath modes u X
    let R := fun t ↦ spatialStrainRemainder chi modes (materialOutputModes modes)
      (u t) nu (torusPoint (X t))
    let f := fun t ↦ spatialVorticityForcing chi modes (u t) nu (torusPoint (X t))
    let z := fun t ↦ spectralResidual (S t).1 (topEigenvalue (S t)) (w t)
    let A := fun t ↦ PancakeSpectralDefectBudget.topRemainderAnisotropy (S t) (R t) (w t)
    IntervalIntegrable A MeasureTheory.volume a b ∧
      physicalSpectralDefect chi modes (u b) (torusPoint (X b)) +
        (∫ t in a..b, ‖z t‖ ^ 2) =
          physicalSpectralDefect chi modes (u a) (torusPoint (X a)) +
            (∫ t in a..b, A t) + (∫ t in a..b, 2 * ⟪z t, f t⟫) := by
  dsimp only
  let S := physicalStrainPath chi modes u X
  let w := physicalVorticityPath modes u X
  let R := fun t ↦ spatialStrainRemainder chi modes (materialOutputModes modes)
    (u t) nu (torusPoint (X t))
  let f := fun t ↦ spatialVorticityForcing chi modes (u t) nu (torusPoint (X t))
  have huc := contDiffOn_coefficients_of_velocityRHS modes u nu a b hk hu hd
  have hXc := contDiffOn_materialPath_of_ODE chi modes u X a b
    (continuousOn_coefficients_of_velocityRHS modes u nu _ hd) hX
  have hSc : ContDiffOn ℝ 1 (fun t ↦ (S t).1) (Set.uIcc a b) :=
    contDiffOn_physicalStrainPath chi modes u X _ huc hXc
  have hwc : ContDiffOn ℝ 1 w (Set.uIcc a b) :=
    contDiffOn_physicalVorticityPath modes u X _ huc hXc
  have hdS : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun tau ↦ (S tau).1) (-(S t).1 * (S t).1 + R t) t := fun t ht ↦
    hasDerivAt_spatialStrain_material chi modes (materialOutputModes modes) u X nu t
      (subset_materialOutputModes modes) (add_mem_materialOutputModes modes) hchi hchir hs
      (hr t ht) hk (hu t ht) (hd t ht) (hX t ht)
  have hdw : ∀ t ∈ Set.uIcc a b, HasDerivAt w ((S t).1 (w t) + f t) t := fun t ht ↦
    hasDerivAt_spatialVorticity_material chi modes u X nu t hchir hs
      (hr t ht) hk (hu t ht) (hd t ht) (hX t ht)
  exact PancakeSpectralDefectBudget.integrated_topSpectralDefect_identity S w R f a b hSc hwc
    (continuousOn_forcing_of_evolution (fun t ↦ (S t).1) w f a b hSc.continuousOn hwc hdw) hdS hdw

end Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalDefectODEBudget
