import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityEighthEnergy

/-!
# The enstrophy balance for an actual local periodic solution

The quadratic companion of the eighth-moment balance. The periodic flux
`2 ⟪ω, ∂_j ω⟫` removes the enstrophy Laplacian after spatial integration,
incompressible transport preserves the spatial mean, and the
time-integrated identity

```text
½ ∫ |ω(t)|² + ν ∫₀ᵗ ∫ |∇ω|² = ½ ∫ |ω₀|² + ∫₀ᵗ ∫ ⟪ω, S ω⟫
```

holds on the whole local interval, including the initial endpoint. The
signed stretching is retained; no bound on it is asserted here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalEnstrophyDiffusion

open scoped RealInnerProductSpace
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeLocalInfiniteVelocity PancakeHigherDerivativeMoments
open PancakeHaarTransportRate PancakeFourierTranslationCurve PancakeMaterialChainRule
open PancakeDyadicDirectionEvolution PancakePeriodicWeakDerivative
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalJointDiffusionBudget
open LocalAlignmentForcing LocalFrozenVorticity LocalAlignmentContinuity LocalSpaceTimeExtension

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance enstrophyCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance enstrophyCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance enstrophyCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

section Spatial

def energyFlux (u : FourierVelocity) (j : Fin 3) (x : T3) : ℝ :=
  2 * ⟪fullVorticity u x, fullCurlGradient u j x⟫

def stretchingDensity (u : FourierVelocity) (x : T3) : ℝ :=
  ⟪fullVorticity u x, fullStrainOperator u x (fullVorticity u x)⟫

theorem continuous_energyFlux (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (j : Fin 3) : Continuous (energyFlux u j) := by
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  exact continuous_const.mul (hw.inner (LocalSquaredGapGradient.continuous_fullCurlGradient u j))

theorem locallyLipschitz_energyFlux_lift (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (j : Fin 3) :
    LocallyLipschitz (fun r : X3 ↦ energyFlux u j (torusPoint r)) := by
  have hp : ContDiff ℝ 1 (fun p : R3 × R3 ↦ 2 * ⟪p.1, p.2⟫) :=
    contDiff_const.mul (contDiff_fst.inner ℝ contDiff_snd)
  have hw := LocalAlignmentTransport.locallyLipschitz_fullVorticity u
    (summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu)
  have hd := LocalVorticityEighthMoment.locallyLipschitz_fullCurlGradient_lift u hu j
  exact hp.locallyLipschitz.comp (g := fun r : X3 ↦
    (fullVorticity u (torusPoint r), fullCurlGradient u j (torusPoint r))) (hw.prodMk hd)

theorem hasDerivAt_energyFlux_shift (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (j : Fin 3) (x : T3) :
    HasDerivAt (fun h ↦ energyFlux u j (x + coordinateShift j h)) (energySecond u j x) 0 := by
  have hw := hasDerivAt_fullVorticity_shift u hu j x 0
  have hd := hasDerivAt_fullCurlGradient_shift u hu j x 0
  have h := (hw.inner ℝ hd).const_mul 2
  apply h.congr_deriv
  rw [energySecond_eq u hu j x]
  simp only [coordinateShift_zero, add_zero, real_inner_self_eq_norm_sq]
  ring

theorem integrable_energySecond_and_integral_zero (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (j : Fin 3) :
    Integrable (energySecond u j) ∧ (∫ x : T3, energySecond u j x) = 0 := by
  have he : shiftRate (energyFlux u j) (coordinateShift j) = energySecond u j :=
    funext (fun x ↦ (hasDerivAt_energyFlux_shift u hu j x).deriv)
  simpa only [he] using integral_coordinateRate_zero (energyFlux u j) j
    (continuous_energyFlux u hu j) (locallyLipschitz_energyFlux_lift u hu j)

theorem integrable_energyLaplacian_and_integral_zero (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    Integrable (energyLaplacian u) ∧ (∫ x : T3, energyLaplacian u x) = 0 := by
  have h (j : Fin 3) := integrable_energySecond_and_integral_zero u hu j
  refine ⟨integrable_finsetSum _ (fun j _ ↦ (h j).1), ?_⟩
  change (∫ x : T3, ∑ j : Fin 3, energySecond u j x) = 0
  rw [integral_finsetSum _ (fun j _ ↦ (h j).1)]
  simp only [(h _).2, Finset.sum_const_zero]

theorem continuous_gradientSquare (u : FourierVelocity) : Continuous (gradientSquare u) :=
  continuous_finsetSum _
    (fun j _ ↦ (LocalSquaredGapGradient.continuous_fullCurlGradient u j).norm.pow 2)

theorem gradientSquare_nonneg (u : FourierVelocity) (x : T3) : 0 ≤ gradientSquare u x := by
  unfold gradientSquare; positivity

theorem continuous_stretchingDensity (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) : Continuous (stretchingDensity u) := by
  have hw := continuous_fullVorticity u hu
  exact hw.inner ((continuous_fullStrainOperator u hu).clm_apply hw)

/-- The spatial mean balance: full-gradient dissipation against the signed
stretching source. -/
theorem integral_materialRate_add_dissipation_eq (u : FourierVelocity) (nu : ℝ)
    (hu : Summable (fourierMoment 3 u)) :
    (∫ x : T3, materialRate u nu x) / 2 + nu * (∫ x : T3, gradientSquare u x) =
      ∫ x : T3, stretchingDensity u x := by
  have hiG : Integrable (gradientSquare u) :=
    (continuous_gradientSquare u).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiS : Integrable (stretchingDensity u) :=
    (continuous_stretchingDensity u
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  obtain ⟨hiL, hzero⟩ := integrable_energyLaplacian_and_integral_zero u hu
  have he : (∫ x : T3, materialRate u nu x) =
      ∫ x : T3, nu * energyLaplacian u x + 2 * stretchingDensity u x -
        (2 * nu) * gradientSquare u x := by
    apply integral_congr_ae
    filter_upwards [] with x
    have h := materialRate_sub_diffusion_add_gradient_eq u nu hu x
    simp only [stretchingDensity]
    linarith only [h]
  have h1 := integral_sub ((hiL.const_mul nu).add (hiS.const_mul 2)) (hiG.const_mul (2 * nu))
  have h2 := integral_add (hiL.const_mul nu) (hiS.const_mul 2)
  simp only [Pi.add_apply] at h1 h2
  rw [h1, h2] at he
  simp only [integral_const_mul, hzero, mul_zero, zero_add] at he
  linarith only [he]

end Spatial

section Time

def meanEnstrophy (u : FourierVelocity) : ℝ := ∫ x : T3, energy u x
def palinstrophy (u : FourierVelocity) : ℝ := ∫ x : T3, gradientSquare u x
def stretching (u : FourierVelocity) : ℝ := ∫ x : T3, stretchingDensity u x

theorem meanEnstrophy_eq (u : FourierVelocity) :
    meanEnstrophy u = ∫ x : T3, ‖fullVorticity u x‖ ^ 2 := rfl

theorem meanEnstrophy_nonneg (u : FourierVelocity) : 0 ≤ meanEnstrophy u :=
  integral_nonneg (fun x ↦ by unfold energy; positivity)

theorem palinstrophy_nonneg (u : FourierVelocity) : 0 ≤ palinstrophy u :=
  integral_nonneg (gradientSquare_nonneg u)

def frozenMaterialRate (u : ℝ → FourierVelocity) (t : ℝ) (x : T3) : ℝ :=
  scalarMaterialRate (fun τ ↦ energy (u τ)) (LocalMeanAlignmentBalance.velocity (u t)) t x

theorem frozenMaterialRate_eq_deriv (u : ℝ → FourierVelocity) (t : ℝ) (x : T3) :
    frozenMaterialRate u t x = deriv (frozenEnergy u t x) 0 := rfl

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients t) q ≤ g q)

include hSum hu in
theorem continuous_enstrophyDensity_spaceTime :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦ energy (s.coefficients z.1) z.2) :=
  (continuous_fullVorticity_spaceTime s g hSum
    (fun t ht q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu t ht q))).norm.pow 2

include hSum hu in
theorem continuous_gradientSquare_spaceTime :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦ gradientSquare (s.coefficients z.1) z.2) :=
  continuous_finsetSum _ (fun j _ ↦
    (LocalVorticityEighthMoment.continuous_fullCurlGradient_spaceTime s g hSum hu j).norm.pow 2)

include hSum hu in
theorem continuous_stretchingDensity_spaceTime :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦ stretchingDensity (s.coefficients z.1) z.2) := by
  have hu2 (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) :
      fourierMoment 2 (s.coefficients t) q ≤ g q :=
    (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu t ht q)
  have hw := continuous_fullVorticity_spaceTime s g hSum hu2
  have hS := continuous_fullStrainOperator_parametric
    (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t)
    (fun q i ↦ (s.continuous q i).comp continuous_subtype_val) g hSum (fun t ↦ hu2 t t.2)
  exact hw.inner (hS.clm_apply hw)

include hSum hu in
theorem continuousOn_meanEnstrophy :
    ContinuousOn (fun t ↦ meanEnstrophy (s.coefficients t)) (Set.Icc 0 T) :=
  continuousOn_spatialIntegral _ (continuous_enstrophyDensity_spaceTime s g hSum hu)

include hSum hu in
theorem continuousOn_palinstrophy :
    ContinuousOn (fun t ↦ palinstrophy (s.coefficients t)) (Set.Icc 0 T) :=
  continuousOn_spatialIntegral _ (continuous_gradientSquare_spaceTime s g hSum hu)

include hSum hu in
theorem continuousOn_stretching :
    ContinuousOn (fun t ↦ stretching (s.coefficients t)) (Set.Icc 0 T) :=
  continuousOn_spatialIntegral _ (continuous_stretchingDensity_spaceTime s g hSum hu)

section Interior

variable (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)

include hI hSum hu in
theorem continuous_extendedEnstrophy :
    Continuous (fun z : ℝ × T3 ↦ energy (coefficients s a b hab z.1) z.2) := by
  let time : ℝ → Set.Icc (0 : ℝ) T := fun t ↦
    ⟨Set.projIcc a b hab t, Set.Ioo_subset_Icc_self (hI (Set.projIcc a b hab t).2)⟩
  have hp : Continuous (fun t : ℝ ↦ (Set.projIcc a b hab t : ℝ)) :=
    continuous_subtype_val.comp (LipschitzWith.projIcc hab).continuous
  have hc : Continuous time := hp.subtype_mk _
  exact (continuous_enstrophyDensity_spaceTime s g hSum hu).comp
    (f := fun z : ℝ × T3 ↦ (time z.1, z.2)) ((hc.comp continuous_fst).prodMk continuous_snd)

include hI hg hSum hu in
theorem locallyLipschitz_extendedEnstrophy :
    LocallyLipschitz (fun z : ℝ × X3 ↦ energy (coefficients s a b hab z.1) (torusPoint z.2)) := by
  have hp : ContDiff ℝ 1 (fun w : R3 ↦ ‖w‖ ^ 2) := contDiff_norm_sq ℝ
  exact hp.locallyLipschitz.comp
    (LocalSpaceTimeExtension.locallyLipschitz_fullVorticity s a b hab hI g hg hSum hu)

theorem frozenMaterialRate_extension_eq (t : ℝ) (ht : t ∈ Set.Ioo a b) (x : T3) :
    frozenMaterialRate (coefficients s a b hab) t x = frozenMaterialRate s.coefficients t x := by
  unfold frozenMaterialRate scalarMaterialRate
  rw [coefficients_eq s a b hab t (Set.Ioo_subset_Icc_self ht)]
  apply Filter.EventuallyEq.deriv_eq
  have hc : Filter.Tendsto (fun h : ℝ ↦ t + h) (nhds 0) (nhds t) := by
    have hc : ContinuousAt (fun h : ℝ ↦ t + h) 0 := by fun_prop
    simpa only [ContinuousAt, add_zero] using hc
  filter_upwards [hc.eventually (Icc_mem_nhds ht.1 ht.2)] with h hh
  rw [coefficients_eq s a b hab (t + h) hh]

include hab hI hg hSum hu in
/-- The material rate is integrable in time and has the actual endpoint difference. -/
theorem intervalIntegral_materialRate_eq_meanEnstrophy :
    IntervalIntegrable (fun t ↦ ∫ x : T3, materialRate (s.coefficients t) nu x) volume a b ∧
      (∫ t in a..b, ∫ x : T3, materialRate (s.coefficients t) nu x) =
        meanEnstrophy (s.coefficients b) - meanEnstrophy (s.coefficients a) := by
  have h := PancakeMeanMaterialBalance.intervalIntegral_materialRate_eq
    (fun t ↦ energy (coefficients s a b hab t))
    (fun t ↦ LocalMeanAlignmentBalance.velocity (coefficients s a b hab t))
    (continuous_extendedEnstrophy s g hSum hu a b hab hI)
    (fun _ ↦ LocalMeanAlignmentBalance.continuous_velocity _)
    (locallyLipschitz_extendedEnstrophy s g hg hSum hu a b hab hI)
    (LocalMeanAlignmentBalance.locallyLipschitz_extendedVelocity s a b hab hI g hSum hu)
    (fun t ↦ Filter.Eventually.of_forall
      (LocalMeanAlignmentBalance.divergence_extendedVelocity s a b hab hI g hSum hu t)) a b
  change IntervalIntegrable
      (fun t ↦ ∫ x : T3, frozenMaterialRate (coefficients s a b hab) t x) volume a b ∧
    (∫ t in a..b, ∫ x : T3, frozenMaterialRate (coefficients s a b hab) t x) =
      meanEnstrophy (coefficients s a b hab b) - meanEnstrophy (coefficients s a b hab a) at h
  rw [coefficients_eq s a b hab b ⟨hab, le_rfl⟩, coefficients_eq s a b hab a ⟨le_rfl, hab⟩] at h
  have he : Set.EqOn
      (fun t ↦ ∫ x : T3, frozenMaterialRate (coefficients s a b hab) t x)
      (fun t ↦ ∫ x : T3, materialRate (s.coefficients t) nu x) (Set.uIoo a b) := by
    intro t ht
    have ht' : t ∈ Set.Ioo a b := by simpa only [Set.uIoo_of_le hab] using ht
    apply integral_congr_ae
    filter_upwards [] with x
    rw [frozenMaterialRate_extension_eq s a b hab t ht' x, frozenMaterialRate_eq_deriv]
    exact (hasDerivAt_frozenEnergy s g hg hSum hu a b hab hI t ht' x).deriv
  exact ⟨h.1.congr_uIoo he, (intervalIntegral.integral_congr_uIoo he).symm.trans h.2⟩

include hab hI hg hSum hu in
theorem interior_enstrophy_identity :
    meanEnstrophy (s.coefficients b) / 2 + (∫ t in a..b, nu * palinstrophy (s.coefficients t)) =
    meanEnstrophy (s.coefficients a) / 2 + ∫ t in a..b, stretching (s.coefficients t) := by
  have hsub : Set.Icc a b ⊆ Set.Icc (0 : ℝ) T := hI.trans Set.Ioo_subset_Icc_self
  have hG := ((continuousOn_palinstrophy s g hSum hu).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) hab
  obtain ⟨hM, he⟩ := intervalIntegral_materialRate_eq_meanEnstrophy s g hg hSum hu a b hab hI
  have hid : (∫ t in a..b, (∫ x : T3, materialRate (s.coefficients t) nu x) / 2 +
      nu * palinstrophy (s.coefficients t)) = ∫ t in a..b, stretching (s.coefficients t) := by
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) T := hsub
      (Set.Ioo_subset_Icc_self (by simpa only [Set.uIoo_of_le hab] using ht))
    have hu' := hSum.of_nonneg_of_le (fourierMoment_nonneg 3 _) (hu t ht')
    simpa only [palinstrophy, stretching] using
      integral_materialRate_add_dissipation_eq (s.coefficients t) nu hu'
  have hsplit := intervalIntegral.integral_add (hM.div_const 2) (hG.const_mul nu)
  rw [hsplit, intervalIntegral.integral_div, he] at hid
  linarith only [hid]

end Interior

include hg hSum hu in
/-- **Exact enstrophy identity** on the supplied local interval, including the
initial endpoint. The signed stretching integral is kept as it is. -/
theorem enstrophy_identity (hT : 0 < T) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    meanEnstrophy (s.coefficients t) / 2 +
        nu * (∫ τ in (0 : ℝ)..t, palinstrophy (s.coefficients τ)) =
      meanEnstrophy u₀ / 2 + ∫ τ in (0 : ℝ)..t, stretching (s.coefficients τ) := by
  have hA := (continuousOn_meanEnstrophy s g hSum hu).div_const 2
  have hG := continuousOn_palinstrophy s g hSum hu
  have hS := continuousOn_stretching s g hSum hu
  have he := intervalIntegral.endpoint_identity_of_interior hT hA (hG.const_mul nu) hS
    (fun a b ha hab hb ↦ interior_enstrophy_identity s g hg hSum hu a b hab.le
      (fun _ hτ ↦ ⟨ha.trans_le hτ.1, hτ.2.trans_lt hb⟩)) t ht
  rw [intervalIntegral.integral_const_mul, s.initial] at he
  exact he

end Time

end Mettapedia.FluidDynamics.NavierStokes.LocalEnstrophyDiffusion
