import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityRadialSource
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityRegularizedPairing

/-!
# Signed lifted-displacement representation of the actual source

Exchange symmetry is used only almost everywhere under spatial integration.
The resulting pair is an absolutely convergent sum of signed Euclidean
image contributions. Every image retains its own displacement. On the
diagonal both the pair and every image contribution vanish, without
dividing by vorticity or choosing a direction there.

The source limit is the actual stretching functional. This is a spatial
representation, not a bound on its accumulation in time.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VorticityRadialPairing

open MeasureTheory Filter PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeBlockReality LocalLowDiffusionBudget VorticityRegularizedQuadratic
open VorticityRadialQuadratic VorticityRadialSource
open Mettapedia.Analysis SignedCrossKernel UnitTorusSchwartzLattice
open scoped RealInnerProductSpace Topology
local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "H" => PeriodicRadialRiesz.tensor (d := 3)
local notation "Lat" => UnitTorusLattice.LatticeSubmodule (ι := Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Measure.IsNegInvariant (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsNegInvariant AddCircle.haarAddCircle)

theorem integrable_entry_sub (i j : Fin 3) (N : ℕ) :
    Integrable (fun p : T3 × T3 ↦ (PeriodicRadialRiesz.entry N i j (p.1 - p.2)).re)
      ((volume : Measure T3).prod volume) := by
  have hi := (PeriodicRadialRiesz.integrable_entry N i j).re.comp_fst (volume : Measure T3)
  exact (measurePreserving_sub_prod (volume : Measure T3) volume).integrable_comp_of_integrable hi

theorem tensor_sub_swap_ae (N : ℕ) :
    ∀ᵐ p : T3 × T3 ∂(volume : Measure T3).prod volume, H N (p.2 - p.1) = H N (p.1 - p.2) := by
  have h := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure T3))
    (ν := (volume : Measure T3))).ae_eq_comp
    (PeriodicRadialRiesz.tensor_neg_ae (d := 3) N)
  have hs := (measurePreserving_sub_prod (volume : Measure T3) volume).quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [hs] with p hp
  change H N (-(p.1 - p.2)) = H N (p.1 - p.2) at hp
  simpa only [neg_sub] using hp

theorem integrable_weightedStretch (n N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    Integrable (fun p : T3 × T3 ↦ weightedStretch n (H N (p.1 - p.2))
      (fullVorticity u p.1) (fullVorticity u p.2)) ((volume : Measure T3).prod volume) := by
  have hw := continuous_fullVorticity u hu
  have ht (i j l : Fin 3) : Integrable (fun p : T3 × T3 ↦
      (PeriodicRadialRiesz.entry N i j (p.1 - p.2)).re *
        (‖fullVorticity u p.1‖ ^ n * crossEntryWeight (fullVorticity u p.1) i j l *
          fullVorticity u p.2 l)) ((volume : Measure T3).prod volume) := by
    let f : C(T3 × T3, ℝ) := ⟨fun p ↦ ‖fullVorticity u p.1‖ ^ n *
        crossEntryWeight (fullVorticity u p.1) i j l * fullVorticity u p.2 l,
      (((hw.comp continuous_fst).norm.pow n).mul
        ((VorticityRegularizedPairing.continuous_crossEntryWeight i j l).comp (hw.comp continuous_fst))).mul
          ((EuclideanSpace.proj l).continuous.comp (hw.comp continuous_snd))⟩
    exact IntegrableKernelPairing.integrable_mul ((volume : Measure T3).prod volume) _
      (integrable_entry_sub i j N) f
  have hi := integrable_finsetSum Finset.univ (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) ↦
    integrable_finsetSum Finset.univ (fun j _ ↦ integrable_finsetSum Finset.univ (fun l _ ↦ ht i j l)))
  apply hi.congr
  filter_upwards [] with p
  simp only [weightedStretch, inner_cross_tensor, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

def pairedSource (n N : ℕ) (u : FourierVelocity) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : T3, ∫ y : T3,
    pairedStretch n (H N (x - y)) (fullVorticity u x) (fullVorticity u y)

theorem source_eq_pairedSource (n N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) : source n N u = pairedSource n N u := by
  have h := integral_weightedStretch_eq_half_pair_of_integrable_of_ae_symmetry volume
    (fun x y : T3 ↦ H N (x - y)) (fullVorticity u) n
    (integrable_weightedStretch n N u hu) (tensor_sub_swap_ae N)
  change _ = pairedSource n N u at h
  rw [← h]
  unfold source
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [weightedStretch, integral_const_mul]
  congr 1
  unfold VorticityRadialQuadratic.quadraticStretch
  rw [← integral_sub_left_eq_self (fun h : T3 ↦
    ⟪EuclideanCrossProduct.cross (fullVorticity u x) (fullVorticity u (x - h)),
      H N h (fullVorticity u x)⟫) volume x]
  simp only [sub_sub_cancel]

def imageDensity (n N : ℕ) (u : FourierVelocity) (x y : T3) (z : Lat) : ℝ :=
  RadialRieszRegularization.radialCoefficient N (EuclideanSpace.single 0 1) (displacement (x - y) z) *
    EuclideanCrossProduct.tripleProduct (fullVorticity u x) (fullVorticity u y) (displacement (x - y) z) *
      ⟪displacement (x - y) z,
        RadialPower.radialPower n (fullVorticity u x) - RadialPower.radialPower n (fullVorticity u y)⟫

theorem hasSum_imageDensity (n N : ℕ) (u : FourierVelocity) (x y : T3) :
    HasSum (imageDensity n N u x y)
      (pairedStretch n (H N (x - y)) (fullVorticity u x) (fullVorticity u y)) := by
  by_cases hxy : x = y
  · subst y
    change HasSum (fun z : Lat ↦ imageDensity n N u x x z) _
    simp only [imageDensity, pairedStretch, sub_self, map_zero, inner_zero_right, mul_zero]
    exact hasSum_zero
  · exact PeriodicRadialRiesz.hasSum_pairedStretch_images N n (EuclideanSpace.single 0 1)
      (by simp) (sub_ne_zero.mpr hxy) (fullVorticity u x) (fullVorticity u y)

def imageSource (n N : ℕ) (u : FourierVelocity) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : T3, ∫ y : T3, ∑' z : Lat, imageDensity n N u x y z

theorem source_eq_imageSource (n N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) : source n N u = imageSource n N u := by
  rw [source_eq_pairedSource n N u hu]
  simp only [pairedSource, imageSource, (hasSum_imageDensity n N u _ _).tsum_eq]

theorem tendsto_imageSource (n : ℕ) (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) :
    Tendsto (fun N : ℕ ↦ imageSource n N u) atTop (𝓝 (VorticityWeightedStretching.fullStretching n u)) := by
  simpa only [← source_eq_imageSource n _ u hu] using tendsto_source n u hu hr hd

theorem tendsto_eighthMoment_imageSource (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) :
    Tendsto (fun N : ℕ ↦ imageSource 6 N u) atTop (𝓝 (LocalVorticityEighthMoment.stretching u)) :=
  tendsto_imageSource 6 u hu hr hd

end Mettapedia.FluidDynamics.NavierStokes.VorticityRadialPairing
