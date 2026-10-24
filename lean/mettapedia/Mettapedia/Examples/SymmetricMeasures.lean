import Mettapedia.MeasureTheory.Integration
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Concrete measures and the boundaries of their observations

The examples use existing Lebesgue, counting, and Gaussian measures. Their
contents inherit laws on measurable events and reconstruct the original
measures. Normalization, translation invariance, and Haar positivity remain
distinct properties; a Gaussian's translated mean is observable.
-/

noncomputable section

open MeasureTheory Set Mettapedia.MeasureTheory
open Mettapedia.MeasureTheory.MeasurableContent
open scoped ENNReal NNReal Classical

namespace Mettapedia.Examples

/-- Lebesgue measure restricted to the unit interval, on the real line. -/
def unitIntervalContent : MeasurableContent ℝ := ofMeasure (volume.restrict (Icc 0 1))

theorem unitInterval_sigmaAdditive : SigmaAdditive unitIntervalContent := ofMeasure_sigmaAdditive _

theorem unitInterval_roundTrip :
    toMeasure unitIntervalContent unitInterval_sigmaAdditive = volume.restrict (Icc 0 1) :=
  toMeasure_ofMeasure _

theorem unitInterval_total : unitIntervalContent univ = 1 := by
  simp [unitIntervalContent, Real.volume_Icc]

theorem unitInterval_half : unitIntervalContent (Icc 0 (1 / 2 : ℝ)) = 1 / 2 := by
  simp only [unitIntervalContent, ofMeasure_apply, Measure.restrict_apply measurableSet_Icc,
    Icc_inter_Icc, Real.volume_Icc]
  norm_num [ENNReal.ofReal_div_of_pos]

/-- Lebesgue measure itself, unlike its restriction, is additive Haar measure. -/
theorem volume_addHaar : Measure.IsAddHaarMeasure (volume : Measure ℝ) := inferInstance

/-- Normalized counting measure; on the empty type it is the zero measure. -/
def uniformContent (n : ℕ) [MeasurableSpace (Fin n)] : MeasurableContent (Fin n) :=
  ofMeasure ((n : ℝ≥0∞)⁻¹ • Measure.count)

theorem uniformContent_sigmaAdditive (n : ℕ) [MeasurableSpace (Fin n)] :
    SigmaAdditive (uniformContent n) := ofMeasure_sigmaAdditive _

theorem uniformContent_apply (n : ℕ) [MeasurableSpace (Fin n)] {s : Set (Fin n)}
    (hs : MeasurableSet s) : uniformContent n s = s.encard / n := by
  simp [uniformContent, Measure.count_apply hs, div_eq_mul_inv, mul_comm]

theorem uniformContent_singleton (n : ℕ) [MeasurableSpace (Fin n)]
    [MeasurableSingletonClass (Fin n)] (i : Fin n) : uniformContent n {i} = 1 / n := by
  simp [uniformContent_apply n (measurableSet_singleton i)]

theorem uniformContent_total (n : ℕ) [MeasurableSpace (Fin n)] (hn : n ≠ 0) :
    uniformContent n univ = 1 := by
  simpa [uniformContent, Measure.count_univ, ENat.card_eq_coe_fintype_card] using
    ENNReal.inv_mul_cancel (show (n : ℝ≥0∞) ≠ 0 by exact_mod_cast hn) (by simp)

theorem uniformContent_empty [MeasurableSpace (Fin 0)] : uniformContent 0 = ofMeasure 0 := by
  apply AddContent.ext
  intro s
  have empty : s = ∅ := Set.eq_empty_of_isEmpty s
  simp [empty]

/-- All variance parameters, including zero, use Mathlib's Gaussian measure. -/
def gaussianContent (mean : ℝ) (variance : ℝ≥0) : MeasurableContent ℝ :=
  ofMeasure (ProbabilityTheory.gaussianReal mean variance)

theorem gaussianContent_sigmaAdditive (mean : ℝ) (variance : ℝ≥0) :
    SigmaAdditive (gaussianContent mean variance) := ofMeasure_sigmaAdditive _

theorem gaussianContent_total (mean : ℝ) (variance : ℝ≥0) :
    gaussianContent mean variance univ = 1 := by simp [gaussianContent]

theorem gaussianContent_roundTrip (mean : ℝ) (variance : ℝ≥0) :
    toMeasure (gaussianContent mean variance) (gaussianContent_sigmaAdditive mean variance) =
      ProbabilityTheory.gaussianReal mean variance := toMeasure_ofMeasure _

theorem gaussianContent_zeroVariance (mean : ℝ) :
    gaussianContent mean 0 = ofMeasure (Measure.dirac mean) := by simp [gaussianContent]

theorem gaussianContent_translate (mean shift : ℝ) (variance : ℝ≥0) :
    toMeasure (pushforward (gaussianContent mean variance) (shift + ·) (measurable_const_add shift))
      (pushforward_sigmaAdditive _ (gaussianContent_sigmaAdditive mean variance) _ _) =
      ProbabilityTheory.gaussianReal (mean + shift) variance := by
  rw [toMeasure_pushforward _ (gaussianContent_sigmaAdditive mean variance) _ _, gaussianContent_roundTrip]
  exact ProbabilityTheory.gaussianReal_map_const_add shift

theorem gaussianContent_not_invariant (mean : ℝ) (variance : ℝ≥0) :
    ¬ Measure.IsAddLeftInvariant (toMeasure (gaussianContent mean variance)
      (gaussianContent_sigmaAdditive mean variance)) := by
  intro invariant
  let _ := invariant
  have moved := invariant.map_add_left_eq_self (1 : ℝ)
  rw [gaussianContent_roundTrip, ProbabilityTheory.gaussianReal_map_const_add] at moved
  have means := (ProbabilityTheory.gaussianReal_ext_iff.mp moved).1
  linarith

/-- Left invariance alone does not ensure the positivity required of Haar measure. -/
theorem zero_invariant_not_haar : Measure.IsAddLeftInvariant (0 : Measure ℝ) ∧
    ¬ Measure.IsAddHaarMeasure (0 : Measure ℝ) := by
  refine ⟨⟨fun _ => Measure.map_zero _⟩, fun haar => ?_⟩
  let _ := haar
  have positive := isOpen_univ.measure_pos (μ := (0 : Measure ℝ)) Set.univ_nonempty
  exact lt_irrefl (0 : ℝ≥0∞) positive

/-- Repeated events retain one union, rather than two additive contributions. -/
theorem overlap_mass : unitIntervalContent (univ ∪ univ) ≠
    unitIntervalContent univ + unitIntervalContent univ := by
  norm_num [unitInterval_total]

/-- A finitely additive weight whose mass escapes every finite stage. -/
def infiniteOnly : Set ℕ →o ℝ≥0∞ where
  toFun s := if s.Finite then 0 else ∞
  monotone' := by
    intro s t h
    by_cases ht : t.Finite
    · simp [ht, ht.subset h]
    · simp [ht]

@[simp] theorem infiniteOnly_apply (s : Set ℕ) :
    infiniteOnly s = if s.Finite then 0 else ∞ := rfl

theorem infiniteOnly_additive : Lattice.DisjointAdditive infiniteOnly := by
  refine ⟨by simp, fun {s t} _ => ?_⟩
  by_cases hs : s.Finite <;> by_cases ht : t.Finite <;> simp [finite_union, hs, ht]

theorem infiniteOnly_not_sigmaAdditive : ¬ Lattice.SigmaAdditive infiniteOnly := by
  intro sigma
  have total := sigma (fun n : ℕ => ({n} : Set ℕ))
    (fun _ _ different => disjoint_singleton.mpr different)
  have union : (⋃ n : ℕ, ({n} : Set ℕ)) = univ := by ext; simp
  simp [union, Set.infinite_univ] at total

theorem infiniteOnly_not_continuous : ¬ Lattice.ContinuousFromBelow infiniteOnly :=
  fun continuous => infiniteOnly_not_sigmaAdditive
    ((Lattice.sigmaAdditive_iff_continuousFromBelow infiniteOnly infiniteOnly_additive).mpr continuous)

/-- Two distinguishable points equipped with the coarse event algebra. -/
inductive CoarseBool | no | yes

instance : MeasurableSpace CoarseBool := ⊥

/-- Off-domain values are deliberately retained, but are not measurable observations. -/
def coarseContent (offDomain : ℝ≥0∞) : MeasurableContent CoarseBool :=
  events_ring.addContent_of_union (fun s => if MeasurableSet s then 0 else offDomain)
    (by simp) (fun {s t} (hs : MeasurableSet s) (ht : MeasurableSet t) _ => by
      simp [hs, ht, hs.union ht])

@[simp] theorem coarseContent_apply (offDomain : ℝ≥0∞) (s : Set CoarseBool) :
    coarseContent offDomain s = if MeasurableSet s then 0 else offDomain := rfl

theorem coarseContent_sigmaAdditive (offDomain : ℝ≥0∞) : SigmaAdditive (coarseContent offDomain) := by
  intro sets hs _
  change (if MeasurableSet (⋃ n, sets n) then 0 else offDomain) =
    ∑' n, if MeasurableSet (sets n) then 0 else offDomain
  simp [hs, MeasurableSet.iUnion hs]

/-- Equal extensions need not identify raw contents outside the measurable domain. -/
theorem coarseContent_collision : coarseContent 0 ≠ coarseContent 1 ∧
    toMeasure (coarseContent 0) (coarseContent_sigmaAdditive 0) =
      toMeasure (coarseContent 1) (coarseContent_sigmaAdditive 1) := by
  have notMeasurable : ¬ MeasurableSet ({CoarseBool.yes} : Set CoarseBool) := by
    rw [MeasurableSpace.measurableSet_bot_iff]
    rintro (empty | full)
    · simpa using congrArg (fun s : Set CoarseBool => CoarseBool.yes ∈ s) empty
    · simpa using congrArg (fun s : Set CoarseBool => CoarseBool.no ∈ s) full
  constructor
  · intro equal
    have values := congrArg (fun c : MeasurableContent CoarseBool => c {CoarseBool.yes}) equal
    simp only [coarseContent_apply, if_neg notMeasurable, zero_ne_one] at values
  · apply (toMeasure_eq_iff _ _ _ _).mpr
    intro s hs
    simp [hs]

end Mettapedia.Examples
