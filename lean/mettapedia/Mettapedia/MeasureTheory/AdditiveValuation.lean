import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Order.Disjointed

/-!
# Additivity, continuity, and measurable observations

Finite additivity and continuity from below are separate assumptions. On a
complete Boolean algebra their combination is equivalent to countable
additivity. For ordinary measures the additivity laws concern measurable
events; values of an additive content on other subsets are not observations.
-/

open Filter Set MeasureTheory
open scoped ENNReal Topology Function

namespace Mettapedia.MeasureTheory

/-- An injective additive regraduation cannot conceal a different combination law. -/
theorem combination_eq_add {combine : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞} {regrade : ℝ≥0∞ → ℝ≥0∞}
    (injective : Function.Injective regrade)
    (additive : ∀ x y, regrade (x + y) = regrade x + regrade y)
    (intertwines : ∀ x y, regrade (combine x y) = regrade x + regrade y) (x y) :
    combine x y = x + y := injective ((intertwines x y).trans (additive x y).symm)

namespace Lattice

variable {α : Type*} [CompleteBooleanAlgebra α]

/-- Zero at the empty event and additivity on disjoint pairs. -/
def DisjointAdditive (w : α → ℝ≥0∞) : Prop :=
  w ⊥ = 0 ∧ ∀ ⦃a b⦄, Disjoint a b → w (a ⊔ b) = w a + w b

/-- Countable disjoint joins, without a finite-total-mass restriction. -/
def SigmaAdditive (w : α → ℝ≥0∞) : Prop :=
  ∀ f : ℕ → α, Pairwise (Disjoint on f) → w (⨆ n, f n) = ∑' n, w (f n)

/-- Increasing event stages converge to the observation of their join. -/
def ContinuousFromBelow (w : α → ℝ≥0∞) : Prop :=
  ∀ f : ℕ → α, Monotone f → Tendsto (w ∘ f) atTop (𝓝 (w (⨆ n, f n)))

theorem continuousFromBelow_iff_iSup (w : α →o ℝ≥0∞) :
    ContinuousFromBelow w ↔ ∀ f : ℕ → α, Monotone f → w (⨆ n, f n) = ⨆ n, w (f n) := by
  constructor
  · intro h f hf
    exact tendsto_nhds_unique (h f hf) (tendsto_atTop_iSup (w.monotone.comp hf))
  · intro h f hf
    rw [h f hf]
    exact tendsto_atTop_iSup (w.monotone.comp hf)

/-- A disjoint prefix is an ordinary finite sum, with the original stages retained. -/
theorem map_partialSups (w : α → ℝ≥0∞) (additive : DisjointAdditive w)
    {f : ℕ → α} (disjoint : Pairwise (Disjoint on f)) (n : ℕ) :
    w (partialSups f n) = ∑ i ∈ Finset.range (n + 1), w (f i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      w (partialSups f (n + 1)) = w (partialSups f n ⊔ f (n + 1)) :=
        congrArg w (by simpa only [Order.succ_eq_add_one] using partialSups_succ f n)
      _ = w (partialSups f n) + w (f (n + 1)) :=
        additive.2 (partialSups_disjoint_of_disjoint f disjoint (Nat.lt_succ_self n))
      _ = _ := by rw [Finset.sum_range_succ, ih]

theorem sigmaAdditive_iff_continuousFromBelow (w : α →o ℝ≥0∞)
    (additive : DisjointAdditive w) : SigmaAdditive w ↔ ContinuousFromBelow w := by
  constructor
  · intro sigma f hf
    have values (n : ℕ) : w (f n) = ∑ i ∈ Finset.range (n + 1), w (disjointed f i) := by
      calc
        w (f n) = w (partialSups (disjointed f) n) := by
          rw [partialSups_disjointed, hf.partialSups_eq]
        _ = _ := map_partialSups w additive (disjoint_disjointed f) n
    have limit := (ENNReal.tendsto_nat_tsum (fun i => w (disjointed f i))).comp
      (tendsto_add_atTop_nat 1)
    have total := sigma (disjointed f) (disjoint_disjointed f)
    rw [iSup_disjointed] at total
    simpa only [Function.comp_def, ← values, ← total] using limit
  · intro continuous f disjoint
    have limit := continuous (partialSups f) (partialSups_monotone f)
    have sums := (ENNReal.tendsto_nat_tsum (fun i => w (f i))).comp
      (tendsto_add_atTop_nat 1)
    rw [iSup_partialSups_eq] at limit
    exact tendsto_nhds_unique limit (by
      simpa only [Function.comp_def, map_partialSups w additive disjoint] using sums)

end Lattice

/-- Additive contents whose laws apply to the declared measurable events. -/
abbrev MeasurableContent (Ω : Type*) [MeasurableSpace Ω] :=
  AddContent ℝ≥0∞ {s : Set Ω | MeasurableSet s}

namespace MeasurableContent

variable {Ω Ξ Ζ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace Ζ]

theorem events_ring : IsSetRing {s : Set Ω | MeasurableSet s} :=
  ⟨MeasurableSet.empty, fun _ _ hs ht => hs.union ht, fun _ _ hs ht => hs.diff ht⟩

/-- Globally additive lattice data also supplies the weaker measurable-event laws. -/
noncomputable def ofLattice (w : Set Ω →o ℝ≥0∞) (additive : Lattice.DisjointAdditive w) :
    MeasurableContent Ω :=
  events_ring.addContent_of_union w additive.1 (fun _ _ hd => additive.2 hd)

@[simp] theorem ofLattice_apply (w : Set Ω →o ℝ≥0∞) (ha : Lattice.DisjointAdditive w)
    (s : Set Ω) : ofLattice w ha s = w s := rfl

/-- Only measurable event families participate in this additivity law. -/
def SigmaAdditive (c : MeasurableContent Ω) : Prop :=
  ∀ f : ℕ → Set Ω, (∀ n, MeasurableSet (f n)) → Pairwise (Disjoint on f) →
    c (⋃ n, f n) = ∑' n, c (f n)

theorem ofLattice_sigmaAdditive (w : Set Ω →o ℝ≥0∞) (ha : Lattice.DisjointAdditive w)
    (hs : Lattice.SigmaAdditive w) : SigmaAdditive (ofLattice w ha) := fun f _ hd => hs f hd

/-- Continuity is required on increasing sequences of measurable events. -/
def ContinuousFromBelow (c : MeasurableContent Ω) : Prop :=
  ∀ f : ℕ → Set Ω, (∀ n, MeasurableSet (f n)) → Monotone f →
    Tendsto (fun n => c (f n)) atTop (𝓝 (c (⋃ n, f n)))

theorem continuousFromBelow_iff_iUnion (c : MeasurableContent Ω) :
    ContinuousFromBelow c ↔ ∀ f : ℕ → Set Ω, (∀ n, MeasurableSet (f n)) →
      Monotone f → c (⋃ n, f n) = ⨆ n, c (f n) := by
  have mono (f : ℕ → Set Ω) (hf : ∀ n, MeasurableSet (f n)) (hm : Monotone f) :
      Monotone (fun n => c (f n)) := fun i j hij =>
    addContent_mono events_ring.isSetSemiring (hf i) (hf j) (hm hij)
  exact ⟨fun h f hf hm => tendsto_nhds_unique (h f hf hm) (tendsto_atTop_iSup (mono f hf hm)),
    fun h f hf hm => h f hf hm ▸ tendsto_atTop_iSup (mono f hf hm)⟩

theorem sigmaAdditive_iff_continuousFromBelow (c : MeasurableContent Ω) :
    SigmaAdditive c ↔ ContinuousFromBelow c := by
  constructor
  · intro h f hf hm
    exact tendsto_atTop_addContent_iUnion_of_addContent_iUnion_eq_tsum events_ring
      (fun f hf _ hd => h f hf hd) hm hf (MeasurableSet.iUnion hf)
  · intro h f hf hd
    exact addContent_iUnion_eq_tsum_of_addContent_iUnion_eq_iSup events_ring c hd hf
      (fun _ hs hm => (continuousFromBelow_iff_iUnion c).mp h _ hs hm)

/-- Restrict an existing measure's additive laws to measurable events. -/
noncomputable def ofMeasure (μ : Measure Ω) : MeasurableContent Ω :=
  events_ring.addContent_of_union μ (measure_empty) (fun _ ht hd => measure_union hd ht)

@[simp] theorem ofMeasure_apply (μ : Measure Ω) (s : Set Ω) : ofMeasure μ s = μ s := rfl

theorem ofMeasure_sigmaAdditive (μ : Measure Ω) : SigmaAdditive (ofMeasure μ) :=
  fun _ hf hd => measure_iUnion hd hf

/-- Extend measurable-event observations by Mathlib's measure construction. -/
noncomputable def toMeasure (c : MeasurableContent Ω) (sigma : SigmaAdditive c) : Measure Ω :=
  Measure.ofMeasurable (fun s _ => c s) addContent_empty (fun f hf hd => sigma f hf hd)

@[simp] theorem toMeasure_apply (c : MeasurableContent Ω) (sigma : SigmaAdditive c)
    {s : Set Ω} (hs : MeasurableSet s) : toMeasure c sigma s = c s :=
  Measure.ofMeasurable_apply s hs

@[simp] theorem toMeasure_ofMeasure (μ : Measure Ω) :
    toMeasure (ofMeasure μ) (ofMeasure_sigmaAdditive μ) = μ :=
  Measure.ext fun _ hs => toMeasure_apply _ _ hs

@[simp] theorem ofMeasure_toMeasure_apply (c : MeasurableContent Ω) (hc : SigmaAdditive c)
    {s : Set Ω} (hs : MeasurableSet s) : ofMeasure (toMeasure c hc) s = c s :=
  toMeasure_apply c hc hs

/-- Equality of constructed measures observes exactly the measurable events. -/
theorem toMeasure_eq_iff (c d : MeasurableContent Ω)
    (hc : SigmaAdditive c) (hd : SigmaAdditive d) :
    toMeasure c hc = toMeasure d hd ↔ ∀ s, MeasurableSet s → c s = d s := by
  constructor
  · intro equal s hs
    simpa only [toMeasure_apply _ _ hs] using congrArg (fun μ : Measure Ω => μ s) equal
  · intro equal
    exact Measure.ext fun s hs => by simp only [toMeasure_apply _ _ hs, equal s hs]

/-- Push events forward by pulling their predicates back along a measurable map. -/
noncomputable def pushforward (c : MeasurableContent Ω) (f : Ω → Ξ) (hf : Measurable f) :
    MeasurableContent Ξ :=
  events_ring.addContent_of_union (fun s => c (f ⁻¹' s)) (by simp)
    (fun hs ht hd => by
      simpa only [preimage_union] using
        addContent_union events_ring (hs.preimage hf) (ht.preimage hf) (hd.preimage f))

@[simp] theorem pushforward_apply (c : MeasurableContent Ω) (f : Ω → Ξ)
    (hf : Measurable f) (s : Set Ξ) : pushforward c f hf s = c (f ⁻¹' s) := rfl

theorem pushforward_sigmaAdditive (c : MeasurableContent Ω) (hc : SigmaAdditive c)
    (f : Ω → Ξ) (hf : Measurable f) : SigmaAdditive (pushforward c f hf) := by
  intro sets hs hd
  simpa only [pushforward_apply, preimage_iUnion] using
    hc (fun n => f ⁻¹' sets n) (fun n => (hs n).preimage hf) (fun _ _ hij => (hd hij).preimage f)

theorem toMeasure_pushforward (c : MeasurableContent Ω) (hc : SigmaAdditive c)
    (f : Ω → Ξ) (hf : Measurable f) :
    toMeasure (pushforward c f hf) (pushforward_sigmaAdditive c hc f hf) =
      (toMeasure c hc).map f := by
  ext s hs
  simp only [toMeasure_apply _ _ hs, pushforward_apply, Measure.map_apply hf hs,
    toMeasure_apply _ _ (hs.preimage hf)]

theorem pushforward_comp (c : MeasurableContent Ω) (f : Ω → Ξ) (hf : Measurable f)
    (g : Ξ → Ζ) (hg : Measurable g) :
    pushforward (pushforward c f hf) g hg = pushforward c (g ∘ f) (hg.comp hf) :=
  AddContent.ext fun _ => rfl

@[simp] theorem pushforward_id (c : MeasurableContent Ω) :
    pushforward c id measurable_id = c := AddContent.ext fun _ => rfl

end MeasurableContent

end Mettapedia.MeasureTheory
