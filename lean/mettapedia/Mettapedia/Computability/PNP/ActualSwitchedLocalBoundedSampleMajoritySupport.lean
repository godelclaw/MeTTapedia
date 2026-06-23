import Mettapedia.Computability.PNP.ActualSwitchedLocalPluginSampleMajorityObstruction

/-!
# PNP bounded sample-majority support lemmas

Exact-visible rule finiteness plus sample-vote, omitted-input, and support-cardinality facts for plug-in majority predictors.
-/

namespace Mettapedia.Computability.PNP

universe v

/-- The exact-visible Boolean rule cube is finite whenever the hidden alphabet
is finite.  The global function-space instance needs decidable equality on the
domain; this instance packages the classical choice at the exact-visible layer. -/
noncomputable instance instFintypeExactVisibleRule
    (Z : Type v) (k : ℕ) [Fintype Z] :
    Fintype (ExactVisibleRule Z k) := by
  classical
  unfold ExactVisibleRule ExactVisiblePostSwitchSurface
  infer_instance

namespace PluginSampleMajority

/-- The graph sample uses exactly one labeled example for each input. -/
theorem length_graphSample {U : Type v} [Fintype U] (rule : U → Bool) :
    (graphSample rule).length = Fintype.card U := by
  simp [graphSample]

/-- Sample-level plug-in majority with an explicit tie-breaking default. -/
def predictWithDefault {U : Type v} [DecidableEq U]
    (default : Bool) (sample : Sample U Bool) (u : U) : Bool :=
  if trueVotes sample u = falseVotes sample u then
    default
  else if falseVotes sample u < trueVotes sample u then
    true
  else
    false

/-- Sample-level plug-in majority with an input-dependent fallback used only on
ties.  This is the natural formal target for attempts to repair a bad fixed
tie-break by choosing the tie-break as a visible-input function. -/
def predictWithFallback {U : Type v} [DecidableEq U]
    (fallback : U → Bool) (sample : Sample U Bool) (u : U) : Bool :=
  if trueVotes sample u = falseVotes sample u then
    fallback u
  else if falseVotes sample u < trueVotes sample u then
    true
  else
    false

@[simp] theorem predictWithDefault_graphSample
    {U : Type v} [Fintype U] [DecidableEq U]
    (default : Bool) (rule : U → Bool) (u : U) :
    predictWithDefault default (graphSample rule) u = rule u := by
  cases h : rule u <;>
    simp [predictWithDefault, trueVotes_graphSample, falseVotes_graphSample, h]

@[simp] theorem predictWithFallback_graphSample
    {U : Type v} [Fintype U] [DecidableEq U]
    (fallback rule : U → Bool) (u : U) :
    predictWithFallback fallback (graphSample rule) u = rule u := by
  cases h : rule u <;>
    simp [predictWithFallback, trueVotes_graphSample, falseVotes_graphSample, h]

@[simp] theorem predictWithFallback_nil
    {U : Type v} [DecidableEq U] (fallback : U → Bool) (u : U) :
    predictWithFallback fallback ([] : Sample U Bool) u = fallback u := by
  simp [predictWithFallback, trueVotes, falseVotes]

/-- The sample that labels exactly the points in a chosen finite support. -/
noncomputable def supportSample {U : Type v}
    (support : Finset U) (rule : U → Bool) : Sample U Bool :=
  support.toList.map (fun u => (u, rule u))

@[simp] theorem length_supportSample {U : Type v}
    (support : Finset U) (rule : U → Bool) :
    (supportSample support rule).length = support.card := by
  simp [supportSample]

@[simp] theorem mem_map_fst_supportSample
    {U : Type v} {support : Finset U} {rule : U → Bool} {u : U} :
    u ∈ (supportSample support rule).map Prod.fst ↔ u ∈ support := by
  simp [supportSample]

theorem trueVotes_supportSample {U : Type v} [DecidableEq U]
    (support : Finset U) (rule : U → Bool) (u : U) :
    trueVotes (supportSample support rule) u =
      if u ∈ support then
        if rule u then 1 else 0
      else 0 := by
  by_cases hu : u ∈ support
  · by_cases h : rule u
    · have hcount : support.toList.count u = 1 := by
        exact List.count_eq_one_of_mem
          support.nodup_toList (by simpa using hu)
      rw [List.count_eq_countP] at hcount
      rw [trueVotes, supportSample, List.countP_map]
      have hcongr :
          List.countP
              ((fun ex : U × Bool => decide (ex.1 = u ∧ ex.2 = true)) ∘
                fun v => (v, rule v))
              support.toList =
            List.countP (fun v => v == u) support.toList := by
        apply List.countP_congr
        intro v _hv
        by_cases hvu : v = u
        · subst hvu
          simp [h]
        · simp [hvu]
      rw [hcongr]
      simpa [hu, h] using hcount
    · rw [trueVotes, supportSample, List.countP_map]
      simp [hu, h]
      intro v _hv hvu
      subst hvu
      exact Bool.eq_false_of_not_eq_true h
  · have hzero :
        trueVotes (supportSample support rule) u = 0 := by
      rw [trueVotes]
      exact List.countP_eq_zero.mpr (by
        intro ex hex hp
        rcases List.mem_map.mp hex with ⟨v, hv, rfl⟩
        have hp' : v = u ∧ rule v = true := of_decide_eq_true hp
        exact hu (by
          simpa [hp'.1] using hv))
    simpa [hu] using hzero

theorem falseVotes_supportSample {U : Type v} [DecidableEq U]
    (support : Finset U) (rule : U → Bool) (u : U) :
    falseVotes (supportSample support rule) u =
      if u ∈ support then
        if rule u then 0 else 1
      else 0 := by
  by_cases hu : u ∈ support
  · by_cases h : rule u
    · rw [falseVotes, supportSample, List.countP_map]
      simp [hu, h]
      intro v _hv hvu
      subst hvu
      exact h
    · have hcount : support.toList.count u = 1 := by
        exact List.count_eq_one_of_mem
          support.nodup_toList (by simpa using hu)
      rw [List.count_eq_countP] at hcount
      rw [falseVotes, supportSample, List.countP_map]
      have hcongr :
          List.countP
              ((fun ex : U × Bool => decide (ex.1 = u ∧ ex.2 = false)) ∘
                fun v => (v, rule v))
              support.toList =
            List.countP (fun v => v == u) support.toList := by
        apply List.countP_congr
        intro v _hv
        by_cases hvu : v = u
        · subst hvu
          simp [h]
        · simp [hvu]
      rw [hcongr]
      simpa [hu, h] using hcount
  · have hzero :
        falseVotes (supportSample support rule) u = 0 := by
      rw [falseVotes]
      exact List.countP_eq_zero.mpr (by
        intro ex hex hp
        rcases List.mem_map.mp hex with ⟨v, hv, rfl⟩
        have hp' : v = u ∧ rule v = false := of_decide_eq_true hp
        exact hu (by
          simpa [hp'.1] using hv))
    simpa [hu] using hzero

/-- Sampling exactly an override support realizes any rule that agrees with
the fallback off that support. -/
theorem predictWithFallback_supportSample_eq_of_eq_off_support
    {U : Type v} [DecidableEq U]
    (fallback rule : U → Bool) (support : Finset U)
    (hoff : ∀ u : U, u ∉ support → fallback u = rule u) :
    predictWithFallback fallback (supportSample support rule) = rule := by
  funext u
  by_cases hu : u ∈ support
  · cases h : rule u <;>
      simp [predictWithFallback, trueVotes_supportSample,
        falseVotes_supportSample, hu, h]
  · simp [predictWithFallback, trueVotes_supportSample,
      falseVotes_supportSample, hu, hoff u hu]

/-- A sample shorter than a finite input alphabet omits some input. -/
theorem exists_not_mem_map_fst_of_length_lt_card {U : Type v} [Fintype U] [DecidableEq U]
    {sample : Sample U Bool} (hlen : sample.length < Fintype.card U) :
    ∃ u : U, u ∉ sample.map Prod.fst := by
  by_contra hnone
  push_neg at hnone
  have huniv : (sample.map Prod.fst).toFinset = (Finset.univ : Finset U) := by
    exact Finset.eq_univ_iff_forall.mpr (by
      intro x
      simpa using hnone x)
  have hcard : Fintype.card U ≤ sample.length := by
    calc
      Fintype.card U = ((sample.map Prod.fst).toFinset).card := by
        simp [huniv]
      _ ≤ (sample.map Prod.fst).length := List.toFinset_card_le (sample.map Prod.fst)
      _ = sample.length := by
        simp
  exact (not_lt_of_ge hcard) hlen

/-- If an input never occurs in the sample, it has no true votes. -/
theorem trueVotes_eq_zero_of_not_mem_map_fst {U : Type v} [DecidableEq U]
    {sample : Sample U Bool} {u : U} (h : u ∉ sample.map Prod.fst) :
    trueVotes sample u = 0 := by
  rw [trueVotes]
  exact List.countP_eq_zero.mpr (by
    intro ex hex hp
    have hp' : ex.1 = u ∧ ex.2 = true := by
      simpa using hp
    exact h (List.mem_map.mpr ⟨ex, hex, hp'.1⟩))

/-- If an input never occurs in the sample, it has no false votes. -/
theorem falseVotes_eq_zero_of_not_mem_map_fst {U : Type v} [DecidableEq U]
    {sample : Sample U Bool} {u : U} (h : u ∉ sample.map Prod.fst) :
    falseVotes sample u = 0 := by
  rw [falseVotes]
  exact List.countP_eq_zero.mpr (by
    intro ex hex hp
    have hp' : ex.1 = u ∧ ex.2 = false := by
      simpa using hp
    exact h (List.mem_map.mpr ⟨ex, hex, hp'.1⟩))

/-- On an input omitted by the sample, the tie-breaking plug-in majority
predicts `true`. -/
theorem predict_eq_true_of_not_mem_map_fst {U : Type v} [DecidableEq U]
    {sample : Sample U Bool} {u : U} (h : u ∉ sample.map Prod.fst) :
    predict sample u = true := by
  have hf : falseVotes sample u = 0 := falseVotes_eq_zero_of_not_mem_map_fst h
  simp [predict, counts, PluginMajorityCounts.predict, hf]

/-- On an input omitted by the sample, the explicit-default plug-in majority
returns exactly the default. -/
theorem predictWithDefault_eq_default_of_not_mem_map_fst
    {U : Type v} [DecidableEq U] {default : Bool}
    {sample : Sample U Bool} {u : U} (h : u ∉ sample.map Prod.fst) :
    predictWithDefault default sample u = default := by
  have ht : trueVotes sample u = 0 := trueVotes_eq_zero_of_not_mem_map_fst h
  have hf : falseVotes sample u = 0 := falseVotes_eq_zero_of_not_mem_map_fst h
  simp [predictWithDefault, ht, hf]

/-- On an input omitted by the sample, an input-dependent fallback plug-in
majority returns the fallback rule. -/
theorem predictWithFallback_eq_fallback_of_not_mem_map_fst
    {U : Type v} [DecidableEq U] {fallback : U → Bool}
    {sample : Sample U Bool} {u : U} (h : u ∉ sample.map Prod.fst) :
    predictWithFallback fallback sample u = fallback u := by
  have ht : trueVotes sample u = 0 := trueVotes_eq_zero_of_not_mem_map_fst h
  have hf : falseVotes sample u = 0 := falseVotes_eq_zero_of_not_mem_map_fst h
  simp [predictWithFallback, ht, hf]

/-- Every sample shorter than the finite alphabet has at least one input on
which plug-in majority predicts `true`. -/
theorem exists_true_prediction_of_length_lt_card {U : Type v} [Fintype U] [DecidableEq U]
    {sample : Sample U Bool} (hlen : sample.length < Fintype.card U) :
    ∃ u : U, predict sample u = true := by
  rcases exists_not_mem_map_fst_of_length_lt_card (sample := sample) hlen with ⟨u, hu⟩
  exact ⟨u, predict_eq_true_of_not_mem_map_fst hu⟩

/-- The finite set of inputs on which a Boolean rule returns `false`. -/
def falseSupport {U : Type v} [Fintype U] (rule : U → Bool) :
    Finset U :=
  (Finset.univ : Finset U).filter (fun u => rule u = false)

@[simp] theorem mem_falseSupport {U : Type v} [Fintype U]
    {rule : U → Bool} {u : U} :
    u ∈ falseSupport rule ↔ rule u = false := by
  simp [falseSupport]

/-- The finite set of inputs on which a Boolean rule differs from a chosen
default value. -/
def nondefaultSupport {U : Type v} [Fintype U] (default : Bool) (rule : U → Bool) :
    Finset U :=
  (Finset.univ : Finset U).filter (fun u => rule u ≠ default)

/-- The finite set of inputs on which one Boolean rule differs from a reference
rule. -/
def disagreementSupport {U : Type v} [Fintype U] (reference rule : U → Bool) :
    Finset U :=
  (Finset.univ : Finset U).filter (fun u => rule u ≠ reference u)

@[simp] theorem mem_nondefaultSupport {U : Type v} [Fintype U]
    {default : Bool} {rule : U → Bool} {u : U} :
    u ∈ nondefaultSupport default rule ↔ rule u ≠ default := by
  simp [nondefaultSupport]

@[simp] theorem mem_disagreementSupport {U : Type v} [Fintype U]
    {reference rule : U → Bool} {u : U} :
    u ∈ disagreementSupport reference rule ↔ rule u ≠ reference u := by
  simp [disagreementSupport]

/-- A disagreement support never has more points than the finite input
alphabet. -/
theorem disagreementSupport_card_le_card {U : Type v} [Fintype U]
    (reference rule : U → Bool) :
    (disagreementSupport reference rule).card ≤ Fintype.card U := by
  classical
  simpa [Finset.card_univ] using
    (Finset.card_le_univ (s := disagreementSupport reference rule))

/-- The rule constantly opposite to the chosen default differs from that default
at every finite input. -/
theorem nondefaultSupport_const_not_card
    {U : Type v} [Fintype U] (default : Bool) :
    (nondefaultSupport default (fun _ : U => !default)).card = Fintype.card U := by
  cases default <;> simp [nondefaultSupport]

/-- If sample-level plug-in majority predicts `false` at an input, then that
input must occur in the sample.  Omitted inputs tie at zero votes and therefore
predict `true`. -/
theorem mem_map_fst_of_predict_eq_false {U : Type v} [DecidableEq U]
    {sample : Sample U Bool} {u : U} (hfalse : predict sample u = false) :
    u ∈ sample.map Prod.fst := by
  by_contra hmissing
  have htrue : predict sample u = true :=
    predict_eq_true_of_not_mem_map_fst (sample := sample) (u := u) hmissing
  rw [hfalse] at htrue
  cases htrue

/-- If explicit-default sample-level plug-in majority differs from the default
at an input, then that input must occur in the sample. -/
theorem mem_map_fst_of_predictWithDefault_ne_default
    {U : Type v} [DecidableEq U] {default : Bool}
    {sample : Sample U Bool} {u : U}
    (hne : predictWithDefault default sample u ≠ default) :
    u ∈ sample.map Prod.fst := by
  by_contra hmissing
  exact hne (predictWithDefault_eq_default_of_not_mem_map_fst hmissing)

/-- If input-dependent fallback plug-in majority differs from its fallback at
an input, then that input must occur in the sample. -/
theorem mem_map_fst_of_predictWithFallback_ne_fallback
    {U : Type v} [DecidableEq U] {fallback : U → Bool}
    {sample : Sample U Bool} {u : U}
    (hne : predictWithFallback fallback sample u ≠ fallback u) :
    u ∈ sample.map Prod.fst := by
  by_contra hmissing
  exact hne (predictWithFallback_eq_fallback_of_not_mem_map_fst hmissing)

/-- The false-support of any sample-level plug-in majority prediction is
contained in the set of visible inputs that appear in the sample. -/
theorem falseSupport_predict_subset_sampleInputs
    {U : Type v} [Fintype U] [DecidableEq U] (sample : Sample U Bool) :
    falseSupport (fun u : U => predict sample u) ⊆
      (sample.map Prod.fst).toFinset := by
  intro u hu
  have hfalse : predict sample u = false := by
    simpa using (mem_falseSupport (rule := fun u : U => predict sample u) (u := u)).1 hu
  have hmem : u ∈ sample.map Prod.fst :=
    mem_map_fst_of_predict_eq_false (sample := sample) (u := u) hfalse
  simpa using hmem

/-- Therefore a sample-level plug-in majority predictor can be false on at most
`sample.length` distinct inputs. -/
theorem falseSupport_predict_card_le_length
    {U : Type v} [Fintype U] [DecidableEq U] (sample : Sample U Bool) :
    (falseSupport (fun u : U => predict sample u)).card ≤ sample.length := by
  calc
    (falseSupport (fun u : U => predict sample u)).card
        ≤ ((sample.map Prod.fst).toFinset).card :=
          Finset.card_le_card (falseSupport_predict_subset_sampleInputs sample)
    _ ≤ (sample.map Prod.fst).length := List.toFinset_card_le (sample.map Prod.fst)
    _ = sample.length := by
          simp

/-- The nondefault support of any explicit-default sample-level plug-in majority
prediction is contained in the set of visible inputs that appear in the sample. -/
theorem nondefaultSupport_predictWithDefault_subset_sampleInputs
    {U : Type v} [Fintype U] [DecidableEq U]
    (default : Bool) (sample : Sample U Bool) :
    nondefaultSupport default (fun u : U => predictWithDefault default sample u) ⊆
      (sample.map Prod.fst).toFinset := by
  intro u hu
  have hne : predictWithDefault default sample u ≠ default := by
    simpa using
      (mem_nondefaultSupport
        (default := default)
        (rule := fun u : U => predictWithDefault default sample u) (u := u)).1 hu
  have hmem : u ∈ sample.map Prod.fst :=
    mem_map_fst_of_predictWithDefault_ne_default
      (default := default) (sample := sample) (u := u) hne
  simpa using hmem

/-- The disagreement support of an input-dependent fallback plug-in majority
prediction is contained in the set of visible inputs that appear in the sample. -/
theorem disagreementSupport_predictWithFallback_subset_sampleInputs
    {U : Type v} [Fintype U] [DecidableEq U]
    (fallback : U → Bool) (sample : Sample U Bool) :
    disagreementSupport fallback (fun u : U => predictWithFallback fallback sample u) ⊆
      (sample.map Prod.fst).toFinset := by
  intro u hu
  have hne : predictWithFallback fallback sample u ≠ fallback u := by
    simpa using
      (mem_disagreementSupport
        (reference := fallback)
        (rule := fun u : U => predictWithFallback fallback sample u) (u := u)).1 hu
  have hmem : u ∈ sample.map Prod.fst :=
    mem_map_fst_of_predictWithFallback_ne_fallback
      (fallback := fallback) (sample := sample) (u := u) hne
  simpa using hmem

/-- Therefore an explicit-default sample-level plug-in majority predictor can
differ from the default on at most `sample.length` distinct inputs. -/
theorem nondefaultSupport_predictWithDefault_card_le_length
    {U : Type v} [Fintype U] [DecidableEq U]
    (default : Bool) (sample : Sample U Bool) :
    (nondefaultSupport default
      (fun u : U => predictWithDefault default sample u)).card ≤ sample.length := by
  calc
    (nondefaultSupport default
        (fun u : U => predictWithDefault default sample u)).card
        ≤ ((sample.map Prod.fst).toFinset).card :=
          Finset.card_le_card
            (nondefaultSupport_predictWithDefault_subset_sampleInputs default sample)
    _ ≤ (sample.map Prod.fst).length := List.toFinset_card_le (sample.map Prod.fst)
    _ = sample.length := by
          simp

/-- Therefore an input-dependent fallback plug-in majority predictor can differ
from its fallback on at most `sample.length` distinct inputs. -/
theorem disagreementSupport_predictWithFallback_card_le_length
    {U : Type v} [Fintype U] [DecidableEq U]
    (fallback : U → Bool) (sample : Sample U Bool) :
    (disagreementSupport fallback
      (fun u : U => predictWithFallback fallback sample u)).card ≤ sample.length := by
  calc
    (disagreementSupport fallback
        (fun u : U => predictWithFallback fallback sample u)).card
        ≤ ((sample.map Prod.fst).toFinset).card :=
          Finset.card_le_card
            (disagreementSupport_predictWithFallback_subset_sampleInputs fallback sample)
    _ ≤ (sample.map Prod.fst).length := List.toFinset_card_le (sample.map Prod.fst)
    _ = sample.length := by
          simp

end PluginSampleMajority

end Mettapedia.Computability.PNP
