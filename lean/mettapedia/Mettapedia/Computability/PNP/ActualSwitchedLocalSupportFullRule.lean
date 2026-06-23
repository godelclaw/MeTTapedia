import Mettapedia.Computability.PNP.ActualSwitchedLocalSupportTransfer
import Mettapedia.Computability.PNP.ActualSwitchedLocalSupportAdaptive

/-!
# Full-rule support obstruction

The arbitrary-support full-rule construction and the exact-decoder/property/query
factorization obstructions for missed exact-visible inputs.
-/

namespace Mettapedia.Computability.PNP

universe v u w

section FiniteObservedSupportFullRule

variable {Z : Type v} {k : ℕ}
variable {Block : Type*}

/-- An actual-local interface over an arbitrary block support whose selected
local rules are still the full exact-visible Boolean rule family.  The observed
block output only probes `rule` through `visibleOf`; all values outside the
image of `visibleOf` remain unconstrained by the observed output. -/
def supportFullRuleActualSwitchedLocalInterface
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k) :
    ActualSwitchedLocalInterface
      Z k (ExactVisibleRule Z k) Block where
  zOf := fun phi => (visibleOf phi).z
  aOf := fun _ phi => (visibleOf phi).a
  bOf := fun phi => (visibleOf phi).b
  localRule := fun rule u => rule u
  output := fun rule phi => rule (visibleOf phi)
  output_eq_local := by
    intro rule phi
    cases visibleOf phi
    rfl

@[simp] theorem supportFullRule_predictorFamily
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k) :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily =
      fullExactVisibleRuleFamily Z k := by
  rfl

theorem supportFullRule_surjective
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k) :
    Function.Surjective
      (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.predict := by
  simpa using fullExactVisibleRuleFamily_surjective Z k

/-- The observed block-output family has a truth-table budget bounded by the
size of the actual block support. -/
theorem supportFullRule_outputFamily_hasBitBudget_card
    [Fintype Block] (visibleOf : Block → ExactVisiblePostSwitchSurface Z k) :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.HasBitBudget
      (Fintype.card Block) := by
  simpa using
    (IndexedPredictorFamily.hasBitBudget_card_of_fintype
      (Index := ExactVisibleRule Z k) (View := Block)
      ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily))

/-- Equivalently, the observed block-output family has a predictor cover of
size at most `2 ^ |Block|`. -/
theorem supportFullRule_outputFamily_finitePredictorCover_card
    [Fintype Block] (visibleOf : Block → ExactVisiblePostSwitchSurface Z k) :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.FinitePredictorCover
      (2 ^ Fintype.card Block) := by
  have hbudget :=
    supportFullRule_outputFamily_hasBitBudget_card
      (Z := Z) (k := k) (Block := Block) visibleOf
  simpa using
    (IndexedPredictorFamily.hasBitBudget_iff_finitePredictorCover.mp hbudget)

/-- The observed block-output family is exactly the pullback of the full
exact-visible local-rule family along the reachable-support map `visibleOf`. -/
theorem supportFullRule_outputFamily_factorsThrough_predictorFamily
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k) :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.FactorsThrough
      visibleOf (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily := by
  intro rule phi
  rfl

/-- If the reachable-support map misses an exact-visible input, two distinct
exact-visible rules have identical observed block-output behaviour. -/
theorem supportFullRule_exists_distinct_rules_same_outputFamily_of_not_surjective
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hnot : ¬ Function.Surjective visibleOf) :
    ∃ rule₀ rule₁ : ExactVisibleRule Z k,
      rule₀ ≠ rule₁ ∧
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
          (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁ ∧
        (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.predict rule₀ ≠
          (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.predict rule₁ := by
  classical
  simp only [Function.Surjective, not_forall] at hnot
  rcases hnot with ⟨u₀, hmissExists⟩
  have hmiss : ∀ phi, visibleOf phi ≠ u₀ := by
    intro phi hphi
    exact hmissExists ⟨phi, hphi⟩
  let rule₀ : ExactVisibleRule Z k := fun _ => false
  let rule₁ : ExactVisibleRule Z k := fun u => if u = u₀ then true else false
  refine ⟨rule₀, rule₁, ?_, ?_, ?_⟩
  · intro heq
    have hpoint := congrFun heq u₀
    simp [rule₀, rule₁] at hpoint
  · funext phi
    simp [ActualSwitchedLocalInterface.outputFamily,
      supportFullRuleActualSwitchedLocalInterface, rule₀, rule₁, hmiss phi]
  · intro heq
    have hpoint := congrFun heq u₀
    simp [supportFullRuleActualSwitchedLocalInterface, rule₀, rule₁] at hpoint

/-- Exact recovery from observed block-output behaviour forces the support map
to hit every exact-visible input. -/
theorem supportFullRule_observedRuleMap_injective_forces_visibleOf_surjective
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hinj :
      Function.Injective
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict) :
    Function.Surjective visibleOf := by
  by_contra hnot
  rcases
    supportFullRule_exists_distinct_rules_same_outputFamily_of_not_surjective
      (Z := Z) (k := k) (Block := Block) visibleOf hnot with
    ⟨rule₀, rule₁, hne, hsame, _hdiff⟩
  exact hne (hinj hsame)

/-- Any decoder that reconstructs every full exact-visible rule from its
observed block-output trace forces the support map to hit every exact-visible
input.  This is the decoder form of the quotient-loss obstruction. -/
theorem supportFullRule_exactDecoder_forces_visibleOf_surjective
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (decode : (Block → Bool) → ExactVisibleRule Z k)
    (hdecode :
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          rule) :
    Function.Surjective visibleOf := by
  by_contra hnot
  rcases
    supportFullRule_exists_distinct_rules_same_outputFamily_of_not_surjective
      (Z := Z) (k := k) (Block := Block) visibleOf hnot with
    ⟨rule₀, rule₁, hne, hsame, _hdiff⟩
  have heq : rule₀ = rule₁ := by
    calc
      rule₀ =
          decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict
              rule₀) := (hdecode rule₀).symm
      _ =
          decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict
              rule₁) := by rw [hsame]
      _ = rule₁ := hdecode rule₁
  exact hne heq

/-- If the support map misses an exact-visible input, no post-processing
decoder can reconstruct all full exact-visible rules from observed block
outputs. -/
theorem supportFullRule_not_exists_exactDecoder_of_not_surjective
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hnot : ¬ Function.Surjective visibleOf) :
    ¬ ∃ decode : (Block → Bool) → ExactVisibleRule Z k,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          rule := by
  rintro ⟨decode, hdecode⟩
  exact hnot
    (supportFullRule_exactDecoder_forces_visibleOf_surjective
      (Z := Z) (k := k) (Block := Block) visibleOf decode hdecode)

/-- More generally, any downstream property decoded from observed block-output
traces must be constant on the fibers of the observed quotient map. -/
theorem supportFullRule_propertyDecoder_constant_on_observedFibers
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {α : Type*} (property : ExactVisibleRule Z k → α)
    (decode : (Block → Bool) → α)
    (hdecode :
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          property rule) :
    ∀ {rule₀ rule₁ : ExactVisibleRule Z k},
      (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁ →
      property rule₀ = property rule₁ := by
  intro rule₀ rule₁ hsame
  calc
    property rule₀ =
        decode
          ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict
            rule₀) := (hdecode rule₀).symm
    _ =
        decode
          ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict
            rule₁) := by rw [hsame]
    _ = property rule₁ := hdecode rule₁

/-- A downstream property is decodable from observed block-output traces
exactly when it is constant on the fibers of the observed quotient map.  This
is the precise factorization criterion for replacing a full-rule target by a
reachable-support quotient. -/
theorem supportFullRule_exists_propertyDecoder_iff_constant_on_observedFibers
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {α : Type*} (property : ExactVisibleRule Z k → α) :
    (∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          property rule) ↔
      ∀ {rule₀ rule₁ : ExactVisibleRule Z k},
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
          (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁ →
        property rule₀ = property rule₁ := by
  constructor
  · rintro ⟨decode, hdecode⟩
    exact
      supportFullRule_propertyDecoder_constant_on_observedFibers
        (Z := Z) (k := k) (Block := Block) visibleOf property decode hdecode
  · intro hconstant
    classical
    refine
      ⟨fun trace =>
          if h :
              ∃ rule : ExactVisibleRule Z k,
                (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule =
                  trace
          then property (Classical.choose h)
          else property (fun _ => false), ?_⟩
    intro rule
    have htrace :
        ∃ rule' : ExactVisibleRule Z k,
          (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule' =
            (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule :=
      ⟨rule, rfl⟩
    dsimp
    rw [dif_pos htrace]
    exact hconstant (Classical.choose_spec htrace)

/-- Therefore any property separating two rules in the same observed-output
fiber cannot be decoded from observed block outputs. -/
theorem supportFullRule_not_exists_propertyDecoder_of_same_output_ne
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {α : Type*} (property : ExactVisibleRule Z k → α)
    {rule₀ rule₁ : ExactVisibleRule Z k}
    (hsame :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁)
    (hprop : property rule₀ ≠ property rule₁) :
    ¬ ∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          property rule := by
  rintro ⟨decode, hdecode⟩
  exact hprop
    (supportFullRule_propertyDecoder_constant_on_observedFibers
      (Z := Z) (k := k) (Block := Block) visibleOf property decode hdecode hsame)

/-- If an exact-visible input is outside the reachable support, even the single
bit "what is the rule value at this input?" cannot be decoded from observed
block outputs. -/
theorem supportFullRule_not_exists_evalDecoder_of_missed_point
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (u₀ : ExactVisiblePostSwitchSurface Z k)
    (hmiss : ∀ phi, visibleOf phi ≠ u₀) :
    ¬ ∃ decode : (Block → Bool) → Bool,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          rule u₀ := by
  classical
  let rule₀ : ExactVisibleRule Z k := fun _ => false
  let rule₁ : ExactVisibleRule Z k := fun u => if u = u₀ then true else false
  have hsame :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁ := by
    funext phi
    simp [ActualSwitchedLocalInterface.outputFamily,
      supportFullRuleActualSwitchedLocalInterface, rule₀, rule₁, hmiss phi]
  have hprop : (fun rule : ExactVisibleRule Z k => rule u₀) rule₀ ≠
      (fun rule : ExactVisibleRule Z k => rule u₀) rule₁ := by
    simp [rule₀, rule₁]
  exact
    supportFullRule_not_exists_propertyDecoder_of_same_output_ne
      (Z := Z) (k := k) (Block := Block) visibleOf
      (fun rule : ExactVisibleRule Z k => rule u₀) hsame hprop

/-- Conversely, a single exact-visible rule bit is decodable from observed
block outputs exactly when that exact-visible input is actually reached by
some block. -/
theorem supportFullRule_exists_evalDecoder_iff_mem_range
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (u₀ : ExactVisiblePostSwitchSurface Z k) :
    (∃ decode : (Block → Bool) → Bool,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          rule u₀) ↔ ∃ phi, visibleOf phi = u₀ := by
  constructor
  · intro hdecode
    by_contra hnot
    exact
      (supportFullRule_not_exists_evalDecoder_of_missed_point
        (Z := Z) (k := k) (Block := Block) visibleOf u₀
        (by
          intro phi hphi
          exact hnot ⟨phi, hphi⟩)) hdecode
  · rintro ⟨phi₀, hphi₀⟩
    refine ⟨fun trace => trace phi₀, ?_⟩
    intro rule
    simp [ActualSwitchedLocalInterface.outputFamily,
      supportFullRuleActualSwitchedLocalInterface, hphi₀]

/-- A decoder for every exact-visible point query exists exactly when the
reachable support hits the whole exact-visible surface. -/
theorem supportFullRule_all_evalDecoders_iff_visibleOf_surjective
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k) :
    (∀ u₀ : ExactVisiblePostSwitchSurface Z k,
      ∃ decode : (Block → Bool) → Bool,
        ∀ rule : ExactVisibleRule Z k,
          decode
              ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
            rule u₀) ↔ Function.Surjective visibleOf := by
  constructor
  · intro hdecode u₀
    exact
      (supportFullRule_exists_evalDecoder_iff_mem_range
        (Z := Z) (k := k) (Block := Block) visibleOf u₀).1 (hdecode u₀)
  · intro hsurj u₀
    exact
      (supportFullRule_exists_evalDecoder_iff_mem_range
        (Z := Z) (k := k) (Block := Block) visibleOf u₀).2 (hsurj u₀)

/-- More generally, a whole family of exact-visible point queries is decodable
from observed block outputs exactly when every queried exact-visible point is
in the reachable support. -/
theorem supportFullRule_exists_queryDecoder_iff_forall_mem_range
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {Query : Type*} (queryOf : Query → ExactVisiblePostSwitchSurface Z k) :
    (∃ decode : (Block → Bool) → Query → Bool,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          fun q => rule (queryOf q)) ↔ ∀ q, ∃ phi, visibleOf phi = queryOf q := by
  constructor
  · rintro ⟨decode, hdecode⟩ q
    exact
      (supportFullRule_exists_evalDecoder_iff_mem_range
        (Z := Z) (k := k) (Block := Block) visibleOf (queryOf q)).1
        ⟨fun trace => decode trace q, by
          intro rule
          exact congrFun (hdecode rule) q⟩
  · intro hreach
    classical
    refine ⟨fun trace q => trace (Classical.choose (hreach q)), ?_⟩
    intro rule
    funext q
    have hq : visibleOf (Classical.choose (hreach q)) = queryOf q :=
      Classical.choose_spec (hreach q)
    simp [ActualSwitchedLocalInterface.outputFamily,
      supportFullRuleActualSwitchedLocalInterface, hq]

/-- Hence a query family containing even one unreachable exact-visible point
cannot be decoded from observed block outputs. -/
theorem supportFullRule_not_exists_queryDecoder_of_missed_query
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {Query : Type*} (queryOf : Query → ExactVisiblePostSwitchSurface Z k)
    (q₀ : Query) (hmiss : ∀ phi, visibleOf phi ≠ queryOf q₀) :
    ¬ ∃ decode : (Block → Bool) → Query → Bool,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          fun q => rule (queryOf q) := by
  intro hdecode
  have hreach :
      ∀ q, ∃ phi, visibleOf phi = queryOf q :=
    (supportFullRule_exists_queryDecoder_iff_forall_mem_range
      (Z := Z) (k := k) (Block := Block) visibleOf queryOf).1 hdecode
  rcases hreach q₀ with ⟨phi, hphi⟩
  exact hmiss phi hphi

/-- An adaptive query tree over exact-visible points is decodable from observed
block outputs whenever every point it may query lies in the reachable support.
This covers downstream algorithms whose later probes depend on earlier rule
answers. -/
theorem supportFullRule_exists_adaptiveQueryDecoder_of_allQueriesReachable
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {α : Type*}
    (tree : AdaptiveBoolQueryTree (ExactVisiblePostSwitchSurface Z k) α)
    (hreach : AdaptiveBoolQueryTree.AllQueriesReachable visibleOf tree) :
    ∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          AdaptiveBoolQueryTree.eval rule tree := by
  rcases
    AdaptiveBoolQueryTree.exists_traceDecoder_of_allQueriesReachable
      visibleOf tree hreach with
    ⟨decode, hdecode⟩
  refine ⟨decode, ?_⟩
  intro rule
  simpa [ActualSwitchedLocalInterface.outputFamily,
    supportFullRuleActualSwitchedLocalInterface] using hdecode rule

/-- Exact adaptive decodability is still just quotient factorization: an
adaptive query tree can be decoded from observed traces exactly when its final
output is constant on observed-output fibers. -/
theorem supportFullRule_exists_adaptiveQueryDecoder_iff_constant_on_observedFibers
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {α : Type*}
    (tree : AdaptiveBoolQueryTree (ExactVisiblePostSwitchSurface Z k) α) :
    (∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          AdaptiveBoolQueryTree.eval rule tree) ↔
      ∀ {rule₀ rule₁ : ExactVisibleRule Z k},
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
          (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁ →
        AdaptiveBoolQueryTree.eval rule₀ tree =
          AdaptiveBoolQueryTree.eval rule₁ tree := by
  exact
    supportFullRule_exists_propertyDecoder_iff_constant_on_observedFibers
      (Z := Z) (k := k) (Block := Block) visibleOf
      (fun rule : ExactVisibleRule Z k => AdaptiveBoolQueryTree.eval rule tree)

/-- Any pair of full exact-visible rules with the same observed block trace
but different adaptive-tree outputs is a complete certificate that the
adaptive computation cannot be decoded from observed traces. -/
theorem supportFullRule_not_exists_adaptiveQueryDecoder_of_same_output_eval_ne
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {α : Type*}
    (tree : AdaptiveBoolQueryTree (ExactVisiblePostSwitchSurface Z k) α)
    {rule₀ rule₁ : ExactVisibleRule Z k}
    (hsame :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁)
    (hne :
      AdaptiveBoolQueryTree.eval rule₀ tree ≠
        AdaptiveBoolQueryTree.eval rule₁ tree) :
    ¬ ∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          AdaptiveBoolQueryTree.eval rule tree := by
  exact
    supportFullRule_not_exists_propertyDecoder_of_same_output_ne
      (Z := Z) (k := k) (Block := Block) visibleOf
      (fun rule : ExactVisibleRule Z k => AdaptiveBoolQueryTree.eval rule tree)
      hsame hne

/-- A one-step adaptive query at an unreachable root already cannot be decoded
when its two root branches produce different final outputs. -/
theorem supportFullRule_not_exists_rootAdaptiveQueryDecoder_of_missed_point_ne
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (u₀ : ExactVisiblePostSwitchSurface Z k)
    {α : Type*} {valueFalse valueTrue : α}
    (hmiss : ∀ phi, visibleOf phi ≠ u₀)
    (hne : valueFalse ≠ valueTrue) :
    ¬ ∃ decode : (Block → Bool) → α,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          AdaptiveBoolQueryTree.eval rule
            (AdaptiveBoolQueryTree.query u₀
              (AdaptiveBoolQueryTree.leaf valueFalse)
              (AdaptiveBoolQueryTree.leaf valueTrue)) := by
  classical
  let rule₀ : ExactVisibleRule Z k := fun _ => false
  let rule₁ : ExactVisibleRule Z k := fun u => if u = u₀ then true else false
  have hsame :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁ := by
    funext phi
    simp [ActualSwitchedLocalInterface.outputFamily,
      supportFullRuleActualSwitchedLocalInterface, rule₀, rule₁, hmiss phi]
  rintro ⟨decode, hdecode⟩
  have heq : valueFalse = valueTrue := by
    calc
      valueFalse =
          AdaptiveBoolQueryTree.eval rule₀
            (AdaptiveBoolQueryTree.query u₀
              (AdaptiveBoolQueryTree.leaf valueFalse)
              (AdaptiveBoolQueryTree.leaf valueTrue)) := by
        simp [AdaptiveBoolQueryTree.eval, rule₀]
      _ =
          decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict
              rule₀) := (hdecode rule₀).symm
      _ =
          decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict
              rule₁) := by rw [hsame]
      _ =
          AdaptiveBoolQueryTree.eval rule₁
            (AdaptiveBoolQueryTree.query u₀
              (AdaptiveBoolQueryTree.leaf valueFalse)
              (AdaptiveBoolQueryTree.leaf valueTrue)) := hdecode rule₁
      _ = valueTrue := by
        simp [AdaptiveBoolQueryTree.eval, rule₁]
  exact hne heq

end FiniteObservedSupportFullRule

end Mettapedia.Computability.PNP
