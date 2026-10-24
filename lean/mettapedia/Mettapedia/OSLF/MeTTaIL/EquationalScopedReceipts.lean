import Mettapedia.OSLF.MeTTaIL.EquationalScopedMatching
import Mettapedia.OSLF.MeTTaIL.CollectionSelectionTrace

/-!
# Proof-relevant receipts for recursive collection matching

Every unordered collection node records its authored path, collection kind and
physical consume/retain decisions. Nested traces are kept in execution order.
The independent soundness theorem forgets the trace into the semantic
collection-decomposition judgment.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.OSLF.MeTTaIL.EquationalScopedReceipts

open Syntax RuleBinding ScopedRuleMatching CanonicalBags CollectionSelection
open EquationalScopedMatching

structure Event where
  path : List Nat
  kind : CollType
  decisions : List Decision
  deriving DecidableEq, Repr

mutual
inductive Matches (compare : Comparison) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) : RulePatternSite → List Nat → Nat → Assignment →
      Pattern → Pattern → List Event → Assignment → Prop where
  | capture {site path depth initial name target final} :
      captureWith? compare rule spec ambient depth site path initial name target = some final →
      Matches compare rule spec ambient site path depth initial (.fvar name) target [] final
  | bound {site path depth initial index} :
      Matches compare rule spec ambient site path depth initial (.bvar index) (.bvar index) [] initial
  | constructor {site path depth initial label schemas targets trace final} :
      Arguments compare rule spec ambient site path depth initial 0 schemas targets trace final →
      Matches compare rule spec ambient site path depth initial
        (.apply label schemas) (.apply label targets) trace final
  | lambda {site path depth initial display actual body target trace final} :
      Matches compare rule spec ambient site (path ++ [0]) (depth + 1)
        initial body target trace final →
      Matches compare rule spec ambient site path depth initial
        (.lambda display body) (.lambda actual target) trace final
  | multiLambda {site path depth initial arity displays actualDisplays body target trace final} :
      Matches compare rule spec ambient site (path ++ [0]) (depth + arity)
        initial body target trace final →
      Matches compare rule spec ambient site path depth initial
        (.multiLambda arity displays body) (.multiLambda arity actualDisplays target) trace final
  | substitution {site path depth initial body targetBody replacement targetReplacement
      middle final bodyTrace replacementTrace} :
      Matches compare rule spec ambient site (path ++ [0]) (depth + 1)
        initial body targetBody bodyTrace middle →
      Matches compare rule spec ambient site (path ++ [1]) depth
        middle replacement targetReplacement replacementTrace final →
      Matches compare rule spec ambient site path depth initial
        (.subst body replacement) (.subst targetBody targetReplacement)
        (bodyTrace ++ replacementTrace) final
  | vector {site path depth initial schemas targets trace final} :
      Arguments compare rule spec ambient site path depth initial 0 schemas targets trace final →
      Matches compare rule spec ambient site path depth initial
        (.collection .vec schemas none) (.collection .vec targets none) trace final
  | vectorRest {site path depth initial schemas targets name trace middle final} :
      Arguments compare rule spec ambient site path depth initial 0 schemas
        (targets.take schemas.length) trace middle →
      captureRestWith? compare rule spec ambient depth site (path ++ [schemas.length])
        middle name .vec (targets.drop schemas.length) = some final →
      Matches compare rule spec ambient site path depth initial
        (.collection .vec schemas (some name)) (.collection .vec targets none) trace final
  | unordered {site path depth initial kind schemas rest targets allocation trace middle final}
      (notVector : kind ≠ .vec) :
      allocation ∈ tracedAllocations (kind == .hashSet) schemas.length (arrange kind targets) →
      Arguments compare rule spec ambient site path depth initial 0 schemas allocation.values trace middle →
      Finished compare rule spec ambient site path depth schemas.length rest kind middle
        (arrange kind allocation.residual) final →
      Matches compare rule spec ambient site path depth initial
        (.collection kind schemas rest) (.collection kind targets none)
        (⟨path, kind, allocation.decisions⟩ :: trace) final

inductive Arguments (compare : Comparison) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) : RulePatternSite → List Nat → Nat → Assignment → Nat →
      List Pattern → List Pattern → List Event → Assignment → Prop where
  | nil {site path depth initial index} :
      Arguments compare rule spec ambient site path depth initial index [] [] [] initial
  | cons {site path depth initial index schema schemas target targets
      middle final headTrace tailTrace} :
      Matches compare rule spec ambient site (path ++ [index]) depth
        initial schema target headTrace middle →
      Arguments compare rule spec ambient site path depth middle (index + 1)
        schemas targets tailTrace final →
      Arguments compare rule spec ambient site path depth initial index
        (schema :: schemas) (target :: targets) (headTrace ++ tailTrace) final
end

mutual
theorem Matches.meaning {compare : Comparison} {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth : Nat}
    {initial final : Assignment} {schema target : Pattern} {trace : List Event}
    (matched : Matches compare rule spec ambient site path depth initial schema target trace final) :
    Meaning compare rule spec ambient site path depth initial schema target final := by
  cases matched with
  | capture captured => simpa [Meaning] using captured
  | bound => simp [Meaning]
  | constructor arguments => simpa [Meaning] using arguments.meaning
  | lambda body => simpa [Meaning] using body.meaning
  | multiLambda body => simpa [Meaning] using body.meaning
  | substitution body replacement =>
      simp only [Meaning]
      exact ⟨_, body.meaning, replacement.meaning⟩
  | vector arguments => simpa [Meaning] using arguments.meaning
  | vectorRest arguments captured =>
      simp only [Meaning, true_and]
      exact ⟨_, arguments.meaning, captured⟩
  | unordered notVector allocated arguments finished =>
      rename_i kind schemas rest targets allocation trace middle
      have rows := arguments.meaning
      have length := EquationalScopedMatching.arguments_length rows
      have erased : allocation.erase ∈
          kindAllocations kind schemas.length (arrange kind targets) := by
        rw [kindAllocations, ← tracedAllocations_erase]
        exact List.mem_map.mpr ⟨allocation, allocated, rfl⟩
      have distinct : kind = .hashSet → (arrange kind targets).Nodup := by
        rintro rfl
        exact canonical_set_distinct targets
      have presented := (allocations_present_exact notVector distinct).mp
        ⟨allocation.residual, by simpa [Allocation.erase, length] using erased, Presents.of_eq rfl⟩
      rw [Meaning.eq_def]
      simp only [true_and, notVector, ↓reduceIte]
      exact ⟨allocation.values, allocation.residual, _,
        (arranged_presents ..).mp presented, rows, finished⟩

theorem Arguments.meaning {compare : Comparison} {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth index : Nat}
    {initial final : Assignment} {schemas targets : List Pattern} {trace : List Event}
    (matched : Arguments compare rule spec ambient site path depth initial index
      schemas targets trace final) :
    ArgumentsMeaning compare rule spec ambient site path depth initial index schemas targets final := by
  cases matched with
  | nil => simp [ArgumentsMeaning]
  | cons head tail =>
      simp only [ArgumentsMeaning]
      exact ⟨_, head.meaning, tail.meaning⟩
end

mutual
/-- Every semantic recursive match has a finite allocation trace. -/
theorem Meaning.traced {compare : Comparison} {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth : Nat}
    {initial final : Assignment} {schema target : Pattern}
    (meaning : Meaning compare rule spec ambient site path depth initial schema target final) :
    ∃ trace, Matches compare rule spec ambient site path depth initial schema target trace final := by
  cases schema with
  | fvar name =>
      rw [Meaning.eq_def] at meaning
      exact ⟨[], .capture meaning⟩
  | bvar expected =>
      cases target <;> simp only [Meaning.eq_def] at meaning
      next actual =>
        rcases meaning with ⟨rfl, rfl⟩
        exact ⟨[], .bound⟩
  | apply label schemas =>
      cases target <;> simp only [Meaning.eq_def] at meaning
      next actual targets =>
        rcases meaning with ⟨rfl, arguments⟩
        obtain ⟨trace, traced⟩ := ArgumentsMeaning.traced arguments
        exact ⟨trace, .constructor traced⟩
  | lambda display body =>
      cases target <;> rw [Meaning.eq_def] at meaning <;> try contradiction
      next actual target =>
        obtain ⟨trace, traced⟩ := Meaning.traced meaning
        exact ⟨trace, .lambda traced⟩
  | multiLambda arity displays body =>
      cases target <;> rw [Meaning.eq_def] at meaning <;> try contradiction
      next actual actualDisplays target =>
        rcases meaning with ⟨rfl, bodyMeaning⟩
        obtain ⟨trace, traced⟩ := Meaning.traced bodyMeaning
        exact ⟨trace, .multiLambda traced⟩
  | subst body replacement =>
      cases target <;> rw [Meaning.eq_def] at meaning <;> try contradiction
      next targetBody targetReplacement =>
        obtain ⟨middle, bodyMeaning, replacementMeaning⟩ := meaning
        obtain ⟨bodyTrace, bodyTraced⟩ := Meaning.traced bodyMeaning
        obtain ⟨replacementTrace, replacementTraced⟩ := Meaning.traced replacementMeaning
        exact ⟨bodyTrace ++ replacementTrace, .substitution bodyTraced replacementTraced⟩
  | collection kind schemas rest =>
      cases target <;> simp only [Meaning.eq_def] at meaning
      next actual targets actualRest =>
        rcases meaning with ⟨rfl, rfl, meaning⟩
        by_cases vector : kind = .vec
        · subst kind
          simp only [↓reduceIte] at meaning
          cases rest with
          | none =>
              obtain ⟨trace, traced⟩ := ArgumentsMeaning.traced meaning
              exact ⟨trace, .vector traced⟩
          | some name =>
              obtain ⟨middle, arguments, captured⟩ := meaning
              obtain ⟨trace, traced⟩ := ArgumentsMeaning.traced arguments
              exact ⟨trace, .vectorRest traced captured⟩
        · simp only [vector, ↓reduceIte] at meaning
          obtain ⟨values, residual, middle, presented, arguments, finished⟩ := meaning
          have length := EquationalScopedMatching.arguments_length arguments
          have distinct : kind = .hashSet → (arrange kind targets).Nodup := by
            rintro rfl
            exact canonical_set_distinct targets
          obtain ⟨actual, allocated, same⟩ :=
            (allocations_present_exact vector distinct).mpr ((arranged_presents ..).mpr presented)
          have erased : (values, actual) ∈
              (tracedAllocations (kind == .hashSet) schemas.length
                (arrange kind targets)).map Allocation.erase := by
            rw [tracedAllocations_erase]
            simpa [kindAllocations, length] using allocated
          obtain ⟨allocation, allocationMember, allocationErase⟩ := List.mem_map.mp erased
          have valuesEq : allocation.values = values := congrArg Prod.fst allocationErase
          have residualEq : allocation.residual = actual := congrArg Prod.snd allocationErase
          obtain ⟨trace, traced⟩ := ArgumentsMeaning.traced arguments
          subst values
          subst actual
          refine ⟨⟨path, kind, allocation.decisions⟩ :: trace,
            .unordered vector allocationMember traced ?_⟩
          simpa only [arrange_eq_of_presents same] using finished
termination_by sizeOf schema
decreasing_by all_goals sizeOf_pattern_dec

theorem ArgumentsMeaning.traced {compare : Comparison} {rule : RewriteRule}
    {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite}
    {path : List Nat} {depth index : Nat} {initial final : Assignment}
    {schemas targets : List Pattern}
    (meaning : ArgumentsMeaning compare rule spec ambient site path depth initial index
      schemas targets final) :
    ∃ trace, Arguments compare rule spec ambient site path depth initial index
      schemas targets trace final := by
  cases schemas with
  | nil =>
      cases targets <;> simp only [ArgumentsMeaning] at meaning
      subst final
      exact ⟨[], .nil⟩
  | cons schema schemas =>
      cases targets with
      | nil => simp [ArgumentsMeaning] at meaning
      | cons target targets =>
          simp only [ArgumentsMeaning] at meaning
          obtain ⟨middle, head, tail⟩ := meaning
          obtain ⟨headTrace, headTraced⟩ := Meaning.traced head
          obtain ⟨tailTrace, tailTraced⟩ := ArgumentsMeaning.traced tail
          exact ⟨headTrace ++ tailTrace, .cons headTraced tailTraced⟩
termination_by sizeOf schemas
decreasing_by all_goals sizeOf_pattern_dec
end

theorem exists_trace_iff_meaning {compare : Comparison} {rule : RewriteRule}
    {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite}
    {path : List Nat} {depth : Nat} {initial final : Assignment}
    {schema target : Pattern} :
    (∃ trace, Matches compare rule spec ambient site path depth initial schema target trace final) ↔
      Meaning compare rule spec ambient site path depth initial schema target final :=
  ⟨fun ⟨_, receipt⟩ => receipt.meaning,
    fun meaning => EquationalScopedReceipts.Meaning.traced meaning⟩

theorem exists_arguments_trace_iff_meaning {compare : Comparison} {rule : RewriteRule}
    {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite}
    {path : List Nat} {depth index : Nat} {initial final : Assignment}
    {schemas targets : List Pattern} :
    (∃ trace, Arguments compare rule spec ambient site path depth initial index
      schemas targets trace final) ↔
      ArgumentsMeaning compare rule spec ambient site path depth initial index schemas targets final :=
  ⟨fun ⟨_, receipt⟩ => receipt.meaning,
    fun meaning => EquationalScopedReceipts.ArgumentsMeaning.traced meaning⟩

private theorem finished_extends {compare : Comparison} {rule : RewriteRule}
    {spec : RuleBindingSpec} {ambient depth index : Nat} {site : RulePatternSite}
    {path : List Nat} {rest : Option String} {kind : CollType}
    {initial final : Assignment} {targets : List Pattern}
    (finished : Finished compare rule spec ambient site path depth index rest kind initial targets final) :
    GeneralScopedMatch.Extends initial final := by
  cases rest with
  | none =>
      rcases finished with ⟨_, rfl⟩
      exact .refl _
  | some name => exact GeneralScopedMatch.captureWith_extends finished

mutual
/-- The declared comparison may validate a repeat, but cannot overwrite a
previous capture. Nested allocations retain that same extension discipline. -/
theorem Matches.extends {compare : Comparison} {rule : RewriteRule}
    {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite} {path : List Nat}
    {depth : Nat} {initial final : Assignment} {schema target : Pattern} {trace : List Event}
    (matched : Matches compare rule spec ambient site path depth initial schema target trace final) :
    GeneralScopedMatch.Extends initial final :=
  match matched with
  | .capture captured => GeneralScopedMatch.captureWith_extends captured
  | .bound => .refl _
  | .constructor arguments => arguments.extends
  | .lambda body => body.extends
  | .multiLambda body => body.extends
  | .substitution body replacement => body.extends.trans replacement.extends
  | .vector arguments => arguments.extends
  | .vectorRest arguments captured =>
      arguments.extends.trans (GeneralScopedMatch.captureWith_extends captured)
  | .unordered _ _ arguments finished => arguments.extends.trans (finished_extends finished)

theorem Arguments.extends {compare : Comparison} {rule : RewriteRule}
    {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite} {path : List Nat}
    {depth index : Nat} {initial final : Assignment} {schemas targets : List Pattern} {trace : List Event}
    (matched : Arguments compare rule spec ambient site path depth initial index schemas targets trace final) :
    GeneralScopedMatch.Extends initial final :=
  match matched with
  | .nil => .refl _
  | .cons head tail => head.extends.trans tail.extends
end

end Mettapedia.OSLF.MeTTaIL.EquationalScopedReceipts
