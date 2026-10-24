import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionPresentation
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionTraceAccounting

/-!
# Source evidence for executable receipt reconstruction

Reconstruction preserves the source collection class and produces a specific
ordinary scoped matching witness with the original captured assignment. The
ordinary evidence is deterministic; it adds no allocation or derivation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Mettapedia.OSLF.MeTTaIL.RecursiveCollectionPresentation

open Syntax RuleBinding ScopedRuleMatching CanonicalBags CollectionSelection
open EquationalScopedMatching CollectionMatcherCompatibility
open GeneralScopedMatchMachine

/-- The same reconstructed children support ordered arguments and a bag that
consumes those children from the front before processing its residual. -/
structure FrontArguments (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (depth index : Nat)
    (initial : Assignment) (schemas presented : List Pattern) (final : Assignment) : Prop where
  ordered : TracedArguments rule spec ambient site path depth initial index schemas presented
    (frontTraceArguments false path index schemas) final
  unordered : ∀ (kind : CollType) (rest : Option String) (residual : List Pattern) (last : Assignment),
    ScopedCollectionMatching.Finished rule spec ambient site path depth (index + schemas.length)
      kind rest final residual last →
    TracedBag rule spec ambient site path depth initial index schemas rest kind (presented ++ residual)
      (frontTraceArguments true path index schemas) last

theorem FrontArguments.nil (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (depth index : Nat) (initial : Assignment) :
    FrontArguments rule spec ambient site path depth index initial [] [] initial := by
  refine ⟨by simpa only [frontTraceArguments] using (TracedArguments.nil (rule := rule) (spec := spec) (ambient := ambient) (site := site) (path := path) (depth := depth) (initial := initial) (index := index)), ?_⟩
  intro kind rest residual last finished
  simp only [List.length_nil, Nat.add_zero] at finished
  cases finished with
  | empty => simpa only [frontTraceArguments, List.nil_append] using (TracedBag.nil (rule := rule) (spec := spec) (ambient := ambient) (site := site) (path := path) (depth := depth) (initial := initial) (index := index) (kind := kind))
  | captured captured => simpa only [frontTraceArguments, List.nil_append] using TracedBag.rest captured

theorem FrontArguments.cons {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth index : Nat}
    {initial middle final : Assignment} {schema target : Pattern} {schemas targets : List Pattern}
    (head : TracedMatches rule spec ambient site (path ++ [index]) depth initial schema target
      (frontTraceAt (path ++ [index]) schema) middle)
    (tail : FrontArguments rule spec ambient site path depth (index + 1) middle schemas targets final) :
    FrontArguments rule spec ambient site path depth index initial
      (schema :: schemas) (target :: targets) final := by
  refine ⟨?_, ?_⟩
  · simpa only [frontTraceArguments, Bool.false_eq_true, ↓reduceIte, List.nil_append] using
      TracedArguments.cons head tail.ordered
  · intro kind rest residual last finished
    have continued := tail.unordered kind rest residual last (by
      convert finished using 1
      simp only [List.length_cons]
      omega)
    simpa only [frontTraceArguments, ↓reduceIte, List.singleton_append, List.cons_append,
      List.getElem_cons_zero, List.eraseIdx_zero] using
      (TracedBag.cons (selected := 0) (within := by simp) head continued)

private theorem finished_literal {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth index : Nat}
    {rest : Option String} {kind : CollType} {initial final : Assignment} {targets : List Pattern}
    (finished : Finished literalBodyComparison rule spec ambient site path depth index rest kind
      initial targets final) :
    ScopedCollectionMatching.Finished rule spec ambient site path depth index kind rest
      initial targets final := by
  cases rest with
  | none => obtain ⟨rfl, rfl⟩ := finished; exact .empty
  | some name => exact .captured (by simpa only [Finished, captureRestWith?_literal] using finished)

private theorem allocated_same {kind : CollType} {schemas targets : List Pattern}
    {allocation : Allocation Pattern} (notVector : kind ≠ .vec)
    (allocated : allocation ∈ tracedAllocations (kind == .hashSet) schemas.length (arrange kind targets))
    (length : schemas.length = allocation.values.length) :
    Same (.collection kind targets none)
      (.collection kind (allocation.values ++ arrange kind allocation.residual) none) := by
  have erased : allocation.erase ∈ kindAllocations kind schemas.length (arrange kind targets) := by
    rw [kindAllocations, ← tracedAllocations_erase]
    exact List.mem_map.mpr ⟨allocation, allocated, rfl⟩
  have distinct : kind = .hashSet → (arrange kind targets).Nodup := by
    rintro rfl
    exact canonical_set_distinct targets
  have presented := (allocations_present_exact notVector distinct).mp
    ⟨allocation.residual, by simpa only [Allocation.erase, length] using erased, Presents.of_eq rfl⟩
  apply (same_iff _ _).mpr
  apply collection_equivalent_of_presents notVector
  exact presents_append_arrange ((arranged_presents ..).mp presented)

mutual
/-- A valid recursive receipt constructs an ordinary source match without
enumerating alternative ordinary matching proofs. -/
theorem presentAt_complete {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial final : Assignment}
    {schema target : Pattern} {trace : List EquationalScopedReceipts.Event}
    (matched : EquationalScopedReceipts.Matches literalBodyComparison rule spec ambient site path depth
      initial schema target trace final) (suffix : List EquationalScopedReceipts.Event) :
    ∃ presented, presentAt path schema target (trace ++ suffix) = some (presented, suffix) ∧
      Same target presented ∧ TracedMatches rule spec ambient site path depth initial schema presented
        (frontTraceAt path schema) final := by
  cases matched with
  | capture captured =>
    refine ⟨_, by simp only [presentAt, List.nil_append], rfl, ?_⟩
    simp only [frontTraceAt]
    exact .capture (by simpa only [captureWith?_literal] using captured)
  | bound =>
    refine ⟨_, by simp [presentAt], rfl, ?_⟩
    simp only [frontTraceAt]
    exact .bound
  | @constructor path depth initial label schemas targets trace final rows =>
    obtain ⟨presented, reconstructed, same, ordinary⟩ := presentArguments_complete rows suffix
    exact ⟨.apply label presented, by simp [presentAt, reconstructed],
      same_apply_congr _ same, by simpa only [frontTraceAt] using TracedMatches.constructor ordinary.ordered⟩
  | @lambda path depth initial display actual body target trace final bodyMatched =>
    obtain ⟨presented, reconstructed, same, ordinary⟩ := presentAt_complete bodyMatched suffix
    exact ⟨.lambda actual presented, by simp only [presentAt, reconstructed, Option.map_some],
      same_lambda_congr _ same, by simpa only [frontTraceAt] using TracedMatches.binder ordinary⟩
  | @multiLambda path depth initial arity displays actual body target trace final bodyMatched =>
    obtain ⟨presented, reconstructed, same, ordinary⟩ := presentAt_complete bodyMatched suffix
    exact ⟨.multiLambda arity actual presented, by simp [presentAt, reconstructed],
      same_multiLambda_congr _ _ same, by simpa only [frontTraceAt] using TracedMatches.binders ordinary⟩
  | @substitution path depth initial body targetBody replacement targetReplacement
      middle final bodyTrace replacementTrace bodyMatched replacementMatched =>
    obtain ⟨body', reconstructedBody, sameBody, ordinaryBody⟩ :=
      presentAt_complete bodyMatched (replacementTrace ++ suffix)
    obtain ⟨replacement', reconstructedReplacement, sameReplacement, ordinaryReplacement⟩ :=
      presentAt_complete replacementMatched suffix
    exact ⟨.subst body' replacement',
      by simp [presentAt, List.append_assoc, reconstructedBody, reconstructedReplacement],
      same_subst_congr sameBody sameReplacement, by simpa only [frontTraceAt] using TracedMatches.substitution ordinaryBody ordinaryReplacement⟩
  | @vector path depth initial schemas targets trace final rows =>
    obtain ⟨presented, reconstructed, same, ordinary⟩ := presentArguments_complete rows suffix
    exact ⟨.collection .vec presented none, by rw [presentAt.eq_def]; simp [reconstructed],
      same_collection_congr _ _ same, by simpa [frontTraceAt] using TracedMatches.vector ordinary.ordered⟩
  | @vectorRest path depth initial schemas targets name trace middle final rows captured =>
    obtain ⟨presented, reconstructed, same, ordinary⟩ := presentArguments_complete rows suffix
    have length : presented.length = schemas.length :=
      same.length_eq.symm.trans (arguments_length rows.meaning).symm
    have sourceSame : Same (.collection .vec targets none)
        (.collection .vec (presented ++ targets.drop schemas.length) none) := by
      apply same_collection_congr
      simpa only [List.take_append_drop] using
        List.rel_append same (forall₂_same_of_map (targets := targets.drop schemas.length) rfl)
    refine ⟨_, by rw [presentAt.eq_def]; simp [reconstructed], sourceSame, ?_⟩
    simp only [frontTraceAt]
    change TracedMatches rule spec ambient site path depth initial
      (.collection .vec schemas (some name))
      (.collection .vec (presented ++ targets.drop schemas.length) none)
      (frontTraceArguments false path 0 schemas) final
    apply TracedMatches.vectorRest (middle := middle)
    · simpa only [← length, List.take_left] using ordinary.ordered
    · simpa only [← length, List.drop_left, captureRestWith?_literal] using captured
  | @unordered path depth initial kind schemas rest targets allocation trace middle final
      notVector allocated rows finished =>
    obtain ⟨presented, reconstructed, same, ordinary⟩ := presentArguments_complete rows suffix
    have replayed := tracedAllocations_replay allocated
    have count := tracedAllocations_length allocated
    have sourceSame := allocated_same notVector allocated (arguments_length rows.meaning)
    have valueSame : Same
        (.collection kind (allocation.values ++ arrange kind allocation.residual) none)
        (.collection kind (presented ++ arrange kind allocation.residual) none) :=
      same_collection_congr _ _ (List.rel_append same (forall₂_same_of_map rfl))
    refine ⟨_, ?_, sourceSame.trans valueSame, ?_⟩
    · rw [presentAt.eq_def]
      simp [List.cons_append, notVector, count, replayed, Allocation.erase, reconstructed]
    · have ordinaryBag := ordinary.unordered kind rest (arrange kind allocation.residual) final
        (by simpa only [Nat.zero_add] using finished_literal finished)
      have flag : (kind != .vec) = true := by cases kind <;> simp_all
      simpa only [frontTraceAt, flag] using
        TracedMatches.bag notVector ordinaryBag
termination_by sizeOf schema
decreasing_by all_goals sizeOf_pattern_dec

theorem presentArguments_complete {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth index : Nat} {initial final : Assignment}
    {schemas targets : List Pattern} {trace : List EquationalScopedReceipts.Event}
    (matched : EquationalScopedReceipts.Arguments literalBodyComparison rule spec ambient site path depth
      initial index schemas targets trace final) (suffix : List EquationalScopedReceipts.Event) :
    ∃ presented, presentArguments path index schemas targets (trace ++ suffix) = some (presented, suffix) ∧
      List.Forall₂ Same targets presented ∧
      FrontArguments rule spec ambient site path depth index initial schemas presented final := by
  cases matched with
  | nil => exact ⟨[], by simp [presentArguments], .nil, FrontArguments.nil ..⟩
  | @cons path depth initial index schema schemas target targets middle final headTrace tailTrace head tail =>
    obtain ⟨head', headReplay, headSame, headOrdinary⟩ := presentAt_complete head (tailTrace ++ suffix)
    obtain ⟨tail', tailReplay, tailSame, tailOrdinary⟩ := presentArguments_complete tail suffix
    exact ⟨head' :: tail', by simp [presentArguments, List.append_assoc, headReplay, tailReplay],
      .cons headSame tailSame, .cons headOrdinary tailOrdinary⟩
termination_by sizeOf schemas
decreasing_by all_goals sizeOf_pattern_dec
end

/-- Published answers, including an interrupted prefix, reconstruct a source
match with exactly their captured assignment. -/
theorem published_presentation (request : RecursiveCollectionMachine.Request) (fuel : Nat)
    {answer : RecursiveCollectionMachine.Answer}
    (published : answer ∈ (RecursiveCollectionMachine.run request fuel
      (RecursiveCollectionMachine.start request)).answers) :
    ∃ presented, presentAt request.path request.schema request.target answer.trace = some (presented, []) ∧
      Same request.target presented ∧
      TracedMatches request.rule request.spec request.ambient request.site request.path request.depth
        request.initial request.schema presented (frontTraceAt request.path request.schema) answer.assignment := by
  simpa only [List.append_nil] using
    presentAt_complete (RecursiveCollectionMachine.published_trace_valid request fuel published) []

end Mettapedia.OSLF.MeTTaIL.RecursiveCollectionPresentation
