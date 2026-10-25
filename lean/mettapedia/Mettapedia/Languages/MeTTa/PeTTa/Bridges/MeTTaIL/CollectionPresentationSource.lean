import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution

/-! # Source correspondence for retained collection presentation replay -/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RecursiveCollectionPresentation
open CanonicalBags CanonicalCompare CollectionSelection
open RuleBinding ScopedRuleMatching EquationalScopedMatching
open InferenceCettaWire (encodePattern encodeCollectionType encodeRest encodeBinder)
open RecursiveCollectionExecution (eventTerm)
open CollectionSelectionExecution (decisionTerm pairTerm booleanTerm)
open Eval BridgeKit WireKit

theorem allocation_covered {table : List String} {kind : CollType} {count : Nat}
    {targets : List Pattern} {allocation : Allocation Pattern}
    (covered : ∀ target ∈ targets, Covered table target)
    (allocated : allocation ∈ tracedAllocations (kind == .hashSet) count (arrange kind targets)) :
    (∀ value ∈ allocation.values, Covered table value) ∧
      (∀ value ∈ allocation.residual, Covered table value) := by
  have erased : allocation.erase ∈ allocations (kind == .hashSet) count (arrange kind targets) := by
    rw [← tracedAllocations_erase]
    exact List.mem_map.mpr ⟨allocation, allocated, rfl⟩
  have member : ∀ value, value ∈ allocation.values ++ allocation.residual → value ∈ arrange kind targets := by
    cases mode : (kind == .hashSet)
    · rw [mode] at erased
      exact fun value inside => (bag_allocations_sound erased).2.mem_iff.mpr inside
    · rw [mode] at erased
      exact fun value inside => ((set_allocations_sound erased).2 value).mpr inside
  constructor
  · intro value inside
    exact covered value ((arrange_mem value).mp (member value (List.mem_append_left _ inside)))
  · intro value inside
    exact covered value ((arrange_mem value).mp (member value (List.mem_append_right _ inside)))

@[metta_head "gslt:collection-presentation:unordered"]
theorem unordered_returns (state : Effects.State) (table : List String) (ordered : NameOrdered table)
    (path : List Nat) (kind : CollType) (schemas targets presented : List Pattern)
    (allocation : Allocation Pattern) (trace remaining : List EquationalScopedReceipts.Event)
    (covered : ∀ target ∈ targets, Covered table target)
    (allocated : allocation ∈ tracedAllocations (kind == .hashSet) schemas.length (arrange kind targets))
    (children : PureReturns library.runtime [] state
      (apply "gslt:collection-presentation:arguments" [encoded (encodeList Term.string table),
        encoded (encodeList Term.natural path), number 0, encoded (encodeList encodePattern schemas),
        encoded (encodeList encodePattern allocation.values), encoded (encodeList eventTerm trace)])
      state (encoded (encodeOption (presentationTerm (encodeList encodePattern)) (some (presented, remaining))))) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-presentation:unordered" [encoded (encodeList Term.string table),
        encoded (encodeList Term.natural path), encoded (encodeCollectionType kind),
        encoded (encodeList encodePattern schemas), encoded (encodeList encodePattern targets),
        encoded (encodeList eventTerm (⟨path, kind, allocation.decisions⟩ :: trace))])
      state (encoded (encodeOption (presentationTerm encodePattern)
        (some (.collection kind (presented ++ arrange kind allocation.residual) none, remaining)))) := by
  have replayed := replay_returns state (kind == .hashSet) (arrange kind targets) allocation.decisions
  rw [tracedAllocations_replay allocated] at replayed
  have count := tracedAllocations_length allocated
  have decisionCount := length_returns decisionTerm state allocation.decisions
  rw [count] at decisionCount
  have residualCovered := (allocation_covered covered allocated).2
  have sorted := arrange_returns state table ordered kind targets covered
  have residual := arrange_returns state table ordered kind allocation.residual residualCovered
  have wrapped := wrap_collection_returns state kind presented (arrange kind allocation.residual) remaining
  cases kind <;>
    presentation_eval [length_returns encodePattern state schemas, decisionCount, sorted,
      replayed, residual, children, wrapped]
      unfolding [encodeCollectionType, booleanTerm, pairTerm, Allocation.erase]

mutual
/-- Valid allocation histories reconstruct the exact source-level result on
the native evaluator, with their unused event suffix intact. -/
theorem presentAt_returns (state : Effects.State) (table : List String) (ordered : NameOrdered table)
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial final : Assignment}
    {schema target : Pattern} {trace : List EquationalScopedReceipts.Event}
    (matched : EquationalScopedReceipts.Matches literalBodyComparison rule spec ambient site path depth
      initial schema target trace final) (covered : Covered table target)
    (suffix : List EquationalScopedReceipts.Event) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-presentation:at" [encoded (encodeList Term.string table),
        encoded (encodeList Term.natural path), encoded (encodePattern schema), encoded (encodePattern target),
        encoded (encodeList eventTerm (trace ++ suffix))])
      state (encoded (encodeOption (presentationTerm encodePattern)
        (presentAt path schema target (trace ++ suffix)))) := by
  cases matched with
  | capture => presentation_eval unfolding [presentAt, encodePattern]
  | bound => presentation_eval unfolding [presentAt, encodePattern]
  | @constructor path depth initial label schemas targets trace final rows =>
    have childrenCovered : ∀ child ∈ targets, Covered table child := by
      intro child member name inside
      exact covered name (by simp only [names, List.mem_cons, mem_namesList]; exact Or.inr ⟨child, member, inside⟩)
    have children := presentArguments_returns state table ordered rows childrenCovered suffix
    obtain ⟨presented, reconstructed, _, _⟩ := presentArguments_complete rows suffix
    rw [reconstructed] at children
    presentation_eval [children, wrap_app_returns state label presented suffix]
      unfolding [presentAt, reconstructed, encodePattern]
  | @lambda path depth initial display actual body target trace final bodyMatched =>
    have childCovered : Covered table target := by
      intro name member
      exact covered name (by simp [names, member])
    have child := presentAt_returns state table ordered bodyMatched childCovered suffix
    obtain ⟨presented, reconstructed, _, _⟩ := presentAt_complete bodyMatched suffix
    rw [reconstructed] at child
    presentation_eval [append_returns Term.natural state path [0], child,
      wrap_lambda_returns state actual presented suffix]
      unfolding [presentAt, reconstructed, encodePattern]
  | @multiLambda path depth initial arity display actual body target trace final bodyMatched =>
    have childCovered : Covered table target := by
      intro name member
      exact covered name (by simp [names, member])
    have child := presentAt_returns state table ordered bodyMatched childCovered suffix
    obtain ⟨presented, reconstructed, _, _⟩ := presentAt_complete bodyMatched suffix
    rw [reconstructed] at child
    presentation_eval [append_returns Term.natural state path [0], child,
      wrap_multiLambda_returns state arity actual presented suffix]
      unfolding [presentAt, reconstructed, encodePattern]
  | @substitution path depth initial body targetBody replacement targetReplacement
      middle final bodyTrace replacementTrace bodyMatched replacementMatched =>
    have bodyCovered : Covered table targetBody := by
      intro name member
      exact covered name (by simp [names, member])
    have replacementCovered : Covered table targetReplacement := by
      intro name member
      exact covered name (by simp [names, member])
    have first := presentAt_returns state table ordered bodyMatched bodyCovered (replacementTrace ++ suffix)
    have second := presentAt_returns state table ordered replacementMatched replacementCovered suffix
    obtain ⟨body', bodyReconstructed, _, _⟩ := presentAt_complete bodyMatched (replacementTrace ++ suffix)
    obtain ⟨replacement', replacementReconstructed, _, _⟩ := presentAt_complete replacementMatched suffix
    rw [bodyReconstructed] at first
    rw [replacementReconstructed] at second
    presentation_eval [append_returns Term.natural state path [0], append_returns Term.natural state path [1],
      first, second, wrap_subst_returns state body' replacement' suffix]
      unfolding [presentAt, List.append_assoc, bodyReconstructed, replacementReconstructed, encodePattern]
  | @vector path depth initial schemas targets trace final rows =>
    have childrenCovered : ∀ child ∈ targets, Covered table child := by
      intro child member name inside
      exact covered name (by simp [names, mem_namesList]; exact ⟨child, member, inside⟩)
    have children := presentArguments_returns state table ordered rows childrenCovered suffix
    obtain ⟨presented, reconstructed, _, _⟩ := presentArguments_complete rows suffix
    rw [reconstructed] at children
    presentation_eval [children, wrap_collection_returns state .vec presented [] suffix]
      unfolding [presentAt.eq_def, reconstructed, encodePattern, encodeRest, encodeCollectionType, List.append_nil]
  | @vectorRest path depth initial schemas targets name trace middle final rows captured =>
    have childrenCovered : ∀ child ∈ targets.take schemas.length, Covered table child := by
      intro child member name inside
      apply covered name
      simp only [names, Option.toList_none, List.append_nil, mem_namesList]
      exact ⟨child, List.mem_of_mem_take member, inside⟩
    have children := presentArguments_returns state table ordered rows childrenCovered suffix
    obtain ⟨presented, reconstructed, _, _⟩ := presentArguments_complete rows suffix
    rw [reconstructed] at children
    presentation_eval [length_returns encodePattern state schemas, take_returns state schemas.length targets,
      drop_returns state schemas.length targets, children,
      wrap_collection_returns state .vec presented (targets.drop schemas.length) suffix]
      unfolding [presentAt.eq_def, reconstructed, encodePattern, encodeRest, encodeCollectionType]
  | @unordered path depth initial kind schemas rest targets allocation trace middle final
      notVector allocated rows finished =>
    have targetsCovered : ∀ target ∈ targets, Covered table target := by
      intro child member name inside
      exact covered name (by simp [names, mem_namesList]; exact ⟨child, member, inside⟩)
    have children := presentArguments_returns state table ordered rows
      (allocation_covered targetsCovered allocated).1 suffix
    obtain ⟨presented, reconstructed, _, _⟩ := presentArguments_complete rows suffix
    rw [reconstructed] at children
    have unordered := unordered_returns state table ordered path kind schemas targets presented
      allocation (trace ++ suffix) suffix targetsCovered allocated children
    have replayed := tracedAllocations_replay allocated
    have count := tracedAllocations_length allocated
    cases kind with
    | vec => exact False.elim (notVector rfl)
    | hashBag | hashSet =>
      presentation_eval [unordered]
        unfolding [presentAt.eq_def, reconstructed, encodePattern, encodeRest, encodeCollectionType,
          List.cons_append, count, replayed, Allocation.erase]
termination_by sizeOf schema
decreasing_by all_goals sizeOf_pattern_dec

theorem presentArguments_returns (state : Effects.State) (table : List String) (ordered : NameOrdered table)
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth index : Nat} {initial final : Assignment}
    {schemas targets : List Pattern} {trace : List EquationalScopedReceipts.Event}
    (matched : EquationalScopedReceipts.Arguments literalBodyComparison rule spec ambient site path depth
      initial index schemas targets trace final) (covered : ∀ target ∈ targets, Covered table target)
    (suffix : List EquationalScopedReceipts.Event) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-presentation:arguments" [encoded (encodeList Term.string table),
        encoded (encodeList Term.natural path), number index, encoded (encodeList encodePattern schemas),
        encoded (encodeList encodePattern targets), encoded (encodeList eventTerm (trace ++ suffix))])
      state (encoded (encodeOption (presentationTerm (encodeList encodePattern))
        (presentArguments path index schemas targets (trace ++ suffix)))) := by
  cases matched with
  | nil => presentation_eval unfolding [presentArguments]
  | @cons path depth initial index schema schemas target targets middle final headTrace tailTrace head tail =>
    have first := presentAt_returns state table ordered head (covered target (by simp)) (tailTrace ++ suffix)
    have second := presentArguments_returns state table ordered tail
      (fun child member => covered child (by simp [member])) suffix
    obtain ⟨head', headReconstructed, _, _⟩ := presentAt_complete head (tailTrace ++ suffix)
    obtain ⟨tail', tailReconstructed, _, _⟩ := presentArguments_complete tail suffix
    rw [headReconstructed] at first
    rw [tailReconstructed] at second
    rw [presentArguments.eq_def]
    simp [List.append_assoc, headReconstructed, tailReconstructed]
    presentation_eval [append_returns Term.natural state path [index], first, second,
      wrap_cons_returns state head' tail' suffix]
termination_by sizeOf schemas
decreasing_by all_goals sizeOf_pattern_dec
end

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution
