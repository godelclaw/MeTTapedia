import Mettapedia.OSLF.MeTTaIL.CollectionMatcherCompatibility
import Mettapedia.OSLF.MeTTaIL.CanonicalMatching

/-!
# Ordinary collection matches at canonical carriers

The outer allocator permits set reuse and overlap after canonicalization.
Element schemas retain the existing set-free scoped matching semantics.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionMatchingNormalization

open Syntax CanonicalBags CollectionSelection CollectionMatcherCompatibility

private theorem presents_symm {kind : CollType} {left right : List Pattern}
    (related : Presents kind left right) : Presents kind right left := by
  cases kind with
  | vec => exact related.symm
  | hashBag => exact related.symm
  | hashSet => exact fun item => (related item).symm

/-- Canonicalizing an ordinary unordered match needs no injectivity of
canonicalization. Set copies may collapse; the collection judgment admits
the corresponding reuse and overlap explicitly. -/
theorem bag_canonical
    {rule : RewriteRule} {spec : RuleBindingSpec} (increasing : IncreasingSpines rule spec)
    {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth index : Nat}
    {initial final : ScopedRuleMatching.Assignment} {schemas targets : List Pattern}
    {rest : Option String} {kind : CollType}
    (unordered : kind ≠ .vec) (free : ∀ schema ∈ schemas, setFree schema = true)
    (matched : GeneralScopedMatch.Bag rule spec ambient site path depth initial
      index schemas rest kind targets final) :
    ScopedCollectionMatching.Matches rule spec ambient site path depth index
      (canonAssignment initial) schemas rest kind (arrange kind (targets.map canon))
      (canonAssignment final) := by
  cases matched with
  | nil =>
    have empty : arrange kind [] = [] := by cases kind <;> rfl
    refine ⟨[], [], canonAssignment initial, ?_, .nil, ?_⟩
    · simpa only [List.map_nil, List.nil_append, empty] using Presents.refl kind []
    · simpa only [List.length_nil, Nat.add_zero, List.map_nil, empty] using
        (ScopedCollectionMatching.Finished.empty (rule := rule) (spec := spec)
          (ambient := ambient) (site := site) (path := path) (depth := depth)
          (index := index) (kind := kind) (initial := canonAssignment initial))
  | @rest _ _ _ _ _ _ targets _ captured =>
    refine ⟨[], targets.map canon, canonAssignment initial,
      presents_symm (presents_arrange kind _), .nil, ?_⟩
    exact .captured (captureRest?_canon increasing captured)
  | cons selected within head tail =>
    obtain ⟨chosen, residual, middle, presents, arguments, finished⟩ :=
      bag_canonical increasing unordered (fun schema member => free schema (List.mem_cons_of_mem _ member)) tail
    refine ⟨canon targets[selected] :: chosen, residual, middle, ?_,
      .cons (matches_canon increasing (free _ List.mem_cons_self) head) arguments, ?_⟩
    · have split : Presents kind (targets.map canon)
          (canon targets[selected] :: (targets.eraseIdx selected).map canon) := by
        have permuted := (List.getElem_cons_eraseIdx_perm within).map canon
        cases kind with
        | vec => exact False.elim (unordered rfl)
        | hashBag => simpa only [Presents, List.map_cons] using permuted.symm
        | hashSet =>
          intro item
          simpa only [List.map_cons] using permuted.mem_iff.symm
      have tailPresents := presents_trans (presents_arrange kind _) presents
      exact presents_trans (presents_symm (presents_arrange kind _))
        (presents_trans split (by simpa only [List.cons_append] using presents_cons tailPresents (canon targets[selected])))
    · convert finished using 1
      simp only [List.length_cons]
      omega
termination_by schemas

theorem matches_canonical
    {rule : RewriteRule} {spec : RuleBindingSpec} (increasing : IncreasingSpines rule spec)
    {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth : Nat}
    {initial final : ScopedRuleMatching.Assignment} {schemas targets : List Pattern}
    {rest : Option String} {kind : CollType}
    (unordered : kind ≠ .vec) (free : ∀ schema ∈ schemas, setFree schema = true)
    (matched : GeneralScopedMatch.Matches rule spec ambient site path depth initial
      (.collection kind schemas rest) (.collection kind targets none) final) :
    ScopedCollectionMatching.Matches rule spec ambient site path depth 0
      (canonAssignment initial) schemas rest kind (arrange kind (targets.map canon))
      (canonAssignment final) := by
  cases matched with
  | bag _ matched => exact bag_canonical increasing unordered free matched
  | vector _ => exact False.elim (unordered rfl)
  | vectorRest _ _ => exact False.elim (unordered rfl)

end Mettapedia.OSLF.MeTTaIL.CollectionMatchingNormalization
