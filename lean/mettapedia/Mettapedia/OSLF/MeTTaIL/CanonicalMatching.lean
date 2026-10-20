import Mettapedia.OSLF.MeTTaIL.CanonicalRenaming
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatch

/-!
# Matching at canonical forms

A machine that keeps every state in canonical form must find every match the presented
semantics finds at an arbitrary presentation. The matcher compares repeated metavariables
literally. On canonical subjects that comparison is faithful when every capture's spine lists
its local variables in increasing order (`IncreasingSpines`): the recovered value is then the
canonical form of the value recovered from the original presentation
(`recoverValue?_canon`), so equal values stay equal.

- `matches_canon`: every match of a schema that decomposes no set (`setFree`) at a subject has a
  match at its canonical form, whose captures are the canonical forms of the original captures
  (`canonAssignment`).

A bag pattern's elements select from the canonical, sorted elements; the residual of a sorted
list is sorted, so a rest captures the canonical form of the original residual. A set's canonical
form drops repetitions, so a pattern that decomposes a set may have no counterpart: `{X, Y}`
matches the presentation `{a, a}` and not its canonical form `{a}`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CanonicalBags

open Syntax PatternLexOrder RuleBinding ScopedRuleMatching GeneralScopedMatch

/-- A captured value with its body in canonical form. -/
def canonValue (value : ContextualValue) : ContextualValue := { value with body := canon value.body }

/-- Every captured body in canonical form. -/
def canonAssignment (assignment : ScopedRuleMatching.Assignment) : ScopedRuleMatching.Assignment :=
  assignment.map fun entry => (entry.1, canonValue entry.2)

/-- Every capture's spine lists its local variables in increasing order. -/
def IncreasingSpines (rule : RewriteRule) (spec : RuleBindingSpec) : Prop :=
  ∀ name site path arguments, arguments? rule spec name site path = some arguments →
    ∀ depth indices, variableSpine? depth arguments = some indices → indices.Pairwise (· < ·)

theorem lookup_canonAssignment (assignment : ScopedRuleMatching.Assignment) (name : String) :
    lookup (canonAssignment assignment) name = (lookup assignment name).map canonValue := by
  induction assignment with
  | nil => rfl
  | cons entry rest ih =>
    unfold lookup at ih ⊢
    simp only [canonAssignment, List.map_cons] at ih ⊢
    by_cases same : entry.1 = name
    · rw [List.find?_cons_of_pos (by simpa using same), List.find?_cons_of_pos (by simpa using same)]; rfl
    · rw [List.find?_cons_of_neg (by simpa using same), List.find?_cons_of_neg (by simpa using same)]; exact ih

theorem assign_canon {assignment final : ScopedRuleMatching.Assignment} {name : String} {value : ContextualValue}
    (assigned : assign assignment name value = some final) :
    assign (canonAssignment assignment) name (canonValue value) = some (canonAssignment final) := by
  unfold assign at assigned ⊢
  rw [lookup_canonAssignment]
  cases found : lookup assignment name with
  | none =>
    rw [found] at assigned
    cases assigned
    rfl
  | some prior =>
    rw [found] at assigned
    simp only [Option.map_some]
    by_cases same : prior = value
    · subst same
      simp only [beq_self_eq_true, if_true, Option.some.injEq] at assigned ⊢
      rw [assigned]
    · simp [same] at assigned

theorem capture?_canon {rule : RewriteRule} {spec : RuleBindingSpec} (increasing : IncreasingSpines rule spec)
    {ambient depth : Nat} {site : RulePatternSite} {path : List Nat} {assignment final : ScopedRuleMatching.Assignment}
    {name : String} {target : Pattern}
    (captured : capture? rule spec ambient depth site path assignment name target = some final) :
    capture? rule spec ambient depth site path (canonAssignment assignment) name (canon target) =
      some (canonAssignment final) := by
  unfold capture? at captured ⊢
  simp only [bind, Option.bind_eq_some_iff] at captured ⊢
  obtain ⟨dependencies, declared, arguments, found, value, recovered, assigned⟩ := captured
  exact ⟨dependencies, declared, arguments, found, canonValue value,
    recoverValue?_canon recovered (increasing name site path arguments found depth), assign_canon assigned⟩

theorem unordered_of_ne_vec {kind : CollType} (notVector : kind ≠ .vec) : Unordered kind = true := by
  cases kind <;> simp_all [Unordered]

theorem hashBag_of_ne {kind : CollType} (notVector : kind ≠ .vec) (notSet : kind ≠ .hashSet) : kind = .hashBag := by
  cases kind <;> simp_all

/-- The residual of a sorted list after selecting one element is the sorted residual. -/
theorem sortLex_eraseIdx (targets : List Pattern) (selected : Nat) (within : selected < targets.length) :
    ∃ (index : Nat) (inside : index < (sortLex (targets.map canon)).length),
      (sortLex (targets.map canon))[index] = canon targets[selected] ∧
      (sortLex (targets.map canon)).eraseIdx index = sortLex ((targets.eraseIdx selected).map canon) := by
  have member : canon targets[selected] ∈ sortLex (targets.map canon) :=
    (sortLex_perm _).mem_iff.mpr (List.mem_map_of_mem (List.getElem_mem within))
  obtain ⟨index, inside, found⟩ := List.getElem_of_mem member
  refine ⟨index, inside, found, ?_⟩
  refine List.Perm.eq_of_pairwise' ((sortLex_pairwise _).sublist (List.eraseIdx_sublist _ _)) (sortLex_pairwise _) ?_
  have whole : List.Perm (canon targets[selected] :: (sortLex (targets.map canon)).eraseIdx index) (targets.map canon) := by
    have := List.getElem_cons_eraseIdx_perm inside
    rw [found] at this
    exact this.trans (sortLex_perm _)
  have original : List.Perm (canon targets[selected] :: (targets.eraseIdx selected).map canon) (targets.map canon) := by
    have := (List.getElem_cons_eraseIdx_perm within).map canon
    simpa [List.map_cons] using this
  exact ((whole.trans original.symm).cons_inv).trans (sortLex_perm _).symm

theorem captureRest?_canon {rule : RewriteRule} {spec : RuleBindingSpec} (increasing : IncreasingSpines rule spec)
    {ambient depth : Nat} {site : RulePatternSite} {path : List Nat} {assignment final : ScopedRuleMatching.Assignment}
    {name : String} {kind : CollType} {elements : List Pattern}
    (captured : captureRest? rule spec ambient depth site path assignment name kind elements = some final) :
    captureRest? rule spec ambient depth site path (canonAssignment assignment) name kind
        (arrange kind (elements.map canon)) = some (canonAssignment final) := by
  unfold captureRest? at captured ⊢
  have := capture?_canon increasing captured
  rwa [canon_collection] at this

mutual
  /-- **Every match of a schema that decomposes no set has a match at the subject's canonical
  form**, with canonical captures. -/
  theorem matches_canon {rule : RewriteRule} {spec : RuleBindingSpec} (increasing : IncreasingSpines rule spec)
      {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth : Nat}
      {initial final : ScopedRuleMatching.Assignment} {schema target : Pattern} (free : setFree schema = true)
      (matched : Matches rule spec ambient site path depth initial schema target final) :
      Matches rule spec ambient site path depth (canonAssignment initial) schema (canon target)
        (canonAssignment final) := by
    cases matched with
    | capture captured => exact .capture (capture?_canon increasing captured)
    | bound => rw [canon]; exact .bound
    | constructor arguments =>
      simp only [setFree] at free
      rw [canon_apply]; exact .constructor (arguments_canon increasing (setFreeList_iff.mp free) arguments)
    | binder body =>
      simp only [setFree] at free
      rw [canon]; exact .binder (matches_canon increasing free body)
    | binders body =>
      simp only [setFree] at free
      rw [canon]; exact .binders (matches_canon increasing free body)
    | substitution body replacement =>
      simp only [setFree, Bool.and_eq_true] at free
      rw [canon]; exact .substitution (matches_canon increasing free.1 body) (matches_canon increasing free.2 replacement)
    | bag notVector bag =>
      obtain ⟨notSet, elementsFree⟩ := setFree_collection free
      rw [canon_collection]
      exact .bag notVector (bag_canon increasing elementsFree (hashBag_of_ne notVector notSet) bag)
    | vector arguments =>
      obtain ⟨_, elementsFree⟩ := setFree_collection free
      rw [canon_collection, arrange_vec]
      exact .vector (arguments_canon increasing elementsFree arguments)
    | vectorRest arguments captured =>
      obtain ⟨_, elementsFree⟩ := setFree_collection free
      rw [canon_collection, arrange_vec]
      have front := arguments_canon increasing elementsFree arguments
      have rest := captureRest?_canon increasing captured
      rw [arrange_vec] at rest
      rw [List.map_take] at front
      rw [List.map_drop] at rest
      exact .vectorRest front rest
  termination_by sizeOf schema

  theorem arguments_canon {rule : RewriteRule} {spec : RuleBindingSpec} (increasing : IncreasingSpines rule spec)
      {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth index : Nat}
      {initial final : ScopedRuleMatching.Assignment} {schemas targets : List Pattern}
      (free : ∀ schema ∈ schemas, setFree schema = true)
      (matched : Arguments rule spec ambient site path depth initial index schemas targets final) :
      Arguments rule spec ambient site path depth (canonAssignment initial) index schemas (targets.map canon)
        (canonAssignment final) := by
    cases matched with
    | nil => exact .nil
    | cons head tail =>
      exact .cons (matches_canon increasing (free _ (.head _)) head)
        (arguments_canon increasing (fun schema member => free schema (.tail _ member)) tail)
  termination_by sizeOf schemas

  /-- A bag match selects from the sorted canonical elements; the residual of a sorted list is
  sorted. -/
  theorem bag_canon {rule : RewriteRule} {spec : RuleBindingSpec} (increasing : IncreasingSpines rule spec)
      {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth index : Nat}
      {initial final : ScopedRuleMatching.Assignment} {schemas : List Pattern} {rest : Option String}
      (free : ∀ schema ∈ schemas, setFree schema = true) {kind : CollType} (bag : kind = .hashBag)
      {targets : List Pattern}
      (matched : Bag rule spec ambient site path depth initial index schemas rest kind targets final) :
      Bag rule spec ambient site path depth (canonAssignment initial) index schemas rest kind
        (arrange kind (targets.map canon)) (canonAssignment final) := by
    subst bag
    cases matched with
    | nil => rw [List.map_nil, arrange_bag]; exact .nil
    | rest captured => exact .rest (captureRest?_canon increasing captured)
    | cons selected within head tail =>
      obtain ⟨position, inside, found, residual⟩ := sortLex_eraseIdx _ selected within
      have headCanon := matches_canon increasing (free _ (.head _)) head
      rw [← found] at headCanon
      have tailCanon := bag_canon increasing (fun schema member => free schema (.tail _ member)) rfl tail
      rw [arrange_bag] at tailCanon ⊢
      rw [← residual] at tailCanon
      exact .cons position inside headCanon tailCanon
  termination_by sizeOf schemas
end

end Mettapedia.OSLF.MeTTaIL.CanonicalBags
