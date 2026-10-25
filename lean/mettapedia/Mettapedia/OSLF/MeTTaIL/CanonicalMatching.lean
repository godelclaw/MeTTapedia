import Mettapedia.OSLF.MeTTaIL.CanonicalRenaming
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatch
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine

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

/-! ## Retaining traces when the subject is already canonical -/

theorem canonical_of_map_eq {patterns : List Pattern}
    (fixed : patterns.map canon = patterns) : ∀ pattern ∈ patterns, canon pattern = pattern := by
  induction patterns with
  | nil => simp
  | cons head tail ih =>
    have parts := List.cons.inj fixed
    intro pattern member
    rcases List.mem_cons.mp member with rfl | later
    · exact parts.1
    · exact ih parts.2 pattern later

theorem canonical_of_arranged {kind : CollType} {patterns : List Pattern}
    (fixed : arrange kind (patterns.map canon) = patterns) :
    ∀ pattern ∈ patterns, canon pattern = pattern := by
  intro pattern member
  have arranged : pattern ∈ arrange kind (patterns.map canon) := by rw [fixed]; exact member
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp ((arrange_mem pattern).mp arranged)
  exact canon_idempotent original

/-- Every retained residual of an already canonical collection is canonical.
For sets, both sortedness and absence of repeated elements are inherited. -/
theorem arranged_sublist {kind : CollType} {patterns residual : List Pattern}
    (fixed : arrange kind (patterns.map canon) = patterns) (retained : residual.Sublist patterns) :
    arrange kind (residual.map canon) = residual := by
  have mapped : residual.map canon = residual := by
    conv_rhs => rw [← List.map_id residual]
    exact List.map_congr_left (fun pattern member => canonical_of_arranged fixed pattern (retained.subset member))
  rw [mapped]
  cases kind with
  | vec => rfl
  | hashBag =>
    have sorted : patterns.Pairwise PatternLe := by
      rw [← fixed]
      exact sortLex_pairwise _
    exact List.Perm.eq_of_pairwise' (sortLex_pairwise _) (sorted.sublist retained) (sortLex_perm _)
  | hashSet =>
    have sorted : patterns.Pairwise PatternLe := by
      rw [← fixed]
      exact (sortLex_pairwise _).sublist (List.dedup_sublist _)
    have unique : patterns.Nodup := by rw [← fixed]; exact List.nodup_dedup _
    have sortedResidual : sortLex residual = residual :=
      List.Perm.eq_of_pairwise' (sortLex_pairwise _) (sorted.sublist retained) (sortLex_perm _)
    rw [arrange_set, sortedResidual]
    exact List.dedup_eq_self.mpr (unique.sublist retained)

mutual
  /-- On canonical subjects, canonicalizing captures preserves an ordinary
  traced match and its exact allocation history. Unlike arbitrary-subject
  normalization, this statement needs no set-free schema restriction. -/
  theorem traced_matches_canonical_subject {rule : RewriteRule} {spec : RuleBindingSpec}
      (increasing : IncreasingSpines rule spec)
      {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth : Nat}
      {initial final : Assignment} {schema target : Pattern}
      {trace : List GeneralScopedMatchMachine.BagChoice}
      (matched : GeneralScopedMatchMachine.TracedMatches rule spec ambient site path depth
        initial schema target trace final) (canonical : canon target = target) :
      GeneralScopedMatchMachine.TracedMatches rule spec ambient site path depth
        (canonAssignment initial) schema target trace (canonAssignment final) := by
    cases matched with
    | capture captured =>
      exact .capture (by simpa only [canonical] using capture?_canon increasing captured)
    | bound => exact .bound
    | constructor arguments =>
      simp only [canon_apply, Pattern.apply.injEq, true_and] at canonical
      exact .constructor (traced_arguments_canonical_subject increasing arguments
        (canonical_of_map_eq canonical))
    | binder body =>
      simp only [canon, Pattern.lambda.injEq, true_and] at canonical
      exact .binder (traced_matches_canonical_subject increasing body canonical)
    | binders body =>
      simp only [canon, Pattern.multiLambda.injEq, true_and] at canonical
      exact .binders (traced_matches_canonical_subject increasing body canonical)
    | substitution body replacement =>
      simp only [canon, Pattern.subst.injEq] at canonical
      exact .substitution
        (traced_matches_canonical_subject increasing body canonical.1)
        (traced_matches_canonical_subject increasing replacement canonical.2)
    | bag notVector matching =>
      simp only [canon_collection, Pattern.collection.injEq, true_and, and_true] at canonical
      exact .bag notVector (traced_bag_canonical_subject increasing matching canonical)
    | vector arguments =>
      simp only [canon_collection, arrange_vec, Pattern.collection.injEq, true_and, and_true] at canonical
      exact .vector (traced_arguments_canonical_subject increasing arguments (canonical_of_map_eq canonical))
    | vectorRest arguments captured =>
      simp only [canon_collection, arrange_vec, Pattern.collection.injEq, true_and, and_true] at canonical
      have each := canonical_of_map_eq canonical
      have rest := captureRest?_canon increasing captured
      rw [arranged_sublist (kind := .vec) canonical (List.drop_sublist _ _)] at rest
      exact .vectorRest
        (traced_arguments_canonical_subject increasing arguments
          (fun pattern member => each pattern (List.mem_of_mem_take member))) rest
  termination_by sizeOf schema

  theorem traced_arguments_canonical_subject {rule : RewriteRule} {spec : RuleBindingSpec}
      (increasing : IncreasingSpines rule spec)
      {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth index : Nat}
      {initial final : Assignment} {schemas targets : List Pattern}
      {trace : List GeneralScopedMatchMachine.BagChoice}
      (matched : GeneralScopedMatchMachine.TracedArguments rule spec ambient site path depth
        initial index schemas targets trace final)
      (canonical : ∀ target ∈ targets, canon target = target) :
      GeneralScopedMatchMachine.TracedArguments rule spec ambient site path depth
        (canonAssignment initial) index schemas targets trace (canonAssignment final) := by
    cases matched with
    | nil => exact .nil
    | cons head tail =>
      exact .cons (traced_matches_canonical_subject increasing head (canonical _ List.mem_cons_self))
        (traced_arguments_canonical_subject increasing tail
          (fun target member => canonical target (List.mem_cons_of_mem _ member)))
  termination_by sizeOf schemas

  theorem traced_bag_canonical_subject {rule : RewriteRule} {spec : RuleBindingSpec}
      (increasing : IncreasingSpines rule spec)
      {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth index : Nat}
      {initial final : Assignment} {schemas targets : List Pattern} {kind : CollType}
      {rest : Option String} {trace : List GeneralScopedMatchMachine.BagChoice}
      (matched : GeneralScopedMatchMachine.TracedBag rule spec ambient site path depth
        initial index schemas rest kind targets trace final)
      (canonical : arrange kind (targets.map canon) = targets) :
      GeneralScopedMatchMachine.TracedBag rule spec ambient site path depth
        (canonAssignment initial) index schemas rest kind targets trace (canonAssignment final) := by
    cases matched with
    | nil => exact .nil
    | rest captured =>
      exact .rest (by simpa only [canonical] using captureRest?_canon increasing captured)
    | cons selected within head tail =>
      exact .cons selected within
        (traced_matches_canonical_subject increasing head
          (canonical_of_arranged canonical _ (List.getElem_mem within)))
        (traced_bag_canonical_subject increasing tail
          (arranged_sublist canonical (List.eraseIdx_sublist _ _)))
  termination_by sizeOf schemas
end

/-! ## Exact reads of canonical provider values -/

mutual
  /-- The existing object-template fragment, with every used occurrence
  supplied by an increasing variable renaming. Explicit substitution needs
  its own operation coherence; an open collection tail is not an object
  template. The check inspects actual occurrence addresses and binder depths. -/
  def checkCanonicalRead (rule : RewriteRule) (spec : RuleBindingSpec)
      (site : RulePatternSite) (path : List Nat) (depth : Nat) : Pattern → Bool
    | .fvar name =>
        (arguments? rule spec name site path).any fun arguments =>
          (variableSpine? depth arguments).any fun indices => decide (indices.Pairwise (· < ·))
    | .bvar _ => true
    | .apply _ arguments => checkCanonicalReadArgs rule spec site path depth 0 arguments
    | .lambda _ body => checkCanonicalRead rule spec site (path ++ [0]) (depth + 1) body
    | .multiLambda arity _ body => checkCanonicalRead rule spec site (path ++ [0]) (depth + arity) body
    | .subst _ _ => false
    | .collection _ elements rest => rest.isNone && checkCanonicalReadArgs rule spec site path depth 0 elements
  termination_by pattern => sizeOf pattern

  def checkCanonicalReadArgs (rule : RewriteRule) (spec : RuleBindingSpec)
      (site : RulePatternSite) (path : List Nat) (depth index : Nat) : List Pattern → Bool
    | [] => true
    | pattern :: patterns =>
        checkCanonicalRead rule spec site (path ++ [index]) depth pattern &&
          checkCanonicalReadArgs rule spec site path depth (index + 1) patterns
  termination_by patterns => sizeOf patterns
end

mutual
  /-- Any checked object template which originally reads a canonical value
  reads exactly that same value after capture normalization. The theorem is
  structural in the entire template, rather than specific to bare variables. -/
  theorem instantiateWith?_canonical_result (operation : Pattern → Pattern → Pattern)
      (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
      (site : RulePatternSite) (path : List Nat) (depth : Nat)
      (assignment : Assignment) (pattern result : Pattern)
      (checked : checkCanonicalRead rule spec site path depth pattern = true)
      (read : ScopedRuleMatching.instantiateWith? operation rule spec ambient site path depth assignment pattern = some result)
      (canonical : canon result = result) :
      ScopedRuleMatching.instantiateWith? operation rule spec ambient site path depth
        (canonAssignment assignment) pattern = some result := by
    cases pattern with
    | fvar name =>
      simp only [checkCanonicalRead, Option.any_eq_true, decide_eq_true_eq] at checked
      obtain ⟨arguments, declared, indices, spine, increasing⟩ := checked
      simp only [ScopedRuleMatching.instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at read ⊢
      obtain ⟨value, found, actual, actualFound, projected⟩ := read
      cases Option.some.inj (declared.symm.trans actualFound)
      refine ⟨canonValue value, ?_, arguments, declared, ?_⟩
      · rw [lookup_canonAssignment, found]; rfl
      · simpa only [canonValue, canonical] using instantiateValue?_canon spine increasing projected
    | bvar index => simpa only [ScopedRuleMatching.instantiateWith?] using read
    | apply label arguments =>
      simp only [ScopedRuleMatching.instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at read ⊢
      obtain ⟨values, valuesRead, rfl⟩ := read
      simp only [canon_apply, Pattern.apply.injEq, true_and] at canonical
      exact ⟨values, instantiateArgsWith?_canonical_results operation rule spec ambient site path depth
        assignment 0 arguments values (by simpa only [checkCanonicalRead] using checked) valuesRead (canonical_of_map_eq canonical), rfl⟩
    | lambda binder body =>
      simp only [ScopedRuleMatching.instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at read ⊢
      obtain ⟨value, valueRead, rfl⟩ := read
      simp only [canon, Pattern.lambda.injEq, true_and] at canonical
      exact ⟨value, instantiateWith?_canonical_result operation rule spec ambient site (path ++ [0])
        (depth + 1) assignment body value (by simpa only [checkCanonicalRead] using checked) valueRead canonical, rfl⟩
    | multiLambda arity binders body =>
      simp only [ScopedRuleMatching.instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at read ⊢
      obtain ⟨value, valueRead, rfl⟩ := read
      simp only [canon, Pattern.multiLambda.injEq, true_and] at canonical
      exact ⟨value, instantiateWith?_canonical_result operation rule spec ambient site (path ++ [0])
        (depth + arity) assignment body value (by simpa only [checkCanonicalRead] using checked) valueRead canonical, rfl⟩
    | subst body replacement => simp only [checkCanonicalRead, Bool.false_eq_true] at checked
    | collection kind elements rest =>
      cases rest with
      | some name => simp only [checkCanonicalRead, Option.isNone_some, Bool.false_and, Bool.false_eq_true] at checked
      | none =>
        simp only [checkCanonicalRead, Option.isNone_none, Bool.true_and] at checked
        simp only [ScopedRuleMatching.instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.some.injEq] at read ⊢
        obtain ⟨values, valuesRead, rfl⟩ := read
        simp only [canon_collection, Pattern.collection.injEq, true_and, and_true] at canonical
        exact ⟨values, instantiateArgsWith?_canonical_results operation rule spec ambient site path depth
          assignment 0 elements values checked valuesRead (canonical_of_arranged canonical), rfl⟩
  termination_by sizeOf pattern

  theorem instantiateArgsWith?_canonical_results (operation : Pattern → Pattern → Pattern)
      (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
      (site : RulePatternSite) (path : List Nat) (depth : Nat)
      (assignment : Assignment) (index : Nat) (patterns results : List Pattern)
      (checked : checkCanonicalReadArgs rule spec site path depth index patterns = true)
      (read : ScopedRuleMatching.instantiateArgsWith? operation rule spec ambient site path depth
        assignment index patterns = some results)
      (canonical : ∀ result ∈ results, canon result = result) :
      ScopedRuleMatching.instantiateArgsWith? operation rule spec ambient site path depth
        (canonAssignment assignment) index patterns = some results := by
    cases patterns with
    | nil => simpa only [ScopedRuleMatching.instantiateArgsWith?] using read
    | cons pattern patterns =>
      simp only [checkCanonicalReadArgs, Bool.and_eq_true] at checked
      simp only [ScopedRuleMatching.instantiateArgsWith?, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at read ⊢
      obtain ⟨head, headRead, tail, tailRead, rfl⟩ := read
      exact ⟨head, instantiateWith?_canonical_result operation rule spec ambient site (path ++ [index]) depth
        assignment pattern head checked.1 headRead (canonical head List.mem_cons_self),
        tail, instantiateArgsWith?_canonical_results operation rule spec ambient site path depth assignment
          (index + 1) patterns tail checked.2 tailRead
          (fun result member => canonical result (List.mem_cons_of_mem _ member)), rfl⟩
  termination_by sizeOf patterns
end

end Mettapedia.OSLF.MeTTaIL.CanonicalBags
