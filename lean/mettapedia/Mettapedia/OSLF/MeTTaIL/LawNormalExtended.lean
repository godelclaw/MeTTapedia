import Mettapedia.OSLF.MeTTaIL.LawNormalAbsorb
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineComparison

/-!
# Extended rules absorb flattened siblings

A rule whose left side is a collection of a flattening kind with a rest, and whose right side is
a collection of that kind with the same rest, fires at a nested collection exactly as it fires at
the flattened parent: the rest absorbs the parent's other elements. This is the extension
condition of rewriting modulo associativity and commutativity (Peterson and Stickel).

- `matches_unassigned`: matching never assigns a name outside its schema;
- `captureRest?_root`: a rest without dependencies at the root captures its residual collection;
- `bag_siblings`: a bag match with a rest also matches with siblings added, the rest absorbing them.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CanonicalBags

open Syntax CollectionLaws RuleBinding ScopedRuleMatching GeneralScopedMatch

theorem lookup_cons_ne {assignment : ScopedRuleMatching.Assignment} {name other : String} {value : ContextualValue}
    (different : other ≠ name) : lookup ((other, value) :: assignment) name = lookup assignment name := by
  unfold lookup
  rw [List.find?_cons_of_neg (by simpa using different)]

theorem assign_other {assignment final : ScopedRuleMatching.Assignment} {name other : String} {value : ContextualValue}
    (assigned : assign assignment other value = some final) (different : other ≠ name) :
    lookup final name = lookup assignment name := by
  unfold assign at assigned
  cases stored : lookup assignment other with
  | none =>
    rw [stored] at assigned
    cases assigned
    exact lookup_cons_ne different
  | some prior =>
    rw [stored] at assigned
    simp only at assigned
    by_cases same : (prior == value) = true
    · rw [if_pos same] at assigned; cases assigned; rfl
    · rw [if_neg same] at assigned; cases assigned

theorem capture?_other {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth : Nat} {site : RulePatternSite}
    {path : List Nat} {assignment final : ScopedRuleMatching.Assignment} {other name : String} {target : Pattern}
    (captured : capture? rule spec ambient depth site path assignment other target = some final) (different : other ≠ name) :
    lookup final name = lookup assignment name := by
  unfold capture? at captured
  simp only [bind, Option.bind_eq_some_iff] at captured
  obtain ⟨_, _, _, _, _, _, assigned⟩ := captured
  exact assign_other assigned different

mutual
  /-- **Matching never assigns a name outside its schema.** -/
  theorem matches_unassigned {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite}
      {path : List Nat} {depth : Nat} {initial final : ScopedRuleMatching.Assignment} {schema target : Pattern}
      {name : String} (matched : Matches rule spec ambient site path depth initial schema target final)
      (outside : name ∉ schema.freeFvarNames) (unassigned : lookup initial name = none) : lookup final name = none := by
    cases matched with
    | capture captured =>
      rw [capture?_other captured (fun same => outside (by simp [Pattern.freeFvarNames, same])), unassigned]
    | bound => exact unassigned
    | constructor arguments =>
      exact arguments_unassigned arguments (fun schema member inside => outside (by
        simp only [Pattern.freeFvarNames, List.mem_flatMap]; exact ⟨schema, member, inside⟩)) unassigned
    | binder body => exact matches_unassigned body (by simpa [Pattern.freeFvarNames] using outside) unassigned
    | binders body => exact matches_unassigned body (by simpa [Pattern.freeFvarNames] using outside) unassigned
    | substitution body replacement =>
      simp only [Pattern.freeFvarNames, List.mem_append, not_or] at outside
      exact matches_unassigned replacement outside.2 (matches_unassigned body outside.1 unassigned)
    | bag _ bag =>
      simp only [Pattern.freeFvarNames, List.mem_append, List.mem_flatMap, not_or, not_exists, not_and] at outside
      exact bag_unassigned bag (fun schema member inside => outside.1 schema member inside)
        (fun same => outside.2 (by rw [same]; simp)) unassigned
    | vector arguments =>
      exact arguments_unassigned arguments (fun schema member inside => outside (by
        simp only [Pattern.freeFvarNames, List.mem_append, List.mem_flatMap]; exact .inl ⟨schema, member, inside⟩))
        unassigned
    | vectorRest arguments captured =>
      simp only [Pattern.freeFvarNames, List.mem_append, List.mem_flatMap, not_or, not_exists, not_and] at outside
      have middle := arguments_unassigned arguments (fun schema member inside => outside.1 schema member inside) unassigned
      unfold captureRest? at captured
      rw [capture?_other captured (fun same => outside.2 (by rw [same]; simp)), middle]
  termination_by sizeOf schema

  theorem arguments_unassigned {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite}
      {path : List Nat} {depth index : Nat} {initial final : ScopedRuleMatching.Assignment} {schemas targets : List Pattern}
      {name : String} (matched : Arguments rule spec ambient site path depth initial index schemas targets final)
      (outside : ∀ schema ∈ schemas, name ∉ schema.freeFvarNames) (unassigned : lookup initial name = none) :
      lookup final name = none := by
    cases matched with
    | nil => exact unassigned
    | cons head tail =>
      exact arguments_unassigned tail (fun schema member => outside schema (.tail _ member))
        (matches_unassigned head (outside _ (.head _)) unassigned)
  termination_by sizeOf schemas

  theorem bag_unassigned {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite}
      {path : List Nat} {depth index : Nat} {initial final : ScopedRuleMatching.Assignment} {schemas : List Pattern}
      {rest : Option String} {kind : CollType} {targets : List Pattern} {name : String}
      (matched : Bag rule spec ambient site path depth initial index schemas rest kind targets final)
      (outside : ∀ schema ∈ schemas, name ∉ schema.freeFvarNames) (notRest : rest ≠ some name)
      (unassigned : lookup initial name = none) : lookup final name = none := by
    cases matched with
    | nil => exact unassigned
    | rest captured =>
      unfold captureRest? at captured
      rw [capture?_other captured (fun same => notRest (by rw [same])), unassigned]
    | cons _ _ head tail =>
      exact bag_unassigned tail (fun schema member => outside schema (.tail _ member)) notRest
        (matches_unassigned head (outside _ (.head _)) unassigned)
  termination_by sizeOf schemas
end

/-- **A rest without dependencies at the root captures its residual collection.** -/
theorem captureRest?_root {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite}
    {path : List Nat} {assignment : ScopedRuleMatching.Assignment} {name : String} {kind : CollType}
    {elements : List Pattern} (noDependencies : dependencies? spec name = some [])
    (noArguments : arguments? rule spec name site path = some [])
    (inScope : (Pattern.collection kind elements none).isWellScopedAt ambient = true) :
    captureRest? rule spec ambient 0 site path assignment name kind elements =
      assign assignment name ⟨[], ambient, .collection kind elements none⟩ := by
  unfold captureRest? capture?
  simp only [noDependencies, noArguments, bind, Option.bind_some]
  have recovered : recoverValue? [] ambient 0 [] (.collection kind elements none) =
      some ⟨[], ambient, .collection kind elements none⟩ := by
    unfold recoverValue?
    have spine : variableSpine? 0 [] = some [] := rfl
    have identity : recoveryAssignment 0 0 ambient [] = Pattern.bvar := by
      funext index; simp [recoveryAssignment]
    have forward : instantiateValue? ⟨[], ambient, .collection kind elements none⟩ ambient 0 [] =
        some (.collection kind elements none) := by
      apply (instantiateValue?_eq_some_iff _ _ _ _ _).mpr
      have occurrence : occurrenceAssignment 0 0 [] = Pattern.bvar := by
        funext index; simp [occurrenceAssignment]
      refine ⟨rfl, rfl, by simpa using inScope, by simp, ?_, by simpa using inScope⟩
      simp only [List.length_nil, occurrence, ContextSubstitution.substitute_id]
    simp [inScope, spine, identity, forward]
  rw [recovered]
  rfl

/-- A successful capture recovered a well-scoped target. -/
theorem captureRest?_scoped {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth : Nat} {site : RulePatternSite}
    {path : List Nat} {assignment final : ScopedRuleMatching.Assignment} {name : String} {kind : CollType}
    {elements : List Pattern}
    (captured : captureRest? rule spec ambient depth site path assignment name kind elements = some final) :
    (Pattern.collection kind elements none).isWellScopedAt (depth + ambient) = true := by
  unfold captureRest? capture? at captured
  simp only [bind, Option.bind_eq_some_iff] at captured
  obtain ⟨_, _, _, _, value, recovered, _⟩ := captured
  unfold recoverValue? at recovered
  split at recovered
  · cases recovered
  · rename_i inScope; simpa using inScope

private theorem getElem_middle {α : Type} (front targets back : List α) (index : Nat) (within : index < targets.length) :
    (front ++ targets ++ back)[front.length + index]'(by simp; omega) = targets[index] := by
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
  simp

private theorem eraseIdx_middle {α : Type} (front targets back : List α) (index : Nat) (within : index < targets.length) :
    (front ++ targets ++ back).eraseIdx (front.length + index) = front ++ targets.eraseIdx index ++ back := by
  rw [List.append_assoc, List.eraseIdx_append_of_length_le (by omega), Nat.add_sub_cancel_left,
    List.eraseIdx_append_of_lt_length within, List.append_assoc]

/-- **A bag match with a rest also matches with siblings added**, the rest absorbing them. -/
theorem bag_siblings {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite}
    {path : List Nat} {name : String} {kind : CollType} (noDependencies : dependencies? spec name = some [])
    (front back : List Pattern) (siblingsScoped : ∀ item ∈ front ++ back, item.isWellScopedAt ambient = true) :
    ∀ {index : Nat} {schemas targets : List Pattern} {initial final : ScopedRuleMatching.Assignment},
      Bag rule spec ambient site path 0 initial index schemas (some name) kind targets final →
      arguments? rule spec name site (path ++ [index + schemas.length]) = some [] →
      (∀ schema ∈ schemas, name ∉ schema.freeFvarNames) → lookup initial name = none →
      ∃ middle residual, final = (name, ⟨[], ambient, .collection kind residual none⟩) :: middle ∧
        (∀ item ∈ residual, item ∈ targets) ∧
        Bag rule spec ambient site path 0 initial index schemas (some name) kind (front ++ targets ++ back)
          ((name, ⟨[], ambient, .collection kind (front ++ residual ++ back) none⟩) :: middle)
  | index, [], targets, initial, final, .rest captured, noArguments, _, unassigned => by
    have inScope := captureRest?_scoped captured
    simp only [Nat.zero_add] at inScope
    simp only [List.length_nil, Nat.add_zero] at noArguments
    rw [captureRest?_root noDependencies noArguments inScope] at captured
    unfold assign at captured
    rw [unassigned] at captured
    cases captured
    refine ⟨initial, targets, rfl, fun _ member => member, .rest ?_⟩
    have extendedScope : (Pattern.collection kind (front ++ targets ++ back) none).isWellScopedAt ambient = true := by
      simp only [Pattern.isWellScopedAt, isWellScopedListAt_iff, List.mem_append] at inScope ⊢
      rintro item ((inFront | inTargets) | inBack)
      · exact siblingsScoped item (by simp [inFront])
      · exact inScope item inTargets
      · exact siblingsScoped item (by simp [inBack])
    rw [captureRest?_root noDependencies noArguments extendedScope]
    unfold assign
    rw [unassigned]
  | index, schema :: schemas, targets, initial, final, .cons selected within head tail, noArguments, outside,
      unassigned => by
    have middleUnassigned := matches_unassigned head (outside schema (.head _)) unassigned
    obtain ⟨middle, residual, finalEq, residualIn, extended⟩ := bag_siblings noDependencies front back siblingsScoped tail
      (by simpa [Nat.add_assoc, Nat.add_comm 1] using noArguments)
      (fun other member => outside other (.tail _ member)) middleUnassigned
    refine ⟨middle, residual, finalEq, fun item member => List.mem_of_mem_eraseIdx (residualIn item member), ?_⟩
    have within' : front.length + selected < (front ++ targets ++ back).length := by simp; omega
    have headExtended := head
    rw [← getElem_middle front targets back selected within] at headExtended
    rw [← eraseIdx_middle front targets back selected within] at extended
    exact .cons (front.length + selected) within' headExtended extended

mutual
  /-- **Instantiation ignores the value of a name the pattern does not mention.** -/
  theorem instantiate_irrelevant (operation : Pattern → Pattern → Pattern) (rule : RewriteRule) (spec : RuleBindingSpec)
      (ambient : Nat) {name : String} (value value' : ContextualValue) (assignment : ScopedRuleMatching.Assignment) :
      ∀ (pattern : Pattern) (site : RulePatternSite) (path : List Nat) (depth : Nat), name ∉ pattern.freeFvarNames →
        instantiateWith? operation rule spec ambient site path depth ((name, value) :: assignment) pattern =
          instantiateWith? operation rule spec ambient site path depth ((name, value') :: assignment) pattern
    | .fvar other, site, path, depth, outside => by
      have different : name ≠ other := fun same => outside (by simp [Pattern.freeFvarNames, same])
      rw [instantiateWith?, instantiateWith?, lookup_cons_ne different, lookup_cons_ne different]
    | .bvar _, _, _, _, _ => by rw [instantiateWith?, instantiateWith?]
    | .apply label arguments, site, path, depth, outside => by
      rw [instantiateWith?, instantiateWith?, instantiateArgs_irrelevant operation rule spec ambient value value' assignment
        arguments site path depth 0 (fun schema member inside => outside (by
          simp only [Pattern.freeFvarNames, List.mem_flatMap]; exact ⟨schema, member, inside⟩))]
    | .lambda binder body, site, path, depth, outside => by
      rw [instantiateWith?, instantiateWith?, instantiate_irrelevant operation rule spec ambient value value' assignment body
        site (path ++ [0]) (depth + 1) (by simpa [Pattern.freeFvarNames] using outside)]
    | .multiLambda arity binders body, site, path, depth, outside => by
      rw [instantiateWith?, instantiateWith?, instantiate_irrelevant operation rule spec ambient value value' assignment body
        site (path ++ [0]) (depth + arity) (by simpa [Pattern.freeFvarNames] using outside)]
    | .subst body replacement, site, path, depth, outside => by
      simp only [Pattern.freeFvarNames, List.mem_append, not_or] at outside
      rw [instantiateWith?, instantiateWith?, instantiate_irrelevant operation rule spec ambient value value' assignment body
        site (path ++ [0]) (depth + 1) outside.1, instantiate_irrelevant operation rule spec ambient value value' assignment
        replacement site (path ++ [1]) depth outside.2]
    | .collection kind elements rest, site, path, depth, outside => by
      simp only [Pattern.freeFvarNames, List.mem_append, List.mem_flatMap, not_or, not_exists, not_and] at outside
      rw [instantiateWith?, instantiateWith?, instantiateArgs_irrelevant operation rule spec ambient value value' assignment
        elements site path depth 0 (fun schema member inside => outside.1 schema member inside)]
      cases rest with
      | none => rfl
      | some other =>
        have different : name ≠ other := fun same => outside.2 (by simp [same])
        simp only [lookup_cons_ne different]
  termination_by pattern => sizeOf pattern

  theorem instantiateArgs_irrelevant (operation : Pattern → Pattern → Pattern) (rule : RewriteRule)
      (spec : RuleBindingSpec) (ambient : Nat) {name : String} (value value' : ContextualValue)
      (assignment : ScopedRuleMatching.Assignment) :
      ∀ (patterns : List Pattern) (site : RulePatternSite) (path : List Nat) (depth index : Nat),
        (∀ pattern ∈ patterns, name ∉ pattern.freeFvarNames) →
        instantiateArgsWith? operation rule spec ambient site path depth ((name, value) :: assignment) index patterns =
          instantiateArgsWith? operation rule spec ambient site path depth ((name, value') :: assignment) index patterns
    | [], _, _, _, _, _ => by rw [instantiateArgsWith?, instantiateArgsWith?]
    | pattern :: patterns, site, path, depth, index, outside => by
      rw [instantiateArgsWith?, instantiateArgsWith?, instantiate_irrelevant operation rule spec ambient value value'
        assignment pattern site (path ++ [index]) depth (outside pattern (.head _)),
        instantiateArgs_irrelevant operation rule spec ambient value value' assignment patterns site path depth (index + 1)
          (fun other member => outside other (.tail _ member))]
  termination_by patterns => sizeOf patterns
end

/-- **The root rest splices its residual into the right side's collection.** -/
theorem instantiate_rest (operation : Pattern → Pattern → Pattern) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) {name : String} {kind : CollType} {schemas explicit residual : List Pattern}
    (middle : ScopedRuleMatching.Assignment) (noArguments : arguments? rule spec name .right [schemas.length] = some [])
    (inScope : (Pattern.collection kind residual none).isWellScopedAt ambient = true)
    (explicitFound : instantiateArgsWith? operation rule spec ambient .right [] 0
      ((name, ⟨[], ambient, .collection kind residual none⟩) :: middle) 0 schemas = some explicit) :
    instantiateWith? operation rule spec ambient .right [] 0
        ((name, ⟨[], ambient, .collection kind residual none⟩) :: middle) (.collection kind schemas (some name)) =
      some (.collection kind (explicit ++ residual) none) := by
  have value : instantiateValue? ⟨[], ambient, .collection kind residual none⟩ ambient 0 [] =
      some (.collection kind residual none) := by
    apply (instantiateValue?_eq_some_iff _ _ _ _ _).mpr
    have occurrence : occurrenceAssignment 0 0 [] = Pattern.bvar := by funext index; simp [occurrenceAssignment]
    refine ⟨rfl, rfl, by simpa using inScope, by simp, ?_, by simpa using inScope⟩
    simp only [List.length_nil, occurrence, ContextSubstitution.substitute_id]
  have found : lookup ((name, (⟨[], ambient, .collection kind residual none⟩ : ContextualValue)) :: middle) name =
      some ⟨[], ambient, .collection kind residual none⟩ := by
    simp [lookup]
  rw [instantiateWith?]
  simp [explicitFound, found, noArguments, value]

open Mettapedia.GSLT.LanguageDef.WellSorted

/-- The rule at an index is extended for a collection kind: its left side is a collection of that
kind with a rest and its right side a collection of that kind with the same rest, used nowhere
else, without dependencies, and it has no premises. -/
def ExtendedAt (environment : GeneralPremise.Environment) (index : Nat) (kind : CollType) : Prop :=
  ∀ rule spec, environment.language.rewrites[index]? = some rule →
    GeneralPremise.specification? environment index = some spec →
    ∃ left right name, rule.left = .collection kind left (some name) ∧ rule.right = .collection kind right (some name) ∧
      (∀ schema ∈ left, name ∉ schema.freeFvarNames) ∧ (∀ schema ∈ right, name ∉ schema.freeFvarNames) ∧
      dependencies? spec name = some [] ∧ arguments? rule spec name .left [left.length] = some [] ∧
      arguments? rule spec name .right [right.length] = some [] ∧ rule.premises = []

/-- **An extended rule firing at a nested collection fires at the collection with siblings added**:
the rest absorbs them, and the result gains them. -/
theorem rootFiring_absorbed {environment : GeneralPremise.Environment} {bound : List TypeExpr} {type type' : TypeExpr}
    {kind : CollType} {elements front back : List Pattern} {index : Nat}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event} {target : Pattern}
    (fired : GeneralPremise.RootFiring environment bound type (.collection kind elements none) index trace captured
      completed history target)
    (extended : ExtendedAt environment index kind) (notVector : kind ≠ .vec)
    (siblingsScoped : ∀ item ∈ front ++ back, item.isWellScopedAt bound.length = true)
    (siblingsObjects : ∀ item ∈ front ++ back, isObjectPattern item = true)
    (sourceSorted' : OpenPatternWellSorted environment.language environment.free bound type'
      (.collection kind (front ++ elements ++ back) none))
    (restTyped : ∀ (rule : RewriteRule) (name : String) (sort : TypeExpr) (residual : List Pattern),
      environment.language.rewrites[index]? = some rule → rule.typeContext.lookup name = some sort →
      (∀ item ∈ residual, item ∈ elements) →
      HasType environment.language environment.free bound (.collection kind residual none) sort →
      HasType environment.language environment.free bound (.collection kind (front ++ residual ++ back) none) sort)
    (targetSorted' : ∀ explicit residual : List Pattern, (∀ item ∈ residual, item ∈ elements) →
      OpenPatternWellSorted environment.language environment.free bound type (.collection kind (explicit ++ residual) none) →
      OpenPatternWellSorted environment.language environment.free bound type'
        (.collection kind (explicit ++ front ++ residual ++ back) none)) :
    ∃ trace' captured' explicit residual, target = .collection kind (explicit ++ residual) none ∧
      GeneralPremise.RootFiring environment bound type' (.collection kind (front ++ elements ++ back) none) index trace'
        captured' captured' history (.collection kind (explicit ++ front ++ residual ++ back) none) := by
  cases fired with
  | @fire _ _ _ _ _ rule spec _ _ _ _ selected specified admitted sourceSorted matched typed premises reduced
      targetSorted =>
    obtain ⟨left, right, name, leftEq, rightEq, outsideLeft, outsideRight, noDependencies, leftArguments,
      rightArguments, unconditional⟩ := extended rule spec selected specified
    rw [unconditional] at premises
    cases premises
    have matchedRoot := GeneralScopedMatchMachine.traced_iff_matches.mp ⟨_, matched⟩
    rw [leftEq] at matchedRoot
    have elementsScoped : ∀ item ∈ elements, item.isWellScopedAt bound.length = true := by
      have := sourceSorted.2.2.2
      unfold ScopeSafeAt at this
      simpa [Pattern.isWellScopedAt, isWellScopedListAt_iff] using this
    cases matchedRoot with
    | bag _ bagMatched =>
      obtain ⟨middle, residual, capturedEq, residualIn, extendedBag⟩ :=
        bag_siblings noDependencies front back siblingsScoped bagMatched (by simpa using leftArguments) outsideLeft rfl
      subst capturedEq
      have residualScoped : (Pattern.collection kind residual none).isWellScopedAt bound.length = true := by
        simp only [Pattern.isWellScopedAt, isWellScopedListAt_iff]
        exact fun item member => elementsScoped item (residualIn item member)
      have extendedScoped : (Pattern.collection kind (front ++ residual ++ back) none).isWellScopedAt bound.length = true := by
        simp only [Pattern.isWellScopedAt, isWellScopedListAt_iff, List.mem_append]
        rintro item ((inFront | inResidual) | inBack)
        · exact siblingsScoped item (by simp [inFront])
        · exact elementsScoped item (residualIn item inResidual)
        · exact siblingsScoped item (by simp [inBack])
      unfold reductWith? at reduced
      rw [rightEq] at reduced
      cases explicitFound : instantiateArgsWith? (ScopedReflectiveExecution.binderOperation environment.reflection rule)
          rule spec bound.length .right [] 0 ((name, ⟨[], bound.length, .collection kind residual none⟩) :: middle) 0
          right with
      | none =>
        rw [instantiateWith?] at reduced
        simp [explicitFound] at reduced
      | some explicit =>
        rw [instantiate_rest _ rule spec bound.length middle rightArguments residualScoped explicitFound] at reduced
        cases reduced
        obtain ⟨trace', traced⟩ := GeneralScopedMatchMachine.traced_iff_matches.mpr (Matches.bag notVector extendedBag)
        have explicitFound' : instantiateArgsWith? (ScopedReflectiveExecution.binderOperation environment.reflection rule)
            rule spec bound.length .right [] 0
            ((name, ⟨[], bound.length, .collection kind (front ++ residual ++ back) none⟩) :: middle) 0 right =
            some explicit := by
          rw [← instantiateArgs_irrelevant _ rule spec bound.length _ _ middle right .right [] 0 0 outsideRight]
          exact explicitFound
        refine ⟨trace', (name, ⟨[], bound.length, .collection kind (front ++ residual ++ back) none⟩) :: middle,
          explicit, residual, rfl, .fire selected specified admitted sourceSorted' ?_ ?_ ?_ ?_
          (targetSorted' explicit residual residualIn targetSorted)⟩
        · rw [leftEq]; exact traced
        · obtain ⟨sorts, objects⟩ := typed
          refine ⟨fun entryName value member => ?_, fun entryName value member => ?_⟩
          · rcases List.mem_cons.mp member with same | inMiddle
            · simp only [Prod.mk.injEq] at same
              obtain ⟨rfl, rfl⟩ := same
              obtain ⟨dependencies, sort, declared, sortFound, sameDependencies, sameAmbient, bodyTyped⟩ :=
                sorts entryName ⟨[], bound.length, .collection kind residual none⟩ (.head _)
              rw [noDependencies, Option.some.injEq] at declared
              subst declared
              exact ⟨[], sort, noDependencies, sortFound, rfl, sameAmbient,
                by simpa using restTyped rule entryName sort residual selected sortFound residualIn (by simpa using bodyTyped)⟩
            · exact sorts entryName value (.tail _ inMiddle)
          · rcases List.mem_cons.mp member with same | inMiddle
            · simp only [Prod.mk.injEq] at same
              obtain ⟨rfl, rfl⟩ := same
              have residualObject := objects entryName ⟨[], bound.length, .collection kind residual none⟩ (.head _)
              simp only [isObjectPattern, Bool.and_eq_true, isObjectPatternList_eq_all, List.all_eq_true] at residualObject ⊢
              refine ⟨rfl, fun item inside => ?_⟩
              simp only [List.mem_append] at inside
              rcases inside with (inFront | inResidual) | inBack
              · exact siblingsObjects item (by simp [inFront])
              · exact residualObject.2 item inResidual
              · exact siblingsObjects item (by simp [inBack])
            · exact objects entryName value (.tail _ inMiddle)
        · rw [unconditional]; exact .nil
        · unfold reductWith?
          rw [rightEq, instantiate_rest _ rule spec bound.length middle rightArguments extendedScoped explicitFound']
          simp [List.append_assoc]
    | vectorRest _ _ => exact absurd rfl notVector

/-! ## Typing of collections of a flattening kind -/

variable {laws : List Laws} {language : LanguageDef} {free : FreeTypeContext}

/-- Every bare constructor of a flattening kind has the same category. -/
def UniqueBare (laws : List Laws) (language : LanguageDef) : Prop :=
  ∀ law kind, lawFor laws kind = some law → ∀ rule₁ ∈ language.terms, ∀ rule₂ ∈ language.terms,
    ∀ name₁ element₁ name₂ element₂, rule₁.params = [.simple name₁ (.collection kind element₁)] →
      rule₂.params = [.simple name₂ (.collection kind element₂)] → rule₁.category = rule₂.category

/-- A typed collection's elements share one type, and any elements of that type give a collection
of the same type. -/
theorem collection_typing {bound : List TypeExpr} {kind : CollType} {elements : List Pattern} {rest : Option String}
    {type : TypeExpr} (typed : HasType language free bound (.collection kind elements rest) type) :
    ∃ element, ElementsHaveType language free bound elements element ∧
      ∀ (elements' : List Pattern) (rest' : Option String), ElementsHaveType language free bound elements' element →
        HasType language free bound (.collection kind elements' rest') type := by
  rcases hasType_collection_inv typed with ⟨element, rfl, items⟩ | ⟨rule, name, element, declared, parameters, rfl, items⟩
  · exact ⟨element, items, fun _ _ items' => .collection items'⟩
  · exact ⟨element, items, fun _ _ items' => .collectionConstructor declared parameters items'⟩

/-- **The elements of a collection of a flattening kind have the category of its bare
constructor**, for strictly typed laws with one such category. -/
theorem lawCollection_elements (strict : LawsTypedStrict laws language free) (unique : UniqueBare laws language)
    {law : Laws} {kind : CollType} (found : lawFor laws kind = some law) {bound : List TypeExpr} {elements : List Pattern}
    {rest : Option String} {type : TypeExpr} (typeOk : LawTypeOk laws language type)
    (typed : HasType language free bound (.collection kind elements rest) type) {rule : GrammarRule}
    (declared : rule ∈ language.terms) {name : String} {element : TypeExpr}
    (parameters : rule.params = [.simple name (.collection kind element)]) :
    ElementsHaveType language free bound elements (.base rule.category) := by
  rcases hasType_collection_inv typed with ⟨element', rfl, items⟩ | ⟨rule', name', element', declared', parameters', rfl, items⟩
  · obtain ⟨witness, witnessDeclared, witnessName, witnessParameters, rfl⟩ := typeOk.lawful found
    rw [unique law kind found witness witnessDeclared rule declared _ _ _ _ witnessParameters parameters] at items
    exact items
  · rw [strict.homogeneous law kind found rule' declared' name' element' parameters',
      unique law kind found rule' declared' rule declared _ _ _ _ parameters' parameters] at items
    exact items

/-- **A collection of a flattening kind can be rebuilt at its type from any elements of the
category of its bare constructor.** -/
theorem lawCollection_rebuild (strict : LawsTypedStrict laws language free) (unique : UniqueBare laws language)
    {law : Laws} {kind : CollType} (found : lawFor laws kind = some law) {bound : List TypeExpr} {elements : List Pattern}
    {rest : Option String} {type : TypeExpr} (typeOk : LawTypeOk laws language type)
    (typed : HasType language free bound (.collection kind elements rest) type) {rule : GrammarRule}
    (declared : rule ∈ language.terms) {name : String} {element : TypeExpr}
    (parameters : rule.params = [.simple name (.collection kind element)]) :
    ∀ (elements' : List Pattern) (rest' : Option String),
      ElementsHaveType language free bound elements' (.base rule.category) →
      HasType language free bound (.collection kind elements' rest') type := by
  intro elements' rest' items
  rcases hasType_collection_inv typed with ⟨element', rfl, _⟩ | ⟨rule', name', element', declared', parameters', rfl, _⟩
  · obtain ⟨witness, witnessDeclared, witnessName, witnessParameters, same⟩ := typeOk.lawful found
    rw [same, unique law kind found witness witnessDeclared rule declared _ _ _ _ witnessParameters parameters]
    exact .collection items
  · have homogeneous := strict.homogeneous law kind found rule' declared' name' element' parameters'
    subst homogeneous
    rw [← unique law kind found rule' declared' rule declared _ _ _ _ parameters' parameters] at items
    exact .collectionConstructor declared' parameters' items

open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence GeneralTypedSites in
theorem argumentsHaveTypes_get {bound : List TypeExpr} :
    ∀ {arguments : List Pattern} {parameters : List TermParam} {index : Nat} {argument : Pattern} {parameter : TermParam}
      {type : TypeExpr}, ArgumentsHaveTypes language free bound arguments parameters → arguments[index]? = some argument →
      parameters[index]? = some parameter → parameterType? parameter = some type →
      HasType language free bound argument type
  | _ :: _, _ :: _, 0, _, _, _, .cons _ parameterType typed _, selected, parameterSelected, typeFound => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at selected parameterSelected
    subst selected; subst parameterSelected
    rw [parameterType, Option.some.injEq] at typeFound
    subst typeFound; exact typed
  | _ :: _, _ :: _, index + 1, _, _, _, .cons _ _ _ tail, selected, parameterSelected, typeFound => by
    simp only [List.getElem?_cons_succ] at selected parameterSelected
    exact argumentsHaveTypes_get tail selected parameterSelected typeFound
  | [], _, _, _, _, _, _, selected, _, _ => by simp at selected

open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence GeneralTypedSites in
/-- **The focus of a licensed site in a well-sorted term is well-sorted.** -/
theorem Licensed.focus_sorted {permissions : OperationalPermissions} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {site : SiteData} (licensed : Licensed language free permissions bound expected source site)
    (sorted : OpenPatternWellSorted language free bound expected source) :
    OpenPatternWellSorted language free site.focusBound site.focusType site.focus := by
  induction licensed with
  | here => exact sorted
  | application declared _ typed _ selected parameterSelected parameterTyped _ _ ih =>
    obtain ⟨_, metadata, object, inScope⟩ := sorted
    have member := List.mem_of_getElem? selected
    apply ih
    refine ⟨argumentsHaveTypes_get typed selected parameterSelected parameterTyped, ?_, ?_, ?_⟩
    · simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_eq_all, List.all_eq_true] at metadata
      exact metadata _ member
    · simp only [isObjectPattern, isObjectPatternList_eq_all, List.all_eq_true] at object
      exact object _ member
    · unfold ScopeSafeAt at inScope ⊢
      simp only [Pattern.isWellScopedAt, isWellScopedListAt_iff] at inScope
      exact inScope _ member
  | lambda _ _ ih =>
    obtain ⟨typed, metadata, object, inScope⟩ := sorted
    apply ih
    cases typed with
    | lambda body =>
      refine ⟨body, ?_, by simpa [isObjectPattern] using object, ?_⟩
      · simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at metadata; exact metadata.2
      · unfold ScopeSafeAt at inScope ⊢; simpa [Pattern.isWellScopedAt] using inScope
  | multiLambda _ _ ih =>
    obtain ⟨typed, metadata, object, inScope⟩ := sorted
    apply ih
    cases typed with
    | multiLambda body =>
      refine ⟨body, ?_, by simpa [isObjectPattern] using object, ?_⟩
      · simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at metadata; exact metadata.2
      · unfold ScopeSafeAt at inScope ⊢
        simp only [Pattern.isWellScopedAt] at inScope
        simpa [List.length_append, List.length_replicate, Nat.add_comm] using inScope
  | directCollection _ typed _ selected _ ih =>
    obtain ⟨_, metadata, object, inScope⟩ := sorted
    have member := List.mem_of_getElem? selected
    apply ih
    refine ⟨elementsHaveType_iff.mp typed _ member, ?_, ?_, ?_⟩
    · simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_eq_all, List.all_eq_true] at metadata
      exact metadata _ member
    · simp only [isObjectPattern, Bool.and_eq_true, isObjectPatternList_eq_all, List.all_eq_true] at object
      exact object.2 _ member
    · unfold ScopeSafeAt at inScope ⊢
      simp only [Pattern.isWellScopedAt, isWellScopedListAt_iff] at inScope
      exact inScope _ member
  | authoredCollection _ _ _ typed _ selected _ ih =>
    obtain ⟨_, metadata, object, inScope⟩ := sorted
    have member := List.mem_of_getElem? selected
    apply ih
    refine ⟨elementsHaveType_iff.mp typed _ member, ?_, ?_, ?_⟩
    · simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_eq_all, List.all_eq_true] at metadata
      exact metadata _ member
    · simp only [isObjectPattern, Bool.and_eq_true, isObjectPatternList_eq_all, List.all_eq_true] at object
      exact object.2 _ member
    · unfold ScopeSafeAt at inScope ⊢
      simp only [Pattern.isWellScopedAt, isWellScopedListAt_iff] at inScope
      exact inScope _ member

end Mettapedia.OSLF.MeTTaIL.CanonicalBags
