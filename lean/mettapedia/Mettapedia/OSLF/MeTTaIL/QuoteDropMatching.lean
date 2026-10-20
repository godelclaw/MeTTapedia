import Mettapedia.OSLF.MeTTaIL.QuoteDropLaws
import Mettapedia.OSLF.MeTTaIL.CanonicalMatching

/-!
# Matching at quote-drop normal forms

A pattern that never mentions the quote constructor (`quoteFree`) matches the quote-drop normal
form of every term it matches, with the normal forms of the original captures
(`matches_normal`). The normal form keeps every constructor other than a quote, every binder,
index and collection, and the order of collection elements; it commutes with the variable
renamings by which captures are recovered (`recoverValue?_normal`), so equal captures stay equal.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.QuoteDrop

open Syntax RuleBinding ScopedRuleMatching GeneralScopedMatch ReflectiveSubstitution CanonicalBags

variable {declaration : ReflectivePresentationDecl}

/-! ## Scope -/

theorem finish_wellScoped (label : String) (arguments : List Pattern) (depth : Nat) :
    (finishNormalizeReflectiveApply declaration label arguments).isWellScopedAt depth =
      (Pattern.apply label arguments).isWellScopedAt depth := by
  unfold finishNormalizeReflectiveApply
  split
  · split
    · split
      · simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt]
      · rfl
    · rfl
  · rfl

theorem wellScopedList_map (depth : Nat) (f : Pattern → Pattern)
    (each : ∀ pattern, (f pattern).isWellScopedAt depth = pattern.isWellScopedAt depth) :
    ∀ items : List Pattern, Pattern.isWellScopedListAt depth (items.map f) = Pattern.isWellScopedListAt depth items
  | [] => rfl
  | item :: rest => by simp [Pattern.isWellScopedListAt, each item, wellScopedList_map depth f each rest]

/-- **The normal form keeps scope.** -/
theorem normal_wellScoped (pattern : Pattern) :
    ∀ depth, (normal declaration pattern).isWellScopedAt depth = pattern.isWellScopedAt depth := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro depth; rw [normal_bvar]
  | hfvar name => intro depth; rw [normal_fvar]
  | happly label arguments ih =>
    intro depth
    rw [normal_apply, finish_wellScoped]
    simp only [Pattern.isWellScopedAt]
    induction arguments with
    | nil => rfl
    | cons first rest restIH =>
      simp only [List.map_cons, Pattern.isWellScopedListAt, ih first (by simp) depth,
        restIH (fun other member => ih other (by simp [member]))]
  | hlambda binder body ih => intro depth; rw [normal_lambda]; simp only [Pattern.isWellScopedAt, ih]
  | hmultiLambda arity binders body ih => intro depth; rw [normal_multiLambda]; simp only [Pattern.isWellScopedAt, ih]
  | hsubst body replacement bodyIH replacementIH =>
    intro depth; rw [normal_subst]; simp only [Pattern.isWellScopedAt, bodyIH, replacementIH]
  | hcollection kind elements rest ih =>
    intro depth
    rw [normal_collection]
    simp only [Pattern.isWellScopedAt]
    induction elements with
    | nil => rfl
    | cons first others restIH =>
      simp only [List.map_cons, Pattern.isWellScopedListAt, ih first (by simp) depth,
        restIH (fun other member => ih other (by simp [member]))]

/-! ## Recovering captures -/

/-- A captured value with its body in normal form. -/
def normalValue (declaration : ReflectivePresentationDecl) (value : ContextualValue) : ContextualValue :=
  { value with body := normal declaration value.body }

/-- Every captured body in normal form. -/
def normalAssignment (declaration : ReflectivePresentationDecl) (assignment : ScopedRuleMatching.Assignment) :
    ScopedRuleMatching.Assignment :=
  assignment.map fun entry => (entry.1, normalValue declaration entry.2)

theorem lookup_normalAssignment (assignment : ScopedRuleMatching.Assignment) (name : String) :
    lookup (normalAssignment declaration assignment) name = (lookup assignment name).map (normalValue declaration) := by
  induction assignment with
  | nil => rfl
  | cons entry rest ih =>
    unfold lookup at ih ⊢
    simp only [normalAssignment, List.map_cons] at ih ⊢
    by_cases same : entry.1 = name
    · rw [List.find?_cons_of_pos (by simpa using same), List.find?_cons_of_pos (by simpa using same)]; rfl
    · rw [List.find?_cons_of_neg (by simpa using same), List.find?_cons_of_neg (by simpa using same)]; exact ih

theorem assign_normal {assignment final : ScopedRuleMatching.Assignment} {name : String} {value : ContextualValue}
    (assigned : assign assignment name value = some final) :
    assign (normalAssignment declaration assignment) name (normalValue declaration value) =
      some (normalAssignment declaration final) := by
  unfold assign at assigned ⊢
  rw [lookup_normalAssignment]
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

theorem recoveryAssignment_renaming (depth dependencies ambient : Nat) (indices : List Nat) :
    Renaming (recoveryAssignment depth dependencies ambient indices) := by
  intro index
  unfold recoveryAssignment
  split
  · split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem mapM_bvars (depth : Nat) : ∀ (arguments : List Pattern) (indices : List Nat),
    arguments.mapM (fun argument => match argument with
      | .bvar index => if index < depth then some index else none
      | _ => none) = some indices → ∀ argument ∈ arguments, ∃ index, argument = .bvar index
  | [], _, _, _, member => absurd member List.not_mem_nil
  | first :: rest, indices, mapped, argument, member => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure] at mapped
    obtain ⟨index, found, others, foundRest, _⟩ := mapped
    rcases List.mem_cons.mp member with rfl | later
    · cases argument with
      | bvar other => exact ⟨other, rfl⟩
      | _ => simp at found
    · exact mapM_bvars depth rest others foundRest argument later

theorem variableSpine?_bvars {depth : Nat} {arguments : List Pattern} {indices : List Nat}
    (spine : variableSpine? depth arguments = some indices) : ∀ argument ∈ arguments, ∃ index, argument = .bvar index := by
  unfold variableSpine? at spine
  simp only [bind, Option.bind_eq_some_iff] at spine
  obtain ⟨found, mapped, _⟩ := spine
  exact mapM_bvars depth arguments found mapped

theorem occurrenceAssignment_renaming {dependencies depth : Nat} {arguments : List Pattern}
    (bvars : ∀ argument ∈ arguments, ∃ index, argument = .bvar index) :
    Renaming (occurrenceAssignment dependencies depth arguments) := by
  intro index
  unfold occurrenceAssignment
  split
  · rw [List.getD_eq_getElem?_getD]
    cases found : arguments[index]? with
    | none => exact ⟨0, rfl⟩
    | some argument => exact bvars argument (List.mem_of_getElem? found)
  · exact ⟨_, rfl⟩

theorem instantiateValue?_normal {value : ContextualValue} {ambient depth : Nat} {arguments : List Pattern}
    (bvars : ∀ argument ∈ arguments, ∃ index, argument = .bvar index) :
    instantiateValue? (normalValue declaration value) ambient depth arguments =
      (instantiateValue? value ambient depth arguments).map (normal declaration) := by
  unfold instantiateValue?
  simp only [normalValue, normal_wellScoped]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · have commuted : ContextSubstitution.substitute (occurrenceAssignment value.dependencies.length depth arguments)
                (normal declaration value.body) =
              normal declaration (ContextSubstitution.substitute
                (occurrenceAssignment value.dependencies.length depth arguments) value.body) :=
            (normalize_substitute_renaming _ (occurrenceAssignment_renaming bvars)).symm
          simp only [commuted, normal_wellScoped]
          split <;> rfl

/-- **A recovered capture's normal form is recovered from the normal form of the subject.** -/
theorem recoverValue?_normal {dependencies : List TypeExpr} {ambient depth : Nat} {arguments : List Pattern}
    {target : Pattern} {value : ContextualValue}
    (found : recoverValue? dependencies ambient depth arguments target = some value) :
    recoverValue? dependencies ambient depth arguments (normal declaration target) = some (normalValue declaration value) := by
  unfold recoverValue? at found ⊢
  rw [normal_wellScoped]
  split at found
  · cases found
  · rename_i inScope
    rw [if_neg inScope]
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at found ⊢
    obtain ⟨indices, spine, rest⟩ := found
    refine ⟨indices, spine, ?_⟩
    split at rest
    · cases rest
    · rename_i lengths
      rw [if_neg lengths]
      have body : ContextSubstitution.substitute (recoveryAssignment depth dependencies.length ambient indices)
          (normal declaration target) =
          normal declaration (ContextSubstitution.substitute (recoveryAssignment depth dependencies.length ambient indices)
            target) :=
        (normalize_substitute_renaming target (recoveryAssignment_renaming _ _ _ _)).symm
      split at rest
      · rename_i forward
        cases rest
        have shape : (⟨dependencies, ambient,
            ContextSubstitution.substitute (recoveryAssignment depth dependencies.length ambient indices)
              (normal declaration target)⟩ : ContextualValue) =
            normalValue declaration ⟨dependencies, ambient,
              ContextSubstitution.substitute (recoveryAssignment depth dependencies.length ambient indices) target⟩ := by
          simp only [normalValue, body]
        rw [shape, instantiateValue?_normal (variableSpine?_bvars spine)]
        have forward' := beq_iff_eq.mp forward
        rw [forward']
        simp
      · cases rest

theorem capture?_normal {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient depth : Nat} {site : RulePatternSite} {path : List Nat} {assignment final : ScopedRuleMatching.Assignment}
    {name : String} {target : Pattern}
    (captured : capture? rule spec ambient depth site path assignment name target = some final) :
    capture? rule spec ambient depth site path (normalAssignment declaration assignment) name (normal declaration target) =
      some (normalAssignment declaration final) := by
  unfold capture? at captured ⊢
  simp only [bind, Option.bind_eq_some_iff] at captured ⊢
  obtain ⟨dependencies, declared, arguments, found, value, recovered, assigned⟩ := captured
  exact ⟨dependencies, declared, arguments, found, normalValue declaration value, recoverValue?_normal recovered,
    assign_normal assigned⟩

theorem captureRest?_normal {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient depth : Nat} {site : RulePatternSite} {path : List Nat} {assignment final : ScopedRuleMatching.Assignment}
    {name : String} {kind : CollType} {elements : List Pattern}
    (captured : captureRest? rule spec ambient depth site path assignment name kind elements = some final) :
    captureRest? rule spec ambient depth site path (normalAssignment declaration assignment) name kind
        (elements.map (normal declaration)) = some (normalAssignment declaration final) := by
  unfold captureRest? at captured ⊢
  have := capture?_normal (declaration := declaration) captured
  rwa [normal_collection] at this

/-! ## Patterns without the quote constructor -/

variable (declaration) in
/-- A pattern that never mentions the quote constructor. -/
def quoteFree : Pattern → Bool
  | .bvar _ | .fvar _ => true
  | .apply label arguments => label != declaration.quoteConstructor && arguments.attach.all fun ⟨argument, _⟩ => quoteFree argument
  | .lambda _ body => quoteFree body
  | .multiLambda _ _ body => quoteFree body
  | .subst body replacement => quoteFree body && quoteFree replacement
  | .collection _ elements _ => elements.attach.all fun ⟨element, _⟩ => quoteFree element
decreasing_by all_goals sizeOf_pattern_dec

theorem quoteFree_apply {label : String} {arguments : List Pattern} (free : quoteFree declaration (.apply label arguments) = true) :
    label ≠ declaration.quoteConstructor ∧ ∀ argument ∈ arguments, quoteFree declaration argument = true := by
  rw [quoteFree] at free
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true, List.mem_attach, true_implies,
    Subtype.forall] at free
  exact ⟨free.1, free.2⟩

theorem quoteFree_collection {kind : CollType} {elements : List Pattern} {rest : Option String}
    (free : quoteFree declaration (.collection kind elements rest) = true) :
    ∀ element ∈ elements, quoteFree declaration element = true := by
  rw [quoteFree] at free
  simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall] at free
  exact free

theorem finish_not_quote {label : String} (notQuote : label ≠ declaration.quoteConstructor) (arguments : List Pattern) :
    finishNormalizeReflectiveApply declaration label arguments = .apply label arguments := by
  unfold finishNormalizeReflectiveApply
  rw [if_neg (by simpa using notQuote)]

theorem map_eraseIdx' {α β : Type} (f : α → β) : ∀ (items : List α) (index : Nat),
    (items.map f).eraseIdx index = (items.eraseIdx index).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | item :: rest, index + 1 => by
    simp only [List.map_cons, List.eraseIdx_cons_succ, map_eraseIdx' f rest index]

mutual
  /-- **Every match of a quote-free pattern at a subject has a match at its normal form**, with
  normalized captures. -/
  theorem matches_normal {rule : RewriteRule} {spec : RuleBindingSpec}
      {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth : Nat}
      {initial final : ScopedRuleMatching.Assignment} {schema target : Pattern}
      (free : quoteFree declaration schema = true)
      (matched : Matches rule spec ambient site path depth initial schema target final) :
      Matches rule spec ambient site path depth (normalAssignment declaration initial) schema (normal declaration target)
        (normalAssignment declaration final) := by
    cases matched with
    | capture captured => exact .capture (capture?_normal captured)
    | bound => rw [normal_bvar]; exact .bound
    | constructor arguments =>
      obtain ⟨notQuote, each⟩ := quoteFree_apply free
      rw [normal_apply, finish_not_quote notQuote]
      exact .constructor (arguments_normal each arguments)
    | binder body =>
      rw [normal_lambda]
      exact .binder (matches_normal (by rw [quoteFree] at free; exact free) body)
    | binders body =>
      rw [normal_multiLambda]
      exact .binders (matches_normal (by rw [quoteFree] at free; exact free) body)
    | substitution body replacement =>
      rw [quoteFree, Bool.and_eq_true] at free
      rw [normal_subst]
      exact .substitution (matches_normal free.1 body) (matches_normal free.2 replacement)
    | bag notVector bag =>
      rw [normal_collection]
      exact .bag notVector (bag_normal (quoteFree_collection free) bag)
    | vector arguments =>
      rw [normal_collection]
      exact .vector (arguments_normal (quoteFree_collection free) arguments)
    | vectorRest arguments captured =>
      rw [normal_collection]
      have front := arguments_normal (quoteFree_collection free) arguments
      have rest := captureRest?_normal (declaration := declaration) captured
      rw [List.map_take] at front
      rw [List.map_drop] at rest
      exact .vectorRest front rest
  termination_by sizeOf schema

  theorem arguments_normal {rule : RewriteRule} {spec : RuleBindingSpec}
      {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth index : Nat}
      {initial final : ScopedRuleMatching.Assignment} {schemas targets : List Pattern}
      (free : ∀ schema ∈ schemas, quoteFree declaration schema = true)
      (matched : Arguments rule spec ambient site path depth initial index schemas targets final) :
      Arguments rule spec ambient site path depth (normalAssignment declaration initial) index schemas
        (targets.map (normal declaration)) (normalAssignment declaration final) := by
    cases matched with
    | nil => exact .nil
    | cons head tail =>
      exact .cons (matches_normal (free _ (by simp)) head)
        (arguments_normal (fun schema member => free schema (by simp [member])) tail)
  termination_by sizeOf schemas

  theorem bag_normal {rule : RewriteRule} {spec : RuleBindingSpec}
      {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth index : Nat}
      {initial final : ScopedRuleMatching.Assignment} {schemas : List Pattern} {rest : Option String}
      {kind : CollType} {targets : List Pattern}
      (free : ∀ schema ∈ schemas, quoteFree declaration schema = true)
      (matched : Bag rule spec ambient site path depth initial index schemas rest kind targets final) :
      Bag rule spec ambient site path depth (normalAssignment declaration initial) index schemas rest kind
        (targets.map (normal declaration)) (normalAssignment declaration final) := by
    cases matched with
    | nil => exact .nil
    | rest captured => exact .rest (captureRest?_normal captured)
    | cons selected within head tail =>
      have headNormal := matches_normal (free _ (by simp)) head
      have tailNormal := bag_normal (fun schema member => free schema (by simp [member])) tail
      rw [← map_eraseIdx'] at tailNormal
      refine .cons selected (by simpa using within) ?_ tailNormal
      simpa using headNormal
  termination_by sizeOf schemas
end

end Mettapedia.OSLF.MeTTaIL.QuoteDrop
