import Mettapedia.OSLF.MeTTaIL.GeneralPremiseCanonicalProjection
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine
import Mettapedia.OSLF.MeTTaIL.GeneralEquationAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralEquationCaptureDomain

/-!
# Matching an instance recovers it

The equation sides admitted for execution (`GeneralEquationAdmission.checkSide`) use injective
local-variable spines at every metavariable occurrence and every collection rest, and no explicit
substitution. For such a side, instantiation can be undone:

- `recover_instantiate`: an instantiated contextual value is recovered exactly by the matcher's
  inverse occurrence substitution;
- `traced_of_instantiate`: matching a side against its own instance (display metadata erased)
  succeeds, with captures that agree with the instantiating assignment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.Inversion

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching

/-! ## Recovering one contextual value -/

/-- One spine argument: a local variable below the occurrence depth. -/
def spineIndex (depth : Nat) (argument : Pattern) : Option Nat :=
  match argument with
  | .bvar index => if index < depth then some index else none
  | _ => none

theorem spineIndex_some {depth : Nat} {argument : Pattern} {index : Nat}
    (found : spineIndex depth argument = some index) : argument = .bvar index ∧ index < depth := by
  cases argument <;> simp [spineIndex] at found
  obtain ⟨below, rfl⟩ := found
  exact ⟨rfl, below⟩

theorem spine_mapM {depth : Nat} :
    ∀ {arguments : List Pattern} {indices : List Nat}, arguments.mapM (spineIndex depth) = some indices →
      arguments = indices.map Pattern.bvar ∧ ∀ index ∈ indices, index < depth := by
  intro arguments
  induction arguments with
  | nil =>
    intro indices mapped
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at mapped
    subst mapped
    simp
  | cons argument arguments ih =>
    intro indices mapped
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at mapped
    obtain ⟨head, headFound, tail, tailFound, rfl⟩ := mapped
    obtain ⟨rfl, below⟩ := spineIndex_some headFound
    obtain ⟨rfl, rest⟩ := ih tailFound
    refine ⟨rfl, ?_⟩
    intro index member
    rcases List.mem_cons.mp member with rfl | later
    · exact below
    · exact rest index later

theorem variableSpine_some {depth : Nat} {arguments : List Pattern} {indices : List Nat}
    (spine : variableSpine? depth arguments = some indices) :
    arguments = indices.map Pattern.bvar ∧ (∀ index ∈ indices, index < depth) ∧ indices.Nodup := by
  unfold variableSpine? at spine
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at spine
  obtain ⟨found, mapped, checked⟩ := spine
  split at checked
  · rename_i nodup
    cases checked
    have shaped := spine_mapM (depth := depth) mapped
    exact ⟨shaped.1, shaped.2, nodup⟩
  · cases checked

/-- Inverse occurrence substitution after occurrence substitution is the identity. -/
theorem recovery_after_occurrence (depth dependencies ambient : Nat) (indices : List Nat)
    (below : ∀ index ∈ indices, index < depth) (nodup : indices.Nodup) (length : indices.length = dependencies)
    (body : Pattern) :
    ContextSubstitution.substitute (recoveryAssignment depth dependencies ambient indices)
      (ContextSubstitution.substitute (occurrenceAssignment dependencies depth (indices.map Pattern.bvar)) body) = body := by
  rw [ContextSubstitution.substitute_comp]
  have identity : (fun index => ContextSubstitution.substitute (recoveryAssignment depth dependencies ambient indices)
      (occurrenceAssignment dependencies depth (indices.map Pattern.bvar) index)) = Pattern.bvar := by
    funext index
    unfold occurrenceAssignment
    split
    · rename_i inside
      have bounded : index < indices.length := length ▸ inside
      rw [List.getD_eq_getElem _ _ (by simpa using bounded), List.getElem_map]
      simp only [ContextSubstitution.substitute, recoveryAssignment]
      have selected := below indices[index] (List.getElem_mem bounded)
      rw [if_pos selected, if_pos (List.getElem_mem bounded), nodup.idxOf_getElem index bounded]
    · rename_i outside
      simp only [ContextSubstitution.substitute, recoveryAssignment]
      rw [if_neg (by omega)]
      congr 1
      omega
  rw [identity, ContextSubstitution.substitute_id]

/-- **Recovery inverts instantiation** at an injective variable spine. -/
theorem recover_instantiate {value : ContextualValue} {ambient depth : Nat} {arguments : List Pattern}
    {target : Pattern} (instantiated : instantiateValue? value ambient depth arguments = some target)
    {indices : List Nat} (spine : variableSpine? depth arguments = some indices) :
    recoverValue? value.dependencies ambient depth arguments target = some value := by
  obtain ⟨shape, below, nodup⟩ := variableSpine_some spine
  have forward := instantiated
  unfold instantiateValue? at instantiated
  split at instantiated
  · cases instantiated
  rename_i sameAmbient
  split at instantiated
  · cases instantiated
  rename_i sameLength
  split at instantiated
  · cases instantiated
  split at instantiated
  · cases instantiated
  dsimp only at instantiated
  split at instantiated
  · rename_i scopedResult
    cases instantiated
    have ambientEq : value.ambient = ambient := by simpa using sameAmbient
    have lengthEq : arguments.length = value.dependencies.length := by simpa using sameLength
    have indicesLength : indices.length = value.dependencies.length := by
      rw [← lengthEq, shape, List.length_map]
    unfold recoverValue?
    rw [if_neg (by simpa using scopedResult)]
    simp only [Option.bind_eq_bind, spine, Option.bind_some]
    rw [if_neg (by simpa using indicesLength)]
    have body : ContextSubstitution.substitute
        (recoveryAssignment depth value.dependencies.length ambient indices)
        (ContextSubstitution.substitute (occurrenceAssignment value.dependencies.length depth arguments) value.body) =
          value.body := by
      rw [shape]
      exact recovery_after_occurrence depth value.dependencies.length ambient indices below nodup indicesLength value.body
    rw [body]
    have same : ({ dependencies := value.dependencies, ambient := ambient, body := value.body } : ContextualValue) = value := by
      cases value
      simp only at ambientEq
      subst ambientEq
      rfl
    rw [same, if_pos (by simpa using forward)]
  · cases instantiated

/-- An instantiated value at a variable spine is canonical when its body is. -/
theorem instantiateValue_canonical {value : ContextualValue} {ambient depth : Nat} {arguments : List Pattern}
    {result : Pattern} (canonical : value.body.hasCanonicalBinderMetadata = true)
    {indices : List Nat} (spine : variableSpine? depth arguments = some indices)
    (instantiated : instantiateValue? value ambient depth arguments = some result) :
    result.hasCanonicalBinderMetadata = true := by
  obtain ⟨shape, _, _⟩ := variableSpine_some spine
  unfold instantiateValue? at instantiated
  split at instantiated <;> try contradiction
  split at instantiated <;> try contradiction
  split at instantiated <;> try contradiction
  split at instantiated <;> try contradiction
  dsimp only at instantiated
  split at instantiated <;> try contradiction
  rw [← Option.some.inj instantiated]
  apply GeneralPremise.contextSubstitute_canonical canonical
  intro index
  simp only [occurrenceAssignment]
  split
  · rw [shape]
    by_cases bounded : index < indices.length
    · rw [List.getD_eq_getElem _ _ (by simpa using bounded), List.getElem_map]
      rfl
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt bounded)]
      rfl
  · rfl

theorem instantiateArgs_length {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth : Nat} {assignment : Assignment} :
    ∀ {index : Nat} {patterns results : List Pattern},
      instantiateArgsWith? Substitution.instantiateBVar rule spec ambient site path depth assignment index patterns =
        some results → results.length = patterns.length
  | _, [], results, instantiated => by
    simp only [instantiateArgsWith?, Option.some.injEq] at instantiated
    subst results
    rfl
  | _, first :: rest, results, instantiated => by
    simp only [instantiateArgsWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
    obtain ⟨_, _, tail, tailInterpreted, equal⟩ := instantiated
    cases Option.some.inj equal
    simp [instantiateArgs_length tailInterpreted]

/-! ## Matching an instance -/

/-- What the instantiating assignment must provide at a side's metavariables: the declared
dependency context and a canonical body. -/
def Fits (spec : RuleBindingSpec) (assignment : Assignment) (names : List String) : Prop :=
  ∀ name ∈ names, ∀ value, lookup assignment name = some value →
    dependencies? spec name = some value.dependencies ∧ value.body.hasCanonicalBinderMetadata = true

theorem Fits.mono {spec : RuleBindingSpec} {assignment : Assignment} {names smaller : List String}
    (fits : Fits spec assignment names) (included : ∀ name ∈ smaller, name ∈ names) :
    Fits spec assignment smaller :=
  fun name member => fits name (included name member)

/-- Assignments below another, by lookup. -/
def Below (small large : Assignment) : Prop :=
  ∀ name value, lookup small name = some value → lookup large name = some value

theorem lookup_cons_self (assignment : Assignment) (name : String) (value : ContextualValue) :
    lookup ((name, value) :: assignment) name = some value := by
  simp [lookup]

theorem lookup_cons_other (assignment : Assignment) {name other : String} (value : ContextualValue)
    (different : other ≠ name) :
    lookup ((name, value) :: assignment) other = lookup assignment other := by
  have notEqual : (name == other) = false := by simpa using (Ne.symm different)
  simp [lookup, notEqual]

theorem assign_below {initial large : Assignment} {name : String} {value : ContextualValue}
    (below : Below initial large) (stored : lookup large name = some value) :
    ∃ final, assign initial name value = some final ∧ Below final large := by
  unfold assign
  cases prior : lookup initial name with
  | none =>
    refine ⟨(name, value) :: initial, rfl, ?_⟩
    intro other otherValue found
    by_cases same : other = name
    · subst other
      rw [lookup_cons_self] at found
      cases found
      exact stored
    · rw [lookup_cons_other _ _ same] at found
      exact below other otherValue found
  | some earlier =>
    have equal : earlier = value := Option.some.inj ((below name earlier prior).symm.trans stored)
    subst earlier
    exact ⟨initial, by simp, below⟩

mutual
  theorem traced_of_instantiate (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
      (site : RulePatternSite) (path : List Nat) (depth : Nat) (assignment initial : Assignment)
      (pattern result : Pattern)
      (supported : GeneralEquationAdmission.checkSide rule spec site path depth pattern = true)
      (instantiated : instantiateAt? rule spec ambient site path depth assignment pattern = some result)
      (fits : Fits spec assignment pattern.freeFvarNames) (below : Below initial assignment) :
      ∃ trace final, GeneralScopedMatchMachine.TracedMatches rule spec ambient site path depth initial
          pattern result.eraseBinderMetadata trace final ∧ Below final assignment ∧
        ∀ name ∈ pattern.freeFvarNames, lookup final name = lookup assignment name := by
    cases pattern with
    | fvar name =>
      simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
      obtain ⟨value, found, arguments, occurrence, interpreted⟩ := instantiated
      simp only [GeneralEquationAdmission.checkSide, occurrence, Bool.and_eq_true] at supported
      obtain ⟨indices, spine⟩ := Option.isSome_iff_exists.mp supported.2
      obtain ⟨dependencies, canonical⟩ := fits name (by simp [Pattern.freeFvarNames]) value found
      have erased : result.eraseBinderMetadata = result :=
        Pattern.eraseBinderMetadata_eq_self_of_canonical (instantiateValue_canonical canonical spine interpreted)
      obtain ⟨final, assigned, finalBelow⟩ := assign_below below found
      refine ⟨[], final, ?_, finalBelow, ?_⟩
      · rw [erased]
        apply GeneralScopedMatchMachine.TracedMatches.capture
        simp only [capture?, dependencies, occurrence, Option.bind_eq_bind, Option.bind_some,
          recover_instantiate interpreted spine]
        exact assigned
      · intro other member
        simp only [Pattern.freeFvarNames, List.mem_singleton] at member
        subst other
        rw [GeneralScopedMatch.assign_lookup assigned, found]
    | bvar index =>
      simp only [instantiateAt?, instantiateWith?, Option.some.injEq] at instantiated
      subst result
      refine ⟨[], initial, ?_, below, by simp [Pattern.freeFvarNames]⟩
      simp only [Pattern.eraseBinderMetadata]
      exact .bound
    | apply constructor arguments =>
      simp only [GeneralEquationAdmission.checkSide] at supported
      simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
      obtain ⟨results, interpreted, equal⟩ := instantiated
      cases Option.some.inj equal
      obtain ⟨trace, final, traced, finalBelow, agree⟩ := tracedArguments_of_instantiate rule spec ambient site
        path depth assignment initial 0 arguments results supported interpreted
        (by simpa [Pattern.freeFvarNames] using fits) below
      refine ⟨trace, final, ?_, finalBelow, by simpa [Pattern.freeFvarNames] using agree⟩
      simpa [Pattern.eraseBinderMetadata] using GeneralScopedMatchMachine.TracedMatches.constructor traced
    | lambda binder body =>
      simp only [GeneralEquationAdmission.checkSide] at supported
      simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
      obtain ⟨bodyResult, interpreted, equal⟩ := instantiated
      cases Option.some.inj equal
      obtain ⟨trace, final, traced, finalBelow, agree⟩ := traced_of_instantiate rule spec ambient site
        (path ++ [0]) (depth + 1) assignment initial body bodyResult supported interpreted
        (by simpa [Pattern.freeFvarNames] using fits) below
      refine ⟨trace, final, ?_, finalBelow, by simpa [Pattern.freeFvarNames] using agree⟩
      simpa [Pattern.eraseBinderMetadata] using
        (GeneralScopedMatchMachine.TracedMatches.binder (display := binder) (actualDisplay := none) traced)
    | multiLambda arity binders body =>
      simp only [GeneralEquationAdmission.checkSide] at supported
      simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
      obtain ⟨bodyResult, interpreted, equal⟩ := instantiated
      cases Option.some.inj equal
      obtain ⟨trace, final, traced, finalBelow, agree⟩ := traced_of_instantiate rule spec ambient site
        (path ++ [0]) (depth + arity) assignment initial body bodyResult supported interpreted
        (by simpa [Pattern.freeFvarNames] using fits) below
      refine ⟨trace, final, ?_, finalBelow, by simpa [Pattern.freeFvarNames] using agree⟩
      simpa [Pattern.eraseBinderMetadata] using
        (GeneralScopedMatchMachine.TracedMatches.binders (display := binders) (actualDisplay := []) traced)
    | subst body replacement => simp [GeneralEquationAdmission.checkSide] at supported
    | collection kind elements rest =>
      simp only [GeneralEquationAdmission.checkSide, Bool.and_eq_true] at supported
      obtain ⟨restOk, supported⟩ := supported
      cases rest with
      | some name =>
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
        obtain ⟨explicit, interpreted, value, found, arguments, occurrence, residualValue, residual, spliced⟩ :=
          instantiated
        simp only [GeneralEquationAdmission.restSupported, occurrence, Bool.and_eq_true] at restOk
        obtain ⟨indices, spine⟩ := Option.isSome_iff_exists.mp restOk.2
        obtain ⟨dependencies, canonical⟩ := fits name (by simp [Pattern.freeFvarNames]) value found
        have elementFits : Fits spec assignment (elements.flatMap Pattern.freeFvarNames) :=
          fits.mono (fun other member => by simp [Pattern.freeFvarNames, member])
        split at spliced
        · rename_i actualKind items
          split at spliced
          · rename_i sameKind
            cases spliced
            obtain rfl : actualKind = kind := beq_iff_eq.mp sameKind
            have residualCanonical := instantiateValue_canonical canonical spine residual
            have itemsErased : items.map Pattern.eraseBinderMetadata = items := by
              have same := Pattern.eraseBinderMetadata_eq_self_of_canonical residualCanonical
              simpa [Pattern.eraseBinderMetadata] using same
            have restStep : ∀ middle, Below middle assignment → ∃ final,
                captureRest? rule spec ambient depth site (path ++ [elements.length]) middle name actualKind items =
                  some final ∧ Below final assignment ∧ lookup final name = lookup assignment name := by
              intro middle middleBelow
              obtain ⟨final, assigned, finalBelow⟩ := assign_below middleBelow found
              refine ⟨final, ?_, finalBelow, by rw [GeneralScopedMatch.assign_lookup assigned, found]⟩
              simp only [captureRest?, capture?, dependencies, occurrence, Option.bind_eq_bind, Option.bind_some,
                recover_instantiate residual spine]
              exact assigned
            have lengths := instantiateArgs_length interpreted
            by_cases vector : actualKind = .vec
            · subst vector
              obtain ⟨trace, middle, traced, middleBelow, agree⟩ := tracedArguments_of_instantiate rule spec ambient
                site path depth assignment initial 0 elements explicit supported interpreted elementFits below
              obtain ⟨final, captured, finalBelow, restAgree⟩ := restStep middle middleBelow
              refine ⟨trace, final, ?_, finalBelow, ?_⟩
              · simp only [Pattern.eraseBinderMetadata, List.map_append, itemsErased]
                apply GeneralScopedMatchMachine.TracedMatches.vectorRest
                · rw [List.take_left' (by simp [lengths])]
                  exact traced
                · rw [List.drop_left' (by simp [lengths])]
                  exact captured
              · intro other member
                simp only [Pattern.freeFvarNames, List.mem_append, Option.toList_some, List.mem_singleton] at member
                rcases member with inElements | rfl
                · have kept := GeneralScopedMatch.capture_extends captured
                  obtain ⟨stored, found'⟩ :=
                    (GeneralEquationCaptureDomain.matchedArguments_captures traced.matching) other inElements
                  rw [kept other stored found', ← found', agree other inElements]
                · exact restAgree
            · obtain ⟨trace, final, traced, finalBelow, agree⟩ := tracedBagRest_of_instantiate rule spec ambient
                site path depth assignment initial 0 actualKind elements explicit items name supported interpreted
                elementFits below (by simpa using restStep)
              refine ⟨trace, final, ?_, finalBelow, by simpa [Pattern.freeFvarNames] using agree⟩
              simp only [Pattern.eraseBinderMetadata, List.map_append, itemsErased]
              exact GeneralScopedMatchMachine.TracedMatches.bag vector traced
          · cases spliced
        · cases spliced
      | none =>
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
        obtain ⟨results, interpreted, equal⟩ := instantiated
        cases Option.some.inj equal
        have elementFits : Fits spec assignment (elements.flatMap Pattern.freeFvarNames) := by
          simpa [Pattern.freeFvarNames] using fits
        by_cases vector : kind = .vec
        · subst vector
          obtain ⟨trace, final, traced, finalBelow, agree⟩ := tracedArguments_of_instantiate rule spec ambient site
            path depth assignment initial 0 elements results supported interpreted elementFits below
          refine ⟨trace, final, ?_, finalBelow, by simpa [Pattern.freeFvarNames] using agree⟩
          simpa [Pattern.eraseBinderMetadata] using GeneralScopedMatchMachine.TracedMatches.vector traced
        · obtain ⟨trace, final, traced, finalBelow, agree⟩ := tracedBag_of_instantiate rule spec ambient site
            path depth assignment initial 0 kind elements results supported interpreted elementFits below
          refine ⟨trace, final, ?_, finalBelow, by simpa [Pattern.freeFvarNames] using agree⟩
          simpa [Pattern.eraseBinderMetadata] using GeneralScopedMatchMachine.TracedMatches.bag vector traced
  termination_by sizeOf pattern

  theorem tracedArguments_of_instantiate (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
      (site : RulePatternSite) (path : List Nat) (depth : Nat) (assignment initial : Assignment)
      (index : Nat) (patterns results : List Pattern)
      (supported : GeneralEquationAdmission.checkArguments rule spec site path depth index patterns = true)
      (instantiated : instantiateArgsWith? Substitution.instantiateBVar rule spec ambient site path depth
        assignment index patterns = some results)
      (fits : Fits spec assignment (patterns.flatMap Pattern.freeFvarNames)) (below : Below initial assignment) :
      ∃ trace final, GeneralScopedMatchMachine.TracedArguments rule spec ambient site path depth initial index
          patterns (results.map Pattern.eraseBinderMetadata) trace final ∧ Below final assignment ∧
        ∀ name ∈ patterns.flatMap Pattern.freeFvarNames, lookup final name = lookup assignment name := by
    cases patterns with
    | nil =>
      simp only [instantiateArgsWith?, Option.some.injEq] at instantiated
      subst results
      exact ⟨[], initial, .nil, below, by simp⟩
    | cons first rest =>
      simp only [GeneralEquationAdmission.checkArguments, Bool.and_eq_true] at supported
      simp only [instantiateArgsWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
      obtain ⟨head, headInterpreted, tail, tailInterpreted, equal⟩ := instantiated
      cases Option.some.inj equal
      obtain ⟨headTrace, middle, headTraced, middleBelow, headAgree⟩ := traced_of_instantiate rule spec ambient
        site (path ++ [index]) depth assignment initial first head supported.1 headInterpreted
        (fits.mono (fun name member => by simp [member])) below
      obtain ⟨tailTrace, final, tailTraced, finalBelow, tailAgree⟩ := tracedArguments_of_instantiate rule spec
        ambient site path depth assignment middle (index + 1) rest tail supported.2 tailInterpreted
        (fits.mono (fun name member => by simp [List.mem_flatMap] at member ⊢; exact Or.inr member)) middleBelow
      refine ⟨headTrace ++ tailTrace, final, .cons headTraced tailTraced, finalBelow, ?_⟩
      intro name member
      simp only [List.flatMap_cons, List.mem_append] at member
      rcases member with inHead | inTail
      · have kept := tailTraced.matching.extends name
        cases stored : lookup middle name with
        | none =>
          obtain ⟨value, found⟩ := (GeneralEquationCaptureDomain.matched_captures headTraced.matching) name inHead
          rw [stored] at found
          cases found
        | some value =>
          rw [kept value stored, ← stored, headAgree name inHead]
      · exact tailAgree name inTail
  termination_by sizeOf patterns

  theorem tracedBag_of_instantiate (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
      (site : RulePatternSite) (path : List Nat) (depth : Nat) (assignment initial : Assignment)
      (index : Nat) (kind : CollType) (patterns results : List Pattern)
      (supported : GeneralEquationAdmission.checkArguments rule spec site path depth index patterns = true)
      (instantiated : instantiateArgsWith? Substitution.instantiateBVar rule spec ambient site path depth
        assignment index patterns = some results)
      (fits : Fits spec assignment (patterns.flatMap Pattern.freeFvarNames)) (below : Below initial assignment) :
      ∃ trace final, GeneralScopedMatchMachine.TracedBag rule spec ambient site path depth initial index
          patterns none kind (results.map Pattern.eraseBinderMetadata) trace final ∧ Below final assignment ∧
        ∀ name ∈ patterns.flatMap Pattern.freeFvarNames, lookup final name = lookup assignment name := by
    cases patterns with
    | nil =>
      simp only [instantiateArgsWith?, Option.some.injEq] at instantiated
      subst results
      exact ⟨[], initial, .nil, below, by simp⟩
    | cons first rest =>
      simp only [GeneralEquationAdmission.checkArguments, Bool.and_eq_true] at supported
      simp only [instantiateArgsWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
      obtain ⟨head, headInterpreted, tail, tailInterpreted, equal⟩ := instantiated
      cases Option.some.inj equal
      obtain ⟨headTrace, middle, headTraced, middleBelow, headAgree⟩ := traced_of_instantiate rule spec ambient
        site (path ++ [index]) depth assignment initial first head supported.1 headInterpreted
        (fits.mono (fun name member => by simp [member])) below
      obtain ⟨tailTrace, final, tailTraced, finalBelow, tailAgree⟩ := tracedBag_of_instantiate rule spec
        ambient site path depth assignment middle (index + 1) kind rest tail supported.2 tailInterpreted
        (fits.mono (fun name member => by simp [List.mem_flatMap] at member ⊢; exact Or.inr member)) middleBelow
      refine ⟨_, final, GeneralScopedMatchMachine.TracedBag.cons 0 (by simp)
        (by simpa using headTraced) (by simpa using tailTraced), finalBelow, ?_⟩
      intro name member
      simp only [List.flatMap_cons, List.mem_append] at member
      rcases member with inHead | inTail
      · have kept := tailTraced.matching.extends name
        cases stored : lookup middle name with
        | none =>
          obtain ⟨value, found⟩ := (GeneralEquationCaptureDomain.matched_captures headTraced.matching) name inHead
          rw [stored] at found
          cases found
        | some value =>
          rw [kept value stored, ← stored, headAgree name inHead]
      · exact tailAgree name inTail
  termination_by sizeOf patterns

  theorem tracedBagRest_of_instantiate (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
      (site : RulePatternSite) (path : List Nat) (depth : Nat) (assignment initial : Assignment)
      (index : Nat) (kind : CollType) (patterns results tail : List Pattern) (name : String)
      (supported : GeneralEquationAdmission.checkArguments rule spec site path depth index patterns = true)
      (instantiated : instantiateArgsWith? Substitution.instantiateBVar rule spec ambient site path depth
        assignment index patterns = some results)
      (fits : Fits spec assignment (patterns.flatMap Pattern.freeFvarNames)) (below : Below initial assignment)
      (restStep : ∀ middle, Below middle assignment → ∃ final,
        captureRest? rule spec ambient depth site (path ++ [index + patterns.length]) middle name kind tail =
          some final ∧ Below final assignment ∧ lookup final name = lookup assignment name) :
      ∃ trace final, GeneralScopedMatchMachine.TracedBag rule spec ambient site path depth initial index
          patterns (some name) kind (results.map Pattern.eraseBinderMetadata ++ tail) trace final ∧
        Below final assignment ∧
        ∀ other ∈ patterns.flatMap Pattern.freeFvarNames ++ [name], lookup final other = lookup assignment other := by
    cases patterns with
    | nil =>
      simp only [instantiateArgsWith?, Option.some.injEq] at instantiated
      subst results
      obtain ⟨final, captured, finalBelow, agree⟩ := restStep initial below
      refine ⟨[], final, .rest (by simpa using captured), finalBelow, ?_⟩
      intro other member
      simp only [List.flatMap_nil, List.nil_append, List.mem_singleton] at member
      subst other
      exact agree
    | cons first rest =>
      simp only [GeneralEquationAdmission.checkArguments, Bool.and_eq_true] at supported
      simp only [instantiateArgsWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
      obtain ⟨head, headInterpreted, tailResults, tailInterpreted, equal⟩ := instantiated
      cases Option.some.inj equal
      obtain ⟨headTrace, middle, headTraced, middleBelow, headAgree⟩ := traced_of_instantiate rule spec ambient
        site (path ++ [index]) depth assignment initial first head supported.1 headInterpreted
        (fits.mono (fun other member => by simp [member])) below
      have shifted : index + 1 + rest.length = index + (first :: rest).length := by simp; omega
      obtain ⟨tailTrace, final, tailTraced, finalBelow, tailAgree⟩ := tracedBagRest_of_instantiate rule spec
        ambient site path depth assignment middle (index + 1) kind rest tailResults tail name supported.2
        tailInterpreted
        (fits.mono (fun other member => by simp [List.mem_flatMap] at member ⊢; exact Or.inr member)) middleBelow
        (by rw [shifted]; exact restStep)
      refine ⟨_, final, GeneralScopedMatchMachine.TracedBag.cons 0 (by simp)
        (by simpa using headTraced) (by simpa using tailTraced), finalBelow, ?_⟩
      intro other member
      simp only [List.flatMap_cons, List.mem_append, List.mem_singleton] at member
      rcases member with (inHead | inRest) | isName
      · have kept := tailTraced.matching.extends other
        cases stored : lookup middle other with
        | none =>
          obtain ⟨value, found⟩ := (GeneralEquationCaptureDomain.matched_captures headTraced.matching) other inHead
          rw [stored] at found
          cases found
        | some value =>
          rw [kept value stored, ← stored, headAgree other inHead]
      · exact tailAgree other (by simp [inRest])
      · exact tailAgree other (by simp [isName])
  termination_by sizeOf patterns
end

/-! ## Rebuilding a matched term -/

/-- Insert an element at every position of a list, front first. -/
def insertions {α : Type} (item : α) : List α → List (List α)
  | [] => [[item]]
  | first :: rest => (item :: first :: rest) :: (insertions item rest).map (first :: ·)

/-- Every order of a list, by inserting each head into every order of its tail. -/
def perms {α : Type} : List α → List (List α)
  | [] => [[]]
  | first :: rest => (perms rest).flatMap (insertions first)

theorem mem_insertions {α : Type} (item : α) :
    ∀ (front back : List α), front ++ item :: back ∈ insertions item (front ++ back) := by
  intro front
  induction front with
  | nil => intro back; cases back <;> simp [insertions]
  | cons first rest ih =>
    intro back
    simp only [List.cons_append, insertions, List.mem_cons, List.mem_map]
    exact Or.inr ⟨_, ih back, rfl⟩

theorem mem_perms {α : Type} : ∀ {items order : List α}, order.Perm items → order ∈ perms items := by
  intro items
  induction items with
  | nil => intro order permuted; rw [List.perm_nil.mp permuted]; simp [perms]
  | cons first rest ih =>
    intro order permuted
    obtain ⟨front, back, rfl⟩ := List.append_of_mem (permuted.symm.subset List.mem_cons_self)
    have cancelled : (front ++ back).Perm rest :=
      (List.perm_cons first).mp (List.perm_middle.symm.trans permuted)
    exact List.mem_flatMap.mpr ⟨_, ih cancelled, mem_insertions first front back⟩

mutual
  /-- The display-erased terms an instance of a side can stand for: the instance itself, with the
  elements of each bag pattern in any order. -/
  def variants : Pattern → Pattern → List Pattern
    | .apply _ patterns, .apply constructor targets =>
        (variantsList patterns targets).map fun elements => .apply constructor elements
    | .lambda _ pattern, .lambda _ target => (variants pattern target).map (.lambda none)
    | .multiLambda _ _ pattern, .multiLambda arity _ target =>
        (variants pattern target).map (.multiLambda arity [])
    | .collection kind patterns none, .collection actual targets none =>
        if kind = .vec then (variantsList patterns targets).map fun elements => .collection actual elements none
        else ((variantsList patterns targets).flatMap perms).map
          fun elements => .collection actual elements none
    | .collection kind patterns (some _), .collection actual targets none =>
        let back := (targets.drop patterns.length).map Pattern.eraseBinderMetadata
        if kind = .vec then
          (variantsList patterns (targets.take patterns.length)).map fun elements =>
            .collection actual (elements ++ back) none
        else ((variantsList patterns (targets.take patterns.length)).flatMap fun elements =>
            perms (elements ++ back)).map fun elements => .collection actual elements none
    | _, target => [target.eraseBinderMetadata]
  termination_by pattern => sizeOf pattern

  def variantsList : List Pattern → List Pattern → List (List Pattern)
    | [], [] => [[]]
    | pattern :: patterns, target :: targets =>
        (variants pattern target).flatMap fun first => (variantsList patterns targets).map (first :: ·)
    | _, _ => []
  termination_by patterns => sizeOf patterns
end

theorem perm_getElem_cons_eraseIdx {α : Type} [DecidableEq α] (items : List α) (index : Nat)
    (bounded : index < items.length) : items.Perm (items[index] :: items.eraseIdx index) :=
  (List.perm_cons_erase (List.getElem_mem bounded)).trans
    (List.Perm.cons _ (List.erase_getElem bounded))

theorem lookup_agree_middle {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial middle final : Assignment}
    {pattern target : Pattern} {headTrace : List GeneralScopedMatchMachine.BagChoice}
    (head : GeneralScopedMatchMachine.TracedMatches rule spec ambient site path depth initial pattern target
      headTrace middle)
    (extension : GeneralScopedMatch.Extends middle final) {assignment : Assignment} {name : String}
    (inHead : name ∈ pattern.freeFvarNames) (agree : lookup assignment name = lookup final name) :
    lookup assignment name = lookup middle name := by
  obtain ⟨value, found⟩ := (GeneralEquationCaptureDomain.matched_captures head.matching) name inHead
  rw [agree, extension name value found, found]

mutual
  theorem instantiate_of_traced {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial final : Assignment}
      {pattern target : Pattern} {trace : List GeneralScopedMatchMachine.BagChoice}
      (traced : GeneralScopedMatchMachine.TracedMatches rule spec ambient site path depth initial pattern target
        trace final)
      (supported : GeneralEquationAdmission.checkSide rule spec site path depth pattern = true)
      (assignment : Assignment)
      (agree : ∀ name ∈ pattern.freeFvarNames, lookup assignment name = lookup final name) :
      ∃ result, instantiateAt? rule spec ambient site path depth assignment pattern = some result ∧
        target.eraseBinderMetadata ∈ variants pattern result := by
    cases pattern with
    | fvar name =>
      cases traced with
      | capture captured =>
        obtain ⟨_, arguments, value, _, occurrence, _, found, instantiated, _⟩ :=
          GeneralScopedMatch.capture_interpretation captured
        have stored : lookup assignment name = some value := by
          rw [agree name (by simp [Pattern.freeFvarNames]), found]
        refine ⟨target, ?_, by simp [variants]⟩
        simp only [instantiateAt?, instantiateWith?, stored, occurrence, Option.bind_eq_bind, Option.bind_some]
        exact instantiated
    | bvar index =>
      cases traced with
      | bound => exact ⟨.bvar index, by simp [instantiateAt?, instantiateWith?],
          by simp [variants, Pattern.eraseBinderMetadata]⟩
    | apply label patterns =>
      cases traced with
      | constructor arguments =>
        simp only [GeneralEquationAdmission.checkSide] at supported
        obtain ⟨results, interpreted, inside⟩ := instantiateArguments_of_traced arguments supported assignment
          (by simpa [Pattern.freeFvarNames] using agree)
        refine ⟨.apply label results, ?_, ?_⟩
        · simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind] at interpreted ⊢
          rw [interpreted]
          rfl
        · simp only [variants, Pattern.eraseBinderMetadata, List.mem_map]
          exact ⟨_, inside, rfl⟩
    | lambda display body =>
      cases traced with
      | binder inner =>
        simp only [GeneralEquationAdmission.checkSide] at supported
        obtain ⟨result, interpreted, inside⟩ := instantiate_of_traced inner supported assignment
          (by simpa [Pattern.freeFvarNames] using agree)
        refine ⟨.lambda display result, ?_, ?_⟩
        · simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind] at interpreted ⊢
          rw [interpreted]
          rfl
        · simp only [variants, Pattern.eraseBinderMetadata, List.mem_map]
          exact ⟨_, inside, rfl⟩
    | multiLambda arity display body =>
      cases traced with
      | binders inner =>
        simp only [GeneralEquationAdmission.checkSide] at supported
        obtain ⟨result, interpreted, inside⟩ := instantiate_of_traced inner supported assignment
          (by simpa [Pattern.freeFvarNames] using agree)
        refine ⟨.multiLambda arity display result, ?_, ?_⟩
        · simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind] at interpreted ⊢
          rw [interpreted]
          rfl
        · simp only [variants, Pattern.eraseBinderMetadata, List.mem_map]
          exact ⟨_, inside, rfl⟩
    | subst body replacement => simp [GeneralEquationAdmission.checkSide] at supported
    | collection kind patterns rest =>
      simp only [GeneralEquationAdmission.checkSide, Bool.and_eq_true] at supported
      obtain ⟨_, supported⟩ := supported
      cases rest with
      | some name =>
        have elementAgree : ∀ other ∈ patterns.flatMap Pattern.freeFvarNames,
            lookup assignment other = lookup final other :=
          fun other member => agree other (by simp [Pattern.freeFvarNames, member])
        have restAgree := agree name (by simp [Pattern.freeFvarNames])
        cases traced with
        | bag notVector bag =>
          obtain ⟨results, interpreted, items, value, arguments, occurrence, stored, residual, elements, inside,
            permuted⟩ := instantiateBagRest_of_traced bag rfl supported assignment elementAgree
          have lengths := instantiateArgs_length interpreted
          have front : (results ++ items).take patterns.length = results := by
            rw [← lengths]; exact List.take_left
          have back : (results ++ items).drop patterns.length = items := by
            rw [← lengths]; exact List.drop_left
          refine ⟨.collection kind (results ++ items) none, ?_, ?_⟩
          · simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind] at interpreted ⊢
            simp only [Nat.zero_add] at occurrence
            simp only [interpreted, restAgree, stored, occurrence, residual, Option.bind_some, beq_self_eq_true,
              if_true]
          · simp only [variants, notVector, if_false, Pattern.eraseBinderMetadata, List.mem_map, List.mem_flatMap]
            rw [front, back]
            exact ⟨_, ⟨elements, inside, mem_perms permuted⟩, rfl⟩
        | vectorRest arguments captured =>
          rename_i targets middle
          have middleAgree : ∀ other ∈ patterns.flatMap Pattern.freeFvarNames,
              lookup assignment other = lookup middle other := fun other member => by
            obtain ⟨stored, found⟩ :=
              (GeneralEquationCaptureDomain.matchedArguments_captures arguments.matching) other member
            rw [elementAgree other member, found]
            exact GeneralScopedMatch.capture_extends captured other stored found
          obtain ⟨results, interpreted, inside⟩ := instantiateArguments_of_traced arguments supported assignment
            middleAgree
          obtain ⟨_, restArguments, value, _, occurrence, _, found, residual, _⟩ :=
            GeneralScopedMatch.capture_interpretation captured
          have lengths := instantiateArgs_length interpreted
          have front : (results ++ targets.drop patterns.length).take patterns.length = results := by
            rw [← lengths]; exact List.take_left
          have back : (results ++ targets.drop patterns.length).drop patterns.length = targets.drop patterns.length := by
            rw [← lengths]; exact List.drop_left
          refine ⟨.collection .vec (results ++ targets.drop patterns.length) none, ?_, ?_⟩
          · simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind] at interpreted ⊢
            simp only [interpreted, restAgree, found, occurrence, residual, Option.bind_some, beq_self_eq_true,
              if_true]
          · simp only [variants, if_true, Pattern.eraseBinderMetadata, List.mem_map]
            rw [front, back]
            refine ⟨_, inside, ?_⟩
            rw [← List.map_append, List.take_append_drop]
      | none =>
        cases traced with
        | bag notVector bag =>
          obtain ⟨results, interpreted, elements, inside, permuted⟩ := instantiateBag_of_traced bag supported
            assignment (by simpa [Pattern.freeFvarNames] using agree)
          refine ⟨.collection kind results none, ?_, ?_⟩
          · simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind] at interpreted ⊢
            rw [interpreted]
            rfl
          · simp only [variants, notVector, if_false, Pattern.eraseBinderMetadata, List.mem_map, List.mem_flatMap]
            exact ⟨_, ⟨elements, inside, mem_perms permuted⟩, rfl⟩
        | vector arguments =>
          obtain ⟨results, interpreted, inside⟩ := instantiateArguments_of_traced arguments supported assignment
            (by simpa [Pattern.freeFvarNames] using agree)
          refine ⟨.collection .vec results none, ?_, ?_⟩
          · simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind] at interpreted ⊢
            rw [interpreted]
            rfl
          · simp only [variants, if_true, Pattern.eraseBinderMetadata, List.mem_map]
            exact ⟨_, inside, rfl⟩
  termination_by structural pattern

  theorem instantiateArguments_of_traced {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial final : Assignment} {index : Nat}
      {patterns targets : List Pattern} {trace : List GeneralScopedMatchMachine.BagChoice}
      (traced : GeneralScopedMatchMachine.TracedArguments rule spec ambient site path depth initial index
        patterns targets trace final)
      (supported : GeneralEquationAdmission.checkArguments rule spec site path depth index patterns = true)
      (assignment : Assignment)
      (agree : ∀ name ∈ patterns.flatMap Pattern.freeFvarNames, lookup assignment name = lookup final name) :
      ∃ results, instantiateArgsWith? Substitution.instantiateBVar rule spec ambient site path depth assignment
          index patterns = some results ∧
        targets.map Pattern.eraseBinderMetadata ∈ variantsList patterns results := by
    cases traced with
    | nil => exact ⟨[], by simp [instantiateArgsWith?], by simp [variantsList]⟩
    | cons head tail =>
      simp only [GeneralEquationAdmission.checkArguments, Bool.and_eq_true] at supported
      obtain ⟨first, firstInterpreted, firstInside⟩ := instantiate_of_traced head supported.1 assignment
        (fun name member => lookup_agree_middle head tail.matching.extends member
          (agree name (by simp [member])))
      obtain ⟨rest, restInterpreted, restInside⟩ := instantiateArguments_of_traced tail supported.2 assignment
        (fun name member => agree name (by simp [List.mem_flatMap] at member ⊢; exact Or.inr member))
      refine ⟨first :: rest, ?_, ?_⟩
      · simp only [instantiateAt?] at firstInterpreted
        simp only [instantiateArgsWith?, firstInterpreted, restInterpreted, Option.bind_eq_bind, Option.bind_some]
      · simp only [List.map_cons, variantsList, List.mem_flatMap, List.mem_map]
        exact ⟨_, firstInside, _, restInside, rfl⟩
  termination_by structural patterns

  theorem instantiateBag_of_traced {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial final : Assignment} {index : Nat}
      {kind : CollType} {patterns targets : List Pattern} {trace : List GeneralScopedMatchMachine.BagChoice}
      (traced : GeneralScopedMatchMachine.TracedBag rule spec ambient site path depth initial index
        patterns none kind targets trace final)
      (supported : GeneralEquationAdmission.checkArguments rule spec site path depth index patterns = true)
      (assignment : Assignment)
      (agree : ∀ name ∈ patterns.flatMap Pattern.freeFvarNames, lookup assignment name = lookup final name) :
      ∃ results, instantiateArgsWith? Substitution.instantiateBVar rule spec ambient site path depth assignment
          index patterns = some results ∧
        ∃ elements ∈ variantsList patterns results, (targets.map Pattern.eraseBinderMetadata).Perm elements := by
    cases traced with
    | nil => exact ⟨[], by simp [instantiateArgsWith?], [], by simp [variantsList], by simp⟩
    | cons selected within head tail =>
      simp only [GeneralEquationAdmission.checkArguments, Bool.and_eq_true] at supported
      obtain ⟨first, firstInterpreted, firstInside⟩ := instantiate_of_traced head supported.1 assignment
        (fun name member => lookup_agree_middle head tail.matching.extends member
          (agree name (by simp [member])))
      obtain ⟨rest, restInterpreted, elements, restInside, permuted⟩ := instantiateBag_of_traced tail supported.2
        assignment (fun name member => agree name (by simp [List.mem_flatMap] at member ⊢; exact Or.inr member))
      refine ⟨first :: rest, ?_, targets[selected].eraseBinderMetadata :: elements, ?_, ?_⟩
      · simp only [instantiateAt?] at firstInterpreted
        simp only [instantiateArgsWith?, firstInterpreted, restInterpreted, Option.bind_eq_bind, Option.bind_some]
      · simp only [variantsList, List.mem_flatMap, List.mem_map]
        exact ⟨_, firstInside, _, restInside, rfl⟩
      · have whole := (perm_getElem_cons_eraseIdx targets selected within).map Pattern.eraseBinderMetadata
        rw [List.map_cons] at whole
        exact whole.trans (List.Perm.cons _ permuted)
  termination_by structural patterns

  theorem instantiateBagRest_of_traced {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial final : Assignment} {index : Nat}
      {kind : CollType} {patterns targets : List Pattern} {rest : Option String} {name : String}
      {trace : List GeneralScopedMatchMachine.BagChoice}
      (traced : GeneralScopedMatchMachine.TracedBag rule spec ambient site path depth initial index
        patterns rest kind targets trace final) (named : rest = some name)
      (supported : GeneralEquationAdmission.checkArguments rule spec site path depth index patterns = true)
      (assignment : Assignment)
      (agree : ∀ other ∈ patterns.flatMap Pattern.freeFvarNames, lookup assignment other = lookup final other) :
      ∃ results, instantiateArgsWith? Substitution.instantiateBVar rule spec ambient site path depth assignment
          index patterns = some results ∧
        ∃ items value arguments, arguments? rule spec name site (path ++ [index + patterns.length]) = some arguments ∧
          lookup final name = some value ∧
          instantiateValue? value ambient depth arguments = some (.collection kind items none) ∧
          ∃ elements ∈ variantsList patterns results,
            (targets.map Pattern.eraseBinderMetadata).Perm (elements ++ items.map Pattern.eraseBinderMetadata) := by
    cases traced with
    | nil => cases named
    | rest captured =>
      cases named
      obtain ⟨_, arguments, value, _, occurrence, _, found, residual, _⟩ :=
        GeneralScopedMatch.capture_interpretation captured
      exact ⟨[], by simp [instantiateArgsWith?], targets, value, arguments, by simpa using occurrence, found,
        residual, [], by simp [variantsList], by simp⟩
    | cons selected within head tail =>
      simp only [GeneralEquationAdmission.checkArguments, Bool.and_eq_true] at supported
      obtain ⟨first, firstInterpreted, firstInside⟩ := instantiate_of_traced head supported.1 assignment
        (fun other member => lookup_agree_middle head tail.matching.extends member
          (agree other (by simp [member])))
      obtain ⟨rest, restInterpreted, items, value, arguments, occurrence, found, residual, elements, restInside,
        permuted⟩ := instantiateBagRest_of_traced tail named supported.2 assignment
          (fun other member => agree other (by simp [List.mem_flatMap] at member ⊢; exact Or.inr member))
      refine ⟨first :: rest, ?_, items, value, arguments, ?_, found, residual,
        targets[selected].eraseBinderMetadata :: elements, ?_, ?_⟩
      · simp only [instantiateAt?] at firstInterpreted
        simp only [instantiateArgsWith?, firstInterpreted, restInterpreted, Option.bind_eq_bind, Option.bind_some]
      · rw [← occurrence]
        congr 2
        simp
        omega
      · simp only [variantsList, List.mem_flatMap, List.mem_map]
        exact ⟨_, firstInside, _, restInside, rfl⟩
      · have whole := (perm_getElem_cons_eraseIdx targets selected within).map Pattern.eraseBinderMetadata
        rw [List.map_cons] at whole
        exact whole.trans (List.Perm.cons _ permuted)
  termination_by structural patterns
end

end Mettapedia.OSLF.MeTTaIL.Complete.Inversion
