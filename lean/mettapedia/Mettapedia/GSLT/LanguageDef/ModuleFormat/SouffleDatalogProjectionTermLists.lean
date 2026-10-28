import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionTerms

/-! Recursive argument tuples use the three actual authored rules. Each
cons step retains its argument child and its tail child in premise order. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.TermLists

open Mettapedia.OSLF.MeTTaIL Syntax Match
open Reference (vector tuple)

def rule (index : Fin 3) : RewriteRule :=
  language.rewrites[28 + index.val]'(by rw [authored_rule_count]; have := index.isLt; omega)

def termSource : Pattern := .apply "ProjectTerm" [.fvar "source"]
def tailSource : Pattern := .apply "ProjectTerms" [.fvar "tail"]
def termPremise : Premise := .congruence termSource (.fvar "value")
def tailPremise : Premise := .congruence tailSource (.apply "Tuple" [.fvar "rest"])

def lhs (index : Fin 3) : Pattern := .apply "ProjectTerms" [
  match index.val with
  | 0 => .apply "dl-src:terms-empty" []
  | 1 => .apply "dl-src:terms-one" [.fvar "source", .fvar "trailing"]
  | _ => .apply "dl-src:terms-more" [.fvar "source", .fvar "before", .fvar "after", .fvar "tail"]]

def rhs (index : Fin 3) : Pattern := .apply "Tuple" [
  match index.val with
  | 0 => .collection .vec [] none
  | 1 => .collection .vec [.fvar "value"] none
  | _ => .collection .vec [.fvar "value"] (some "rest")]

def premises (index : Fin 3) : List Premise :=
  match index.val with
  | 0 => []
  | 1 => [termPremise]
  | _ => [termPremise, tailPremise]

theorem rule_at (index : Fin 3) : language.rewrites[28 + index.val]? = some (rule index) := by
  simp [rule]

theorem rule_left (index : Fin 3) : (rule index).left = lhs index := by
  fin_cases index <;> decide +kernel

theorem rule_right (index : Fin 3) : (rule index).right = rhs index := by
  fin_cases index <;> decide +kernel

theorem rule_premises (index : Fin 3) : (rule index).premises = premises index := by
  fin_cases index <;> decide +kernel

def call (source : Pattern) : Pattern := .apply "ProjectTerms" [source]
def empty : Pattern := .apply "dl-src:terms-empty" []
def one (source trailing : Pattern) : Pattern := .apply "dl-src:terms-one" [source,trailing]
def more (source before after tail : Pattern) : Pattern :=
  .apply "dl-src:terms-more" [source,before,after,tail]

def oneBindings (source trailing : Pattern) : Bindings := [("trailing",trailing),("source",source)]
def moreBindings (source before after tail : Pattern) : Bindings :=
  [("before",before),("tail",tail),("after",after),("source",source)]
def withValue (bindings : Bindings) (value : Pattern) : Bindings := ("value",value) :: bindings

def withRest (bindings : Bindings) (rest : List Pattern) : Bindings :=
  ("rest",vector rest) :: bindings

theorem match_empty : matchPattern (rule 0).left (call empty) = [[]] := by
  rw [rule_left]
  decide +kernel

theorem match_one (source trailing : Pattern) :
    matchPattern (rule 1).left (call (one source trailing)) = [oneBindings source trailing] := by
  rw [rule_left]
  simp [lhs, call, one, oneBindings, matchPattern, matchArgs, mergeBindings]

theorem match_more (source before after tail : Pattern) :
    matchPattern (rule 2).left (call (more source before after tail)) =
      [moreBindings source before after tail] := by
  rw [rule_left]
  simp [lhs, call, more, moreBindings, matchPattern, matchArgs, mergeBindings]

theorem rhs_plain (sites : Pattern) (bindings : Bindings) (index : Fin 3) :
    applyBindingsScoped sites bindings 0 (rule index).right = applyBindings bindings (rhs index) := by
  rw [rule_right]
  apply applyBindingsScoped_zero_of_binderFree
  fin_cases index <;> decide +kernel

theorem rhs_empty (sites : Pattern) :
    applyBindingsScoped sites [] 0 (rule 0).right = tuple [] := by
  rw [rhs_plain]
  simp [rhs, tuple, vector, applyBindings]

theorem rhs_one (sites source trailing value : Pattern) :
    applyBindingsScoped sites (withValue (oneBindings source trailing) value) 0 (rule 1).right =
      tuple [value] := by
  rw [rhs_plain]
  simp [rhs, withValue, oneBindings, tuple, vector, applyBindings]

theorem rhs_more (sites source before after tail value : Pattern) (rest : List Pattern) :
    applyBindingsScoped sites (withRest (withValue (moreBindings source before after tail) value) rest)
      0 (rule 2).right = tuple (value :: rest) := by
  rw [rhs_plain]
  simp [rhs, withRest, withValue, moreBindings, tuple, vector, applyBindings]

theorem term_source_one (sites source trailing : Pattern) :
    applyBindingsScoped sites (oneBindings source trailing) 0 termSource =
      .apply "ProjectTerm" [source] := by
  simp [termSource, oneBindings, applyBindingsScoped_apply, applyBindingsScoped_fvar_zero, applyBindings]

theorem term_source_more (sites source before after tail : Pattern) :
    applyBindingsScoped sites (moreBindings source before after tail) 0 termSource =
      .apply "ProjectTerm" [source] := by
  simp [termSource, moreBindings, applyBindingsScoped_apply, applyBindingsScoped_fvar_zero, applyBindings]

theorem tail_source_more (sites source before after tail value : Pattern) :
    applyBindingsScoped sites (withValue (moreBindings source before after tail) value) 0 tailSource = call tail := by
  simp [tailSource, withValue, moreBindings, call, applyBindingsScoped_apply,
    applyBindingsScoped_fvar_zero, applyBindings]

theorem empty_step (environment : Engine.RelationEnv) :
    ReferenceStep.Step environment language (call empty) (tuple []) := by
  apply (ReferenceStep.step_rule_iff environment language _ _).mpr
  refine ⟨28,rule 0,rule_at 0,[],?_,[],?_,rhs_empty _⟩
  · rw [match_empty]
    exact List.mem_singleton_self _
  · rw [rule_premises]
    exact ⟨[],.nil _⟩

theorem one_step (environment : Engine.RelationEnv) (source trailing value : Pattern)
    (child : ReferenceStep.Step environment language (.apply "ProjectTerm" [source]) value) :
    ReferenceStep.Step environment language (call (one source trailing)) (tuple [value]) := by
  apply (ReferenceStep.step_rule_iff environment language _ _).mpr
  refine ⟨29,rule 1,rule_at 1,oneBindings source trailing,?_,
    withValue (oneBindings source trailing) value,?_,rhs_one _ _ _ _⟩
  · rw [match_one]
    exact List.mem_singleton_self _
  · rw [rule_premises]
    change ∃ witnesses, ReferenceStep.PremisesValid environment language _ _ [termPremise] witnesses _
    rw [ReferenceStep.premises_cons_iff]
    refine ⟨withValue (oneBindings source trailing) value,?_,?_⟩
    · rw [termPremise, ReferenceStep.congruence_iff]
      refine ⟨value,[("value",value)],?_,by simp [matchPattern],?_⟩
      · change ReferenceStep.Step environment language
          (applyBindingsScoped _ (oneBindings source trailing) 0 termSource) value
        rw [term_source_one]
        exact child
      · simp [oneBindings, withValue, mergeBindings]
    · exact ⟨[],.nil _⟩

theorem more_step (environment : Engine.RelationEnv)
    (source before after tail value : Pattern) (rest : List Pattern)
    (headChild : ReferenceStep.Step environment language (.apply "ProjectTerm" [source]) value)
    (tailChild : ReferenceStep.Step environment language (call tail) (tuple rest)) :
    ReferenceStep.Step environment language (call (more source before after tail)) (tuple (value :: rest)) := by
  apply (ReferenceStep.step_rule_iff environment language _ _).mpr
  refine ⟨30,rule 2,rule_at 2,moreBindings source before after tail,?_,
    withRest (withValue (moreBindings source before after tail) value) rest,?_,rhs_more _ _ _ _ _ _ _⟩
  · rw [match_more]
    exact List.mem_singleton_self _
  · rw [rule_premises]
    change ∃ witnesses, ReferenceStep.PremisesValid environment language _ _
      [termPremise,tailPremise] witnesses _
    rw [ReferenceStep.premises_cons_iff]
    refine ⟨withValue (moreBindings source before after tail) value,?_,?_⟩
    · rw [termPremise, ReferenceStep.congruence_iff]
      refine ⟨value,[("value",value)],?_,by simp [matchPattern],?_⟩
      · change ReferenceStep.Step environment language
          (applyBindingsScoped _ (moreBindings source before after tail) 0 termSource) value
        rw [term_source_more]
        exact headChild
      · simp [moreBindings, withValue, mergeBindings]
    · rw [ReferenceStep.premises_cons_iff]
      refine ⟨withRest (withValue (moreBindings source before after tail) value) rest,?_,?_⟩
      · rw [tailPremise, ReferenceStep.congruence_iff]
        refine ⟨tuple rest,[("rest",vector rest)],?_,?_,?_⟩
        · change ReferenceStep.Step environment language
            (applyBindingsScoped _ (withValue (moreBindings source before after tail) value) 0 tailSource)
            (tuple rest)
          rw [tail_source_more]
          exact tailChild
        · simp [tuple, matchPattern, matchArgs, mergeBindings]
        · simp [moreBindings, withValue, withRest, mergeBindings]
      · exact ⟨[],.nil _⟩

theorem reference_of_step (environment : Engine.RelationEnv) (source target : Pattern)
    (stepped : ReferenceStep.Step environment language (call source) target) :
    ∃ values, Reference.terms? source = some values ∧ target = tuple values := by
  obtain ⟨index, candidate, selected, found, initial, matched, final, holds, output⟩ :=
    (step_candidates_iff environment "ProjectTerms" [source] target).mp stepped
  rw [terms_candidates] at candidate
  simp only [List.mem_cons, List.not_mem_nil, or_false] at candidate
  rcases candidate with rfl | rfl | rfl
  · have atRule : language.rewrites[28]? = some (rule 0) := rule_at 0
    rw [atRule] at found
    cases Option.some.inj found
    have shape := source_constructor_of_match "ProjectTerms" "dl-src:terms-empty" []
      (by simpa [rule_left, lhs] using matched)
    obtain ⟨arguments, sourceEqual, length⟩ := shape
    have nil : arguments = [] := List.length_eq_zero_iff.mp length
    subst arguments
    subst source
    change initial ∈ matchPattern (rule 0).left (call empty) at matched
    have emptyMatched : initial = [] := by simpa only [match_empty, List.mem_singleton] using matched
    subst initial
    rw [rule_premises] at holds
    have same : [] = final := (ReferenceStep.premises_nil_iff environment language _ _ _).mp holds
    subst final
    rw [rhs_empty] at output
    exact ⟨[],rfl,output.symm⟩
  · have atRule : language.rewrites[29]? = some (rule 1) := rule_at 1
    rw [atRule] at found
    cases Option.some.inj found
    have shape := source_constructor_of_match "ProjectTerms" "dl-src:terms-one"
      [.fvar "source",.fvar "trailing"] (by simpa [rule_left, lhs] using matched)
    obtain ⟨arguments, sourceEqual, length⟩ := shape
    obtain ⟨literal,trailing,rfl⟩ := List.length_eq_two.mp length
    subst source
    change initial ∈ matchPattern (rule 1).left (call (one literal trailing)) at matched
    have initialEqual : initial = oneBindings literal trailing := by
      simpa only [match_one, List.mem_singleton] using matched
    subst initial
    rw [rule_premises] at holds
    change ∃ witnesses, ReferenceStep.PremisesValid environment language _ _ [termPremise] witnesses _ at holds
    rw [ReferenceStep.premises_cons_iff] at holds
    obtain ⟨middle, child, tailValid⟩ := holds
    have same : middle = final := (ReferenceStep.premises_nil_iff environment language _ _ _).mp tailValid
    subst final
    rw [termPremise, ReferenceStep.congruence_iff] at child
    obtain ⟨value, extension, childStep, matchedValue, merged⟩ := child
    change ReferenceStep.Step environment language
      (applyBindingsScoped _ (oneBindings literal trailing) 0 termSource) value at childStep
    rw [term_source_one] at childStep
    have projected := (Terms.reference_exact environment literal value).mp childStep
    simp only [matchPattern, List.mem_singleton] at matchedValue
    subst extension
    simp [oneBindings, mergeBindings] at merged
    cases merged
    change applyBindingsScoped _ (withValue (oneBindings literal trailing) value) 0 (rule 1).right = target at output
    rw [rhs_one] at output
    refine ⟨[value],?_,output.symm⟩
    change (Reference.term? literal).map (· :: []) = some [value]
    rw [projected]
    rfl
  · have atRule : language.rewrites[30]? = some (rule 2) := rule_at 2
    rw [atRule] at found
    cases Option.some.inj found
    have shape := source_constructor_of_match "ProjectTerms" "dl-src:terms-more"
      [.fvar "source",.fvar "before",.fvar "after",.fvar "tail"]
      (by simpa [rule_left, lhs] using matched)
    obtain ⟨arguments, sourceEqual, length⟩ := shape
    obtain ⟨literal,before,after,tail,rfl⟩ := List.length_eq_four.mp length
    subst source
    change initial ∈ matchPattern (rule 2).left (call (more literal before after tail)) at matched
    have initialEqual : initial = moreBindings literal before after tail := by
      simpa only [match_more, List.mem_singleton] using matched
    subst initial
    rw [rule_premises] at holds
    change ∃ witnesses, ReferenceStep.PremisesValid environment language _ _
      [termPremise,tailPremise] witnesses _ at holds
    rw [ReferenceStep.premises_cons_iff] at holds
    obtain ⟨middle, child, later⟩ := holds
    rw [termPremise, ReferenceStep.congruence_iff] at child
    obtain ⟨value, extension, childStep, matchedValue, merged⟩ := child
    change ReferenceStep.Step environment language
      (applyBindingsScoped _ (moreBindings literal before after tail) 0 termSource) value at childStep
    rw [term_source_more] at childStep
    have headProjected := (Terms.reference_exact environment literal value).mp childStep
    simp only [matchPattern, List.mem_singleton] at matchedValue
    subst extension
    simp [moreBindings, mergeBindings] at merged
    cases merged
    rw [ReferenceStep.premises_cons_iff] at later
    obtain ⟨last, child, tailValid⟩ := later
    have same : last = final := (ReferenceStep.premises_nil_iff environment language _ _ _).mp tailValid
    subst final
    rw [tailPremise, ReferenceStep.congruence_iff] at child
    obtain ⟨candidate, extension, tailStep, matchedRest, mergedRest⟩ := child
    change ReferenceStep.Step environment language
      (applyBindingsScoped _ (withValue (moreBindings literal before after tail) value) 0 tailSource)
      candidate at tailStep
    rw [tail_source_more] at tailStep
    obtain ⟨rest, tailProjected, candidateEqual⟩ := reference_of_step environment tail candidate tailStep
    subst candidate
    simp [tuple, matchPattern, matchArgs, mergeBindings] at matchedRest
    subst extension
    simp [mergeBindings] at mergedRest
    cases mergedRest
    change applyBindingsScoped _
      (withRest (withValue (moreBindings literal before after tail) value) rest) 0 (rule 2).right = target at output
    rw [rhs_more] at output
    refine ⟨value :: rest,?_,output.symm⟩
    rw [Reference.terms?]
    simp only [headProjected, tailProjected, Option.bind_eq_bind, Option.bind_some]
    rfl
termination_by sizeOf source
decreasing_by simp_all; omega

theorem step_of_reference (environment : Engine.RelationEnv) (source : Pattern) (values : List Pattern)
    (projected : Reference.terms? source = some values) :
    ReferenceStep.Step environment language (call source) (tuple values) := by
  unfold Reference.terms? at projected
  split at projected
  · cases Option.some.inj projected
    exact empty_step environment
  · obtain ⟨value, literalProjected, rfl⟩ := Option.map_eq_some_iff.mp projected
    exact one_step environment _ _ value ((Terms.reference_exact environment _ _).mpr literalProjected)
  · rename_i literal before after tail
    cases headProjected : Reference.term? literal with
    | none => simp [headProjected, Option.bind_eq_bind] at projected
    | some value =>
      cases tailProjected : Reference.terms? tail with
      | none => simp [headProjected, tailProjected, Option.bind_eq_bind] at projected
      | some rest =>
        simp only [headProjected, tailProjected, Option.bind_eq_bind, Option.bind_some] at projected
        change some (value :: rest) = some values at projected
        cases Option.some.inj projected
        exact more_step environment literal before after tail value rest
          ((Terms.reference_exact environment _ _).mpr headProjected)
          (step_of_reference environment tail rest tailProjected)
  · cases projected
termination_by sizeOf source
decreasing_by simp_all; omega

theorem reference_exact (environment : Engine.RelationEnv) (source target : Pattern) :
    ReferenceStep.Step environment language (call source) target ↔
      (Reference.terms? source).map tuple = some target := by
  constructor
  · intro stepped
    obtain ⟨values, projected, rfl⟩ := reference_of_step environment source target stepped
    rw [projected]
    rfl
  · intro projected
    obtain ⟨values, valuesProjected, rfl⟩ := Option.map_eq_some_iff.mp projected
    exact step_of_reference environment source values valuesProjected

#print axioms reference_of_step
#print axioms step_of_reference
#print axioms reference_exact

#print axioms match_more
#print axioms empty_step
#print axioms one_step
#print axioms more_step

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.TermLists
