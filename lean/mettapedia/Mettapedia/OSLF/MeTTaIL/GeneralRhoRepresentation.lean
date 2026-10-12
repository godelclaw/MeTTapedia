import Mettapedia.OSLF.MeTTaIL.GeneralRhoTyping

/-!
# Object representation through the selected reflective operation

These structural laws retain canonical binder metadata and exclude pending
schema substitutions and open tails. They are independent of scoped typing
and apply to every reflective declaration on the shared Pattern carrier.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRho

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Substitution ReflectiveSubstitution ReflectiveInstantiation

def Represented (pattern : Pattern) : Prop :=
  pattern.hasCanonicalBinderMetadata = true ∧ isObjectPattern pattern = true

private theorem objectList_iff (patterns : List Pattern) :
    isObjectPatternList patterns = true ↔ ∀ pattern ∈ patterns, isObjectPattern pattern = true := by
  induction patterns with
  | nil => simp [isObjectPatternList]
  | cons head tail ih => simp [isObjectPatternList, ih]

theorem represented_apply_iff (constructor : String) (arguments : List Pattern) :
    Represented (.apply constructor arguments) ↔ ∀ pattern ∈ arguments, Represented pattern := by
  simp only [Represented, Pattern.hasCanonicalBinderMetadata, isObjectPattern,
    Pattern.hasCanonicalBinderMetadataList_eq_true_iff, objectList_iff]
  constructor
  · rintro ⟨metadata, objects⟩ pattern member
    exact ⟨metadata pattern member, objects pattern member⟩
  · intro represented
    exact ⟨fun p hp => (represented p hp).1, fun p hp => (represented p hp).2⟩

theorem represented_collection_iff (kind : CollType) (elements : List Pattern) :
    Represented (.collection kind elements none) ↔ ∀ pattern ∈ elements, Represented pattern := by
  simpa only [Represented, Pattern.hasCanonicalBinderMetadata, isObjectPattern,
    Option.isNone_none, Bool.true_and] using represented_apply_iff "" elements

theorem lift_represented (cutoff shift : Nat) {pattern : Pattern}
    (represented : Represented pattern) : Represented (liftBVars cutoff shift pattern) := by
  induction pattern using Pattern.inductionOn generalizing cutoff with
  | hbvar index =>
      unfold liftBVars
      split <;> exact ⟨rfl, rfl⟩
  | hfvar name => exact represented
  | happly constructor arguments ih =>
      apply (represented_apply_iff _ _).mpr
      rw [liftBVarsList_eq_map]
      rintro result member
      obtain ⟨original, sourceMember, rfl⟩ := List.mem_map.mp member
      exact ih original sourceMember cutoff ((represented_apply_iff _ _).mp represented original sourceMember)
  | hlambda binder body ih =>
      simp only [liftBVars, Represented, Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true,
        isObjectPattern] at represented ⊢
      have result := ih (cutoff + 1) ⟨represented.1.2, represented.2⟩
      exact ⟨⟨represented.1.1, result.1⟩, result.2⟩
  | hmultiLambda arity binders body ih =>
      simp only [liftBVars, Represented, Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true,
        isObjectPattern] at represented ⊢
      have result := ih (cutoff + arity) ⟨represented.1.2, represented.2⟩
      exact ⟨⟨represented.1.1, result.1⟩, result.2⟩
  | hsubst body replacement _ _ => simp [Represented, isObjectPattern] at represented
  | hcollection kind elements rest ih =>
      have restNone : rest = none := by
        cases rest <;> simp_all [Represented, isObjectPattern]
      subst rest
      apply (represented_collection_iff _ _).mpr
      rw [liftBVarsList_eq_map]
      rintro result member
      obtain ⟨original, sourceMember, rfl⟩ := List.mem_map.mp member
      exact ih original sourceMember cutoff ((represented_collection_iff _ _).mp represented original sourceMember)

private theorem instantiate_variable_represented (depth : Nat) {replacement : Pattern}
    (represented : Represented replacement) (index : Nat) :
    Represented (instantiateBVarAt depth replacement (.bvar index)) := by
  unfold instantiateBVarAt
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact lift_represented 0 depth represented
    · exact ⟨rfl, rfl⟩

private theorem finish_represented (declaration : ReflectivePresentationDecl)
    (constructor : String) {arguments : List Pattern}
    (represented : ∀ pattern ∈ arguments, Represented pattern) :
    Represented (finishNormalizeReflectiveApply declaration constructor arguments) := by
  unfold finishNormalizeReflectiveApply
  split
  · split
    · rename_i drop name
      split
      · exact (represented_apply_iff drop [name]).mp (represented _ (by simp)) name (by simp)
      · exact (represented_apply_iff _ _).mpr represented
    · exact (represented_apply_iff _ _).mpr represented
  · exact (represented_apply_iff _ _).mpr represented

private theorem normalize_list_map (declaration : ReflectivePresentationDecl) (patterns : List Pattern) :
    normalizeReflectiveList declaration patterns = patterns.map (normalizeReflective declaration) := by
  induction patterns with
  | nil => rfl
  | cons head tail ih => simp [normalizeReflectiveList, ih]

theorem normalize_represented (declaration : ReflectivePresentationDecl) {pattern : Pattern}
    (represented : Represented pattern) : Represented (normalizeReflective declaration pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar _ | hfvar _ => exact represented
  | happly constructor arguments ih =>
      apply finish_represented
      rw [normalize_list_map]
      rintro result member
      obtain ⟨original, sourceMember, rfl⟩ := List.mem_map.mp member
      exact ih original sourceMember ((represented_apply_iff _ _).mp represented original sourceMember)
  | hlambda binder body ih =>
      simp only [normalizeReflective, Represented, Pattern.hasCanonicalBinderMetadata,
        Bool.and_eq_true, isObjectPattern] at represented ⊢
      have result := ih ⟨represented.1.2, represented.2⟩
      exact ⟨⟨represented.1.1, result.1⟩, result.2⟩
  | hmultiLambda arity binders body ih =>
      simp only [normalizeReflective, Represented, Pattern.hasCanonicalBinderMetadata,
        Bool.and_eq_true, isObjectPattern] at represented ⊢
      have result := ih ⟨represented.1.2, represented.2⟩
      exact ⟨⟨represented.1.1, result.1⟩, result.2⟩
  | hsubst _ _ _ _ => simp [Represented, isObjectPattern] at represented
  | hcollection kind elements rest ih =>
      have restNone : rest = none := by cases rest <;> simp_all [Represented, isObjectPattern]
      subst rest
      apply (represented_collection_iff _ _).mpr
      rw [normalize_list_map]
      rintro result member
      obtain ⟨original, sourceMember, rfl⟩ := List.mem_map.mp member
      exact ih original sourceMember ((represented_collection_iff _ _).mp represented original sourceMember)

private theorem nameMark_represented (declaration : ReflectivePresentationDecl) (depth : Nat)
    {replacement name : Pattern} (replacementRepresented : Represented replacement)
    (nameRepresented : Represented name) :
    Represented (nameMark declaration depth replacement name).1 := by
  have normalized := normalize_represented declaration nameRepresented
  unfold nameMark
  generalize normalizeReflective declaration name = actual at normalized ⊢
  cases actual <;> try exact normalized
  exact instantiate_variable_represented depth replacementRepresented _

private def dropResult (declaration : ReflectivePresentationDecl) (constructor : String)
    (name : Pattern) (changed : Bool) : Pattern :=
  match name, changed with
  | .apply quote [process], true =>
      if quote == declaration.quoteConstructor then process else .apply constructor [name]
  | _, _ => .apply constructor [name]

private theorem finish_drop_represented (declaration : ReflectivePresentationDecl)
    (constructor : String) {name : Pattern} (changed : Bool)
    (represented : Represented name) :
    Represented (dropResult declaration constructor name changed) := by
  have rebuilt : Represented (.apply constructor [name]) :=
    (represented_apply_iff _ _).mpr (by simpa using represented)
  unfold dropResult
  cases changed with
  | false =>
      cases name <;> try exact rebuilt
      rename_i quote processes
      cases processes with
      | nil => exact rebuilt
      | cons process processes =>
          cases processes <;> exact rebuilt
  | true =>
      cases name <;> try exact rebuilt
      rename_i quote processes
      cases processes with
      | nil => exact rebuilt
      | cons process processes =>
          cases processes with
          | nil =>
              change Represented (if quote == declaration.quoteConstructor then process
                else .apply constructor [.apply quote [process]])
              split
              · exact (represented_apply_iff quote [process]).mp represented process (by simp)
              · exact rebuilt
          | cons _ _ => exact rebuilt

private theorem instantiate_list_map (declaration : ReflectivePresentationDecl)
    (depth : Nat) (replacement : Pattern) (patterns : List Pattern) :
    instantiateList declaration depth replacement patterns = patterns.map (instantiate declaration depth replacement) := by
  induction patterns with
  | nil => rfl
  | cons head tail ih => simp [instantiateList, ih]

theorem instantiate_represented (declaration : ReflectivePresentationDecl) (depth : Nat)
    {replacement pattern : Pattern} (replacementRepresented : Represented replacement)
    (represented : Represented pattern) :
    Represented (instantiate declaration depth replacement pattern) := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index => exact instantiate_variable_represented depth replacementRepresented index
  | hfvar _ => exact represented
  | happly constructor arguments ih =>
      have each := (represented_apply_iff _ _).mp represented
      have listResult : ∀ pattern ∈ instantiateList declaration depth replacement arguments, Represented pattern := by
        rw [instantiate_list_map]
        rintro result member
        obtain ⟨original, sourceMember, rfl⟩ := List.mem_map.mp member
        exact ih original sourceMember depth (each original sourceMember)
      cases arguments with
      | nil => exact ⟨rfl, rfl⟩
      | cons first rest =>
          cases rest with
          | nil =>
              simp only [instantiate]
              split
              · exact nameMark_represented declaration depth replacementRepresented represented
              · split
                · have marked := nameMark_represented declaration depth replacementRepresented (each first (by simp))
                  generalize nameMark declaration depth replacement first = actual at marked ⊢
                  cases actual with
                  | mk name changed => exact finish_drop_represented declaration constructor changed marked
                · exact (represented_apply_iff _ _).mpr (by
                    simpa using ih first (by simp) depth (each first (by simp)))
          | cons _ _ => exact (represented_apply_iff _ _).mpr listResult
  | hlambda binder body ih =>
      simp only [instantiate, Represented, Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true,
        isObjectPattern] at represented ⊢
      have result := ih (depth + 1) ⟨represented.1.2, represented.2⟩
      exact ⟨⟨represented.1.1, result.1⟩, result.2⟩
  | hmultiLambda arity binders body ih =>
      simp only [instantiate, Represented, Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true,
        isObjectPattern] at represented ⊢
      have result := ih (depth + arity) ⟨represented.1.2, represented.2⟩
      exact ⟨⟨represented.1.1, result.1⟩, result.2⟩
  | hsubst _ _ _ _ => simp [Represented, isObjectPattern] at represented
  | hcollection kind elements rest ih =>
      have restNone : rest = none := by cases rest <;> simp_all [Represented, isObjectPattern]
      subst rest
      apply (represented_collection_iff _ _).mpr
      rw [instantiate_list_map]
      rintro result member
      obtain ⟨original, sourceMember, rfl⟩ := List.mem_map.mp member
      exact ih original sourceMember depth ((represented_collection_iff _ _).mp represented original sourceMember)

open DerivedPresentationSyntax

mutual
theorem derived_name_data {free : FreeSortContext} {bound : List String} {name : Pattern}
    (typed : NameWellSorted rhoReflectivePresentation free bound name) : HasType language (typeFree free) (typeBound bound) name (.base "Name") ∧ Represented name := by
  refine ⟨derived_name_typed typed, ?_⟩
  cases typed with
  | bvar _ | fvar _ => exact ⟨rfl, rfl⟩
  | quote process =>
      apply (represented_apply_iff _ _).mpr
      simpa using (derived_process_data process).2
termination_by sizeOf name

theorem derived_process_data {free : FreeSortContext} {bound : List String} {process : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free bound process) : HasType language (typeFree free) (typeBound bound) process (.base "Proc") ∧ Represented process := by
  refine ⟨derived_process_typed typed, ?_⟩
  cases typed with
  | bvar _ | fvar _ | unit => exact ⟨rfl, rfl⟩
  | drop name =>
      apply (represented_apply_iff _ _).mpr
      simpa using (derived_name_data name).2
  | output channel payload =>
      apply (represented_apply_iff _ _).mpr
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro pattern (rfl | rfl)
      · exact (derived_name_data channel).2
      · exact (derived_process_data payload).2
  | input channel body =>
      apply (represented_apply_iff _ _).mpr
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro pattern (rfl | rfl)
      · exact (derived_name_data channel).2
      · simpa [Represented, Pattern.hasCanonicalBinderMetadata, isObjectPattern] using
          (derived_process_data body).2
  | parallel processes =>
      exact (represented_collection_iff _ _).mpr ((derived_processes_data processes).2)
termination_by sizeOf process

theorem derived_processes_data {free : FreeSortContext} {bound : List String} {processes : List Pattern}
    (typed : ProcListWellSorted rhoReflectivePresentation free bound processes) :
    ElementsHaveType language (typeFree free) (typeBound bound) processes (.base "Proc") ∧
      (∀ process ∈ processes, Represented process) := by
  refine ⟨derived_processes_typed typed, ?_⟩
  cases typed with
  | nil => simp
  | cons process processes =>
      simp only [List.mem_cons]
      rintro pattern (rfl | member)
      · exact (derived_process_data process).2
      · exact (derived_processes_data processes).2 pattern member
termination_by sizeOf processes
end

theorem derived_name_represented {free : FreeSortContext} {bound : List String} {name : Pattern}
    (typed : NameWellSorted rhoReflectivePresentation free bound name) : Represented name :=
  (derived_name_data typed).2

theorem derived_process_represented {free : FreeSortContext} {bound : List String} {process : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free bound process) : Represented process :=
  (derived_process_data typed).2

theorem derived_processes_represented {free : FreeSortContext} {bound : List String} {processes : List Pattern}
    (typed : ProcListWellSorted rhoReflectivePresentation free bound processes) :
    ∀ process ∈ processes, Represented process := (derived_processes_data typed).2

theorem derived_name_open {free : FreeSortContext} {bound : List String} {name : Pattern}
    (typed : NameWellSorted rhoReflectivePresentation free bound name) :
    OpenPatternWellSorted language (typeFree free) (typeBound bound) (.base "Name") name :=
  ⟨derived_name_typed typed, (derived_name_represented typed).1,
    (derived_name_represented typed).2, (derived_name_typed typed).isWellScopedAt⟩

theorem derived_process_open {free : FreeSortContext} {bound : List String} {process : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free bound process) :
    OpenPatternWellSorted language (typeFree free) (typeBound bound) (.base "Proc") process :=
  ⟨derived_process_typed typed, (derived_process_represented typed).1,
    (derived_process_represented typed).2, (derived_process_typed typed).isWellScopedAt⟩

end Mettapedia.OSLF.MeTTaIL.GeneralRho
