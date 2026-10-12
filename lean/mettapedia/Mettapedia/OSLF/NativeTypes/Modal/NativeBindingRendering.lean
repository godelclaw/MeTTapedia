import Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingSource
import Mettapedia.OSLF.Syntax.BindingPatternRendering
import Mettapedia.GSLT.LanguageDef.TypedBoundSubstitution

/-!
# The authored binder printer preserves actual contextual substitution

The generated binding signature is rendered by its original constructor
labels and computed parameter scopes. Its canonical printer agrees with the
independent generic binding rendering. Consequently intrinsic substitution
prints as the same simultaneous substitution used by operational receipts.
No interpretation of an arbitrary function as a raw binder is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeBindingRendering

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.NativeTypes.Generation
open CurriedBindingLanguage BindingSemanticAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted

variable {language : LanguageDef}

def rendering (language : LanguageDef) : PatternRendering.Rendering (signature language) where
  operation origin arguments := .apply language.terms[origin.index.val].label arguments
  shift _ _ _ _ := rfl
  bind _ _ _ := rfl

theorem variable_index {context : List String} {sort : String} (position : Var context sort) :
    (varIdx (S := signature language) position).val = variableIndex position := by
  induction position <;> simp_all [varIdx, variableIndex]

theorem wrap_length {left right : List String} (same : left.length = right.length)
    (body : Pattern) : wrap left body = wrap right body := by
  induction left generalizing right with
  | nil => cases right <;> simp_all [wrap]
  | cons head tail ih =>
      cases right with
      | nil => simp at same
      | cons other rest => exact congrArg (Pattern.lambda none) (ih (Nat.succ.inj same))

theorem wrap_render (domains : List String) (body : Pattern) :
    wrap domains body = PatternRendering.wrapBinders domains body := by
  induction domains <;> simp_all [wrap, PatternRendering.wrapBinders]

theorem parameter_render {parameter : TermParam} {scope : List String} {sort : String}
    (meaning : ParameterMeaning parameter scope sort) (body : Pattern) :
    printArgument parameter body = PatternRendering.wrapBinders scope body := by
  cases meaning with
  | data => rfl
  | shorthand => rfl
  | @binding binder bodyName domain bodyType domains result spine =>
      have decoded := (binderSpine?_exact _ _ _).mpr (BinderSpine.binder domain spine)
      simp only [printArgument, decoded]
      exact (wrap_length (by simp) body).trans (wrap_render _ body)

theorem print_render_sized (n : Nat) :
    (∀ {context : List String} {sort : String} (term : Term (signature language) context sort),
      CurriedBindingLanguage.termSize term < n → toPattern term = PatternRendering.encodeTerm (rendering language) term) ∧
    (∀ (parameters : List TermParam)
      (_supported : ∀ parameter ∈ parameters, ∃ scope sort, ParameterMeaning parameter scope sort)
      {context : List String} {arity : List (List String × String)}
      (arguments : Args (signature language) arity context),
      arity = slots parameters → CurriedBindingLanguage.argsSize arguments < n →
      toPatterns parameters arguments = PatternRendering.encodeArgs (rendering language) arguments) := by
  induction n with
  | zero => constructor <;> intros <;> omega
  | succ n ih =>
      constructor
      · intro context sort term small
        change Ctx (signature language) at context
        change (signature language).Srt at sort
        cases term with
        | var position => exact congrArg Pattern.bvar (variable_index position).symm
        | op origin arguments =>
            have smaller : CurriedBindingLanguage.argsSize arguments < n := by simp only [CurriedBindingLanguage.termSize] at small; omega
            exact congrArg (Pattern.apply language.terms[origin.index.val].label)
              (ih.2 _ origin.parameters arguments rfl smaller)
      · intro parameters supported context arity arguments aligned small
        change Ctx (signature language) at context
        change List (List (signature language).Srt × (signature language).Srt) at arity
        cases arguments with
        | nil => cases parameters <;> rfl
        | @cons binders result tail ctx body rest =>
            cases parameters with
            | nil => simp [slots] at aligned
            | cons parameter parameters =>
                obtain ⟨scope, sort, meaning⟩ := supported parameter (by simp)
                have headSlot := (List.cons.inj aligned).1.trans (slot_meaning meaning)
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj headSlot
                have smallerBody : CurriedBindingLanguage.termSize body < n := by simp only [CurriedBindingLanguage.argsSize] at small; omega
                have smallerRest : CurriedBindingLanguage.argsSize rest < n := by simp only [CurriedBindingLanguage.argsSize] at small; omega
                change printArgument parameter (toPattern body) :: toPatterns parameters rest =
                  PatternRendering.wrapBinders binders (PatternRendering.encodeTerm (rendering language) body) ::
                    PatternRendering.encodeArgs (rendering language) rest
                rw [parameter_render meaning, ih.1 body smallerBody,
                  ih.2 parameters (fun p member => supported p (by simp [member])) rest
                    (List.cons.inj aligned).2 smallerRest]
                rfl

theorem print_render {context : List String} {sort : String}
    (term : Term (signature language) context sort) :
    toPattern term = PatternRendering.encodeTerm (rendering language) term :=
  (print_render_sized (CurriedBindingLanguage.termSize term + 1)).1 term (Nat.lt_succ_self _)

def assignment {source target : List String} (substitution : Sub (signature language) source target) :
    ContextSubstitution.Assignment :=
  fun index => if index < source.length then
    PatternRendering.encodeSub (rendering language) substitution index
  else .bvar (index - source.length + target.length)

theorem assignment_variable {source target : List String}
    (substitution : Sub (signature language) source target) {sort : String} (position : Var source sort) :
    assignment substitution (variableIndex position) = toPattern (substitution sort position) := by
  rw [← variable_index position]
  unfold assignment
  have inside : (varIdx (S := signature language) position).val < source.length :=
    (varIdx (S := signature language) position).isLt
  rw [if_pos inside]
  exact (PatternRendering.encodeSub_at_var (rendering language) substitution position).trans
    (print_render _).symm

theorem print_substitution {source target : List String}
    (substitution : Sub (signature language) source target) {sort : String}
    (term : Term (signature language) source sort) :
    toPattern (Binding.bind substitution term) =
      ContextSubstitution.substitute (assignment substitution) (toPattern term) := by
  rw [print_render, print_render]
  apply PatternRendering.encodeTerm_bind_of_assignment (rendering language) substitution
  intro sort position
  change String at sort
  change Var (Srt := String) source sort at position
  exact (congrArg (assignment substitution) (variable_index position)).trans
    ((assignment_variable substitution position).trans (print_render _))

def typedAssignment {source target : List String}
    (substitution : Sub (signature language) source target) :
    TypedBoundAssignment language FreeTypeContext.empty
      (Mettapedia.GSLT.Poly.BindingLanguage.typeContext source)
      (Mettapedia.GSLT.Poly.BindingLanguage.typeContext target) where
  assignment := assignment substitution
  typed := by
    intro index type selected
    obtain ⟨sort, member, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? selected)
    obtain ⟨position, atIndex⟩ := Mettapedia.GSLT.Poly.BindingLanguage.exists_var_of_get
      (Mettapedia.GSLT.Poly.BindingLanguage.lookup_base selected)
    rw [← atIndex, ← variableIndex_eq_varIndex position, assignment_variable]
    exact toPattern_typed (substitution sort position)

theorem assignment_outside {source target : List String}
    (substitution : Sub (signature language) source target) {index : Nat}
    (outside : source.length ≤ index) :
    assignment substitution index = .bvar (index - source.length + target.length) := by
  simp only [assignment, Nat.not_lt.mpr outside, ite_false]

theorem assignment_images {source target : List String}
    (substitution : Sub (signature language) source target) (index : Nat) :
    isObjectPattern (assignment substitution index) = true ∧
      (assignment substitution index).hasCanonicalBinderMetadata = true := by
  by_cases inside : index < source.length
  · obtain ⟨position, atIndex⟩ := Mettapedia.GSLT.Poly.BindingLanguage.exists_var_of_get
      (show source[index]? = some source[index] from List.getElem?_eq_getElem inside)
    rw [← atIndex, ← variableIndex_eq_varIndex position, assignment_variable]
    exact ⟨toPattern_object _, toPattern_canonical _⟩
  · rw [assignment_outside substitution (Nat.le_of_not_gt inside)]
    exact ⟨rfl, rfl⟩


theorem assignment_identity (context : List String) :
    assignment (fun _ position => Term.var position : Sub (signature language) context context) =
      Pattern.bvar := by
  funext index
  by_cases inside : index < context.length
  · obtain ⟨position, atIndex⟩ := Mettapedia.GSLT.Poly.BindingLanguage.exists_var_of_get
      (show context[index]? = some context[index] from List.getElem?_eq_getElem inside)
    rw [← atIndex, ← variableIndex_eq_varIndex position, assignment_variable]
    rfl
  · rw [assignment_outside _ (Nat.le_of_not_gt inside)]
    congr 1
    omega

theorem assignment_composition {source middle target : List String}
    (first : Sub (signature language) source middle)
    (second : Sub (signature language) middle target) :
    assignment (fun sort position => Binding.bind second (first sort position)) =
      fun index => ContextSubstitution.substitute (assignment second) (assignment first index) := by
  funext index
  by_cases inside : index < source.length
  · obtain ⟨position, atIndex⟩ := Mettapedia.GSLT.Poly.BindingLanguage.exists_var_of_get
      (show source[index]? = some source[index] from List.getElem?_eq_getElem inside)
    rw [← atIndex, ← variableIndex_eq_varIndex position, assignment_variable,
      assignment_variable, print_substitution]
  · rw [assignment_outside _ (Nat.le_of_not_gt inside),
      assignment_outside first (Nat.le_of_not_gt inside)]
    simp only [ContextSubstitution.substitute]
    rw [assignment_outside second (by omega)]
    congr 1
    omega

end Mettapedia.OSLF.NativeTypes.Modal.NativeBindingRendering
