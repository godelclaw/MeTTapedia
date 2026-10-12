import Mettapedia.OSLF.NativeTypes.Generation.Occurrences

open Mettapedia.OSLF.Framework

/-!
# Context-variable agreement of the two generated occurrence readings

The ordinary address traversal reads sibling names before descending. The
structural zipper reads the filled context from left to right. Their orders
can differ, particularly when a collection retains a remainder. This module
proves exact membership agreement, so every generated rely name still has
its corresponding input coordinate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.Occurrences

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites (contextAddress)
open RedexPosition

private theorem indexed_siblings_after {α : Type} (values : List α) (first excluded : Nat)
    (earlier : excluded < first) (names : α → List String) :
    (values.zipIdx first).flatMap (fun entry => if entry.2 = excluded then [] else names entry.1) =
      values.flatMap names := by
  induction values generalizing first with
  | nil => rfl
  | cons value values ih =>
      have different : first ≠ excluded := by omega
      simp only [List.zipIdx_cons, List.flatMap_cons, different, if_false]
      rw [ih (first + 1) (by omega)]

private theorem indexed_siblings {α : Type} (before : List α) (focus : α) (after : List α)
    (first : Nat) (names : α → List String) :
    ((before ++ focus :: after).zipIdx first).flatMap
      (fun entry => if entry.2 = first + before.length then [] else names entry.1) =
      before.flatMap names ++ after.flatMap names := by
  induction before generalizing first with
  | nil =>
      simp only [List.nil_append, List.length_nil, Nat.add_zero, List.zipIdx_cons,
        List.flatMap_cons, if_true]
      exact indexed_siblings_after after (first + 1) first (by omega) names
  | cons value before ih =>
      have different : first ≠ first + (before.length + 1) := by omega
      simp only [List.cons_append, List.length_cons, List.zipIdx_cons, List.flatMap_cons,
        different, if_false]
      simp only [show first + (before.length + 1) = (first + 1) + before.length from by omega,
        ih (first + 1), List.append_assoc]

private theorem indexed_siblings_zero {α : Type} (before : List α) (focus : α) (after : List α)
    (names : α → List String) :
    (before ++ focus :: after).zipIdx.flatMap
      (fun entry => if entry.2 = before.length then [] else names entry.1) =
      before.flatMap names ++ after.flatMap names := by
  simpa only [Nat.zero_add] using indexed_siblings before focus after 0 names

private theorem fvarNamesList_flatMap (patterns : List Pattern) :
    fvarNamesList patterns = patterns.flatMap fvarNames := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns ih => simp only [fvarNamesList, List.flatMap_cons, ih]

/-- This fact holds for every structural context and every focus, rather
than only the fixed-arity communication examples. -/
theorem context_freevars_member (context : OneHoleContext) (focus : Pattern) (name : String) :
    name ∈ contextFreeVars (context.fill focus) (contextAddress context) ↔
      name ∈ contextNames context := by
  induction context generalizing focus with
  | hole => simp [contextAddress, contextFreeVars, contextNames, OneHoleContext.fill, fvarNames]
  | apply constructor before inner after ih =>
      simp only [contextAddress, contextFreeVars, contextNames, OneHoleContext.fill, localVars,
        children, childAt]
      rw [indexed_siblings_zero]
      simp [fvarNames, fvarNamesList_flatMap, ih, contextNames, or_left_comm, or_comm]
  | lambda binder inner ih =>
      simpa [contextAddress, contextFreeVars, contextNames, OneHoleContext.fill, localVars,
        children, childAt, fvarNames] using ih focus
  | multiLambda arity binders inner ih =>
      simpa [contextAddress, contextFreeVars, contextNames, OneHoleContext.fill, localVars,
        children, childAt, fvarNames] using ih focus
  | substBody inner replacement ih =>
      simp [contextAddress, contextFreeVars, contextNames, OneHoleContext.fill, localVars,
        children, childAt, fvarNames, ih, or_comm]
  | substReplacement body inner ih =>
      simp [contextAddress, contextFreeVars, contextNames, OneHoleContext.fill, localVars,
        children, childAt, fvarNames, ih]
  | collection kind before inner after rest ih =>
      simp only [contextAddress, contextFreeVars, contextNames, OneHoleContext.fill, localVars,
        children, childAt]
      rw [indexed_siblings_zero]
      simp [fvarNames, fvarNamesList_flatMap, ih, contextNames, or_left_comm, or_comm]

theorem selected_context_freevars_member {focus host : Pattern} {context : OneHoleContext}
    (selected : Selects focus context host) (name : String) :
    name ∈ contextFreeVars host (contextAddress context) ↔ name ∈ contextNames context := by
  rw [← selected.fill_eq]
  exact context_freevars_member context focus name

theorem selected_rely_member {focus host : Pattern} {context : OneHoleContext}
    (selected : Selects focus context host) (name : String) :
    name ∈ relyVars host (contextAddress context) ↔
      name ∈ contextNames context ∧ name ∉ fvarNames focus := by
  simp [relyVars, focusFreeVars, selected_subtermAt selected,
    selected_context_freevars_member selected name]

theorem generated_rely_member {language : LanguageDef} {site : Site}
    (member : site ∈ generate language) (name : String) :
    name ∈ relyVars site.rule.left site.position ↔ name ∈ site.relyNames := by
  rw [rely_names_spec]
  exact selected_rely_member ((generate_spec _ _).mp member).2 name

end Mettapedia.OSLF.NativeTypes.Generation.Occurrences
