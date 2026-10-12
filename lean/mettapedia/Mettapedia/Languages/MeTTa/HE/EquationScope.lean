import Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps
import Mettapedia.Languages.MeTTa.HE.Spec.Match.ModelTheory

/-!
# Finite scope at equation selection

The scope contains every variable in the query, retained atoms, stored binding
values, assigned keys and equality endpoints. Its structural scan has no
evaluation-fuel parameter. Membership realizes the independent evaluator's
`QueryVisibleName` relation at every atom depth.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.EquationScope

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open LeaTTaBridge
open Spec.Match.Merge
open Spec.Match.ModelTheory
open Spec.Eval.Steps

/-- Ordered support of a binding presentation, including nested values. -/
def bindingNames (bindings : Bindings) : List String :=
  bindings.assignments.flatMap (fun entry =>
    entry.1 :: (toLeaTTaAtom entry.2).vars) ++
  bindings.equalities.flatMap (fun edge => [edge.1, edge.2])

/-- Names forbidden to a fresh equation instance. -/
def visibleNames (live : List Atom) (query : Atom) (incoming : Bindings) : List String :=
  (toLeaTTaAtom query).vars ++
    live.flatMap (fun atom => (toLeaTTaAtom atom).vars) ++ bindingNames incoming

theorem bindingNames_toFinset (bindings : Bindings) :
    (bindingNames bindings).toFinset = bindingSupport bindings := rfl

/-- The complete finite scope is exactly the declarative visible-name scope. -/
theorem mem_visibleNames_iff (live : List Atom) (query : Atom) (incoming : Bindings)
    (name : String) :
    name ∈ visibleNames live query incoming ↔ QueryVisibleName live query incoming name := by
  simp only [visibleNames, bindingNames, List.mem_append, List.mem_flatMap]
  constructor
  · rintro ((queryMember | liveMember) | bindingMember)
    · exact Or.inl (atomOccurs_iff_mem_translated_vars.mpr queryMember)
    · obtain ⟨atom, member, occurrence⟩ := liveMember
      exact Or.inr (Or.inl ⟨atom, member, atomOccurs_iff_mem_translated_vars.mpr occurrence⟩)
    · rcases bindingMember with assigned | equality
      · obtain ⟨⟨key, value⟩, member, occurrence⟩ := assigned
        simp only [List.mem_cons] at occurrence
        rcases occurrence with rfl | occurrence
        · exact Or.inr (Or.inr (Or.inl ⟨value, member⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inl
            ⟨key, value, member, atomOccurs_iff_mem_translated_vars.mpr occurrence⟩)))
      · obtain ⟨⟨left, right⟩, member, occurrence⟩ := equality
        simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrence
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨left, right, member, occurrence⟩)))
  · rintro (queryOccurs | liveOccurs | assigned | storedOccurs | equality)
    · exact Or.inl (Or.inl (atomOccurs_iff_mem_translated_vars.mp queryOccurs))
    · obtain ⟨atom, member, occurrence⟩ := liveOccurs
      exact Or.inl (Or.inr ⟨atom, member, atomOccurs_iff_mem_translated_vars.mp occurrence⟩)
    · obtain ⟨value, member⟩ := assigned
      exact Or.inr (Or.inl ⟨(name, value), member, by simp⟩)
    · obtain ⟨key, value, member, occurrence⟩ := storedOccurs
      exact Or.inr (Or.inl ⟨(key, value), member,
        List.mem_cons_of_mem _ (atomOccurs_iff_mem_translated_vars.mp occurrence)⟩)
    · obtain ⟨left, right, member, occurrence⟩ := equality
      exact Or.inr (Or.inr ⟨(left, right), member, by simpa using occurrence⟩)

theorem query_occurrence_mem {live : List Atom} {query : Atom} {incoming : Bindings}
    {name : String} (occurrence : AtomOccurs query name) :
    name ∈ visibleNames live query incoming :=
  (mem_visibleNames_iff live query incoming name).mpr (Or.inl occurrence)

theorem retained_occurrence_mem {live : List Atom} {query atom : Atom} {incoming : Bindings}
    {name : String} (member : atom ∈ live) (occurrence : AtomOccurs atom name) :
    name ∈ visibleNames live query incoming :=
  (mem_visibleNames_iff live query incoming name).mpr
    (Or.inr (Or.inl ⟨atom, member, occurrence⟩))

theorem assignment_key_mem {live : List Atom} {query value : Atom} {incoming : Bindings}
    {name : String} (member : (name, value) ∈ incoming.assignments) :
    name ∈ visibleNames live query incoming :=
  (mem_visibleNames_iff live query incoming name).mpr
    (Or.inr (Or.inr (Or.inl ⟨value, member⟩)))

theorem assignment_value_occurrence_mem {live : List Atom} {query value : Atom}
    {incoming : Bindings} {key name : String} (member : (key, value) ∈ incoming.assignments)
    (occurrence : AtomOccurs value name) :
    name ∈ visibleNames live query incoming :=
  (mem_visibleNames_iff live query incoming name).mpr
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨key, value, member, occurrence⟩))))

theorem equality_left_mem {live : List Atom} {query : Atom} {incoming : Bindings}
    {left right : String} (member : (left, right) ∈ incoming.equalities) :
    left ∈ visibleNames live query incoming :=
  (mem_visibleNames_iff live query incoming left).mpr
    (Or.inr (Or.inr (Or.inr (Or.inr ⟨left, right, member, Or.inl rfl⟩))))

theorem equality_right_mem {live : List Atom} {query : Atom} {incoming : Bindings}
    {left right : String} (member : (left, right) ∈ incoming.equalities) :
    right ∈ visibleNames live query incoming :=
  (mem_visibleNames_iff live query incoming right).mpr
    (Or.inr (Or.inr (Or.inr (Or.inr ⟨left, right, member, Or.inr rfl⟩))))

end Mettapedia.Languages.MeTTa.HE.EquationScope
