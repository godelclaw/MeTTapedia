import Mettapedia.Machines.Cursor.TermPathPosting

/-!
# Rigid-prefix refinement of a term-path frontier

An uncertain projection at one path does not make every other coordinate
uncertain. A second rigid key can refute a row while retaining unknown prefixes.
The refined frontier gives exactly the same ordered matching occurrences,
including duplicates, under independent query and stored-variable environments.

This is the ordinary finite-term fragment of `TermPathPosting`. Private carriers,
numeric promotion, storage generations and native memory ownership require their
adapter checks; the theorem does not verify the C representation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.TermPathPostingRefinement

open TermPathPosting

/-- Keep unknown and absent projections; only a different rigid key refutes. -/
def prefixCompatible (key : Nat) : Projection → Bool
  | .key value => value == key
  | _ => true

theorem separate_unifier_prefix_compatible
    (queryEnvironment rowEnvironment : Nat → Term)
    (query row : Term) (path : List Nat) (key : Nat)
    (queryKey : project query path = .key key)
    (unifier : subst queryEnvironment query = subst rowEnvironment row) :
    prefixCompatible key (project row path) = true := by
  have accepted := separate_unifier_not_refuted
    queryEnvironment rowEnvironment query row path key queryKey unifier
  cases projection : project row path <;>
    simp_all [prefixCompatible, accepts]

def refineFrontier (path prefixPath : List Nat) (key prefixKey : Nat)
    (occurrences : List (Nat × Term)) : List (Nat × Term) :=
  occurrences.filter fun occurrence =>
    accepts key (project occurrence.2 path) &&
      prefixCompatible prefixKey (project occurrence.2 prefixPath)

theorem exact_refined_occurrences (query : Term)
    (path prefixPath : List Nat) (key prefixKey : Nat)
    (queryKey : project query path = .key key)
    (queryPrefix : project query prefixPath = .key prefixKey)
    (occurrences : List (Nat × Term)) :
    (refineFrontier path prefixPath key prefixKey occurrences).filter (fun occurrence => by
      classical
      exact decide (∃ queryEnvironment rowEnvironment,
        subst queryEnvironment query = subst rowEnvironment occurrence.2)) =
    occurrences.filter (fun occurrence => by
      classical
      exact decide (∃ queryEnvironment rowEnvironment,
        subst queryEnvironment query = subst rowEnvironment occurrence.2)) := by
  classical
  rw [refineFrontier, List.filter_filter]
  apply List.filter_congr
  intro occurrence _
  by_cases unifier : ∃ queryEnvironment rowEnvironment,
      subst queryEnvironment query = subst rowEnvironment occurrence.2
  · obtain ⟨queryEnvironment, rowEnvironment, equal⟩ := unifier
    have accepted := separate_unifier_not_refuted queryEnvironment rowEnvironment
      query occurrence.2 path key queryKey equal
    have compatible := separate_unifier_prefix_compatible queryEnvironment rowEnvironment
      query occurrence.2 prefixPath prefixKey queryPrefix equal
    simp [accepted, compatible]
  · simp [unifier]

theorem duplicate_occurrences_control :
    refineFrontier [2] [0] 7 9
      [(0, .node [.key 9, .key 1, .var 2]),
       (1, .node [.key 8, .var 2, .var 2]),
       (2, .node [.key 9, .key 1, .var 2]), (3, .var 0)] =
      [(0, .node [.key 9, .key 1, .var 2]),
       (2, .node [.key 9, .key 1, .var 2]), (3, .var 0)] := by
  simp [refineFrontier, accepts, prefixCompatible, project]

theorem uncertain_field_does_not_hide_prefix_clash :
    accepts 7 (project (.node [.key 8, .var 2, .var 2]) [2]) = true ∧
      prefixCompatible 9 (project (.node [.key 8, .var 2, .var 2]) [0]) = false := by
  decide

theorem variable_prefix_must_remain :
    prefixCompatible 9 (project (.var 0) [0]) = true ∧
      project (.var 0) [0] ≠ .key 9 := by decide

/-- Refine uncertain postings only; keyed rows retain the canonical match. -/
def refineUncertainFrontier (path prefixPath : List Nat) (key prefixKey : Nat)
    (occurrences : List (Nat × Term)) : List (Nat × Term) :=
  occurrences.filter fun occurrence =>
    accepts key (project occurrence.2 path) &&
      match project occurrence.2 path with
      | .uncertain => prefixCompatible prefixKey (project occurrence.2 prefixPath)
      | _ => true

theorem exact_uncertain_refined_occurrences (query : Term)
    (path prefixPath : List Nat) (key prefixKey : Nat)
    (queryKey : project query path = .key key)
    (queryPrefix : project query prefixPath = .key prefixKey)
    (occurrences : List (Nat × Term)) :
    (refineUncertainFrontier path prefixPath key prefixKey occurrences).filter
      (fun occurrence => by
        classical
        exact decide (∃ queryEnvironment rowEnvironment,
          subst queryEnvironment query = subst rowEnvironment occurrence.2)) =
    occurrences.filter (fun occurrence => by
      classical
      exact decide (∃ queryEnvironment rowEnvironment,
        subst queryEnvironment query = subst rowEnvironment occurrence.2)) := by
  classical
  rw [refineUncertainFrontier, List.filter_filter]
  apply List.filter_congr
  intro occurrence _
  by_cases unifier : ∃ queryEnvironment rowEnvironment,
      subst queryEnvironment query = subst rowEnvironment occurrence.2
  · obtain ⟨queryEnvironment, rowEnvironment, equal⟩ := unifier
    have accepted := separate_unifier_not_refuted queryEnvironment rowEnvironment
      query occurrence.2 path key queryKey equal
    have compatible := separate_unifier_prefix_compatible queryEnvironment rowEnvironment
      query occurrence.2 prefixPath prefixKey queryPrefix equal
    cases projection : project occurrence.2 path <;>
      simp_all [accepts]
  · simp [unifier]

theorem uncertain_refinement_controls :
    refineUncertainFrontier [2] [0] 7 9
      [(0, .node [.key 8, .key 1, .key 7]),
       (1, .node [.key 8, .var 2, .var 2]),
       (2, .node [.key 9, .key 1, .var 2]),
       (3, .node [.key 9, .key 1, .var 2]), (4, .var 0)] =
      [(0, .node [.key 8, .key 1, .key 7]),
       (2, .node [.key 9, .key 1, .var 2]),
       (3, .node [.key 9, .key 1, .var 2]), (4, .var 0)] := by
  simp [refineUncertainFrontier, accepts, prefixCompatible, project]

end Mettapedia.Machines.Cursor.TermPathPostingRefinement
