import Mettapedia.Machines.ContextualCarrierSupport
import Mettapedia.Machines.ConstraintPropagation

/-!
# Reachable context for conditional returns

A conditional result has two roots: its value and its pending check. Projecting
only the value's variables can change the check. The finite Horn worklist closes
both supports under the current binding store. Restricting to that computed
context preserves every finite substitution derivation of either root, in both
directions. Unreachable cycles do not require an acyclicity premise.

This concerns logical substitution support. Native relocation, attributed
variables, ownership and mutable-store synchronization require separate checks.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ConditionalContextProjection

open ContextualCarrierSupport ConstraintPropagation

variable {Cell : Type} [DecidableEq Cell] [Fintype Cell]

def rules (store : Store Cell) (cell : Cell) : HornRule Cell :=
  ⟨{cell}, (store cell).map support |>.getD ∅⟩

def retained (store : Store Cell) (select : Selector Cell)
    (value check : Term Cell) : Finset Cell :=
  solve (rules store) select (support value ∪ support check)

def restrict (store : Store Cell) (kept : Finset Cell) : Store Cell :=
  fun cell => if cell ∈ kept then store cell else none

theorem roots_retained (store : Store Cell) (select : Selector Cell)
    (value check : Term Cell) :
    support value ∪ support check ⊆ retained store select value check :=
  (solve_least_model (rules store) select _).1

theorem retained_closed (store : Store Cell) (select : Selector Cell)
    (value check : Term Cell) {cell : Cell} {image : Term Cell}
    (member : cell ∈ retained store select value check)
    (bound : store cell = some image) :
    support image ⊆ retained store select value check := by
  have closed := (solve_least_model (rules store) select
    (support value ∪ support check)).2.1 cell
  have enabled : (rules store cell).premises ⊆ retained store select value check := by
    simpa [rules] using member
  simpa [rules, bound, retained] using closed enabled

theorem retained_least (store : Store Cell) (select : Selector Cell)
    (value check : Term Cell) (upper : Finset Cell)
    (roots : support value ∪ support check ⊆ upper)
    (closed : ∀ cell ∈ upper, ∀ image, store cell = some image → support image ⊆ upper) :
    retained store select value check ⊆ upper := by
  apply (solve_least_model (rules store) select _).2.2 upper roots
  intro cell enabled
  have member : cell ∈ upper := by simpa [rules] using enabled
  cases bound : store cell with
  | none => simp [rules, bound]
  | some image => simpa [rules, bound] using closed cell member image bound

omit [Fintype Cell] in
theorem restrict_substitution (store : Store Cell) (kept : Finset Cell)
    (closed : ∀ cell ∈ kept, ∀ image, store cell = some image → support image ⊆ kept)
    {term result : Term Cell} (roots : support term ⊆ kept) :
    Substitutes (restrict store kept) term result ↔ Substitutes store term result := by
  constructor
  · intro observed
    induction observed with
    | literal flag => exact .literal flag
    | @unbound cell absent =>
        have member : cell ∈ kept := roots (by simp [support])
        exact .unbound (by simpa [restrict, member] using absent)
    | @binding cell image result bound _ ih =>
        have member : cell ∈ kept := roots (by simp [support])
        have original : store cell = some image := by
          simpa [restrict, member] using bound
        exact .binding original (ih (closed cell member image original))
    | pair _ _ leftIH rightIH =>
        exact .pair (leftIH (Finset.Subset.trans Finset.subset_union_left roots))
          (rightIH (Finset.Subset.trans Finset.subset_union_right roots))
  · intro observed
    induction observed with
    | literal flag => exact .literal flag
    | @unbound cell absent =>
        exact .unbound (by simp [restrict, absent])
    | @binding cell image result bound _ ih =>
        have member : cell ∈ kept := roots (by simp [support])
        exact .binding (by simp [restrict, member, bound])
          (ih (closed cell member image bound))
    | pair _ _ leftIH rightIH =>
        exact .pair (leftIH (Finset.Subset.trans Finset.subset_union_left roots))
          (rightIH (Finset.Subset.trans Finset.subset_union_right roots))

theorem conditional_roots_preserved (store : Store Cell) (select : Selector Cell)
    (value check valueImage checkImage : Term Cell) :
    let projected := restrict store (retained store select value check)
    (Substitutes projected value valueImage ↔ Substitutes store value valueImage) ∧
    (Substitutes projected check checkImage ↔ Substitutes store check checkImage) := by
  have roots := roots_retained store select value check
  have closed : ∀ cell ∈ retained store select value check, ∀ image,
      store cell = some image → support image ⊆ retained store select value check :=
    fun _ member _ bound => retained_closed store select value check member bound
  exact ⟨restrict_substitution store _ closed
      (Finset.Subset.trans Finset.subset_union_left roots),
    restrict_substitution store _ closed
      (Finset.Subset.trans Finset.subset_union_right roots)⟩

theorem retention_policy_independent (store : Store Cell)
    (left right : Selector Cell) (value check : Term Cell) :
    retained store left value check = retained store right value check :=
  solve_policy_independent (rules store) left right _

/-- Selecting a subvalue cannot require bindings outside the collection's
closed context, provided the same pending check travels with the selection. -/
theorem selected_value_support (store : Store Cell) (select : Selector Cell)
    (collection value check : Term Cell) (selected : support value ⊆ support collection) :
    retained store select value check ⊆ retained store select collection check := by
  apply retained_least store select value check _
  · exact (Finset.union_subset_union_left selected).trans
      (roots_retained store select collection check)
  · intro cell member image bound
    exact retained_closed store select collection check member bound

namespace Controls

def chain : Store (Fin 3) := fun cell =>
  if cell = 0 then some (.var 1)
  else if cell = 1 then some (.literal true)
  else some (.var 2)

theorem transitive_check_reads :
    Substitutes chain (.var 0) (.literal true) :=
  .binding (cell := 0) (image := .var 1) (by simp [chain])
    (.binding (cell := 1) (image := .literal true) (by simp [chain]) (.literal true))

theorem value_only_projection_changes_check :
    ¬ Substitutes (restrict chain (support (.literal false)))
      (.var 0) (.literal true) := by
  intro observed
  cases observed with
  | binding bound _ => simp [restrict, support] at bound

theorem unreachable_cycle_is_discarded (select : Selector (Fin 3)) :
    retained chain select (.literal false) (.var 0) = {0, 1} := by
  apply Finset.Subset.antisymm
  · apply retained_least chain select _ _ {0, 1}
    · simp [support]
    · intro cell member image bound
      simp only [Finset.mem_insert, Finset.mem_singleton] at member
      rcases member with rfl | rfl
      · simp [chain] at bound
        subst image
        simp [support]
      · simp [chain] at bound
        subst image
        simp [support]
  · have seed : (0 : Fin 3) ∈ retained chain select (.literal false) (.var 0) :=
      roots_retained chain select _ _ (by simp [support])
    have next := retained_closed chain select (.literal false) (.var 0) seed
      (show chain 0 = some (.var 1) by simp [chain])
    simp only [support, Finset.singleton_subset_iff] at next
    simp [Finset.insert_subset_iff, seed, next]

end Controls
end Mettapedia.Machines.ConditionalContextProjection

#print axioms Mettapedia.Machines.ConditionalContextProjection.roots_retained
#print axioms Mettapedia.Machines.ConditionalContextProjection.retained_closed
#print axioms Mettapedia.Machines.ConditionalContextProjection.retained_least
#print axioms Mettapedia.Machines.ConditionalContextProjection.restrict_substitution
#print axioms Mettapedia.Machines.ConditionalContextProjection.conditional_roots_preserved
#print axioms Mettapedia.Machines.ConditionalContextProjection.retention_policy_independent
#print axioms Mettapedia.Machines.ConditionalContextProjection.selected_value_support
#print axioms Mettapedia.Machines.ConditionalContextProjection.Controls.transitive_check_reads
#print axioms Mettapedia.Machines.ConditionalContextProjection.Controls.value_only_projection_changes_check
#print axioms Mettapedia.Machines.ConditionalContextProjection.Controls.unreachable_cycle_is_discarded
