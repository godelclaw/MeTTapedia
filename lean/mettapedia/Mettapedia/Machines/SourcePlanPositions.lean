import Mettapedia.Machines.AdditiveTreeFold
import Mettapedia.Machines.SourceAccounting

/-!
# Occurrence numbering before plan normalization

The elaborated plan is an occurrence tree, even when equal syntax shares
storage. The independent reference flattens that tree recursively and then
numbers its entries. The native loop instead pops one pending occurrence,
checks the word limit, assigns the next position and pushes its children.

This joins plan traversal to SourceAccounting's retained-position laws.
It does not equate preorder with runtime execution order. Call revisits,
dynamic scheduling, source-to-plan classification and C pointer storage
retain separate correspondence obligations. Failed native drafts must remain
unpublished, since the C traversal can have assigned an earlier prefix.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SourcePlanPositions

open AdditiveTreeFold

variable {Metadata : Type}

mutual
  def flatten : AdditiveTreeFold.Tree Metadata → List (Metadata × Nat)
    | .node metadata debit children => (metadata, debit) :: flattenForest children
  termination_by tree => sizeOf tree

  def flattenForest : List (AdditiveTreeFold.Tree Metadata) → List (Metadata × Nat)
    | [] => []
    | tree :: rest => flatten tree ++ flattenForest rest
  termination_by trees => sizeOf trees
end

@[simp] theorem flattenForest_append (first later : List (AdditiveTreeFold.Tree Metadata)) :
    flattenForest (first ++ later) = flattenForest first ++ flattenForest later := by
  induction first with
  | nil => simp [flattenForest]
  | cons tree rest ih => simp [flattenForest, ih, List.append_assoc]

/-- Work is newest-first; reverse physical pushes put the first child here. -/
def assign (maximum last : Nat) : List (AdditiveTreeFold.Tree Metadata) → Option (List (Nat × (Metadata × Nat)))
  | [] => some []
  | .node metadata debit children :: rest =>
      if last < maximum then
        (assign maximum (last + 1) (children ++ rest)).map
          ((last + 1, (metadata, debit)) :: ·)
      else none
termination_by work => forestNodes work
decreasing_by simp [forestNodes, nodes]

/-- Recursive flattening and native stack assignment agree, including exact
word-limit refusal. Equal metadata never collapses distinct occurrences. -/
theorem assignment_refines (maximum last : Nat) (work : List (AdditiveTreeFold.Tree Metadata))
    (inRange : last ≤ maximum) :
    assign maximum last work =
      if last + forestNodes work ≤ maximum then
        some (SourceAccounting.numberFrom (last + 1) (flattenForest work))
      else none := by
  fun_induction assign maximum last work <;>
    simp_all [flatten, flattenForest, forestNodes, nodes, SourceAccounting.numberFrom]
  all_goals first | omega | (split <;> simp_all <;> omega)

theorem assigned_positions (maximum last : Nat) (work : List (AdditiveTreeFold.Tree Metadata))
    (entries : List (Nat × (Metadata × Nat)))
    (inRange : last ≤ maximum)
    (assigned : assign maximum last work = some entries) :
    entries.map Prod.fst = List.range' (last + 1) (flattenForest work).length := by
  rw [assignment_refines maximum last work inRange] at assigned
  split at assigned
  · cases Option.some.inj assigned
    exact SourceAccounting.numbered_positions _ _
  · simp at assigned

theorem assigned_positions_distinct (maximum last : Nat) (work : List (AdditiveTreeFold.Tree Metadata))
    (entries : List (Nat × (Metadata × Nat)))
    (inRange : last ≤ maximum)
    (assigned : assign maximum last work = some entries) :
    (entries.map Prod.fst).Nodup := by
  rw [assigned_positions maximum last work entries inRange assigned]
  exact List.nodup_range'

/-- Filtering the numbered inventory retains the source coordinates, with
gaps. Normalization cannot renumber surviving work by its new list position. -/
theorem retained_positions (maximum last : Nat) (work : List (AdditiveTreeFold.Tree Metadata))
    (entries : List (Nat × (Metadata × Nat)))
    (inRange : last ≤ maximum)
    (assigned : assign maximum last work = some entries)
    (keep : Nat × (Metadata × Nat) → Bool) :
    ((entries.filter keep).map Prod.fst).Sublist
      (List.range' (last + 1) (flattenForest work).length) := by
  rw [← assigned_positions maximum last work entries inRange assigned]
  exact List.Sublist.map Prod.fst List.filter_sublist

theorem numbered_payload (position : Nat) (entries : List (Metadata × Nat)) :
    (SourceAccounting.numberFrom position entries).map Prod.snd = entries := by
  induction entries generalizing position with
  | nil => rfl
  | cons first rest ih => simp [SourceAccounting.numberFrom, ih]

theorem debit_payload_retained (maximum last : Nat) (work : List (AdditiveTreeFold.Tree Metadata))
    (entries : List (Nat × (Metadata × Nat)))
    (inRange : last ≤ maximum)
    (assigned : assign maximum last work = some entries) :
    entries.map Prod.snd = flattenForest work := by
  rw [assignment_refines maximum last work inRange] at assigned
  split at assigned
  · cases Option.some.inj assigned
    exact numbered_payload _ _
  · simp at assigned

namespace Controls

def repeated : List (AdditiveTreeFold.Tree Nat) :=
  [.node 10 1 [.node 20 0 [], .node 20 3 []]]

theorem repeated_payloads_have_distinct_positions :
    assign 100 0 repeated = some [(1, 10, 1), (2, 20, 0), (3, 20, 3)] := by
  decide +kernel

theorem node_limit_refuses_complete_draft : assign 2 0 repeated = none := by
  decide +kernel

theorem reverse_child_push_changes_occurrences :
    assign 100 0 [.node 10 1 [.node 20 3 [], .node 20 0 []]] ≠
      assign 100 0 repeated := by
  decide +kernel

theorem pruning_then_renumbering_changes_receipt :
    ((SourceAccounting.numberFrom 1 (flattenForest repeated)).filter
      (fun entry => entry.1 != 2)).map Prod.fst = [1, 3] ∧
    (SourceAccounting.numberFrom 1 [(10, 1), (20, 3)]).map Prod.fst = [1, 2] := by
  decide +kernel

end Controls
end Mettapedia.Machines.SourcePlanPositions

#print axioms Mettapedia.Machines.SourcePlanPositions.assignment_refines
#print axioms Mettapedia.Machines.SourcePlanPositions.assigned_positions
#print axioms Mettapedia.Machines.SourcePlanPositions.assigned_positions_distinct
#print axioms Mettapedia.Machines.SourcePlanPositions.retained_positions
#print axioms Mettapedia.Machines.SourcePlanPositions.numbered_payload
#print axioms Mettapedia.Machines.SourcePlanPositions.debit_payload_retained
#print axioms Mettapedia.Machines.SourcePlanPositions.Controls.repeated_payloads_have_distinct_positions
#print axioms Mettapedia.Machines.SourcePlanPositions.Controls.node_limit_refuses_complete_draft
#print axioms Mettapedia.Machines.SourcePlanPositions.Controls.reverse_child_push_changes_occurrences
#print axioms Mettapedia.Machines.SourcePlanPositions.Controls.pruning_then_renumbering_changes_receipt
