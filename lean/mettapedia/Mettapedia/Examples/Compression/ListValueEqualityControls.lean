import Mettapedia.Machines.Cursor.ListValueEquality

/-! Representation and identity controls for equality inside data records. -/

set_option autoImplicit false

namespace Mettapedia.Examples.Compression.ListValueEqualityControls

open Machines.Cursor.ListCells Machines.Cursor.ListCells.Tm
open Machines.Cursor.ListValueEquality

private def cellRecord : Tm := .expr [.sym 7, .cell (.sym 1) (.expr [.sym 2])]
private def flatRecord : Tm := .expr [.sym 7, .expr [.sym 1, .sym 2]]

theorem nested_carrier_counterexample : rawEq cellRecord flatRecord = false ∧
    referenceEq cellRecord flatRecord = some true ∧ normalizedEq cellRecord flatRecord = true := by decide

theorem record_tag_is_preserved :
    normalizedEq cellRecord (.expr [.sym 8, .expr [.sym 1, .sym 2]]) = false := by decide

theorem order_is_not_bag_equality :
    normalizedEq cellRecord (.expr [.sym 7, .expr [.sym 2, .sym 1]]) = false := by decide

theorem duplicate_occurrences_are_not_deduplicated :
    normalizedEq (.cell (.sym 1) (.expr [.sym 1])) (.expr [.sym 1]) = false := by decide

theorem variable_identity_is_not_unification :
    normalizedEq (.cell (.var 0) (.expr [])) (.expr [.var 1]) = false ∧
      normalizedEq (.cell (.var 0) (.expr [])) (.expr [.var 0]) = true := by decide

theorem invalid_tag_needs_admission :
    rawEq .tag .tag = true ∧ referenceEq .tag .tag = none := by decide

theorem nested_record_is_closed : Closed cellRecord := by
  apply Closed.flat _ (by decide)
  intro term present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl
  · exact .sym 7
  · apply Closed.cell (.sym 1)
    apply Closed.flat _ (by decide)
    intro value member
    cases List.mem_singleton.mp member
    exact .sym 2

theorem flat_record_is_closed : Closed flatRecord := by
  apply Closed.flat _ (by decide)
  intro term present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl
  · exact .sym 7
  · apply Closed.flat _ (by decide)
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .sym 1
    · exact .sym 2

theorem record_reference_instance :
    referenceEq cellRecord flatRecord = some (normalizedEq cellRecord flatRecord) :=
  normalized_matches_reference nested_record_is_closed flat_record_is_closed

#print axioms rawEq_iff
#print axioms flattened_equality_exact
#print axioms normalized_equality_exact
#print axioms normalized_matches_reference
#print axioms representation_invariant
#print axioms nested_carrier_counterexample
#print axioms record_tag_is_preserved
#print axioms order_is_not_bag_equality
#print axioms duplicate_occurrences_are_not_deduplicated
#print axioms variable_identity_is_not_unification
#print axioms invalid_tag_needs_admission
#print axioms nested_record_is_closed
#print axioms flat_record_is_closed
#print axioms record_reference_instance

end Mettapedia.Examples.Compression.ListValueEqualityControls
