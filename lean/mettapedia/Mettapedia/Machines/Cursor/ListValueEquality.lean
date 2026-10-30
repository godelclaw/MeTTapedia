import Mettapedia.Machines.Cursor.ListCells

/-!
# Value equality observes logical list representations

The reference compares the existing ListCells readings. The implementation
normalizes closed cells and then compares their syntax structurally. These
independent computations agree on the closed list/data fragment, including
cells nested inside records. Variable identities remain distinct.

Opaque quote/closure policy, numerical leaf equality and native ownership are
separate boundaries; this model does not reinterpret syntax beneath them or
claim verification of native C execution.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ListValueEquality

open ListCells ListCells.Tm

mutual
  def rawEq : Tm → Tm → Bool
    | .sym first, .sym second => decide (first = second)
    | .var first, .var second => decide (first = second)
    | .tag, .tag => true
    | .expr first, .expr second => rawListEq first second
    | _, _ => false

  def rawListEq : List Tm → List Tm → Bool
    | [], [] => true
    | first :: rest, second :: later => rawEq first second && rawListEq rest later
    | _, _ => false
end

private theorem rawListEq_iff (xs : List Tm)
    (children : ∀ x ∈ xs, ∀ y, rawEq x y = true ↔ x = y) :
    ∀ ys, rawListEq xs ys = true ↔ xs = ys := by
  induction xs with
  | nil => intro ys; cases ys <;> simp [rawListEq]
  | cons first rest ih =>
      intro ys
      cases ys with
      | nil => simp [rawListEq]
      | cons second later =>
          have head := children first (List.mem_cons_self ..) second
          have tail := ih (fun x hx => children x (List.mem_cons_of_mem _ hx)) later
          simpa only [rawListEq, Bool.and_eq_true, List.cons.injEq] using and_congr head tail

theorem rawEq_iff (first second : Tm) : rawEq first second = true ↔ first = second := by
  induction first using Tm.induction generalizing second with
  | sym name => cases second <;> simp [rawEq]
  | var index => cases second <;> simp [rawEq]
  | tag => cases second <;> simp [rawEq]
  | expr children ih =>
      cases second with
      | sym name => simp [rawEq]
      | var index => simp [rawEq]
      | tag => simp [rawEq]
      | expr later => simpa only [rawEq, Tm.expr.injEq] using rawListEq_iff children ih later

def normalizedEq (first second : Tm) : Bool := rawEq first.flat second.flat

def referenceEq (first second : Tm) : Option Bool :=
  match first.denote, second.denote with
  | some left, some right => some (decide (left = right))
  | _, _ => none

theorem flattened_equality_exact {first second : Tm} (left : Closed first) (right : Closed second) :
    first.flat = second.flat ↔ first.denote = second.denote := by
  constructor
  · intro same
    have observed := congrArg Tm.denote same
    simpa only [denote_flat] using observed
  · intro same
    apply TagFree.denote_injective left.tagFree_flat right.tagFree_flat
    simpa only [denote_flat] using same

theorem normalized_equality_exact {first second : Tm} (left : Closed first) (right : Closed second) :
    normalizedEq first second = true ↔ first.denote = second.denote := by
  rw [normalizedEq, rawEq_iff, flattened_equality_exact left right]

private theorem closed_has_reading {term : Tm} (closed : Closed term) :
    ∃ reading, term.denote = some reading := by
  obtain ⟨reading, found⟩ := closed.tagFree_flat.wellFormed
  exact ⟨reading, by rwa [denote_flat] at found⟩

theorem normalized_matches_reference {first second : Tm} (left : Closed first) (right : Closed second) :
    referenceEq first second = some (normalizedEq first second) := by
  obtain ⟨a, firstReading⟩ := closed_has_reading left
  obtain ⟨b, secondReading⟩ := closed_has_reading right
  simp only [referenceEq, firstReading, secondReading]
  apply congrArg some
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, normalized_equality_exact left right]
  simp only [firstReading, secondReading, Option.some.injEq]

theorem representation_invariant {first second first' second' : Tm}
    (left : Closed first) (right : Closed second) (left' : Closed first') (right' : Closed second')
    (firstReading : first.denote = first'.denote) (secondReading : second.denote = second'.denote) :
    normalizedEq first second = normalizedEq first' second' := by
  apply Bool.eq_iff_iff.mpr
  rw [normalized_equality_exact left right, normalized_equality_exact left' right', firstReading, secondReading]

end Mettapedia.Machines.Cursor.ListValueEquality
