import Mathlib.Data.List.Sort

/-! # Stable bounded selection with integer scores

Earlier source entries are eligible. Sorting retains every occurrence, puts
higher scores first, and preserves input order at equal scores. Truncation
then enforces the requested result budget. Scores are integers; this module
does not identify a floating-point computation with real arithmetic.
-/

set_option autoImplicit false

namespace List.StableTopK

variable {α : Type*}

def insert (score : α → Int) (value : α) : List α → List α
  | [] => [value]
  | first :: rest =>
      if score value ≥ score first then value :: first :: rest
      else first :: insert score value rest

def sort (score : α → Int) : List α → List α
  | [] => []
  | first :: rest => insert score first (sort score rest)

/-- Keep only the requested prefix after each insertion. -/
def bounded (score : α → Int) : Nat → List α → List α
  | 0, _ => []
  | _ + 1, [] => []
  | budget + 1, first :: rest =>
      (insert score first (bounded score (budget + 1) rest)).take (budget + 1)

theorem take_insert_take (score : α → Int) (value : α) (budget : Nat) (values : List α) :
    (insert score value (values.take budget)).take budget =
      (insert score value values).take budget := by
  induction budget generalizing values with
  | zero => simp
  | succ budget ih =>
    cases values with
    | nil => simp [insert]
    | cons first rest =>
      by_cases order : score value ≥ score first
      · simp [List.take_succ_cons, insert, order]
        cases budget <;> simp [List.take_succ_cons, List.take_take]
      · simp [List.take_succ_cons, insert, order, ih]

theorem bounded_eq_take_sort (score : α → Int) (budget : Nat) (values : List α) :
    bounded score budget values = (sort score values).take budget := by
  cases budget with
  | zero => simp [bounded]
  | succ budget =>
    induction values with
    | nil => simp [bounded, sort]
    | cons first rest ih => simp [bounded, sort, ih, take_insert_take]

theorem length_bounded_le (score : α → Int) (budget : Nat) (values : List α) :
    (bounded score budget values).length ≤ budget := by
  rw [bounded_eq_take_sort, List.length_take]
  exact Nat.min_le_left _ _

def eligible (index : α → Nat) (before : Nat) (values : List α) : List α :=
  values.filter (fun value => decide (index value < before))

def select (score : α → Int) (index : α → Nat) (before budget : Nat)
    (values : List α) : List α :=
  (sort score (eligible index before values)).take budget

theorem insert_eq_orderedInsert (score : α → Int) (value : α) (values : List α) :
    insert score value values = values.orderedInsert (fun x y => score x ≥ score y) value := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp only [insert, List.orderedInsert_cons, ih]

theorem sort_eq_insertionSort (score : α → Int) (values : List α) :
    sort score values = values.insertionSort (fun x y => score x ≥ score y) := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp only [sort, List.insertionSort_cons, insert_eq_orderedInsert, ih]

theorem sort_perm (score : α → Int) (values : List α) :
    sort score values ~ values := by
  rw [sort_eq_insertionSort]
  exact List.perm_insertionSort _ _

theorem sort_ordered (score : α → Int) (values : List α) :
    (sort score values).Pairwise (fun x y => score x ≥ score y) := by
  let : Std.Total (fun x y : α => score x ≥ score y) := ⟨fun x y => le_total _ _⟩
  let : IsTrans α (fun x y => score x ≥ score y) := ⟨fun _ _ _ h₁ h₂ => le_trans h₂ h₁⟩
  rw [sort_eq_insertionSort]
  exact List.pairwise_insertionSort _ _

theorem insert_filter_score (score : α → Int) (value : α) (values : List α) (key : Int) :
    (insert score value values).filter (fun x => decide (score x = key)) =
      if score value = key then value :: values.filter (fun x => decide (score x = key))
      else values.filter (fun x => decide (score x = key)) := by
  induction values with
  | nil => simp [insert, List.filter_cons]
  | cons first rest ih =>
    by_cases order : score value ≥ score first
    · simp only [insert, if_pos order, List.filter_cons, decide_eq_true_eq]
    · simp only [insert, if_neg order, List.filter_cons, ih, decide_eq_true_eq]
      by_cases equal : score value = key
      · have different : score first ≠ key := by
          intro same
          exact order (by simp [equal, same])
        simp [equal, different]
      · simp [equal]

/-- Stability preserves the entire list of equal-score occurrences, not just
their set or their number. -/
theorem sort_filter_score (score : α → Int) (values : List α) (key : Int) :
    (sort score values).filter (fun x => decide (score x = key)) =
      values.filter (fun x => decide (score x = key)) := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp [sort, insert_filter_score, ih, List.filter_cons]

theorem length_select (score : α → Int) (index : α → Nat) (before budget : Nat)
    (values : List α) :
    (select score index before budget values).length =
      min budget (eligible index before values).length := by
  simp only [select, List.length_take, (sort_perm score _).length_eq]

theorem length_select_le (score : α → Int) (index : α → Nat) (before budget : Nat)
    (values : List α) : (select score index before budget values).length ≤ budget := by
  rw [length_select]
  exact Nat.min_le_left _ _

theorem selected_source {score : α → Int} {index : α → Nat} {before budget : Nat}
    {values : List α} {value : α} (member : value ∈ select score index before budget values) :
    value ∈ values ∧ index value < before := by
  have h := (sort_perm score _).mem_iff.mp (List.mem_of_mem_take member)
  simpa [eligible] using h

theorem selected_ordered (score : α → Int) (index : α → Nat) (before budget : Nat)
    (values : List α) :
    (select score index before budget values).Pairwise (fun x y => score x ≥ score y) :=
  (sort_ordered score _).sublist (List.take_sublist _ _)

/-- No omitted eligible occurrence outranks a returned one. -/
theorem selection_boundary (score : α → Int) (index : α → Nat) (before budget : Nat)
    (values : List α) :
    ∀ x ∈ select score index before budget values,
      ∀ y ∈ (sort score (eligible index before values)).drop budget, score x ≥ score y := by
  have ordered := sort_ordered score (eligible index before values)
  rw [← List.take_append_drop budget (sort score (eligible index before values)),
    List.pairwise_append] at ordered
  exact ordered.2.2

theorem selected_stable (score : α → Int) (index : α → Nat) (before budget : Nat)
    (values : List α) (key : Int) :
    (select score index before budget values).filter (fun x => decide (score x = key)) <+
      (eligible index before values).filter (fun x => decide (score x = key)) := by
  rw [← sort_filter_score score (eligible index before values) key]
  exact (List.take_sublist budget _).filter _

end List.StableTopK
