import Mettapedia.Languages.FiniteChoice.ScopedObservation

/-!
# Producer and interface correspondence for scoped observations

Finite scans inspect actual rows. Negative grades keep exact point premises,
checked at their subject of use. Parser consumption and type-level emptiness
remain separate from result cardinality. No runtime representation is assumed.
-/
set_option autoImplicit false
namespace Mettapedia.Languages.FiniteChoice.ScopedObservation

/-- Actual row inspection; each position is a distinct occurrence. -/
def scanWork {Key Value : Type} [DecidableEq Key] (query : Key) :
    Nat → List (Key × Value) → List (Work Value)
  | _, [] => []
  | ordinal, (key, value) :: rest =>
      (if key = query then .emit (.witness [ordinal] value) else .skip) ::
        scanWork query (ordinal + 1) rest

theorem scanWork_length {Key Value : Type} [DecidableEq Key] (query : Key)
    (ordinal : Nat) (rows : List (Key × Value)) :
    (scanWork query ordinal rows).length = rows.length := by
  induction rows generalizing ordinal with
  | nil => rfl
  | cons row rest ih => simp [scanWork, ih]

theorem scanWork_empty_iff {Key Value : Type} [DecidableEq Key] (query : Key)
    (ordinal : Nat) (rows : List (Key × Value)) :
    (scanWork query ordinal rows).flatMap Work.output = [] ↔
      ∀ row ∈ rows, row.1 ≠ query := by
  induction rows generalizing ordinal with
  | nil => simp [scanWork]
  | cons row rest ih =>
    obtain ⟨key, value⟩ := row
    by_cases h : key = query <;> simp [scanWork, h, Work.output, ih]

/-- Completion plus absence comes from all consumed candidates. -/
theorem scan_completed_absence {Key Value : Type} [DecidableEq Key] (query : Key)
    (rows : List (Key × Value)) (fuel : Nat)
    (h : (observe (run fuel
      (⟨(rows, query), [], scanWork query 0 rows⟩ : Cursor _ Value))).Empty) :
    lookup query rows = none := by
  apply (lookup_none_iff query rows).mpr
  apply (scanWork_empty_iff query 0 rows).mp
  simpa [Cursor.meaning] using finite_run_empty_sound fuel _ h

theorem scan_coverage_finishes {Key Value : Type} [DecidableEq Key] (query : Key)
    (rows : List (Key × Value)) :
    (run rows.length
      (⟨(rows, query), [], scanWork query 0 rows⟩ : Cursor _ Value)).remaining = [] := by
  simpa [scanWork_length] using all_work_finishes (rows, query) [] (scanWork query 0 rows)

def GradeHolds {Key Value : Type} [DecidableEq Key]
    (rows : List (Key × Value)) (premises : List Key) : Prop :=
  ∀ key ∈ premises, lookup key rows = none

def checkGrade {Key Value : Type} [DecidableEq Key]
    (rows : List (Key × Value)) (premises : List Key) : Bool :=
  premises.all fun key => (lookup key rows).isNone

theorem checkGrade_sound {Key Value : Type} [DecidableEq Key]
    (rows : List (Key × Value)) (premises : List Key)
    (checked : checkGrade rows premises = true) : GradeHolds rows premises := by
  simpa [checkGrade, GradeHolds, List.all_eq_true] using checked

theorem grade_conjunction {Key Value : Type} [DecidableEq Key]
    (rows : List (Key × Value)) (left right : List Key) :
    GradeHolds rows (left ++ right) ↔ GradeHolds rows left ∧ GradeHolds rows right := by
  simp [GradeHolds, List.mem_append, or_imp, forall_and]

theorem grade_requires_subject_revalidation :
    GradeHolds [(1, "other")] [2] ∧
      ¬ GradeHolds [(2, "new"), (1, "other")] [2] := by
  simp [GradeHolds, lookup]

structure ParseOccurrence (Value : Type) where
  consumed : Nat
  value : Value

theorem epsilon_is_not_no_parse {Value : Type} (value : Value) :
    ([⟨0, value⟩] : List (ParseOccurrence Value)) ≠ [] := List.cons_ne_nil _ _

theorem empty_type_eliminates {claim : Prop} (impossible : PEmpty) : claim :=
  impossible.elim

/-- A report spelling alone cannot discharge a negative premise. -/
theorem unscoped_tag_cannot_establish_grade :
    ¬ (∀ rows : List (Nat × Nat), GradeHolds rows [2]) := by
  intro claimed
  have bad := claimed [(2, 7)]
  simp [GradeHolds, lookup] at bad

#print axioms scan_completed_absence
#print axioms scan_coverage_finishes
#print axioms checkGrade_sound
#print axioms grade_conjunction
#print axioms grade_requires_subject_revalidation
#print axioms empty_type_eliminates
end Mettapedia.Languages.FiniteChoice.ScopedObservation
