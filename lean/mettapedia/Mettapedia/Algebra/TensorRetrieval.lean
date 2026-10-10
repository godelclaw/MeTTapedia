import Std

/-!
# Failure-preserving validation of finite retrieval candidates

Projecting failures once and returning the original successful candidate view
has the same outcome as recursive validation that rebuilds that view. Candidate
occurrences and their order are retained. Validation precedes selection, even
when zero results are requested. The visit count is an abstract model; actual
interpreter allocation and running time require independent measurements.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.TensorRetrieval

variable {Error Value : Type}

abbrev Candidate (Error Value : Type) := Sum Error Value

def failures : List (Candidate Error Value) → List Error
  | [] => []
  | .inl error :: rest => error :: failures rest
  | .inr _ :: rest => failures rest

/-- The original, recursive rebuilding policy. -/
def rebuildValidate : List (Candidate Error Value) → Except Error (List (Candidate Error Value))
  | [] => .ok []
  | .inl error :: _ => .error error
  | .inr value :: rest =>
      match rebuildValidate rest with
      | .error error => .error error
      | .ok valid => .ok (.inr value :: valid)

/-- A complete failure projection followed by reuse of the original view. -/
def validate (candidates : List (Candidate Error Value)) :
    Except Error (List (Candidate Error Value)) :=
  match failures candidates with
  | [] => .ok candidates
  | error :: _ => .error error

theorem validate_nil : validate ([] : List (Candidate Error Value)) = .ok [] := rfl

theorem validate_failure (error : Error) (rest : List (Candidate Error Value)) :
    validate (.inl error :: rest) = .error error := rfl

theorem validate_success (value : Value) (rest : List (Candidate Error Value)) :
    validate (.inr value :: rest) =
      match validate rest with
      | .error error => .error error
      | .ok valid => .ok (.inr value :: valid) := by
  simp only [validate, failures]
  cases failures rest <;> rfl

theorem validate_eq_rebuildValidate (candidates : List (Candidate Error Value)) :
    validate candidates = rebuildValidate candidates := by
  induction candidates with
  | nil => rfl
  | cons candidate rest ih =>
    cases candidate with
    | inl error => rfl
    | inr value => rw [validate_success, ih]; rfl

theorem successful_view_is_original (candidates valid : List (Candidate Error Value))
    (accepted : validate candidates = .ok valid) : valid = candidates := by
  cases projection : failures candidates with
  | nil =>
    have same : candidates = valid := by simpa [validate, projection] using accepted
    exact same.symm
  | cons error rest => simp [validate, projection] at accepted

theorem validate_ok_iff (candidates : List (Candidate Error Value)) :
    validate candidates = .ok candidates ↔ failures candidates = [] := by
  simp only [validate]
  cases failures candidates <;> simp

theorem failures_append (left right : List (Candidate Error Value)) :
    failures (left ++ right) = failures left ++ failures right := by
  induction left with
  | nil => rfl
  | cons candidate rest ih =>
    cases candidate <;> simp [failures, ih]

theorem failure_after_successful_prefix (initial rest : List (Candidate Error Value))
    (error : Error) (clean : failures initial = []) :
    validate (initial ++ .inl error :: rest) = .error error := by
  simp [validate, failures_append, clean, failures]

theorem later_failures_do_not_replace_first (error later : Error)
    (middle rest : List (Candidate Error Value)) :
    validate (.inl error :: (middle ++ .inl later :: rest)) = .error error := rfl

theorem successful_occurrences_preserved (values : List Value) :
    validate (values.map Sum.inr : List (Candidate Error Value)) = .ok (values.map Sum.inr) := by
  apply (validate_ok_iff _).mpr
  induction values with
  | nil => rfl
  | cons value rest ih => simpa [failures] using ih

/-- The selector is intentionally abstract: validation constrains every one. -/
def selectChecked (selector : Nat → List (Candidate Error Value) → List Value)
    (requested : Nat) (candidates : List (Candidate Error Value)) : Except Error (List Value) :=
  match validate candidates with
  | .error error => .error error
  | .ok valid => .ok (selector requested valid)

theorem failed_selection (selector : Nat → List (Candidate Error Value) → List Value)
    (requested : Nat) (candidates : List (Candidate Error Value)) (error : Error)
    (failed : validate candidates = .error error) :
    selectChecked selector requested candidates = .error error := by
  simp [selectChecked, failed]

theorem zero_requested_does_not_hide_failure
    (selector : Nat → List (Candidate Error Value) → List Value)
    (error : Error) (rest : List (Candidate Error Value)) :
    selectChecked selector 0 (.inl error :: rest) = .error error := rfl

theorem clean_selection (selector : Nat → List (Candidate Error Value) → List Value)
    (requested : Nat) (candidates : List (Candidate Error Value))
    (clean : failures candidates = []) :
    selectChecked selector requested candidates = .ok (selector requested candidates) := by
  simp [selectChecked, validate, clean]

def scanVisits : List (Candidate Error Value) → Nat
  | [] => 0
  | _ :: rest => 1 + scanVisits rest

theorem scanVisits_eq_length (candidates : List (Candidate Error Value)) :
    scanVisits candidates = candidates.length := by
  induction candidates with
  | nil => rfl
  | cons candidate rest ih => simp [scanVisits, ih, Nat.add_comm]

theorem scanVisits_append (left right : List (Candidate Error Value)) :
    scanVisits (left ++ right) = scanVisits left + scanVisits right := by
  simp [scanVisits_eq_length]

theorem failures_length_le (candidates : List (Candidate Error Value)) :
    (failures candidates).length ≤ candidates.length := by
  induction candidates with
  | nil => exact Nat.le_refl 0
  | cons candidate rest ih =>
    cases candidate <;> simp only [failures, List.length_cons]
    · exact Nat.succ_le_succ ih
    · exact Nat.le_trans ih (Nat.le_succ _)

theorem filtering_successes_can_hide_failure :
    validate ([.inr 7, .inl 9] : List (Candidate Nat Nat)) ≠ .ok [.inr 7] := by
  simp [validate, failures]

theorem boundary_failure_survives_zero_selection :
    selectChecked (fun _ _ => []) 0 ([.inr 7, .inl 9] : List (Candidate Nat Nat)) = .error 9 := by
  rfl

end Mettapedia.Algebra.TensorRetrieval
