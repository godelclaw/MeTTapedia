import Mettapedia.Languages.MeTTa.PeTTa.ExplicitEvaluation

/-!
# Collapsing call-free runtime translations

Explicit evaluation classifies a term under the current program. A positive
certificate permits replacing its complete construction plan by one literal
instruction. This is stronger than merely remembering that evaluation once
finished: a later program can make an old data head callable.

These laws extend the finite occurrence compiler, preserving its complete
answer list. They do not establish native pointer lifetime, effects, or C
implementation adequacy. In particular, moving a certificate between storage
owners requires a separate proof that the represented term is unchanged.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.TranslationValueCertificates

open ExplicitEvaluation
open ValueOccurrences (Program choices choices_singletons)

/-- A decidable, compositional certificate for the code-evaluation boundary.
Opaque values are already values; every application must be inert and have
certified children. -/
def callFree (P : Program) : Term → Bool
  | .value _ => true
  | .application _ ts =>
      !P.isCall (Term.syntax.syntaxList ts) && list P ts
where
  list (P : Program) : List Term → Bool
    | [] => true
    | t :: ts => callFree P t && list P ts

theorem callFree_list_iff (P : Program) (ts : List Term) :
    callFree.list P ts = true ↔ ∀ t ∈ ts, callFree P t = true := by
  induction ts with
  | nil => simp [callFree.list]
  | cons t ts ih => simp [callFree.list, ih]

/-- A certified translation returns the original syntax exactly once. -/
theorem evaluate_callFree (P : Program) (t : Term)
    (certificate : callFree P t = true) :
    evaluate P .code t = [t.syntax] := by
  match t with
  | .value a => rfl
  | .application captured ts =>
    have parts : P.isCall (Term.syntax.syntaxList ts) = false ∧
        callFree.list P ts = true := by
      simpa [callFree] using certificate
    have children := list P ts
      (fun t ht => evaluate_callFree P t ((callFree_list_iff P ts).mp parts.2 t ht))
    simp [evaluate, childMode, children, choices_singletons,
      isCall, parts.1, Term.syntax]
termination_by sizeOf t
where
  list (P : Program) (ts : List Term)
      (ih : ∀ t ∈ ts, evaluate P .code t = [t.syntax]) :
      evaluate.evaluateList P .code ts =
        (Term.syntax.syntaxList ts).map (fun a => [a]) := by
    induction ts with
    | nil => rfl
    | cons t ts tail =>
      simp only [evaluate.evaluateList, Term.syntax.syntaxList, List.map_cons]
      rw [ih t (by simp), tail (fun t ht => ih t (by simp [ht]))]

/-- Only the certified branch drops the full construction plan. -/
def compileWithValues (P : Program) (t : Term) : Instruction :=
  if callFree P t then .literal t.syntax else compile P .code t

theorem execute_compileWithValues (P : Program) (t : Term) :
    execute P (compileWithValues P t) = evaluate P .code t := by
  by_cases h : callFree P t = true
  · simp [compileWithValues, h, execute, evaluate_callFree P t h]
  · simp [compileWithValues, h, execute_compile]

/-- Dropping callable heads cannot invalidate a positive certificate.
This does not require equality of answer functions: certified terms call none. -/
theorem callFree_mono (P Q : Program)
    (noNewCalls : ∀ args, Q.isCall args = true → P.isCall args = true)
    (t : Term) (certificate : callFree P t = true) : callFree Q t = true := by
  match t with
  | .value _ => rfl
  | .application _ ts =>
    have parts : P.isCall (Term.syntax.syntaxList ts) = false ∧
        callFree.list P ts = true := by
      simpa [callFree] using certificate
    have root : Q.isCall (Term.syntax.syntaxList ts) = false := by
      cases h : Q.isCall (Term.syntax.syntaxList ts) with
      | false => rfl
      | true => have bad := noNewCalls _ h; simp [parts.1] at bad
    have children : callFree.list Q ts = true :=
      (callFree_list_iff Q ts).mpr fun t ht =>
        callFree_mono P Q noNewCalls t ((callFree_list_iff P ts).mp parts.2 t ht)
    simp [callFree, root, children]
termination_by sizeOf t

theorem reuse_after_removing_calls (P Q : Program)
    (noNewCalls : ∀ args, Q.isCall args = true → P.isCall args = true)
    (t : Term) (certificate : callFree P t = true) :
    execute Q (.literal t.syntax) = evaluate Q .code t := by
  simpa [execute] using
    (evaluate_callFree Q t (callFree_mono P Q noNewCalls t certificate)).symm

namespace Examples

def before : Program where
  isCall _ := false
  answers _ := []

theorem earlier_data_has_certificate :
    callFree before ExplicitEvaluation.Examples.late = true := by decide

theorem new_definition_revokes_certificate :
    callFree ExplicitEvaluation.Examples.current
      ExplicitEvaluation.Examples.late = false := by decide

/-- An unchanged term and an earlier success do not license a cached value
after the program learns that its head is callable. Multiplicity changes too. -/
theorem stale_value_changes_answers :
    execute ExplicitEvaluation.Examples.current
        (.literal ExplicitEvaluation.Examples.late.syntax) ≠
      evaluate ExplicitEvaluation.Examples.current .code
        ExplicitEvaluation.Examples.late := by decide

end Examples
end Mettapedia.Languages.MeTTa.PeTTa.TranslationValueCertificates
