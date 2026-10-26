import Mettapedia.UniversalAlgebra.Instances.Monoid
import Mettapedia.UniversalAlgebra.BoundedTerm

/-!
# Ordered word semantics for monoid terms

Units contribute no variables and multiplication concatenates occurrences.
The resulting word retains order and multiplicity. Evaluating that word by
the free-monoid lift agrees with the independently defined term evaluator;
simultaneous substitution replaces each occurrence by its supplied word.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra.Monoid.Term

/-- The ordered variable-occurrence word of a monoid term. -/
def variableWord : Term signature → List Nat
  | .var index => [index]
  | .op .mul arguments =>
      variableWord (arguments ⟨0, by decide⟩) ++
        variableWord (arguments ⟨1, by decide⟩)
  | .op .one _arguments => []

@[simp] theorem variableWord_var (index : Nat) :
    variableWord (.var index : Term signature) = [index] := rfl

@[simp] theorem variableWord_one : variableWord one = [] := rfl

@[simp] theorem variableWord_mul (left right : Term signature) :
    variableWord (mul left right) = variableWord left ++ variableWord right := rfl

/-- A single ordered word realizes term evaluation in every Mathlib monoid. -/
theorem evaluate_eq_lift {Carrier : Type} [Monoid Carrier] (valuation : Nat → Carrier) :
    ∀ term : Term signature,
      term.evaluate (mathlibModel Carrier) valuation =
        FreeMonoid.lift valuation (FreeMonoid.ofList (variableWord term))
  | .var _ => by simp [variableWord]
  | .op .one _arguments => rfl
  | .op .mul arguments => by
      change (arguments ⟨0, by decide⟩).evaluate (mathlibModel Carrier) valuation *
          (arguments ⟨1, by decide⟩).evaluate (mathlibModel Carrier) valuation =
        FreeMonoid.lift valuation (FreeMonoid.ofList
          (variableWord (arguments ⟨0, by decide⟩) ++ variableWord (arguments ⟨1, by decide⟩)))
      rw [FreeMonoid.ofList_append, map_mul, evaluate_eq_lift valuation (arguments ⟨0, by decide⟩),
        evaluate_eq_lift valuation (arguments ⟨1, by decide⟩)]

/-- Evaluation in a free monoid substitutes valuation words for occurrences. -/
theorem toList_evaluate_freeMonoid {Generator : Type}
    (valuation : Nat → FreeMonoid Generator) (term : Term signature) :
    FreeMonoid.toList (term.evaluate (mathlibModel (FreeMonoid Generator)) valuation) =
      (variableWord term).flatMap (fun index => FreeMonoid.toList (valuation index)) := by
  simp only [evaluate_eq_lift, FreeMonoid.lift_ofList, FreeMonoid.toList_prod, List.map_map]
  rfl

theorem variableWord_subst (substitution : Nat → Term signature) :
    ∀ term : Term signature,
      variableWord (term.subst substitution) =
        (variableWord term).flatMap (fun index => variableWord (substitution index))
  | .var _ => by simp [variableWord]
  | .op .one _arguments => rfl
  | .op .mul arguments => by
      change variableWord ((arguments ⟨0, by decide⟩).subst substitution) ++
          variableWord ((arguments ⟨1, by decide⟩).subst substitution) =
        (variableWord (arguments ⟨0, by decide⟩) ++ variableWord (arguments ⟨1, by decide⟩)).flatMap _
      rw [List.flatMap_append, variableWord_subst substitution (arguments ⟨0, by decide⟩),
        variableWord_subst substitution (arguments ⟨1, by decide⟩)]

/-- Every occurrence obeys a supplied finite variable bound. -/
theorem variableWord_mem_lt {bound : Nat} {term : Term signature}
    (bounded : term.VariablesBelow bound) {index : Nat}
    (member : index ∈ variableWord term) : index < bound := by
  induction term with
  | var variableIndex =>
      simp only [variableWord, List.mem_singleton] at member
      exact member ▸ bounded
  | op operation arguments ih =>
      cases operation with
      | mul =>
          simp only [variableWord, List.mem_append] at member
          exact member.elim (ih ⟨0, by decide⟩ (bounded ⟨0, by decide⟩))
            (ih ⟨1, by decide⟩ (bounded ⟨1, by decide⟩))
      | one => cases member

theorem variableWord_eq_nil_of_variablesBelow_zero {term : Term signature}
    (bounded : term.VariablesBelow 0) : variableWord term = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun _ member =>
    Nat.not_lt_zero _ (variableWord_mem_lt bounded member)

/-- Finite argument evaluation agrees with substitution on the same ordered word. -/
theorem toList_evaluateBelow_freeMonoid {Generator : Type} {bound : Nat}
    (arguments : Fin bound → FreeMonoid Generator)
    (term : Term signature) (bounded : term.VariablesBelow bound) :
    FreeMonoid.toList
        (term.evaluateBelow (mathlibModel (FreeMonoid Generator)) arguments bounded) =
      (variableWord term).flatMap (fun index =>
        if below : index < bound then FreeMonoid.toList (arguments ⟨index, below⟩) else []) := by
  rw [Term.evaluateBelow_eq_evaluate (mathlibModel (FreeMonoid Generator)) arguments
    (fun index => if below : index < bound then arguments ⟨index, below⟩ else 1)
    (by intro index below; simp only [below, dite_true]), toList_evaluate_freeMonoid]
  apply List.flatMap_congr
  intro index _member
  split <;> simp_all only [FreeMonoid.toList_one]

end Mettapedia.UniversalAlgebra.Monoid.Term
