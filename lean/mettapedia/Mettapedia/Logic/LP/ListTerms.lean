import Mettapedia.Logic.LP.Substitution

/-!
# Lists in first-order terms

The function symbol `n` represents a list of exactly `n` elements. Variable
sharing and substitution remain those of the existing first-order term type.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LP.ListTerms

abbrev signature (Constant Variable : Type) : LPSignature where
  constants := Constant
  vars := Variable
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Nat
  functionArity := id

variable {Constant Variable : Type}

abbrev ListTerm (Constant Variable : Type) := Term (signature Constant Variable)

def ofList (terms : List (ListTerm Constant Variable)) : ListTerm Constant Variable :=
  .app terms.length (fun index => terms.get index)

def toList : ListTerm Constant Variable → Option (List (ListTerm Constant Variable))
  | .app _ children => some (List.ofFn children)
  | _ => none

@[simp] theorem toList_ofList (terms : List (ListTerm Constant Variable)) :
    toList (ofList terms) = some terms := by
  simp [toList,ofList]

theorem app_congr {n m : Nat} (lengths : n = m)
    {left : Fin n → ListTerm Constant Variable}
    {right : Fin m → ListTerm Constant Variable}
    (pointwise : ∀ index, left index = right (Fin.cast lengths index)) :
    (Term.app n left : ListTerm Constant Variable) = .app m right := by
  subst lengths
  have equal : left = right := funext pointwise
  rw [equal]

theorem apply_ofList (witness : Subst (signature Constant Variable))
    (terms : List (ListTerm Constant Variable)) :
    witness.applyTerm (ofList terms) = ofList (terms.map witness.applyTerm) := by
  unfold ofList
  rw [Subst.applyTerm_app]
  exact app_congr (List.length_map _).symm (fun index => by simp)

theorem ofList_injective : Function.Injective (@ofList Constant Variable) := by
  intro left right same
  unfold ofList at same
  injection same with lengths functions
  apply List.ext_get lengths
  intro index leftBound rightBound
  have pointwise {n m : Nat} (equal : n = m)
      {f : Fin n → ListTerm Constant Variable} {g : Fin m → ListTerm Constant Variable}
      (same : HEq f g) (index : Nat) (bound : index < n) :
      f ⟨index,bound⟩ = g ⟨index,equal ▸ bound⟩ := by
    subst equal
    cases same
    rfl
  exact pointwise lengths functions index leftBound

theorem ofList_toList (term : ListTerm Constant Variable)
    (terms : List (ListTerm Constant Variable)) (view : toList term = some terms) :
    ofList terms = term := by
  cases term with
  | var _ => simp [toList] at view
  | const _ => simp [toList] at view
  | app arity children =>
      simp only [toList,Option.some.injEq] at view
      subst terms
      unfold ofList
      apply app_congr (by simp)
      intro index
      simp only [List.get_eq_getElem, List.getElem_ofFn]
      apply congrArg children
      exact Fin.ext rfl

theorem toList_eq_some_iff (term : ListTerm Constant Variable)
    (terms : List (ListTerm Constant Variable)) :
    toList term = some terms ↔ term = ofList terms := by
  constructor
  · intro view; exact (ofList_toList term terms view).symm
  · rintro rfl; exact toList_ofList terms

end Mettapedia.Logic.LP.ListTerms
