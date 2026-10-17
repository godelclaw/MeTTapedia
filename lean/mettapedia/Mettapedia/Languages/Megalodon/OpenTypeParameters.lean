import Mettapedia.Languages.Megalodon.SourceTypeParameters

/-!
# Simultaneous source specialization with open type arguments

Source parameters are numbered in declaration order. Arguments can refer to
an enclosing type context; replacing source parameter zero repeatedly would
then substitute into an argument inserted earlier. Simultaneous substitution
and reversal into nested binders avoid that capture. No closed-argument
restriction or fixed number of type parameters is imposed here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.OpenTypeParameters
open MathdataKernel SourceTypeParameters

/-- Simultaneous substitution, preserving binders internal to the source type.
Variables beyond the parameter interval refer to the surrounding context. -/
def substitute (arguments : List Tp) (depth : Nat) : Tp → Tp
  | .var index => if index < depth then .var index else
      match arguments[index - depth]? with
      | some argument => argument.shift 0 depth
      | none => .var (index - arguments.length)
  | .prop => .prop
  | .base index => .base index
  | .arr domain codomain => .arr (substitute arguments depth domain) (substitute arguments depth codomain)
  | .all body => .all (substitute arguments (depth + 1) body)

/-- Removing the outer binders in application order. The remaining binders
protect every free variable in an already inserted argument. -/
def removeBinders : List Tp → Tp → Tp
  | [], body => body
  | argument :: arguments, body => removeBinders arguments (Tp.instantiateAt arguments.length argument body)

private theorem instantiateAt_bind (count depth : Nat) (argument body : Tp) :
    Tp.instantiateAt depth argument (SourceTypeParameters.bind count body) =
      SourceTypeParameters.bind count (Tp.instantiateAt (depth + count) argument body) := by
  induction count generalizing depth with
  | zero => simp [SourceTypeParameters.bind]
  | succ count ih => simp [SourceTypeParameters.bind, Tp.instantiateAt, ih, Nat.add_comm, Nat.add_left_comm]

theorem specialize_bind (arguments : List Tp) (body : Tp) :
    specialize arguments (SourceTypeParameters.bind arguments.length body) = some (removeBinders arguments body) := by
  induction arguments generalizing body with
  | nil => rfl
  | cons argument arguments ih =>
      simp only [List.length_cons, SourceTypeParameters.bind, specialize, Tp.instantiate, instantiateAt_bind,
        Nat.zero_add, removeBinders]
      exact ih _

private theorem instantiate_shift (body : Tp) (depth count : Nat) (argument : Tp) :
    Tp.instantiateAt (depth + count) argument (Tp.shift depth (count + 1) body) =
      Tp.shift depth count body := by
  induction body generalizing depth with
  | var index =>
      by_cases below : index < depth
      · simp [Tp.shift, Tp.instantiateAt, below, show index < depth + count by omega]
      · simp [Tp.shift, Tp.instantiateAt, below,
          show ¬ index + (count + 1) < depth + count by omega,
          show index + (count + 1) ≠ depth + count by omega,
          show index + (count + 1) - 1 = index + count by omega]
  | prop | base => rfl
  | arr _ _ ihd ihc => simp [Tp.shift, Tp.instantiateAt, ihd, ihc]
  | all body ih =>
      simpa [Tp.shift, Tp.instantiateAt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        congrArg Tp.all (ih (depth + 1))

theorem inserted_argument_protected (arguments : List Tp) (body : Tp) :
    removeBinders arguments (Tp.shift 0 arguments.length body) = body := by
  induction arguments with
  | nil => simp [removeBinders, Tp.shift_zero]
  | cons argument arguments ih =>
      have step := instantiate_shift body 0 arguments.length argument
      simp only [Nat.zero_add] at step
      rw [List.length_cons, removeBinders, step]
      exact ih

private theorem removeBinders_arr (arguments : List Tp) (domain codomain : Tp) :
    removeBinders arguments (.arr domain codomain) =
      .arr (removeBinders arguments domain) (removeBinders arguments codomain) := by
  induction arguments generalizing domain codomain with
  | nil => rfl
  | cons argument arguments ih => simp [removeBinders, Tp.instantiateAt, ih]

private theorem removeBinders_prop (arguments : List Tp) : removeBinders arguments .prop = .prop := by
  induction arguments <;> simp_all [removeBinders, Tp.instantiateAt]

private theorem removeBinders_base (arguments : List Tp) (index : Nat) :
    removeBinders arguments (.base index) = .base index := by
  induction arguments <;> simp_all [removeBinders, Tp.instantiateAt]

theorem source_variable (arguments : List Tp) (index : Nat) (scope : index < arguments.length) :
    removeBinders arguments (.var (reverseIndex arguments.length 0 index)) = arguments[index] := by
  induction arguments generalizing index with
  | nil => simp at scope
  | cons argument arguments ih =>
      cases index with
      | zero =>
          simp [reverseIndex, removeBinders, Tp.instantiateAt, inserted_argument_protected]
      | succ index =>
          have within : index < arguments.length := by simpa using scope
          have mapped : arguments.length - (index + 1) < arguments.length := by omega
          have same : arguments.length - 1 - index = arguments.length - (index + 1) := by omega
          simpa [reverseIndex, removeBinders, Tp.instantiateAt, within, mapped, same,
            show index + 1 < arguments.length + 1 by omega] using ih index within

/-- Source-to-binder specialization is exact for arbitrary open arguments.
The source body is a plain type scoped by its declared parameters. -/
theorem specialization (arguments : List Tp) (body : Tp)
    (formed : body.plainWellFormed arguments.length = true) :
    specialize arguments (SourceTypeParameters.bind arguments.length (type arguments.length 0 body)) =
      some (substitute arguments 0 body) := by
  rw [specialize_bind]
  congr 1
  induction body with
  | var index =>
      have scope : index < arguments.length := by simpa [Tp.plainWellFormed] using formed
      simpa [type, substitute, List.getElem?_eq_getElem scope, Tp.shift_zero] using source_variable arguments index scope
  | prop => exact removeBinders_prop arguments
  | base index => exact removeBinders_base arguments index
  | arr domain codomain ihd ihc =>
      simp only [Tp.plainWellFormed, Bool.and_eq_true] at formed
      simp [type, substitute, removeBinders_arr, ihd formed.1, ihc formed.2]
  | all body ih => simp [Tp.plainWellFormed] at formed

theorem inferTerm_applyTypes (environment : Environment) (depth : Nat) (context : List Tp)
    (arguments : List Tp) (function : Tm)
    (formed : ∀ argument ∈ arguments, argument.plainWellFormed depth = true) :
    inferTerm environment depth context (applyTypes arguments function) =
      (inferTerm environment depth context function).bind (specialize arguments) := by
  induction arguments generalizing function with
  | nil => simp [applyTypes, specialize]
  | cons argument arguments ih =>
      have first := formed argument (by simp)
      have rest : ∀ value ∈ arguments, value.plainWellFormed depth = true := by
        intro value member
        exact formed value (by simp [member])
      rw [applyTypes, ih _ rest]
      simp only [inferTerm, first, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases inferred : inferTerm environment depth context function with
      | none => rfl
      | some value => cases value <;> rfl

theorem checked_specialization (environment : Environment) (depth : Nat) (context : List Tp)
    (arguments : List Tp) (function : Tm) (body : Tp)
    (bodyFormed : body.plainWellFormed arguments.length = true)
    (argumentsFormed : ∀ argument ∈ arguments, argument.plainWellFormed depth = true)
    (checked : inferTerm environment depth context function =
      some (SourceTypeParameters.bind arguments.length (type arguments.length 0 body))) :
    inferTerm environment depth context (applyTypes arguments function) = some (substitute arguments 0 body) := by
  rw [inferTerm_applyTypes environment depth context arguments function argumentsFormed, checked]
  exact specialization arguments body bodyFormed

theorem enclosing_parameter_survives :
    specialize [.var 0, .base 0] (SourceTypeParameters.bind 2 (type 2 0 (.arr (.var 0) (.var 1)))) =
      some (.arr (.var 0) (.base 0)) := by decide

theorem sequential_source_substitution_captures :
    instantiateParameters [.var 0, .base 0] (.arr (.var 0) (.var 1)) = .arr (.base 0) (.base 0) ∧
      instantiateParameters [.var 0, .base 0] (.arr (.var 0) (.var 1)) ≠
        substitute [.var 0, .base 0] 0 (.arr (.var 0) (.var 1)) := by decide

theorem checked_open_application :
    let environment : Environment := { terms :=
      [{ name := "sourceFunction", type := SourceTypeParameters.bind 2 (type 2 0 (.arr (.var 0) (.var 1))) }] }
    inferTerm environment 1 [] (applyTypes [.var 0, .base 0] (.named "sourceFunction")) =
      some (.arr (.var 0) (.base 0)) := by decide

theorem escaping_argument_refused :
    let environment : Environment := { terms :=
      [{ name := "sourceFunction", type := SourceTypeParameters.bind 2 (type 2 0 (.arr (.var 0) (.var 1))) }] }
    inferTerm environment 0 [] (applyTypes [.var 0, .base 0] (.named "sourceFunction")) = none := by decide

end Mettapedia.Languages.Megalodon.OpenTypeParameters
