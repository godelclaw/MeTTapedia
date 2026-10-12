import Mettapedia.Logic.HOL.Syntax.NamedElaboration
import Mathlib.Data.List.Forall2

/-!
# Closed HOL elaboration of curried applications

Characterizations of `NamedElaboration.infer` on closed constants and curried
application spines, for an arbitrary constant signature.  The HE groundings
translate an expression `(h a₁ … aₙ)` to such a spine and read its type off
these lemmas.
-/

namespace Mettapedia.Languages.MeTTa.HE.TypeGrounding

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.NamedElaboration

variable {Base : Type} [DecidableEq Base]
variable {ConstName : Type} {Const : Ty Base → Type}

/-- Closed elaboration of a named HOL term at one HOL type. -/
def Elaborates (signature : Signature ConstName Const)
    (term : NamedTerm Base String ConstName) (type : Ty Base) : Prop :=
  ∃ intrinsic : Term Const [] type,
    infer signature (BinderNames.nil : BinderNames Base String []) term =
      .ok ⟨type, intrinsic⟩

omit [DecidableEq Base] in
private theorem ok_someTerm_iff {error : Type}
    {left right : Ty Base} (term : Term Const [] left) :
    (∃ other : Term Const [] right,
      (Except.ok ⟨left, term⟩ : Except error (SomeTerm Const [])) =
        .ok ⟨right, other⟩) ↔ left = right := by
  constructor
  · rintro ⟨other, equal⟩
    have := congrArg (fun result : Except error (SomeTerm Const []) =>
      match result with
      | .ok value => some value.type
      | .error _ => none) equal
    simpa using this
  · rintro rfl
    exact ⟨term, rfl⟩

/-- A curried application elaborates at `ρ` exactly when its function
elaborates at some `σ ⇒ ρ` and its argument at `σ`. -/
theorem elaborates_app_iff {signature : Signature ConstName Const}
    {function argument : NamedTerm Base String ConstName} {result : Ty Base} :
    Elaborates signature (.app function argument) result ↔
      ∃ domain, Elaborates signature function (.arr domain result) ∧
        Elaborates signature argument domain := by
  constructor
  · rintro ⟨intrinsic, inferred⟩
    cases functionInferred : infer signature
        (BinderNames.nil : BinderNames Base String []) function with
    | error failure =>
        simp [infer, functionInferred] at inferred
    | ok functionResult =>
        obtain ⟨functionType, functionTerm⟩ := functionResult
        cases functionType with
        | prop => simp [infer, functionInferred] at inferred
        | base name => simp [infer, functionInferred] at inferred
        | arr domain codomain =>
            cases argumentInferred : infer signature
                (BinderNames.nil : BinderNames Base String []) argument with
            | error failure =>
                simp [infer, functionInferred, argumentInferred] at inferred
            | ok argumentResult =>
                obtain ⟨argumentType, argumentTerm⟩ := argumentResult
                by_cases sameType : argumentType = domain
                · subst sameType
                  simp [infer, functionInferred, argumentInferred, expectType] at inferred
                  obtain ⟨codomainEq, _⟩ := inferred
                  subst codomainEq
                  exact ⟨argumentType, ⟨functionTerm, functionInferred⟩,
                    ⟨argumentTerm, argumentInferred⟩⟩
                · simp [infer, functionInferred, argumentInferred, expectType,
                    sameType] at inferred
  · rintro ⟨domain, ⟨functionTerm, functionInferred⟩,
      ⟨argumentTerm, argumentInferred⟩⟩
    refine ⟨.app functionTerm argumentTerm, ?_⟩
    simp [infer, functionInferred, argumentInferred, expectType]

/-- A constant elaborates exactly at the type its signature assigns. -/
theorem elaborates_constant_iff {signature : Signature ConstName Const}
    {name : ConstName} {type : Ty Base} :
    Elaborates signature (.constant name) type ↔
      ∃ constant : Const type, signature name = some ⟨type, constant⟩ := by
  constructor
  · rintro ⟨intrinsic, inferred⟩
    cases lookup : signature name with
    | none => simp [infer, lookup] at inferred
    | some resolved =>
        obtain ⟨resolvedType, constant⟩ := resolved
        simp only [infer, lookup] at inferred
        have typeEq : resolvedType = type :=
          (ok_someTerm_iff (error := Error Base String ConstName) _).mp
            ⟨intrinsic, inferred⟩
        subst typeEq
        exact ⟨constant, rfl⟩
  · rintro ⟨constant, lookup⟩
    refine ⟨.const constant, ?_⟩
    simp [infer, lookup]

/-- Elaboration of a left-nested spine of curried applications. -/
theorem elaborates_foldl_app_iff {signature : Signature ConstName Const}
    {α : Type} (translate : α → NamedTerm Base String ConstName) :
    ∀ (function : NamedTerm Base String ConstName) (arguments : List α)
      (result : Ty Base),
      Elaborates signature
          (arguments.foldl (fun accumulated argument =>
            .app accumulated (translate argument)) function) result ↔
        ∃ argumentTypes : List (Ty Base),
          Elaborates signature function (argumentTypes.foldr Ty.arr result) ∧
            List.Forall₂ (fun argument type =>
              Elaborates signature (translate argument) type)
              arguments argumentTypes
  | function, [], result => by
      constructor
      · intro elaborated
        exact ⟨[], elaborated, .nil⟩
      · rintro ⟨argumentTypes, elaborated, arguments⟩
        cases arguments
        exact elaborated
  | function, argument :: arguments, result => by
      rw [List.foldl_cons, elaborates_foldl_app_iff translate]
      constructor
      · rintro ⟨argumentTypes, applied, rest⟩
        obtain ⟨domain, functionElaborates, argumentElaborates⟩ :=
          elaborates_app_iff.mp applied
        exact ⟨domain :: argumentTypes, functionElaborates,
          .cons argumentElaborates rest⟩
      · rintro ⟨argumentTypes, functionElaborates, all⟩
        cases all with
        | cons argumentElaborates rest =>
            exact ⟨_, elaborates_app_iff.mpr
              ⟨_, functionElaborates, argumentElaborates⟩, rest⟩

omit [DecidableEq Base] in
/-- Curried arrows of equal length are equal only componentwise. -/
theorem foldr_arr_injective :
    ∀ {left right : List (Ty Base)} {leftResult rightResult : Ty Base},
      left.length = right.length →
      left.foldr Ty.arr leftResult = right.foldr Ty.arr rightResult →
      left = right ∧ leftResult = rightResult
  | [], [], _, _, _, equal => ⟨rfl, equal⟩
  | [], _ :: _, _, _, lengths, _ => by simp at lengths
  | _ :: _, [], _, _, lengths, _ => by simp at lengths
  | leftHead :: leftTail, rightHead :: rightTail, _, _, lengths, equal => by
      simp only [List.foldr_cons] at equal
      obtain ⟨heads, tails⟩ := Ty.arr.inj equal
      obtain ⟨tailsEqual, results⟩ :=
        foldr_arr_injective (by simpa using lengths) tails
      exact ⟨by rw [heads, tailsEqual], results⟩

end Mettapedia.Languages.MeTTa.HE.TypeGrounding
