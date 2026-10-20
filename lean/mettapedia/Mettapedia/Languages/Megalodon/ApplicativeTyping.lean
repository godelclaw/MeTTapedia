import Mettapedia.Languages.Megalodon.MathdataKernel
import Mettapedia.Logic.HOL.Syntax.ClosedElaboration

/-!
# Finite applicative signatures in the Mathdata type checker

An interned simple type signature is translated to Mathdata primitives.
Constants retain their table positions, base types retain their indices,
and application is checked by `MathdataKernel.inferTerm` itself. The source
judgment is the existing, independently defined `ApplicativeTyped` relation.

This realizes instantiated type contracts, including flat function values
represented as base types with explicit application constants. It does not
identify a flat source arrow with a curried arrow, perform scheme inference,
or grant any logical axioms. Other named HOL syntax is rejected by this
particular translation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.ApplicativeTyping

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.NamedElaboration
open MathdataKernel

abbrev Source := NamedTerm Nat String Nat

def encodeType : Ty Nat → Tp
  | .prop => .prop
  | .base index => .base index
  | .arr domain result => .arr (encodeType domain) (encodeType result)

theorem encodeType_injective : Function.Injective encodeType := by
  intro left
  induction left with
  | prop => intro right same; cases right <;> simp_all [encodeType]
  | base index => intro right same; cases right <;> simp_all [encodeType]
  | arr domain result domainIH resultIH =>
      intro right same
      cases right with
      | prop => simp [encodeType] at same
      | base _ => simp [encodeType] at same
      | arr otherDomain otherResult =>
          have parts := Tp.arr.inj same
          exact congrArg₂ Ty.arr (domainIH parts.1) (resultIH parts.2)

theorem encodeType_plain (depth : Nat) (type : Ty Nat) :
    (encodeType type).plainWellFormed depth = true := by
  induction type <;> simp_all [encodeType, Tp.plainWellFormed]

def environment (signature : List (Ty Nat)) : Environment where
  primitives := signature.map encodeType

def translate : Source → Option Tm
  | .constant index => some (.prim index)
  | .app function argument => do
      return .app (← translate function) (← translate argument)
  | _ => none

/-- Actual Mathdata inference after the structural translation. -/
def infer (signature : List (Ty Nat)) (source : Source) : Option Tp := do
  let target ← translate source
  inferTerm (environment signature) 0 [] target

theorem infer_constant (signature : List (Ty Nat)) (index : Nat) :
    infer signature (.constant index) = signature[index]?.map encodeType := by
  simp [infer, translate, inferTerm, environment]

theorem infer_app (signature : List (Ty Nat)) (function argument : Source) :
    infer signature (.app function argument) = (do
      let .arr domain result ← infer signature function | none
      let actual ← infer signature argument
      if actual = domain then some result else none) := by
  cases hf : translate function with
  | none => simp [infer, translate, hf]
  | some f =>
      cases ht : inferTerm (environment signature) 0 [] f with
      | none => cases ha : translate argument <;> simp [infer, translate, inferTerm, hf, ha, ht]
      | some type =>
          cases type <;> cases ha : translate argument <;>
            simp [infer, translate, inferTerm, hf, ha, ht]

theorem typed_infers {signature : List (Ty Nat)} {source : Source} {type : Ty Nat}
    (typed : ApplicativeTyped (fun name => signature[name]?) source type) :
    infer signature source = some (encodeType type) := by
  induction typed with
  | constant lookup => simp [infer_constant, lookup]
  | app _ _ functionIH argumentIH =>
      simp [infer_app, functionIH, argumentIH, encodeType]

/-- Inference cannot invent a Mathdata type outside the source type image. -/
theorem inferred_source {signature : List (Ty Nat)} {source : Source} {target : Tp}
    (accepted : infer signature source = some target) :
    ∃ type, target = encodeType type ∧
      ApplicativeTyped (fun name => signature[name]?) source type := by
  induction source generalizing target with
  | constant index =>
      rw [infer_constant] at accepted
      cases lookup : signature[index]? with
      | none => simp [lookup] at accepted
      | some type =>
          exact ⟨type, (Option.some.inj (by simpa [lookup] using accepted)).symm,
            .constant lookup⟩
  | app function argument functionIH argumentIH =>
      rw [infer_app] at accepted
      cases hf : infer signature function with
      | none => simp [hf] at accepted
      | some functionType =>
          obtain ⟨sourceFunctionType, rfl, functionTyped⟩ := functionIH hf
          cases sourceFunctionType with
          | prop => simp [hf, encodeType] at accepted
          | base _ => simp [hf, encodeType] at accepted
          | arr domain result =>
              cases ha : infer signature argument with
              | none => simp [hf, ha, encodeType] at accepted
              | some argumentType =>
                  obtain ⟨sourceArgumentType, rfl, argumentTyped⟩ := argumentIH ha
                  by_cases same : encodeType sourceArgumentType = encodeType domain
                  · have equal := encodeType_injective same
                    subst sourceArgumentType
                    refine ⟨result, ?_, .app functionTyped argumentTyped⟩
                    simpa [hf, ha, encodeType] using accepted.symm
                  · simp [hf, ha, encodeType, same] at accepted
  | _ =>
      simp [infer, translate] at accepted

theorem infer_iff (signature : List (Ty Nat)) (source : Source) (type : Ty Nat) :
    infer signature source = some (encodeType type) ↔
      ApplicativeTyped (fun name => signature[name]?) source type := by
  constructor
  · intro accepted
    obtain ⟨found, same, typed⟩ := inferred_source accepted
    have equal := encodeType_injective same
    simpa [equal] using typed
  · exact typed_infers

theorem refusal_iff (signature : List (Ty Nat)) (source : Source) :
    infer signature source = none ↔
      ¬ ∃ type, ApplicativeTyped (fun name => signature[name]?) source type := by
  constructor
  · intro refused ⟨type, typed⟩
    have accepted := typed_infers typed
    rw [refused] at accepted
    contradiction
  · intro noType
    cases found : infer signature source with
    | none => rfl
    | some target =>
        obtain ⟨type, _, typed⟩ := inferred_source found
        exact False.elim (noType ⟨type, typed⟩)

namespace Controls

/-- Base 2 is a flat two-argument function value; base 0 and base 1 are
its two argument types. The application operation is a separate constant. -/
def signature : List (Ty Nat) :=
  [.base 2, .base 0, .base 1,
    .arr (.base 2) (.arr (.base 0) (.arr (.base 1) (.base 3)))]

def application : Source :=
  .app (.app (.app (.constant 3) (.constant 0)) (.constant 1)) (.constant 2)

example : infer signature application = some (.base 3) := by decide

example : infer signature (.app (.constant 0) (.constant 1)) = none := by decide

example : infer signature
    (.app (.app (.app (.constant 3) (.constant 0)) (.constant 2)) (.constant 1)) = none := by
  decide

example : infer signature (.constant 4) = none := by decide

end Controls

#print axioms infer_iff
#print axioms refusal_iff

end Mettapedia.Languages.Megalodon.ApplicativeTyping
