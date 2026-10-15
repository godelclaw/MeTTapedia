import Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier
import Mettapedia.OSLF.Syntax.LambdaAuthoredTypingComparison

open Mettapedia.OSLF.Framework

/-!
# Recover scoped lambda terms from authored patterns

The decoder checks the original two-constructor grammar and ambient de Bruijn
context. Its result retains the exact source rendering, so a successful parse
cannot replace the supplied program by a different intrinsic term.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Lambda.Decode

open Mettapedia.OSLF.Binding
open LambdaContextualRung
open LambdaScopedAuthoringComparison (encodeTerm encodeArgs wrapBinders)
open Mettapedia.OSLF.MeTTaIL.Syntax

def decodeVar : (Γ : Ctx sig) → (index : Nat) →
    Option {value : Var Γ .term // (varIdx (S := sig) value).val = index}
  | [], _ => none
  | .term :: _, 0 => some ⟨.zero, rfl⟩
  | .term :: Γ, index + 1 =>
      (decodeVar Γ index).map fun found =>
        ⟨.succ found.val, by
          change (varIdx (S := sig) found.val).val + 1 = index + 1
          exact congrArg (· + 1) found.property⟩

theorem variable_complete : {Γ : Ctx sig} → (value : Var Γ .term) →
    decodeVar Γ (varIdx (S := sig) value).val = some ⟨value, rfl⟩
  | _, .zero => rfl
  | .term :: _, .succ value => by
      simp only [varIdx, Fin.val_succ, decodeVar, variable_complete value, Option.map_some]

def decode (Γ : Ctx sig) : (source : Pattern) →
    Option {value : Term sig Γ .term // encodeTerm value = source}
  | .bvar index =>
      (decodeVar Γ index).map fun found =>
        ⟨.var found.val, by
          change Pattern.bvar (varIdx (S := sig) found.val).val = Pattern.bvar index
          exact congrArg Pattern.bvar found.property⟩
  | .apply "App" [function, argument] => do
      let functionValue ← decode Γ function
      let argumentValue ← decode Γ argument
      pure ⟨appT functionValue.val argumentValue.val, by
        simp only [appT, encodeTerm, encodeArgs, wrapBinders, List.foldr_nil]
        rw [functionValue.property, argumentValue.property]⟩
  | .apply "Lam" [.lambda none body] => do
      let bodyValue ← decode (.term :: Γ) body
      pure ⟨lamT bodyValue.val, by
        simp only [lamT, encodeTerm, encodeArgs, wrapBinders, List.foldr_cons, List.foldr_nil]
        rw [bodyValue.property]⟩
  | _ => none
termination_by source => sizeOf source

theorem decode_complete : {Γ : Ctx sig} → (source : Term sig Γ .term) →
    decode Γ (encodeTerm source) = some ⟨source, rfl⟩
  | _, .var value => by
      simp only [encodeTerm, decode, variable_complete value, Option.map_some]
  | _, .op .app (.cons function (.cons argument .nil)) => by
      simp only [encodeTerm, encodeArgs, wrapBinders, List.foldr_nil, decode]
      erw [decode_complete function, decode_complete argument]
      rfl
  | _, .op .lam (.cons body .nil) => by
      simp only [encodeTerm, encodeArgs, wrapBinders, List.foldr_cons, List.foldr_nil, decode]
      erw [decode_complete body]
      rfl
termination_by _ source => Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.nodeCount source
decreasing_by
  all_goals simp only [Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.nodeCount,
    Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.argumentNodeCount]; omega

theorem encode_injective {Γ : Ctx sig} (first second : Term sig Γ .term)
    (equal : encodeTerm first = encodeTerm second) : first = second := by
  have recovered := congrArg (fun source => (decode Γ source).map Subtype.val) equal
  rw [decode_complete, decode_complete] at recovered
  exact Option.some.inj recovered

theorem accepted_exact (Γ : Ctx sig) (source : Pattern) :
    (decode Γ source).isSome = true ↔ ∃ value : Term sig Γ .term, encodeTerm value = source := by
  constructor
  · intro accepted
    cases output : decode Γ source with
    | none => simp [output] at accepted
    | some value => exact ⟨value.val, value.property⟩
  · rintro ⟨value, rfl⟩
    simp [decode_complete]

theorem encode_object : {Γ : Ctx sig} → (source : Term sig Γ .term) →
    Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPattern (encodeTerm source) = true
  | _, .var _ => rfl
  | _, .op .app (.cons function (.cons argument .nil)) => by
      change (Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPattern (encodeTerm function) &&
        (Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPattern (encodeTerm argument) && true)) = true
      rw [encode_object function, encode_object argument]
      rfl
  | _, .op .lam (.cons body .nil) => by
      change (Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPattern (encodeTerm body) && true) = true
      rw [encode_object body]
      rfl
termination_by _ source => Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.nodeCount source
decreasing_by
  all_goals simp only [Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.nodeCount,
    Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.argumentNodeCount]; omega

end Mettapedia.OSLF.NativeTypes.Instances.Lambda.Decode
