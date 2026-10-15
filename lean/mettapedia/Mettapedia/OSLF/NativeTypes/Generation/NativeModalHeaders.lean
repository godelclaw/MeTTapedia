import Mettapedia.OSLF.NativeTypes.Generation.NativeDeclarations
import Mettapedia.OSLF.NativeTypes.Modal.NativeEventDeclarations
import Mettapedia.OSLF.NativeTypes.Generation.NativeModalParameters

/-!
# Typed native modal headers read from the generated schema catalogue

Each entry keeps its original schema index and independently decoded authored
program, focus and binder types. A focus beneath binders is exposed as an
ordered function parameter, rather than a raw term in the ambient context.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.NativeModalHeaders

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Modal.NativeEventDeclarations
open NativeSignature

variable (plan : Plan)

structure Header where
  origin : Index plan
  program : Carrier plan.snapshot.language
  focus : Carrier plan.snapshot.language
  focusBinders : List (Carrier plan.snapshot.language)
  rely : List (NativeModalParameters.Parameter (schema plan origin))
  matched : List (NativeModalParameters.Parameter (schema plan origin))

def decode? (origin : Index plan) : Option (Header plan) := do
  let program ← decodeType? plan.snapshot.language (schema plan origin).programCarrier
  let focus ← decodeType? plan.snapshot.language (schema plan origin).focusCarrier
  let binders ← decodeList (decodeType? plan.snapshot.language) (schema plan origin).focusBound
  let rely ← NativeModalParameters.decodeAll? (schema plan origin) (schema plan origin).relyNames
  let matched ← NativeModalParameters.decodeAll? (schema plan origin) (schema plan origin).matchedNames
  pure ⟨origin, program, focus, binders, rely, matched⟩

def decodeAll? : Option (List (Header plan)) :=
  decodeList (decode? plan) (List.finRange (schemas plan).length)

def Header.focusArgument (header : Header plan) : Carrier plan.snapshot.language :=
  header.focusBinders.reverse.foldr Carrier.function header.focus

theorem decode_sound {origin : Index plan} {header : Header plan}
    (decoded : decode? plan origin = some header) :
    header.origin = origin ∧
      header.program.source = (schema plan origin).programCarrier ∧
      header.focus.source = (schema plan origin).focusCarrier ∧
      List.Forall₂ (fun source carrier => carrier.source = source)
        (schema plan origin).focusBound header.focusBinders := by
  cases program : decodeType? plan.snapshot.language (schema plan origin).programCarrier with
  | none => simp [decode?, program] at decoded
  | some programCarrier =>
      cases focus : decodeType? plan.snapshot.language (schema plan origin).focusCarrier with
      | none => simp [decode?, program, focus] at decoded
      | some focusCarrier =>
          cases binders : decodeList (decodeType? plan.snapshot.language) (schema plan origin).focusBound with
          | none => simp [decode?, program, focus, binders] at decoded
          | some binderCarriers =>
              cases rely : NativeModalParameters.decodeAll? (schema plan origin) (schema plan origin).relyNames with
              | none => simp [decode?, program, focus, binders, rely] at decoded
              | some relyParameters =>
                  cases matched : NativeModalParameters.decodeAll? (schema plan origin) (schema plan origin).matchedNames with
                  | none => simp [decode?, program, focus, binders, rely, matched] at decoded
                  | some matchedParameters =>
                      simp [decode?, program, focus, binders, rely, matched] at decoded
                      cases decoded
                      exact ⟨rfl, decodeType?_sound program, decodeType?_sound focus,
                        (decodeList_sound binders).imp (fun _ _ found => decodeType?_sound found)⟩

theorem decode_parameters {origin : Index plan} {header : Header plan}
    (decoded : decode? plan origin = some header) :
    header.rely.map (fun parameter => parameter.slot.name) = (schema plan header.origin).relyNames ∧
      header.matched.map (fun parameter => parameter.slot.name) = (schema plan header.origin).matchedNames := by
  cases program : decodeType? plan.snapshot.language (schema plan origin).programCarrier with
  | none => simp [decode?, program] at decoded
  | some programCarrier =>
      cases focus : decodeType? plan.snapshot.language (schema plan origin).focusCarrier with
      | none => simp [decode?, program, focus] at decoded
      | some focusCarrier =>
          cases binders : decodeList (decodeType? plan.snapshot.language) (schema plan origin).focusBound with
          | none => simp [decode?, program, focus, binders] at decoded
          | some binderCarriers =>
              cases rely : NativeModalParameters.decodeAll? (schema plan origin) (schema plan origin).relyNames with
              | none => simp [decode?, program, focus, binders, rely] at decoded
              | some relyParameters =>
                  cases matched : NativeModalParameters.decodeAll? (schema plan origin) (schema plan origin).matchedNames with
                  | none => simp [decode?, program, focus, binders, rely, matched] at decoded
                  | some matchedParameters =>
                      simp [decode?, program, focus, binders, rely, matched] at decoded
                      cases decoded
                      exact ⟨NativeModalParameters.decodeAll_names _ rely,
                        NativeModalParameters.decodeAll_names _ matched⟩

theorem decodeAll_origins {headers : List (Header plan)}
    (decoded : decodeAll? plan = some headers) :
    List.Forall₂ (fun origin header => header.origin = origin)
      (List.finRange (schemas plan).length) headers :=
  (decodeList_sound decoded).imp (fun _ _ found => (decode_sound plan found).1)

theorem decodeAll_length {headers : List (Header plan)}
    (decoded : decodeAll? plan = some headers) :
    headers.length = (schemas plan).length := by
  have ordered := (decodeAll_origins plan decoded).length_eq
  simpa using ordered.symm

end Mettapedia.OSLF.NativeTypes.Generation.NativeModalHeaders
