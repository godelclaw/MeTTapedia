import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclaredBindingDependent
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLTraceQualifiedExtensionalSemantics

/-!
# Declared bindings in the constructed contextual set model

The source judgment below interprets private references, abstraction, and
`where` directly in the existing set-family model. In particular, the value
of a `where` is interpreted in the outer environment before that environment
is extended. Its interpretation as native application is a theorem using
the actual trace-product beta law, rather than a supplied interface field.

Core payloads retain the existing qualified HOL interpretation. The judgment
does not assign a meaning to arbitrary opaque constants or assert soundness
of arbitrary native conversion. Private-reference admission is the separate
source typing judgment; spelling never supplies that admission.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.DeclaredBindingTraceSemantics

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation DeclaredBindingDependent
open PrivateIdentityContexts (Name Frame)
open Mettapedia.Logic.HOL.Embedding
open ZFSetContextualInterpretation (SetFamily Section Extension)
open NativeTraceLambdaSemantics (Context)

universe u

inductive Denotes (a : ZFSet.{u}) : {n : Nat} → (context : Context.{u} n) →
    Source Tower.Head n → (family : SetFamily context.Environment) → Section family → Prop where
  | core {n : Nat} {context : Context.{u} n} {term : Tower.Tm n}
      {family : SetFamily context.Environment} {value : Section family}
      (meaning : NativeHOLTraceQualifiedExtensionalSemantics.Denotes a context term family value) :
      Denotes a context (.core term) family value
  | reference {n : Nat} (context : Context.{u} n) (name : Name) (index : Fin n) :
      Denotes a context (.reference name index) (context.family index) (context.projection index)
  | lambda {n : Nat} {context : Context.{u} n} (name : Name)
      {domain : SetFamily context.Environment} {codomain : SetFamily (Extension domain)}
      {body : Source Tower.Head (n + 1)} {value : Section codomain}
      (bodyMeaning : Denotes a (context.snoc domain) body codomain value) :
      Denotes a context (.lambda name body) (ZFSetTraceContextual.piFamily domain codomain)
        (ZFSetTraceContextual.lam value)
  | whereBinding {n : Nat} {context : Context.{u} n} (name : Name)
      {domain : SetFamily context.Environment} {codomain : SetFamily (Extension domain)}
      {value : Source Tower.Head n} {body : Source Tower.Head (n + 1)}
      {valueSection : Section domain} {bodySection : Section codomain}
      (valueMeaning : Denotes a context value domain valueSection)
      (bodyMeaning : Denotes a (context.snoc domain) body codomain bodySection) :
      Denotes a context (.whereBinding name value body)
        (fun environment => codomain ⟨environment, valueSection environment⟩)
        (fun environment => bodySection ⟨environment, valueSection environment⟩)
  | result {n : Nat} {context : Context.{u} n} {source : Source Tower.Head n}
      {family : SetFamily context.Environment} {value : Section family}
      (meaning : Denotes a context source family value) :
      Denotes a context (.result source) family value
  | app {n : Nat} {context : Context.{u} n}
      {domain : SetFamily context.Environment} {codomain : SetFamily (Extension domain)}
      {function argument : Source Tower.Head n}
      {functionValue : Section (ZFSetTraceContextual.piFamily domain codomain)}
      {argumentValue : Section domain}
      (functionMeaning : Denotes a context function
        (ZFSetTraceContextual.piFamily domain codomain) functionValue)
      (argumentMeaning : Denotes a context argument domain argumentValue) :
      Denotes a context (.app function argument)
        (fun environment => codomain ⟨environment, argumentValue environment⟩)
        (ZFSetTraceContextual.app functionValue argumentValue)

theorem translation_preserves {a : ZFSet.{u}} {n : Nat} {context : Context.{u} n}
    {source : Source Tower.Head n} {family : SetFamily context.Environment}
    {value : Section family} (meaning : Denotes a context source family value) :
    NativeHOLTraceQualifiedExtensionalSemantics.Denotes a context
      (translate source) family value := by
  induction meaning with
  | core meaning => exact meaning
  | reference context name index => exact .mixed (.variable context index)
  | lambda name _ ih => exact .abstraction ih
  | whereBinding name _ _ valueInduction bodyInduction =>
      exact (NativeHOLTraceQualifiedExtensionalSemantics.Denotes.application
        (.abstraction bodyInduction) valueInduction).change_value
        (ZFSetTraceContextual.app_lam _ _)
  | result _ ih => exact ih
  | app _ _ functionInduction argumentInduction => exact .application functionInduction argumentInduction

theorem Denotes.cast_family {a : ZFSet.{u}} {n : Nat} {context : Context.{u} n}
    {source : Source Tower.Head n} {first second : SetFamily context.Environment}
    {value : Section first} (meaning : Denotes a context source first value)
    (equal : first = second) :
    Denotes a context source second (NativeTraceDisplayedSubstitution.castSection equal value) := by
  cases equal
  exact meaning

theorem Denotes.change_value {a : ZFSet.{u}} {n : Nat} {context : Context.{u} n}
    {source : Source Tower.Head n} {family : SetFamily context.Environment}
    {first second : Section family} (meaning : Denotes a context source family first)
    (equal : first = second) : Denotes a context source family second := by
  cases equal
  exact meaning

/-- Private-key changes leave the interpreted environments and sections
unchanged; neither a new proof witness nor a new object value is selected. -/
theorem Denotes.rekey {a : ZFSet.{u}} {n : Nat} {context : Context.{u} n}
    {source : Source Tower.Head n} {family : SetFamily context.Environment}
    {value : Section family} (meaning : Denotes a context source family value)
    (map : Nat → Nat) : Denotes a context (DeclaredBindingDependent.rekey map source) family value := by
  induction meaning with
  | core meaning => exact .core meaning
  | reference context name index => exact .reference context _ index
  | lambda name _ ih => exact .lambda _ ih
  | whereBinding name _ _ valueInduction bodyInduction => exact .whereBinding _ valueInduction bodyInduction
  | result _ ih => exact .result ih
  | app _ _ functionInduction argumentInduction => exact .app functionInduction argumentInduction

/-- A displayed renaming of the actual set model acts through the previously
proved substitution square. It preserves the complete semantic section. -/
theorem translated_renaming {a : ZFSet.{u}} {n : Nat} {context : Context.{u} n}
    {source : Source Tower.Head n} {family : SetFamily context.Environment}
    {value : Section family} (meaning : Denotes a context source family value)
    {m : Nat} (frame : Frame m) {destination : Context.{u} m} {rho : Ren n m}
    {morphism : NativeTraceContextMorphisms.Morphism context destination}
    (displayed : NativeTraceDisplayedSubstitution.Renaming context destination rho morphism) :
    NativeHOLTraceQualifiedExtensionalSemantics.Denotes a destination
      (translate (substituteInto frame (renSub rho) source))
      (morphism.reindexFamily family) (morphism.reindexSection value) := by
  rw [renaming_square]
  exact (translation_preserves meaning).rename displayed

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.DeclaredBindingTraceSemantics
