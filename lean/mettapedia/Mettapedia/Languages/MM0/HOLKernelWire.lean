import Mettapedia.Languages.MM0.HOLKernelSyntax
import Mettapedia.Languages.MM0.HOLSyntaxWire

/-!
# The existing HOL wire syntax and actual MM0 kernel preterms

Name resolution interprets the existing symbolic HOL producer as an MM0
application spine. The comparison covers all source type and term
constructors, retaining the chosen variable positions and binding names.
Names, constants and type parameters are resolved by explicit tables.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelWire

open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax
abbrev Wire := HOLSyntaxWire.Wire

def constructorReference (references : Symbol → Nat) (name : String) : Option Nat :=
  (Symbol.all.find? (fun constructor => constructor.name == name)).map references

theorem constructorReference_name (references : Symbol → Nat) (constructor : Symbol) :
    constructorReference references constructor.name = some (references constructor) := by
  cases constructor <;> simp [constructorReference, Symbol.all, Symbol.name]

mutual

def read (resolveVariable : String → Option Nat) (references : Symbol → Nat) : Wire → Option Preterm
  | .symbol name => (resolveVariable name).map .var
  | .application name arguments => do
      let constructor ← constructorReference references name
      let values ← readList resolveVariable references arguments
      pure (Preterm.applyArgs (.term constructor) values)
  | .string _ | .natural _ => none

def readList (resolveVariable : String → Option Nat) (references : Symbol → Nat) :
    List Wire → Option (List Preterm)
  | [] => some []
  | head :: tail => do
      let value ← read resolveVariable references head
      let values ← readList resolveVariable references tail
      pure (value :: values)

end

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

theorem encodeType_read (resolveVariable : String → Option Nat) (references : Symbol → Nat)
    (baseWire : Base → Wire) (baseCode : Base → Preterm)
    (compatible : ∀ index, read resolveVariable references (baseWire index) = some (baseCode index))
    (source : Ty Base) :
    read resolveVariable references (HOLSyntaxWire.encodeType baseWire source) =
      some (encodeType references baseCode source) := by
  induction source with
  | prop => simp [HOLSyntaxWire.encodeType, read, readList, constructorReference, Symbol.all,
      Symbol.name, encodeType, applySymbol]
  | base index => exact compatible index
  | arr domain result ihd ihr =>
      simp [HOLSyntaxWire.encodeType, read, readList, constructorReference, Symbol.all,
        Symbol.name, ihd, ihr, encodeType, applySymbol]

theorem encodeTerm_read (resolveVariable : String → Option Nat) (references : Symbol → Nat)
    (baseWire : Base → Wire) (baseCode : Base → Preterm)
    (constantWire : ∀ {type}, Const type → Wire) (constantCode : ∀ {type}, Const type → Preterm)
    (fresh : Nat → String) (binders : Nat → Nat)
    (baseCompatible : ∀ index, read resolveVariable references (baseWire index) = some (baseCode index))
    (constantCompatible : ∀ {type} (constant : Const type),
      read resolveVariable references (constantWire constant) = some (constantCode constant))
    {gamma : Ctx Base} {type : Ty Base} (source : Term Const gamma type) :
    ∀ (names : Names gamma) (positions : Positions gamma) (depth : Nat),
      (∀ {type} (index : Var gamma type), resolveVariable (names index) = some (positions index)) →
      (∀ offset < source.binderDepth, resolveVariable (fresh (depth + offset)) = some (binders (depth + offset))) →
      read resolveVariable references (HOLSyntaxWire.encodeTerm baseWire constantWire fresh names depth source) =
        some (encodeTerm references baseCode constantCode binders positions depth source) := by
  induction source with
  | var index =>
      intro names positions depth compatible _
      simp [HOLSyntaxWire.encodeTerm, encodeTerm, read, compatible]
  | const symbol => intro _ _ _ _ _; exact constantCompatible symbol
  | top | bot =>
      intro _ _ _ _ _
      simp [HOLSyntaxWire.encodeTerm, encodeTerm, read, readList, constructorReference,
        Symbol.all, Symbol.name, applySymbol]
  | app first second ihf ihs | and first second ihf ihs | or first second ihf ihs
  | imp first second ihf ihs | eq first second ihf ihs =>
      intro names positions depth compatible bindersCompatible
      have one := ihf names positions depth compatible (fun offset before =>
        bindersCompatible offset (Nat.lt_of_lt_of_le before (Nat.le_max_left _ _)))
      have two := ihs names positions depth compatible (fun offset before =>
        bindersCompatible offset (Nat.lt_of_lt_of_le before (Nat.le_max_right _ _)))
      simp [HOLSyntaxWire.encodeTerm, encodeTerm, read, readList, constructorReference,
        Symbol.all, Symbol.name, one, two, encodeType_read resolveVariable references baseWire baseCode baseCompatible,
        applySymbol]
  | not body ih =>
      intro names positions depth compatible bindersCompatible
      have bodyRead := ih names positions depth compatible bindersCompatible
      simp [HOLSyntaxWire.encodeTerm, encodeTerm, read, readList, constructorReference,
        Symbol.all, Symbol.name, bodyRead, applySymbol]
  | @lam domain gamma result body ih | @all domain gamma body ih | @ex domain gamma body ih =>
      intro names positions depth compatible bindersCompatible
      have head : resolveVariable (fresh depth) = some (binders depth) := by
        simpa only [Nat.add_zero] using bindersCompatible 0 (Nat.zero_lt_succ _)
      have bodyNames : ∀ {type} (index : Var (domain :: gamma) type),
          resolveVariable (Names.lift (fresh depth) names index) =
            some (Positions.extend (binders depth) positions index) := by
        intro type index
        cases index with
        | vz => exact head
        | vs index => exact compatible index
      have bodyBinders : ∀ offset < body.binderDepth,
          resolveVariable (fresh (depth + 1 + offset)) = some (binders (depth + 1 + offset)) := by
        intro offset before
        have found := bindersCompatible (offset + 1) (Nat.add_lt_add_right before 1)
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
      have bodyRead := ih (Names.lift (fresh depth) names)
        (Positions.extend (binders depth) positions) (depth + 1) bodyNames bodyBinders
      simp [HOLSyntaxWire.encodeTerm, encodeTerm, read, readList, constructorReference,
        Symbol.all, Symbol.name, head, bodyRead,
        encodeType_read resolveVariable references baseWire baseCode baseCompatible, applySymbol]

#print axioms encodeType_read
#print axioms encodeTerm_read

end Mettapedia.Languages.MM0.HOLKernelWire
