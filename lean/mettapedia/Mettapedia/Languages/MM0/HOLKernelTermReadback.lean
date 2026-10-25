import Mettapedia.Languages.MM0.HOLKernelSyntax
import Mettapedia.Logic.HOL.Syntax.NamedContexts

/-!
# Intrinsic HOL syntax reconstructed from native MM0 application spines

The reader is parameterized by a constant lookup and the regular-parameter
prefix length. It retains typed variable lookup and explicit binder names,
checks applications and equality annotations, and refuses parameter capture.
The single distinguished base sort is represented by regular type parameter
zero. No semantic model or source proof is an input.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelTermReadback
open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax
open NamedElaboration (BinderNames SomeTerm)

universe u
variable {Const : Ty Unit → Type u}

abbrev Names (gamma : Ctx Unit) := BinderNames Unit Nat gamma
abbrev Decoded (Const : Ty Unit → Type u) (gamma : Ctx Unit) := SomeTerm Const gamma

def readHead (references : HOLKernelSyntax.Symbol → Nat) (index : Nat) :
    Option HOLKernelSyntax.Symbol :=
  HOLKernelSyntax.Symbol.all.find? (fun constructor => references constructor == index)

theorem readHead_reference (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references) (constructor : HOLKernelSyntax.Symbol) :
    readHead references (references constructor) = some constructor := by
  unfold readHead
  have predicates : (fun other => references other == references constructor) =
      (fun other => other == constructor) := by
    funext other
    apply Bool.eq_iff_iff.mpr
    simpa only [beq_iff_eq] using faithful.eq_iff
  rw [predicates]
  cases constructor <;> decide

theorem readHead_sound (references : HOLKernelSyntax.Symbol → Nat) (index : Nat)
    (constructor : HOLKernelSyntax.Symbol) (found : readHead references index = some constructor) :
    references constructor = index := by
  have matched : (references constructor == index) = true :=
    List.find?_some (p := fun candidate => references candidate == index) (a := constructor) found
  exact eq_of_beq matched

def readType (references : HOLKernelSyntax.Symbol → Nat) : Preterm → Option (Ty Unit)
  | .var 0 => some (.base ())
  | .term index => if readHead references index = some .bool then some .prop else none
  | .app (.app (.term index) domain) codomain => do
      if readHead references index = some .function then
        pure (.arr (← readType references domain) (← readType references codomain))
      else none
  | _ => none


/-- Every decoded type reproduces its submitted preterm, including its
actual constructor references and the distinguished regular type parameter. -/
theorem readType_sound (references : HOLKernelSyntax.Symbol → Nat) (native : Preterm)
    (type : Ty Unit) (found : readType references native = some type) :
    encodeType references (fun _ : Unit => Preterm.var 0) type = native := by
  cases native with
  | var index =>
      cases index with
      | zero =>
          have same : Ty.base () = type := by simpa [readType] using found
          subst type
          rfl
      | succ index => simp [readType] at found
  | term index =>
      by_cases head : readHead references index = some .bool
      · have same : Ty.prop = type := by simpa [readType, head] using found
        subst type
        simp only [encodeType, applySymbol, Preterm.applyArgs]
        exact congrArg Preterm.term (readHead_sound references index .bool head)
      · simp [readType, head] at found
  | app function argument =>
      cases function with
      | var index => simp [readType] at found
      | term index => simp [readType] at found
      | app head domain =>
          cases head with
          | var index => simp [readType] at found
          | app head value => simp [readType] at found
          | term index =>
              by_cases constructor : readHead references index = some .function
              · cases left : readType references domain with
                | none => simp [readType, constructor, left] at found
                | some domainType =>
                    cases right : readType references argument with
                    | none => simp [readType, constructor, left, right] at found
                    | some codomainType =>
                        have same : Ty.arr domainType codomainType = type := by
                          simpa [readType, constructor, left, right] using found
                        subst type
                        simp only [encodeType, applySymbol, Preterm.applyArgs,
                          readType_sound references domain domainType left,
                          readType_sound references argument codomainType right,
                          readHead_sound references index .function constructor]
              · simp [readType, constructor] at found
termination_by sizeOf native

def expect {gamma : Ctx Unit} (type : Ty Unit) (decoded : Decoded Const gamma) :
    Option (Term Const gamma type) :=
  (NamedElaboration.expectType (VarName := Nat) (ConstName := Nat) type decoded).toOption

@[simp] theorem expect_same {gamma : Ctx Unit} {type : Ty Unit} (term : Term Const gamma type) :
    expect type ⟨type, term⟩ = some term := by
  simp only [expect, NamedElaboration.expectType_same]
  rfl

def readVariable (constants : Nat → Option (NamedElaboration.SomeConst Const)) {gamma : Ctx Unit} (names : Names gamma) (index : Nat) : Option (Decoded Const gamma) :=
  match names.lookup? index with
  | some resolved => some ⟨resolved.1, .var resolved.2⟩
  | none => (constants index).map fun resolved => ⟨resolved.1, .const resolved.2⟩

def application {gamma : Ctx Unit} (function argument : Decoded Const gamma) : Option (Decoded Const gamma) :=
  match function with
  | ⟨.arr domain codomain, term⟩ => (expect domain argument).map fun value => ⟨codomain, .app term value⟩
  | _ => none

def logicalBinary {gamma : Ctx Unit}
    (constructor : Formula Const gamma → Formula Const gamma → Formula Const gamma)
    (first second : Decoded Const gamma) : Option (Decoded Const gamma) := do
  pure ⟨.prop, constructor (← expect .prop first) (← expect .prop second)⟩

def readTermWith
    (extras : {gamma : Ctx Unit} → Preterm → Option (Decoded Const gamma)) (references : HOLKernelSyntax.Symbol → Nat)
    (constants : Nat → Option (NamedElaboration.SomeConst Const)) (parameters : Nat) :
    {gamma : Ctx Unit} → Names gamma → Preterm → Option (Decoded Const gamma)
  | _, names, .var index => readVariable constants names index
  | _, _, .term index =>
      match readHead references index with
      | some .truth => some ⟨.prop, .top⟩
      | some .falsity => some ⟨.prop, .bot⟩
      | _ => extras (.term index)
  | _, names, .app (.term index) body => do
      if readHead references index = some .notc then
        pure ⟨.prop, .not (← expect .prop (← readTermWith extras references constants parameters names body))⟩
      else extras (.app (.term index) body)
  | _, names, .app (.app (.term index) first) second => do
      let first' ← readTermWith extras references constants parameters names first
      let second' ← readTermWith extras references constants parameters names second
      match readHead references index with
      | some .app => application first' second'
      | some .andc => logicalBinary .and first' second'
      | some .orc => logicalBinary .or first' second'
      | some .impc => logicalBinary .imp first' second'
      | _ => none
  | _, names, .app (.app (.app (.term index) first) second) third => do
      match readHead references index with
      | some .eqc =>
          match readType references first with
          | none => none
          | some type => do
              let left ← expect type (← readTermWith extras references constants parameters names second)
              let right ← expect type (← readTermWith extras references constants parameters names third)
              pure ⟨.prop, .eq left right⟩
      | some .lam | some .allc | some .exc =>
          let .var binder := first | none
          if binder < parameters then none else do
            match readType references second with
            | none => none
            | some domain => do
                let body ← readTermWith extras references constants parameters (BinderNames.cons (type := domain) binder names) third
                match readHead references index with
                | some .lam => pure ⟨.arr domain body.type, .lam body.term⟩
                | some .allc => pure ⟨.prop, .all (← expect .prop body)⟩
                | some .exc => pure ⟨.prop, .ex (← expect .prop body)⟩
                | _ => none
      | _ => none
  | _, _, _ => none
termination_by _ _ term => sizeOf term




abbrev TermReader (Const : Ty Unit → Type u) :=
  {gamma : Ctx Unit} → Names gamma → Preterm → Option (Decoded Const gamma)

def readTerm (references : HOLKernelSyntax.Symbol → Nat)
    (constants : Nat → Option (NamedElaboration.SomeConst Const)) (parameters : Nat) :
    TermReader Const :=
  readTermWith (fun {_} _ => none) references constants parameters


def readObjectWith {gamma : Ctx Unit} (reader : TermReader Const)
    (names : Names gamma) (type : Ty Unit) (native : Preterm) :
    Option (Term Const gamma type) := do
  expect type (← reader names native)

def readFormula (references : HOLKernelSyntax.Symbol → Nat)
    (constants : Nat → Option (NamedElaboration.SomeConst Const)) (parameters : Nat) {gamma : Ctx Unit}
    (names : Names gamma) (native : Preterm) : Option (Formula Const gamma) := do
  expect .prop (← readTerm references constants parameters names native)

#print axioms readHead_sound
#print axioms readType_sound
#print axioms readHead_reference
end Mettapedia.Languages.MM0.HOLKernelTermReadback
