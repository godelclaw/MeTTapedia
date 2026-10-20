import Mettapedia.Languages.OpenTheory.Syntax
import Mettapedia.GSLT.LanguageDef.CettaWireTerm

/-!
# The equality index of HOL abstraction/representation

The source contracts are `abs : A → N`, `rep : N → A` and `a : N`.
Their roundtrip has type `N`. The maintained source checker therefore accepts
its equality at `N` and rejects equality at `A` when those types differ.

This is a typing comparison for the displayed source formula. It does not
establish inconsistency of an untyped presentation or a refinement theorem
for the MM0 compiler. A concrete source/native declaration comparison must
retain the supplied presentation and its assumptions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLTypeDefinitionBoundary

open Mettapedia.Languages.OpenTheory

def boolean : Ty := .op (.mk (Name.global "bool") .undefined) []

def value (defined : Ty) : SourceTerm := .var (Name.global "a") defined

def roundtrip (representation defined : Ty) : SourceTerm :=
  .app (.var (Name.global "abs") (.function representation defined))
    (.app (.var (Name.global "rep") (.function defined representation)) (value defined))

def equation (index : Ty) (left right : SourceTerm) : SourceTerm :=
  .app (.app (.const (.mk (Name.global "=") .undefined)
    (.function index (.function index boolean))) left) right

theorem roundtrip_typed (representation defined : Ty) :
    (roundtrip representation defined).inferType = some defined := by
  simp [roundtrip, value, SourceTerm.inferType]

/-- Equality at the actual operand type is accepted by the independent
source checker for arbitrary representation and defined types. -/
theorem defined_equality_typed (representation defined : Ty) :
    (equation defined (roundtrip representation defined) (value defined)).inferType =
      some boolean := by
  simp [equation, value, SourceTerm.inferType, roundtrip_typed]

theorem representation_equality_refused (representation defined : Ty)
    (different : representation ≠ defined) :
    (equation representation (roundtrip representation defined) (value defined)).inferType =
      none := by
  simp [equation, value, SourceTerm.inferType, roundtrip_typed, different]

theorem defined_equality_checked (representation defined : Ty) :
    (equation defined (roundtrip representation defined) (value defined)).check ≠ none := by
  intro refused
  have failure := (SourceTerm.check_eq_none_iff _).mp refused
  rw [defined_equality_typed] at failure
  cases failure

theorem representation_equality_check_refused (representation defined : Ty)
    (different : representation ≠ defined) :
    (equation representation (roundtrip representation defined) (value defined)).check = none :=
  (SourceTerm.check_eq_none_iff _).mpr (representation_equality_refused _ _ different)

def distinctDefined : Ty := .function boolean boolean

theorem distinct_types : boolean ≠ distinctDefined := by
  intro equal
  have lengths := congrArg (fun type => match type with
    | Ty.var _ => 0
    | Ty.op _ arguments => arguments.length) equal
  cases lengths

/-- Independent native-statement reference. The compiler and native source
decoder must agree on the complete declaration, including its original
premises. Printing this data grants no theorem authority. -/
def definitionStatement : String :=
  let conclusion : Mettapedia.GSLT.LanguageDef.CettaWire.Term :=
    .application "im" [
      .application "an" [.symbol "G", .application "ty" [.symbol "a",
        .application "tydef" [.symbol "P"]]],
      .application "thm" [.application "eqc" [
        .application "tydef" [.symbol "P"],
        .application "app" [.application "abs" [.symbol "P"],
          .application "app" [.application "rep" [.symbol "P"], .symbol "a"]],
        .symbol "a"]]]
  "(axiom abs_rep ((var G wff ()) (var A type ()) (var P term ()) " ++
    "(var t term ()) (var a term ())) " ++
    "((im (thm (T)) (ty P (fun A (bool)))) (im G (thm (app P t)))) " ++
    conclusion.render ++ ")"

def verdicts : List (String × Bool) := [
  ("abstraction-representation roundtrip retains defined type",
    (roundtrip boolean distinctDefined).inferType.isSome),
  ("defined-type equality passes the maintained source checker",
    (equation distinctDefined (roundtrip boolean distinctDefined) (value distinctDefined)).check.isSome),
  ("representation-type equality refuses for distinct types",
    (equation boolean (roundtrip boolean distinctDefined) (value distinctDefined)).check.isNone)]

theorem all_verdicts : verdicts.all Prod.snd = true := by decide +kernel

end Mettapedia.Languages.MM0.HOLTypeDefinitionBoundary
