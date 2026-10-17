import Mettapedia.GSLT.LanguageDef.RegexClassInterpretation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Portable
import Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

/-!
# Typed module presentation of symbolic character classes

The nine class constructors have the scalar-set interpretation proved in
`RegexClassInterpretation`. The equation family below is licensed by that
interpretation, with the simple-fold provider laws as an explicit obligation.
This is an algebra presentation, not an installation of equations into the
host evaluator. Native interval preparation is a realization of the stated
set observation; its implementation is a separate conformance obligation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.RegexClassAuthoring

open Mettapedia.OSLF.MeTTaIL.Syntax
open RegexClassInterpretation
open CettaWire (Term)

def encode : Expr → Term
  | .empty => .application "re:class-empty" []
  | .universe => .application "re:class-universe" []
  | .range low high => .application "re:class-range" [.natural low, .natural high]
  | .property name => .application "re:class-property" [.string name]
  | .union left right => .application "re:class-union" [encode left, encode right]
  | .intersection left right => .application "re:class-intersection" [encode left, encode right]
  | .difference left right => .application "re:class-difference" [encode left, encode right]
  | .complement body => .application "re:class-complement" [encode body]
  | .fold body => .application "re:class-fold" [encode body]

def decode : Term → Option Expr
  | .application "re:class-empty" [] => some .empty
  | .application "re:class-universe" [] => some .universe
  | .application "re:class-range" [.natural low, .natural high] => some (.range low high)
  | .application "re:class-property" [.string name] => some (.property name)
  | .application "re:class-union" [left, right] => do return .union (← decode left) (← decode right)
  | .application "re:class-intersection" [left, right] => do
      return .intersection (← decode left) (← decode right)
  | .application "re:class-difference" [left, right] => do
      return .difference (← decode left) (← decode right)
  | .application "re:class-complement" [body] => .complement <$> decode body
  | .application "re:class-fold" [body] => .fold <$> decode body
  | _ => none
termination_by term => sizeOf term

@[simp] theorem decode_encode (expression : Expr) : decode (encode expression) = some expression := by
  induction expression with
  | empty | «universe» | range | property => simp [encode, decode]
  | union left right before after => simp [encode, decode, before, after]
  | intersection left right before after => simp [encode, decode, before, after]
  | difference left right before after => simp [encode, decode, before, after]
  | complement body ih => simp [encode, decode, ih]
  | fold body ih => simp [encode, decode, ih]

theorem encode_injective : Function.Injective encode := by
  intro first second same
  have decoded := congrArg decode same
  simpa using decoded

inductive Schema where
  | parameter (name : String)
  | empty
  | universe
  | union (left right : Schema)
  | intersection (left right : Schema)
  | difference (left right : Schema)
  | complement (body : Schema)
  | fold (body : Schema)
  deriving DecidableEq, Repr

def Schema.instantiate (environment : String → Expr) : Schema → Expr
  | .parameter name => environment name
  | .empty => .empty
  | .universe => .universe
  | .union left right => .union (left.instantiate environment) (right.instantiate environment)
  | .intersection left right => .intersection (left.instantiate environment) (right.instantiate environment)
  | .difference left right => .difference (left.instantiate environment) (right.instantiate environment)
  | .complement body => .complement (body.instantiate environment)
  | .fold body => .fold (body.instantiate environment)

def Schema.pattern : Schema → Pattern
  | .parameter name => .fvar name
  | .empty => .apply "re:class-empty" []
  | .universe => .apply "re:class-universe" []
  | .union left right => .apply "re:class-union" [left.pattern, right.pattern]
  | .intersection left right => .apply "re:class-intersection" [left.pattern, right.pattern]
  | .difference left right => .apply "re:class-difference" [left.pattern, right.pattern]
  | .complement body => .apply "re:class-complement" [body.pattern]
  | .fold body => .apply "re:class-fold" [body.pattern]

inductive Law where
  | unionEmptyLeft | unionEmptyRight
  | intersectionEmptyLeft | intersectionEmptyRight
  | differenceEmptyRight | differenceEmptyLeft
  | complementEmpty | complementUniverse | complementTwice
  | foldEmpty | foldTwice
  deriving DecidableEq, Repr

def Law.name : Law → String
  | .unionEmptyLeft => "class-union-empty-left"
  | .unionEmptyRight => "class-union-empty-right"
  | .intersectionEmptyLeft => "class-intersection-empty-left"
  | .intersectionEmptyRight => "class-intersection-empty-right"
  | .differenceEmptyRight => "class-difference-empty-right"
  | .differenceEmptyLeft => "class-difference-empty-left"
  | .complementEmpty => "class-complement-empty"
  | .complementUniverse => "class-complement-universe"
  | .complementTwice => "class-complement-twice"
  | .foldEmpty => "class-fold-empty"
  | .foldTwice => "class-fold-twice"

private def p : Schema := .parameter "p"

def Law.sides : Law → Schema × Schema
  | .unionEmptyLeft => (.union .empty p, p)
  | .unionEmptyRight => (.union p .empty, p)
  | .intersectionEmptyLeft => (.intersection .empty p, .empty)
  | .intersectionEmptyRight => (.intersection p .empty, .empty)
  | .differenceEmptyRight => (.difference p .empty, p)
  | .differenceEmptyLeft => (.difference .empty p, .empty)
  | .complementEmpty => (.complement .empty, .universe)
  | .complementUniverse => (.complement .universe, .empty)
  | .complementTwice => (.complement (.complement p), p)
  | .foldEmpty => (.fold .empty, .empty)
  | .foldTwice => (.fold (.fold p), .fold p)

def laws : List Law := [.unionEmptyLeft, .unionEmptyRight,
  .intersectionEmptyLeft, .intersectionEmptyRight, .differenceEmptyRight, .differenceEmptyLeft,
  .complementEmpty, .complementUniverse, .complementTwice, .foldEmpty, .foldTwice]

def Law.equation (law : Law) : Equation where
  name := law.name
  typeContext := [("p", .base "RegexClass")]
  premises := []
  left := law.sides.1.pattern
  right := law.sides.2.pattern

theorem Law.sound (provider : Provider) (foldLaws : FoldLaws provider)
    (law : Law) (environment : String → Expr) :
    meaning provider (law.sides.1.instantiate environment) =
      meaning provider (law.sides.2.instantiate environment) := by
  cases law with
  | complementTwice => exact complement_twice provider (environment "p")
  | foldTwice => exact fold_idempotent provider foldLaws (environment "p")
  | foldEmpty => ext scalar; simp [Law.sides, Schema.instantiate, meaning]
  | unionEmptyLeft | unionEmptyRight | intersectionEmptyLeft | intersectionEmptyRight |
    differenceEmptyRight | differenceEmptyLeft | complementEmpty | complementUniverse =>
      simp [Law.sides, Schema.instantiate, p, meaning]

private def operator (label category : String) (arguments : List (String × String)) : GrammarRule where
  label := label
  category := category
  params := arguments.map fun argument => .simple argument.1 (.base argument.2)
  syntaxPattern := .terminal label :: arguments.map fun argument => .nonTerminal argument.1

def terms : List GrammarRule := [
  operator "re:class-empty" "RegexClass" [],
  operator "re:class-universe" "RegexClass" [],
  operator "re:class-range" "RegexClass" [("low", "ClassScalar"), ("high", "ClassScalar")],
  operator "re:class-property" "RegexClass" [("name", "ClassProperty")],
  operator "re:class-union" "RegexClass" [("left", "RegexClass"), ("right", "RegexClass")],
  operator "re:class-intersection" "RegexClass" [("left", "RegexClass"), ("right", "RegexClass")],
  operator "re:class-difference" "RegexClass" [("left", "RegexClass"), ("right", "RegexClass")],
  operator "re:class-complement" "RegexClass" [("body", "RegexClass")],
  operator "re:class-fold" "RegexClass" [("body", "RegexClass")]]

def theory : LanguageDef where
  name := "RegexClassAlgebraV1"
  types := [⟨"ClassScalar", .builtinInt⟩, ⟨"ClassProperty", .builtinString⟩, "RegexClass"]
  terms := terms
  equations := laws.map Law.equation
  rewrites := []

open scoped Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

def authored : LanguageDef := languageDef! {
  name : "RegexClassAlgebraV1"
  types { ![i64] as ClassScalar ![str] as ClassProperty RegexClass }
  terms {
    «re:class-empty». |- "re:class-empty" : RegexClass;
    «re:class-universe». |- "re:class-universe" : RegexClass;
    «re:class-range». low:ClassScalar, high:ClassScalar |- "re:class-range" low high : RegexClass;
    «re:class-property». «name»:ClassProperty |- "re:class-property" «name» : RegexClass;
    «re:class-union». left:RegexClass, right:RegexClass |- "re:class-union" left right : RegexClass;
    «re:class-intersection». left:RegexClass, right:RegexClass |-
      "re:class-intersection" left right : RegexClass;
    «re:class-difference». left:RegexClass, right:RegexClass |-
      "re:class-difference" left right : RegexClass;
    «re:class-complement». body:RegexClass |- "re:class-complement" body : RegexClass;
    «re:class-fold». body:RegexClass |- "re:class-fold" body : RegexClass;
  }
  equations {
    «class-union-empty-left». p:RegexClass |-
      "re:class-union"("re:class-empty"(), p) = p;
    «class-union-empty-right». p:RegexClass |-
      "re:class-union"(p, "re:class-empty"()) = p;
    «class-intersection-empty-left». p:RegexClass |-
      "re:class-intersection"("re:class-empty"(), p) = "re:class-empty"();
    «class-intersection-empty-right». p:RegexClass |-
      "re:class-intersection"(p, "re:class-empty"()) = "re:class-empty"();
    «class-difference-empty-right». p:RegexClass |-
      "re:class-difference"(p, "re:class-empty"()) = p;
    «class-difference-empty-left». p:RegexClass |-
      "re:class-difference"("re:class-empty"(), p) = "re:class-empty"();
    «class-complement-empty». p:RegexClass |-
      "re:class-complement"("re:class-empty"()) = "re:class-universe"();
    «class-complement-universe». p:RegexClass |-
      "re:class-complement"("re:class-universe"()) = "re:class-empty"();
    «class-complement-twice». p:RegexClass |-
      "re:class-complement"("re:class-complement"(p)) = p;
    «class-fold-empty». p:RegexClass |-
      "re:class-fold"("re:class-empty"()) = "re:class-empty"();
    «class-fold-twice». p:RegexClass |-
      "re:class-fold"("re:class-fold"(p)) = "re:class-fold"(p);
  }
  rewrites {}
}

theorem authored_exact : authored = theory := by rfl

theorem every_equation_sound (provider : Provider) (foldLaws : FoldLaws provider)
    (equation : Equation) (member : equation ∈ theory.equations) :
    ∃ law ∈ laws, equation = law.equation ∧ ∀ environment : String → Expr,
      meaning provider (law.sides.1.instantiate environment) =
        meaning provider (law.sides.2.instantiate environment) := by
  obtain ⟨law, inLaws, same⟩ := List.mem_map.mp member
  exact ⟨law, inLaws, same.symm, Law.sound provider foldLaws law⟩

def portable : Term := Portable.coreCodec.encode theory

theorem portable_recovery : Portable.coreCodec.decode portable = some authored := by
  rw [authored_exact]
  exact Portable.coreCodec.decode_encode theory

namespace Controls

theorem class_codec_retains_negation_outside_fold :
    decode (encode (.complement (.fold (.property "gc=Nd")))) =
      some (.complement (.fold (.property "gc=Nd"))) := decode_encode _

theorem class_codec_retains_set_operations :
    decode (encode (.difference (.property "Alphabetic") (.range 65 90))) =
      some (.difference (.property "Alphabetic") (.range 65 90)) := decode_encode _

theorem fold_order_is_not_erased_by_codec :
    encode (.fold (.complement (.range 97 97))) ≠ encode (.complement (.fold (.range 97 97))) := by
  intro equal
  have impossible := encode_injective equal
  cases impossible

theorem unknown_constructor_is_not_an_empty_class :
    decode (.application "re:unknown-class" []) = none := by simp [decode]

end Controls

#print axioms decode_encode
#print axioms Law.sound
#print axioms every_equation_sound
#print axioms portable_recovery

end Mettapedia.GSLT.LanguageDef.ModuleFormat.RegexClassAuthoring
