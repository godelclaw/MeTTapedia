import Mettapedia.GSLT.LanguageDef.WellSorted
import Mathlib.Logic.Relation

open Mettapedia.OSLF.Framework

/-!
# Constructor-generated structural type formers

Every authored constructor contributes a former, retaining its declaration
position. Its meaning is the image, in the equation quotient, of the typed
constructor introduction. Binding parameters use the existing ordered typing
judgment; bare collection constructors use their declared representation.
No invariant representative root is assumed when equations change roots.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Structural

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- An authored position and the declaration found there. -/
structure Former where
  index : Nat
  declaration : GrammarRule
  deriving Repr, DecidableEq

/-- One former per declaration, including distinct repeated declarations. -/
def structuralFormers (language : LanguageDef) : List Former :=
  language.terms.zipIdx.map fun entry => ⟨entry.2, entry.1⟩

theorem mem_structuralFormers_iff (language : LanguageDef) (former : Former) :
    former ∈ structuralFormers language ↔
      language.terms[former.index]? = some former.declaration := by
  simp only [structuralFormers, List.mem_map]
  constructor
  · rintro ⟨⟨declaration, index⟩, member, equal⟩
    cases equal
    exact (List.mem_zipIdx_iff_getElem?).mp member
  · intro lookup
    exact ⟨(former.declaration, former.index),
      (List.mem_zipIdx_iff_getElem?).mpr lookup, by cases former; rfl⟩

theorem structuralFormers_length (language : LanguageDef) :
    (structuralFormers language).length = language.terms.length := by
  simp [structuralFormers]

/-- The actual typed introduction of one declaration, before taking equations.
Binder representation and parameter order are checked by `ArgumentsHaveTypes`.
-/
inductive ConstructorValue (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (declaration : GrammarRule) : Type where
  | ordinary (arguments : List Pattern)
      (ordinary : ¬ UsesBareCollection declaration)
      (typed : ArgumentsHaveTypes language free bound arguments declaration.params)
  | collection (parameterName : String) (kind : CollType) (elementType : TypeExpr)
      (elements : List Pattern) (rest : Option String)
      (shape : declaration.params =
        [.simple parameterName (.collection kind elementType)])
      (typed : ElementsHaveType language free bound elements elementType)

namespace ConstructorValue

variable {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {declaration : GrammarRule}

def pattern : ConstructorValue language free bound declaration → Pattern
  | .ordinary arguments _ _ => .apply declaration.label arguments
  | .collection _ kind _ elements rest _ _ => .collection kind elements rest

/-- A bare collection realizes the one declared collection-valued parameter. -/
def arguments : ConstructorValue language free bound declaration → List Pattern
  | .ordinary arguments _ _ => arguments
  | .collection _ kind _ elements rest _ _ => [.collection kind elements rest]

theorem typed (value : ConstructorValue language free bound declaration)
    (member : declaration ∈ language.terms) :
    HasType language free bound value.pattern (.base declaration.category) := by
  cases value with
  | ordinary arguments ordinary typed => exact .constructor member ordinary typed
  | collection parameterName kind elementType elements rest shape typed =>
      exact .collectionConstructor member shape typed

theorem arguments_typed (value : ConstructorValue language free bound declaration) :
    ArgumentsHaveTypes language free bound value.arguments declaration.params := by
  cases value with
  | ordinary arguments ordinary typed => exact typed
  | collection parameterName kind elementType elements rest shape typed =>
      rw [shape]
      exact .cons trivial rfl (.collection typed) .nil

theorem arguments_length (value : ConstructorValue language free bound declaration) :
    value.arguments.length = declaration.params.length := by
  exact value.arguments_typed.length_eq

end ConstructorValue

/-- Structural membership is the typed constructor image modulo the actual
equations. Equal representatives may have different syntactic roots. -/
def StructuralHolds (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (equation : Pattern → Pattern → Prop)
    (former : Former) (term : Pattern) : Prop :=
  former ∈ structuralFormers language ∧
    ∃ value : ConstructorValue language free bound former.declaration,
      equation term value.pattern

/-- Membership classifies exactly the typed constructor image; this follows
from the enumeration and introductions, rather than an authored root table. -/
theorem structural_former_exact (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (equation : Pattern → Pattern → Prop)
    (former : Former) (term : Pattern) :
    StructuralHolds language free bound equation former term ↔
      language.terms[former.index]? = some former.declaration ∧
      ((∃ arguments, ¬ UsesBareCollection former.declaration ∧
          ArgumentsHaveTypes language free bound arguments former.declaration.params ∧
          equation term (.apply former.declaration.label arguments)) ∨
        ∃ parameterName kind elementType elements rest,
          former.declaration.params =
            [.simple parameterName (.collection kind elementType)] ∧
          ElementsHaveType language free bound elements elementType ∧
          equation term (.collection kind elements rest)) := by
  rw [StructuralHolds, mem_structuralFormers_iff]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨value, related⟩
    cases value with
    | ordinary arguments ordinary typed => exact Or.inl ⟨arguments, ordinary, typed, related⟩
    | collection parameterName kind elementType elements rest shape typed =>
        exact Or.inr ⟨parameterName, kind, elementType, elements, rest, shape, typed, related⟩
  · rintro (⟨arguments, ordinary, typed, related⟩ |
      ⟨parameterName, kind, elementType, elements, rest, shape, typed, related⟩)
    · exact ⟨.ordinary arguments ordinary typed, related⟩
    · exact ⟨.collection parameterName kind elementType elements rest shape typed, related⟩

theorem structural_equation_invariant {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {equation : Pattern → Pattern → Prop}
    (laws : Equivalence equation) (former : Former) {left right : Pattern}
    (related : equation left right) :
    StructuralHolds language free bound equation former left ↔
      StructuralHolds language free bound equation former right := by
  constructor
  · rintro ⟨member, value, witness⟩
    exact ⟨member, value, laws.trans (laws.symm related) witness⟩
  · rintro ⟨member, value, witness⟩
    exact ⟨member, value, laws.trans related witness⟩

/-- With no equations and an ordinary declaration, the structural former is
the positional typed constructor root. -/
theorem structural_free_root {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {former : Former} (member : former ∈ structuralFormers language)
    (ordinary : ¬ UsesBareCollection former.declaration) (term : Pattern) :
    StructuralHolds language free bound Eq former term ↔
      ∃ arguments, term = .apply former.declaration.label arguments ∧
        ArgumentsHaveTypes language free bound arguments former.declaration.params := by
  constructor
  · rintro ⟨_, value, equation⟩
    cases value with
    | ordinary arguments _ typed => exact ⟨arguments, equation, typed⟩
    | collection parameterName kind elementType elements rest shape typed =>
        exact False.elim (ordinary ⟨parameterName, kind, elementType, shape⟩)
  · rintro ⟨arguments, equal, typed⟩
    exact ⟨member, .ordinary arguments ordinary typed, equal⟩

end Mettapedia.OSLF.NativeTypes.Structural
