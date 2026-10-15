import Mettapedia.OSLF.NativeTypes.Structural.Formers
import Mettapedia.GSLT.LanguageDef.EquationSemantics

open Mettapedia.OSLF.Framework

/-!
# Spatial formers recovered from authored collection declarations

A self-sorted hash-bag constructor with a flattening declaration supplies a
spatial join. Its parameter, algebra and optional unit are checked against
the original grammar. The join uses the actual bare collection carrier.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Structural

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics

structure SpatialShape where
  parameterName : String
  algebra : CollectionAlgebra
  deriving DecidableEq, Repr

def unitAuthored? (language : LanguageDef) (declaration : GrammarRule)
    (algebra : CollectionAlgebra) : Bool :=
  match algebra.unit with
  | none => true
  | some unit => language.terms.any fun candidate =>
      candidate.label == unit && candidate.category == declaration.category &&
        candidate.params.isEmpty

def spatialShape? (language : LanguageDef) (declaration : GrammarRule) : Option SpatialShape :=
  match declaration.params, declaration.algebra? with
  | [.simple name (.collection .hashBag (.base category))], some algebra =>
      if category == declaration.category && algebra.flatten &&
          unitAuthored? language declaration algebra then some ⟨name, algebra⟩ else none
  | _, _ => none

theorem unitAuthored?_sound {language : LanguageDef} {declaration : GrammarRule}
    {algebra : CollectionAlgebra} (checked : unitAuthored? language declaration algebra = true) :
    ∀ unit, algebra.unit = some unit →
      ∃ unitRule ∈ language.terms, unitRule.label = unit ∧
        unitRule.category = declaration.category ∧ unitRule.params = [] := by
  intro unit equal
  simp only [unitAuthored?, equal, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
    List.isEmpty_iff] at checked
  rcases checked with ⟨unitRule, member, ⟨label, category⟩, params⟩
  exact ⟨unitRule, member, label, category, params⟩

theorem spatialShape?_sound {language : LanguageDef} {declaration : GrammarRule}
    {shape : SpatialShape} (checked : spatialShape? language declaration = some shape) :
    declaration.params = [.simple shape.parameterName
      (.collection .hashBag (.base declaration.category))] ∧
      declaration.algebra? = some shape.algebra ∧ shape.algebra.flatten = true ∧
      unitAuthored? language declaration shape.algebra = true := by
  unfold spatialShape? at checked
  split at checked
  · rename_i name category algebra params declared
    split at checked
    · rename_i enabled
      simp only [Bool.and_eq_true, beq_iff_eq] at enabled
      cases checked
      rcases enabled with ⟨⟨same, flatten⟩, unit⟩
      exact ⟨by simpa [same] using params, declared, flatten, unit⟩
    · cases checked
  · cases checked

theorem spatialShape?_algebraRule {language : LanguageDef} {former : Former}
    (member : former ∈ structuralFormers language) {shape : SpatialShape}
    (checked : spatialShape? language former.declaration = some shape) :
    AlgebraRule language former.declaration .hashBag shape.algebra := by
  obtain ⟨params, declared, _, unit⟩ := spatialShape?_sound checked
  exact ⟨List.mem_of_getElem? ((mem_structuralFormers_iff _ _).mp member), declared,
    ⟨shape.parameterName, params⟩, unitAuthored?_sound unit⟩

/-- The real typed binary join of two process values in the bag carrier. -/
def SpatialHolds (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (equation : Pattern → Pattern → Prop)
    (former : Former) (first second : Pattern → Prop) (term : Pattern) : Prop :=
  former ∈ structuralFormers language ∧
    ∃ shape, spatialShape? language former.declaration = some shape ∧
      ∃ left right, HasType language free bound left (.base former.declaration.category) ∧
        HasType language free bound right (.base former.declaration.category) ∧
        equation term (.collection .hashBag [left, right] none) ∧ first left ∧ second right

theorem spatial_equation_invariant {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {equation : Pattern → Pattern → Prop}
    (laws : Equivalence equation) (former : Former) (first second : Pattern → Prop)
    {left right : Pattern} (related : equation left right) :
    SpatialHolds language free bound equation former first second left ↔
      SpatialHolds language free bound equation former first second right := by
  constructor
  · rintro ⟨member, shape, checked, a, b, aType, bType, witness, firstHolds, secondHolds⟩
    exact ⟨member, shape, checked, a, b, aType, bType,
      laws.trans (laws.symm related) witness, firstHolds, secondHolds⟩
  · rintro ⟨member, shape, checked, a, b, aType, bType, witness, firstHolds, secondHolds⟩
    exact ⟨member, shape, checked, a, b, aType, bType,
      laws.trans related witness, firstHolds, secondHolds⟩

end Mettapedia.OSLF.NativeTypes.Structural
