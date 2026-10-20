import Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
import Mettapedia.OSLF.NativeTypes.Semantics.Structural.Propositional

open Mettapedia.OSLF.Framework

/-!
# Decisions for generated propositional native meanings

The executable formula is obtained by recursive translation of the existing
expression syntax. A single interpreted domain guard restores domain-relative
implication and complement. The comparison is derived from formation and
primitive leaf interpretation; no composite comparison is an interface law.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Reference.Propositional

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Generation (Generated)
open Mettapedia.OSLF.NativeTypes.SortProfiles.Source (LeafCodes leafCarriers leafSorts)
open Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodes (Expression Formed rawMeaning Refusal)
open Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes (Model)
open Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeIntroduction (EquationsInterpreted)
open Mettapedia.OSLF.NativeTypes.Semantics.Structural (theory)
open ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core

namespace Native
export Mettapedia.OSLF.NativeTypes.Semantics.Structural.Propositional
  (LeafEquationsInterpreted leaf_equation_transport denotation denotation_comparison
    Family family_support compile compilation_sound)
end Native

/-- The only semantic input comparisons concern the actual domain and
individual leaves at their declared carrier and sort. -/
structure Atoms {generated : Generated} (model : Model generated) (bound : List TypeExpr)
    (leaves : LeafCodes generated bound) (carrier : TypeExpr) (sort : HSort)
    (admitted : Pattern → Prop) where
  domain : Test (theory generated bound carrier) admitted
  leaf : Nat → Test (theory generated bound carrier) admitted
  domain_exact : ∀ source, domain.predicate source ↔ (model bound).sortDomain carrier sort source
  leaf_exact : ∀ index, leafCarriers leaves index = carrier → leafSorts leaves index = sort →
    ∀ source, (model bound).sortDomain carrier sort source →
      ((leaf index).predicate source ↔ (leaves index).2.2.meaning source)

def Atoms.tests {generated : Generated} {model : Model generated} {bound : List TypeExpr}
    {leaves : LeafCodes generated bound} {carrier : TypeExpr} {sort : HSort} {admitted : Pattern → Prop}
    (atoms : Atoms model bound leaves carrier sort admitted) :
    Option Nat → Test (theory generated bound carrier) admitted
  | none => atoms.domain
  | some index => atoms.leaf index

/-- Executable observations for actual type-code leaves, before expression
translation. Primitive equation interpretation separately proves invariance. -/
structure BooleanAtoms {generated : Generated} (model : Model generated) (bound : List TypeExpr)
    (leaves : LeafCodes generated bound) (carrier : TypeExpr) (sort : HSort) where
  domain : Pattern → Bool
  domain_exact : ∀ source, domain source = true ↔ (model bound).sortDomain carrier sort source
  leaf : Nat → Pattern → Bool
  leaf_exact : ∀ index source, leaf index source = true ↔ (leaves index).2.2.meaning source

def interpretedLeaf {generated : Generated} {bound : List TypeExpr}
    {leaves : LeafCodes generated bound} (equations : Native.LeafEquationsInterpreted bound leaves)
    (carrier : TypeExpr) (index : Nat) (carried : leafCarriers leaves index = carrier) :
    GSLTTypeSynthesis.EquationPredicate (theory generated bound carrier) where
  val source := (leaves index).2.2.meaning source
  property := by
    intro first second related
    apply Native.leaf_equation_transport equations index
    change Relation.EqvGen (Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics.Equation
      generated.plan bound carrier) first second at related
    simpa only [carried] using related

def Atoms.ofBoolean {generated : Generated} {model : Model generated} (equations : EquationsInterpreted model)
    {bound : List TypeExpr} {leaves : LeafCodes generated bound}
    (leafEquations : Native.LeafEquationsInterpreted bound leaves) {carrier : TypeExpr} {sort : HSort}
    (observations : BooleanAtoms model bound leaves carrier sort) (admitted : Pattern → Prop) :
    Atoms model bound leaves carrier sort admitted where
  domain := Test.ofBoolean (Mettapedia.OSLF.NativeTypes.Semantics.Structural.sortPredicate model equations bound carrier sort)
    observations.domain observations.domain_exact
  leaf index :=
    if carried : leafCarriers leaves index = carrier then
      Test.ofBoolean (interpretedLeaf leafEquations carrier index carried)
        (observations.leaf index) (observations.leaf_exact index)
    else Test.ofBoolean ⟨fun _ => False, by intro _ _ _; rfl⟩ (fun _ => false)
      (fun _ => by simp only [Bool.false_eq_true, iff_self])
  domain_exact _ := Iff.rfl
  leaf_exact index carried _kinded _source _domain := by
    simp only [dif_pos carried]
    exact Iff.rfl

def translateRaw : Expression → Formula (Option Nat)
  | .leaf index => .atom (some index)
  | .top => .top
  | .bottom => .bottom
  | .conjunction first second => .conj (translateRaw first) (translateRaw second)
  | .disjunction first second => .disj (translateRaw first) (translateRaw second)
  | .implication first second => .imp (translateRaw first) (translateRaw second)
  | .negation inner => .neg (translateRaw inner)

def translate (expression : Expression) : Formula (Option Nat) :=
  .conj (.atom none) (translateRaw expression)

theorem raw_translation_comparison {generated : Generated} {model : Model generated}
    {bound : List TypeExpr} {leaves : LeafCodes generated bound} {carrier : TypeExpr} {sort : HSort}
    {admitted : Pattern → Prop} (atoms : Atoms model bound leaves carrier sort admitted)
    {expression : Expression}
    (formed : Formed generated.logicFragment (leafCarriers leaves) (leafSorts leaves) carrier sort expression)
    (source : Pattern) (domain : (model bound).sortDomain carrier sort source)
    (spatial : Mettapedia.OSLF.NativeTypes.Decision.Spatial.SpatialTheory (theory generated bound carrier) := .empty _) :
    Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.denotation atoms.tests (translateRaw expression) spatial source ↔
      rawMeaning leaves expression source := by
  induction formed with
  | leaf index carried kinded => exact atoms.leaf_exact index carried kinded source domain
  | top _ => exact Iff.rfl
  | bottom _ => exact Iff.rfl
  | conjunction _ _ _ first second => exact and_congr first second
  | disjunction _ _ _ first second => exact or_congr first second
  | implication _ _ _ first second => exact imp_congr first second
  | negation _ _ inner => exact not_congr inner

theorem translation_comparison {generated : Generated} {model : Model generated}
    {bound : List TypeExpr} {leaves : LeafCodes generated bound} {carrier : TypeExpr} {sort : HSort}
    {admitted : Pattern → Prop} (atoms : Atoms model bound leaves carrier sort admitted)
    {expression : Expression}
    (formed : Formed generated.logicFragment (leafCarriers leaves) (leafSorts leaves) carrier sort expression)
    (source : Pattern)
    (spatial : Mettapedia.OSLF.NativeTypes.Decision.Spatial.SpatialTheory (theory generated bound carrier) := .empty _) :
    Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.denotation atoms.tests (translate expression) spatial source ↔
      (model bound).sortDomain carrier sort source ∧ rawMeaning leaves expression source := by
  change (atoms.domain.predicate source ∧ _ ) ↔ _
  constructor
  · rintro ⟨within, holds⟩
    have domain := (atoms.domain_exact source).mp within
    exact ⟨domain, (raw_translation_comparison atoms formed source domain spatial).mp holds⟩
  · rintro ⟨domain, holds⟩
    exact ⟨(atoms.domain_exact source).mpr domain,
      (raw_translation_comparison atoms formed source domain spatial).mpr holds⟩

theorem native_comparison {generated : Generated} {model : Model generated}
    (equations : EquationsInterpreted model) {bound : List TypeExpr} {leaves : LeafCodes generated bound}
    (leafEquations : Native.LeafEquationsInterpreted bound leaves) {carrier : TypeExpr} {sort : HSort}
    {admitted : Pattern → Prop} (atoms : Atoms model bound leaves carrier sort admitted)
    {expression : Expression}
    (formed : Formed generated.logicFragment (leafCarriers leaves) (leafSorts leaves) carrier sort expression)
    (source : Pattern)
    (spatial : Mettapedia.OSLF.NativeTypes.Decision.Spatial.SpatialTheory (theory generated bound carrier) := .empty _) :
    Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.denotation atoms.tests (translate expression) spatial source ↔
      Native.denotation model equations bound leaves carrier sort expression source :=
  (translation_comparison atoms formed source spatial).trans
    (Native.denotation_comparison equations leafEquations formed source).symm

def run {generated : Generated} {model : Model generated} (equations : EquationsInterpreted model)
    {bound : List TypeExpr} {leaves : LeafCodes generated bound}
    (leafEquations : Native.LeafEquationsInterpreted bound leaves) {carrier : TypeExpr} {sort : HSort}
    {admitted : Pattern → Prop} (backend : Backend (theory generated bound carrier) admitted)
    (atoms : Atoms model bound leaves carrier sort admitted) (expression : Expression)
    (formed : Formed generated.logicFragment (leafCarriers leaves) (leafSorts leaves) carrier sort expression)
    (source : Pattern) (budget : Nat) :
    Outcome (Native.denotation model equations bound leaves carrier sort expression source) :=
  Outcome.map (native_comparison equations leafEquations atoms formed source backend.spatial.theory)
    (Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.check backend atoms.tests (translate expression) source budget)

theorem run_answer {generated : Generated} {model : Model generated} (equations : EquationsInterpreted model)
    {bound : List TypeExpr} {leaves : LeafCodes generated bound}
    (leafEquations : Native.LeafEquationsInterpreted bound leaves) {carrier : TypeExpr} {sort : HSort}
    {admitted : Pattern → Prop} (backend : Backend (theory generated bound carrier) admitted)
    (atoms : Atoms model bound leaves carrier sort admitted) (expression : Expression)
    (formed : Formed generated.logicFragment (leafCarriers leaves) (leafSorts leaves) carrier sort expression)
    (source : Pattern) (budget : Nat) :
    (run equations leafEquations backend atoms expression formed source budget).answer =
      (Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.check backend atoms.tests (translate expression) source budget).answer := by
  unfold run
  cases Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.check backend atoms.tests (translate expression) source budget <;> rfl

theorem run_complete {generated : Generated} {model : Model generated} (equations : EquationsInterpreted model)
    {bound : List TypeExpr} {leaves : LeafCodes generated bound}
    (leafEquations : Native.LeafEquationsInterpreted bound leaves) {carrier : TypeExpr} {sort : HSort}
    {admitted : Pattern → Prop} (backend : Backend (theory generated bound carrier) admitted)
    (atoms : Atoms model bound leaves carrier sort admitted) (expression : Expression)
    (formed : Formed generated.logicFragment (leafCarriers leaves) (leafSorts leaves) carrier sort expression)
    (source : Pattern) (sourceAdmitted : admitted source) (budget : Nat)
    (enough : workBound backend atoms.tests (translate expression) source ≤ budget) :
    (run equations leafEquations backend atoms expression formed source budget).Decided :=
  Outcome.map_decided _ _
    (checked_complete backend atoms.tests (translate expression) source sourceAdmitted budget enough)

theorem run_conclusive_mono {generated : Generated} {model : Model generated}
    (equations : EquationsInterpreted model) {bound : List TypeExpr} {leaves : LeafCodes generated bound}
    (leafEquations : Native.LeafEquationsInterpreted bound leaves) {carrier : TypeExpr} {sort : HSort}
    {admitted : Pattern → Prop} (backend : Backend (theory generated bound carrier) admitted)
    (atoms : Atoms model bound leaves carrier sort admitted) (expression : Expression)
    (formed : Formed generated.logicFragment (leafCarriers leaves) (leafSorts leaves) carrier sort expression)
    (source : Pattern) (first second : Nat) (answer : Bool) (more : first ≤ second)
    (conclusive : (run equations leafEquations backend atoms expression formed source first).answer = some answer) :
    (run equations leafEquations backend atoms expression formed source second).answer = some answer := by
  rw [run_answer] at conclusive ⊢
  exact conclusive_mono backend atoms.tests (translate expression) source answer conclusive more

def familyRun {generated : Generated} {model : Model generated} (equations : EquationsInterpreted model)
    {bound : List TypeExpr} {leaves : LeafCodes generated bound}
    (leafEquations : Native.LeafEquationsInterpreted bound leaves) {carrier : TypeExpr} {sort : HSort}
    {admitted : Pattern → Prop} (backend : Backend (theory generated bound carrier) admitted)
    (atoms : Atoms model bound leaves carrier sort admitted) (expression : Expression)
    (formed : Formed generated.logicFragment (leafCarriers leaves) (leafSorts leaves) carrier sort expression)
    (source : Pattern) (budget : Nat) :
    Outcome (Nonempty (Native.Family model bound leaves carrier sort expression source)) :=
  Outcome.map (Native.family_support equations leafEquations formed source).symm
    (run equations leafEquations backend atoms expression formed source budget)

/-- The original propositional compiler checks selected connectives and the
actual carrier/sort of every used leaf before native execution. -/
def compileAndCheck {generated : Generated} {model : Model generated} (equations : EquationsInterpreted model)
    {bound : List TypeExpr} {leaves : LeafCodes generated bound}
    (leafEquations : Native.LeafEquationsInterpreted bound leaves) {carrier : TypeExpr} {sort : HSort}
    {admitted : Pattern → Prop} (backend : Backend (theory generated bound carrier) admitted)
    (atoms : Atoms model bound leaves carrier sort admitted) (expression : Expression)
    (source : Pattern) (budget : Nat) :
    Except Refusal (Outcome (Native.denotation model equations bound leaves carrier sort expression source)) :=
  match checked : Native.compile model bound leaves carrier sort expression with
  | .error reason => .error reason
  | .ok _output => .ok (run equations leafEquations backend atoms expression
      (Native.compilation_sound checked).2 source budget)

end Mettapedia.OSLF.NativeTypes.Decision.Reference.Propositional
