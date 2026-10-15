import Mettapedia.OSLF.NativeTypes.Semantics.Structural

open Mettapedia.OSLF.Framework

/-!
# Propositional native outputs over interpreted equation classes

The native expression is computed recursively from invariant leaf closures and
domain-relative logical operations. Primitive interpretation laws on the input
leaves prove agreement with generated expression denotation. Its dependent
family uses products, sums and functions, retaining logical evidence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Structural.Propositional

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation (Generated)
open Mettapedia.OSLF.NativeTypes.SortProfiles.Source (LeafCodes leafCarriers leafSorts)
open Mettapedia.OSLF.NativeTypes.Generation.PropositionalCodes (Expression Formed rawMeaning Refusal)
open Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes (Model)
open Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeIntroduction (EquationsInterpreted equation_sort_transport)
open Mettapedia.OSLF.NativeTypes.Semantics.Structural (theory sortPredicate)
open GSLTTypeSynthesis
open ModalHypercube (HSort)

universe u

/-- This law is checked at each leaf's declared carrier and primitive equation
completion. No composite expression or final comparison occurs in it. -/
def LeafEquationsInterpreted {generated : Generated} (bound : List TypeExpr)
    (leaves : LeafCodes generated bound) : Prop :=
  ∀ index first (receipt : GeneralEquationJobs.Receipt),
    GeneralEquationJobs.Completion generated.plan bound (leafCarriers leaves index) first receipt →
    ((leaves index).2.2.meaning first ↔ (leaves index).2.2.meaning receipt.target)

theorem leaf_equation_transport {generated : Generated} {bound : List TypeExpr}
    {leaves : LeafCodes generated bound} (interpreted : LeafEquationsInterpreted bound leaves)
    (index : Nat) {first second : Pattern}
    (related : Relation.EqvGen
      (GeneralOccurrenceSemantics.Equation generated.plan bound (leafCarriers leaves index)) first second) :
    (leaves index).2.2.meaning first ↔ (leaves index).2.2.meaning second := by
  induction related with
  | rel first second equation =>
      obtain ⟨receipt, complete, endpoint⟩ := equation
      exact endpoint ▸ interpreted index first receipt complete
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

def meet {system : Mettapedia.GSLT.GSLT.{u}} (first second : EquationPredicate system) :
    EquationPredicate system where
  val term := first term ∧ second term
  property := by
    intro left right equivalent
    exact and_congr (first.2 equivalent) (second.2 equivalent)

def join {system : Mettapedia.GSLT.GSLT.{u}} (first second : EquationPredicate system) :
    EquationPredicate system where
  val term := first term ∨ second term
  property := by
    intro left right equivalent
    exact or_congr (first.2 equivalent) (second.2 equivalent)

def implication {system : Mettapedia.GSLT.GSLT.{u}}
    (domain first second : EquationPredicate system) : EquationPredicate system where
  val term := domain term ∧ (first term → second term)
  property := by
    intro left right equivalent
    exact and_congr (domain.2 equivalent) (imp_congr (first.2 equivalent) (second.2 equivalent))

def complement {system : Mettapedia.GSLT.GSLT.{u}}
    (domain inner : EquationPredicate system) : EquationPredicate system where
  val term := domain term ∧ ¬ inner term
  property := by
    intro left right equivalent
    exact and_congr (domain.2 equivalent) (not_congr (inner.2 equivalent))

def bottom (system : Mettapedia.GSLT.GSLT.{u}) : EquationPredicate system where
  val _ := False
  property := by
    intro first second related
    exact Iff.rfl

def denotation {generated : Generated} (model : Model generated) (equations : EquationsInterpreted model)
    (bound : List TypeExpr) (leaves : LeafCodes generated bound) (carrier : TypeExpr) (sort : HSort) :
    Expression → EquationPredicate (theory generated bound carrier)
  | .leaf index => saturatePredicate _ (fun term =>
      (model bound).sortDomain carrier sort term ∧ (leaves index).2.2.meaning term)
  | .top => sortPredicate model equations bound carrier sort
  | .bottom => bottom _
  | .conjunction first second =>
      meet (denotation model equations bound leaves carrier sort first)
        (denotation model equations bound leaves carrier sort second)
  | .disjunction first second =>
      join (denotation model equations bound leaves carrier sort first)
        (denotation model equations bound leaves carrier sort second)
  | .implication first second =>
      implication (sortPredicate model equations bound carrier sort)
        (denotation model equations bound leaves carrier sort first)
        (denotation model equations bound leaves carrier sort second)
  | .negation inner => complement (sortPredicate model equations bound carrier sort)
      (denotation model equations bound leaves carrier sort inner)

def nativeType {generated : Generated} (model : Model generated) (equations : EquationsInterpreted model)
    (bound : List TypeExpr) (leaves : LeafCodes generated bound)
    (carrier : TypeExpr) (sort : HSort) (expression : Expression) :
    GSLTNativeType (theory generated bound carrier) where
  sort := ()
  pred := denotation model equations bound leaves carrier sort expression

/-- The canonical predicate stays inside the actual domain even before any
formation or leaf-comparison certificate is supplied. -/
theorem denotation_sort_bounded {generated : Generated} (model : Model generated)
    (equations : EquationsInterpreted model) (bound : List TypeExpr)
    (leaves : LeafCodes generated bound) (carrier : TypeExpr) (sort : HSort)
    (expression : Expression) (term : Pattern) :
    denotation model equations bound leaves carrier sort expression term →
      (model bound).sortDomain carrier sort term := by
  induction expression with
  | leaf index =>
      rintro ⟨representative, related, domain, _⟩
      exact (equation_sort_transport equations bound carrier sort related).mpr domain
  | top => exact fun inhabited => inhabited
  | bottom => exact fun falsehood => falsehood.elim
  | conjunction first second ihFirst _ => exact fun inhabited => ihFirst inhabited.1
  | disjunction first second ihFirst ihSecond => exact fun inhabited => inhabited.elim ihFirst ihSecond
  | implication first second _ _ => exact fun inhabited => inhabited.1
  | negation inner _ => exact fun inhabited => inhabited.1

theorem denotation_carrier_bounded {generated : Generated} (model : Model generated)
    (equations : EquationsInterpreted model) (bound : List TypeExpr)
    (leaves : LeafCodes generated bound) (carrier : TypeExpr) (sort : HSort)
    (expression : Expression) (term : Pattern)
    (inhabited : denotation model equations bound leaves carrier sort expression term) :
    HasType generated.snapshot.language generated.snapshot.free bound term carrier :=
  (model bound).carrierBounded carrier sort term
    (denotation_sort_bounded model equations bound leaves carrier sort expression term inhabited)

theorem denotation_comparison {generated : Generated} {model : Model generated}
    (equations : EquationsInterpreted model) {bound : List TypeExpr}
    {leaves : LeafCodes generated bound} (leafEquations : LeafEquationsInterpreted bound leaves)
    {carrier : TypeExpr} {sort : HSort} {expression : Expression}
    (formed : Formed generated.logicFragment (leafCarriers leaves) (leafSorts leaves) carrier sort expression)
    (term : Pattern) : denotation model equations bound leaves carrier sort expression term ↔
      (model bound).sortDomain carrier sort term ∧ rawMeaning leaves expression term := by
  induction formed with
  | leaf index carrierEqual _ =>
      apply saturatePredicate_apply_iff_of_invariant
      intro first second related
      have conversion : Relation.EqvGen
          (GeneralOccurrenceSemantics.Equation generated.plan bound carrier) first second := related
      exact and_congr (equation_sort_transport equations bound carrier sort related)
        (leaf_equation_transport leafEquations index (by simpa only [carrierEqual] using conversion))
  | top _ => exact ⟨fun inhabited => ⟨inhabited, trivial⟩, fun inhabited => inhabited.1⟩
  | bottom _ => exact ⟨fun falsehood => falsehood.elim, fun inhabited => inhabited.2⟩
  | conjunction _ _ _ ihFirst ihSecond =>
      change (_ ∧ _) ↔ _
      rw [ihFirst, ihSecond]
      exact ⟨fun ⟨⟨domain, first⟩, ⟨_, second⟩⟩ => ⟨domain, first, second⟩,
        fun ⟨domain, first, second⟩ => ⟨⟨domain, first⟩, ⟨domain, second⟩⟩⟩
  | disjunction _ _ _ ihFirst ihSecond =>
      change (_ ∨ _) ↔ _
      rw [ihFirst, ihSecond]
      exact ⟨fun inhabited => inhabited.elim (fun ⟨domain, first⟩ => ⟨domain, .inl first⟩)
          (fun ⟨domain, second⟩ => ⟨domain, .inr second⟩),
        fun ⟨domain, inhabited⟩ => inhabited.elim (fun first => .inl ⟨domain, first⟩)
          (fun second => .inr ⟨domain, second⟩)⟩
  | implication _ _ _ ihFirst ihSecond =>
      change (_ ∧ (_ → _)) ↔ _
      rw [ihFirst, ihSecond]
      exact ⟨fun ⟨domain, implication⟩ => ⟨domain, fun first => (implication ⟨domain, first⟩).2⟩,
        fun ⟨domain, implication⟩ => ⟨domain, fun first => ⟨domain, implication first.2⟩⟩⟩
  | negation _ _ ih =>
      change (_ ∧ ¬ _) ↔ _
      rw [ih]
      exact ⟨fun ⟨domain, excluded⟩ => ⟨domain, fun inner => excluded ⟨domain, inner⟩⟩,
        fun ⟨domain, excluded⟩ => ⟨domain, fun inner => excluded inner.2⟩⟩

/-- The family is computed from expression syntax. Product, sum and function
evidence is retained rather than replaced with a lift of the final denotation. -/
def Family {generated : Generated} (model : Model generated) (bound : List TypeExpr)
    (leaves : LeafCodes generated bound) (carrier : TypeExpr) (sort : HSort) : Expression → Pattern → Type
  | .leaf index, term => PLift ((model bound).sortDomain carrier sort term ∧ (leaves index).2.2.meaning term)
  | .top, term => PLift ((model bound).sortDomain carrier sort term)
  | .bottom, _ => PEmpty
  | .conjunction first second, term =>
      Family model bound leaves carrier sort first term × Family model bound leaves carrier sort second term
  | .disjunction first second, term =>
      Family model bound leaves carrier sort first term ⊕ Family model bound leaves carrier sort second term
  | .implication first second, term => PLift ((model bound).sortDomain carrier sort term) ×
      (Family model bound leaves carrier sort first term → Family model bound leaves carrier sort second term)
  | .negation inner, term => PLift ((model bound).sortDomain carrier sort term) ×
      (Family model bound leaves carrier sort inner term → PEmpty)

def Comprehension {generated : Generated} (model : Model generated) (bound : List TypeExpr)
    (leaves : LeafCodes generated bound) (carrier : TypeExpr) (sort : HSort) (expression : Expression) : Type :=
  (term : Pattern) × Family model bound leaves carrier sort expression term

private theorem function_support {first second : Type} :
    Nonempty (first → second) ↔ (Nonempty first → Nonempty second) := by
  classical
  constructor
  · rintro ⟨function⟩ ⟨argument⟩
    exact ⟨function argument⟩
  · intro implication
    by_cases inhabited : Nonempty first
    · exact ⟨fun _ => Classical.choice (implication inhabited)⟩
    · exact ⟨fun argument => False.elim (inhabited ⟨argument⟩)⟩

theorem family_denotation {generated : Generated} (model : Model generated) (bound : List TypeExpr)
    (leaves : LeafCodes generated bound) (carrier : TypeExpr) (sort : HSort) (expression : Expression)
    (term : Pattern) : Nonempty (Family model bound leaves carrier sort expression term) ↔
      (model bound).sortDomain carrier sort term ∧ rawMeaning leaves expression term := by
  induction expression with
  | leaf _ => exact ⟨fun ⟨inhabited⟩ => inhabited.down, fun inhabited => ⟨⟨inhabited⟩⟩⟩
  | top =>
      exact ⟨fun ⟨inhabited⟩ => ⟨inhabited.down, trivial⟩, fun inhabited => ⟨⟨inhabited.1⟩⟩⟩
  | bottom =>
      constructor
      · rintro ⟨falsehood⟩
        cases falsehood
      · intro inhabited
        exact inhabited.2.elim
  | conjunction first second ihFirst ihSecond =>
      change Nonempty (_ × _) ↔ _
      rw [nonempty_prod, ihFirst, ihSecond]
      exact ⟨fun ⟨⟨domain, first⟩, ⟨_, second⟩⟩ => ⟨domain, first, second⟩,
        fun ⟨domain, first, second⟩ => ⟨⟨domain, first⟩, ⟨domain, second⟩⟩⟩
  | disjunction first second ihFirst ihSecond =>
      change Nonempty (_ ⊕ _) ↔ _
      rw [nonempty_sum, ihFirst, ihSecond]
      exact ⟨fun inhabited => inhabited.elim (fun ⟨domain, first⟩ => ⟨domain, .inl first⟩)
          (fun ⟨domain, second⟩ => ⟨domain, .inr second⟩),
        fun ⟨domain, inhabited⟩ => inhabited.elim (fun first => .inl ⟨domain, first⟩)
          (fun second => .inr ⟨domain, second⟩)⟩
  | implication first second ihFirst ihSecond =>
      change Nonempty (_ × (_ → _)) ↔ _
      rw [nonempty_prod, function_support, ihFirst, ihSecond]
      constructor
      · rintro ⟨⟨domain⟩, implication⟩
        exact ⟨domain.down, fun first => (implication ⟨domain.down, first⟩).2⟩
      · rintro ⟨domain, implication⟩
        exact ⟨⟨⟨domain⟩⟩, fun first => ⟨domain, implication first.2⟩⟩
  | negation inner ih =>
      change Nonempty (_ × (_ → PEmpty)) ↔ _
      rw [nonempty_prod, function_support, ih]
      constructor
      · rintro ⟨⟨domain⟩, excluded⟩
        exact ⟨domain.down, fun inner => (excluded ⟨domain.down, inner⟩).elim
          (fun falsehood => nomatch falsehood)⟩
      · rintro ⟨domain, excluded⟩
        exact ⟨⟨⟨domain⟩⟩, fun inner => (excluded inner.2).elim⟩

theorem family_support {generated : Generated} {model : Model generated}
    (equations : EquationsInterpreted model) {bound : List TypeExpr}
    {leaves : LeafCodes generated bound} (leafEquations : LeafEquationsInterpreted bound leaves)
    {carrier : TypeExpr} {sort : HSort} {expression : Expression}
    (formed : Formed generated.logicFragment (leafCarriers leaves) (leafSorts leaves) carrier sort expression)
    (term : Pattern) : Nonempty (Family model bound leaves carrier sort expression term) ↔
      denotation model equations bound leaves carrier sort expression term :=
  (family_denotation model bound leaves carrier sort expression term).trans
    (denotation_comparison equations leafEquations formed term).symm

theorem comprehension_exact {generated : Generated} {model : Model generated}
    (equations : EquationsInterpreted model) {bound : List TypeExpr}
    {leaves : LeafCodes generated bound} (leafEquations : LeafEquationsInterpreted bound leaves)
    {carrier : TypeExpr} {sort : HSort} {expression : Expression}
    (formed : Formed generated.logicFragment (leafCarriers leaves) (leafSorts leaves) carrier sort expression)
    (term : Pattern) :
    (∃ inhabitant : Comprehension model bound leaves carrier sort expression, inhabitant.1 = term) ↔
      denotation model equations bound leaves carrier sort expression term := by
  constructor
  · rintro ⟨⟨source, family⟩, equal⟩
    change source = term at equal
    subst source
    exact (family_support equations leafEquations formed term).mp ⟨family⟩
  · intro inhabited
    obtain ⟨family⟩ := (family_support equations leafEquations formed term).mpr inhabited
    exact ⟨⟨term, family⟩, rfl⟩

structure Output {generated : Generated} (model : Model generated) (bound : List TypeExpr)
    (leaves : LeafCodes generated bound) (carrier : TypeExpr) (sort : HSort) where
  classified : Mettapedia.OSLF.NativeTypes.Semantics.Sorted.PropositionalCodes.ClassifiedCode generated bound (model bound) leaves carrier sort

def Output.predicate {generated : Generated} {model : Model generated}
    (equations : EquationsInterpreted model) {bound : List TypeExpr} {leaves : LeafCodes generated bound}
    {carrier : TypeExpr} {sort : HSort} (output : Output model bound leaves carrier sort) :
    EquationPredicate (theory generated bound carrier) :=
  denotation model equations bound leaves carrier sort output.classified.expression

def Output.native {generated : Generated} {model : Model generated}
    (equations : EquationsInterpreted model) {bound : List TypeExpr} {leaves : LeafCodes generated bound}
    {carrier : TypeExpr} {sort : HSort} (output : Output model bound leaves carrier sort) :
    GSLTNativeType (theory generated bound carrier) where
  sort := ()
  pred := output.predicate equations

def compile {generated : Generated} (model : Model generated) (bound : List TypeExpr)
    (leaves : LeafCodes generated bound) (carrier : TypeExpr) (sort : HSort) (expression : Expression) :
    Except Refusal (Output model bound leaves carrier sort) :=
  (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.PropositionalCodes.compile generated bound (model bound) leaves carrier sort expression).map
    (fun classified => ⟨classified⟩)

theorem compilation_complete {generated : Generated} (model : Model generated) (bound : List TypeExpr)
    (leaves : LeafCodes generated bound) (carrier : TypeExpr) (sort : HSort) (expression : Expression)
    (formed : Formed generated.logicFragment (leafCarriers leaves) (leafSorts leaves) carrier sort expression) :
    ∃ output, compile model bound leaves carrier sort expression = .ok output ∧
      output.classified.expression = expression := by
  obtain ⟨classified, checked, expressionEqual⟩ :=
    Mettapedia.OSLF.NativeTypes.Semantics.Sorted.PropositionalCodes.formation_complete generated bound (model bound)
      leaves carrier sort expression formed
  exact ⟨⟨classified⟩, by simp [compile, checked, Except.map], expressionEqual⟩

theorem compilation_sound {generated : Generated} {model : Model generated} {bound : List TypeExpr}
    {leaves : LeafCodes generated bound} {carrier : TypeExpr} {sort : HSort} {expression : Expression}
    {output : Output model bound leaves carrier sort}
    (checked : compile model bound leaves carrier sort expression = .ok output) :
    output.classified.expression = expression ∧
      Formed generated.logicFragment (leafCarriers leaves) (leafSorts leaves) carrier sort expression := by
  unfold compile at checked
  cases result : Mettapedia.OSLF.NativeTypes.Semantics.Sorted.PropositionalCodes.compile generated bound (model bound)
      leaves carrier sort expression with
  | error refusal => simp [result, Except.map] at checked
  | ok classified =>
      simp only [result, Except.map, Except.ok.injEq] at checked
      subst output
      exact Mettapedia.OSLF.NativeTypes.Semantics.Sorted.PropositionalCodes.formation_sound result

theorem generated_native_comparison {generated : Generated} {model : Model generated}
    (equations : EquationsInterpreted model) {bound : List TypeExpr}
    {leaves : LeafCodes generated bound} (leafEquations : LeafEquationsInterpreted bound leaves)
    {carrier : TypeExpr} {sort : HSort} (output : Output model bound leaves carrier sort) (term : Pattern) :
    output.classified.code.meaning term ↔ output.predicate equations term :=
  (output.classified.readout term).trans
    (denotation_comparison equations leafEquations output.classified.formation term).symm

theorem compiled_native_comparison {generated : Generated} {model : Model generated}
    (equations : EquationsInterpreted model) {bound : List TypeExpr}
    {leaves : LeafCodes generated bound} (leafEquations : LeafEquationsInterpreted bound leaves)
    {carrier : TypeExpr} {sort : HSort} {expression : Expression}
    {output : Output model bound leaves carrier sort}
    (checked : compile model bound leaves carrier sort expression = .ok output) (term : Pattern) :
    output.predicate equations term ↔
      (model bound).sortDomain carrier sort term ∧ rawMeaning leaves expression term := by
  have expressionEqual := (compilation_sound checked).1
  change denotation model equations bound leaves carrier sort output.classified.expression term ↔ _
  rw [← expressionEqual]
  exact denotation_comparison equations leafEquations output.classified.formation term

theorem generated_family_comparison {generated : Generated} {model : Model generated}
    {bound : List TypeExpr} {leaves : LeafCodes generated bound} {carrier : TypeExpr} {sort : HSort}
    (output : Output model bound leaves carrier sort) (term : Pattern) :
    output.classified.code.meaning term ↔
      Nonempty (Family model bound leaves carrier sort output.classified.expression term) :=
  (output.classified.readout term).trans
    (family_denotation model bound leaves carrier sort output.classified.expression term).symm

theorem native_satisfaction {generated : Generated} {model : Model generated}
    (equations : EquationsInterpreted model) {bound : List TypeExpr}
    {leaves : LeafCodes generated bound} (leafEquations : LeafEquationsInterpreted bound leaves)
    {carrier : TypeExpr} {sort : HSort} (output : Output model bound leaves carrier sort) (term : Pattern) :
    (gsltOSLF (theory generated bound carrier)).satisfies (S := ()) term (output.native equations).pred ↔
      output.classified.code.meaning term :=
  (generated_native_comparison equations leafEquations output term).symm

theorem native_bounded {generated : Generated} {model : Model generated}
    (equations : EquationsInterpreted model) {bound : List TypeExpr}
    {leaves : LeafCodes generated bound} (leafEquations : LeafEquationsInterpreted bound leaves)
    {carrier : TypeExpr} {sort : HSort} (output : Output model bound leaves carrier sort)
    {term : Pattern} (inhabited : output.predicate equations term) :
    (model bound).sortDomain carrier sort term :=
  (denotation_comparison equations leafEquations output.classified.formation term).mp inhabited |>.1

theorem native_carrier_bounded {generated : Generated} {model : Model generated}
    (equations : EquationsInterpreted model) {bound : List TypeExpr}
    {leaves : LeafCodes generated bound} (leafEquations : LeafEquationsInterpreted bound leaves)
    {carrier : TypeExpr} {sort : HSort} (output : Output model bound leaves carrier sort)
    {term : Pattern} (inhabited : output.predicate equations term) :
    HasType generated.snapshot.language generated.snapshot.free bound term carrier :=
  (model bound).carrierBounded _ _ _ (native_bounded equations leafEquations output inhabited)

theorem quotient_membership {generated : Generated} {model : Model generated}
    (equations : EquationsInterpreted model) {bound : List TypeExpr}
    {leaves : LeafCodes generated bound} (leafEquations : LeafEquationsInterpreted bound leaves)
    {carrier : TypeExpr} {sort : HSort} (output : Output model bound leaves carrier sort) (term : Pattern) :
    descendPredicate _ (output.predicate equations) (Quotient.mk _ term) ↔
      Nonempty (Family model bound leaves carrier sort output.classified.expression term) :=
  (family_support equations leafEquations output.classified.formation term).symm

#print axioms denotation_comparison
#print axioms family_denotation
#print axioms family_support
#print axioms compiled_native_comparison
#print axioms quotient_membership
#print axioms denotation_sort_bounded
#print axioms comprehension_exact

end Mettapedia.OSLF.NativeTypes.Semantics.Structural.Propositional
