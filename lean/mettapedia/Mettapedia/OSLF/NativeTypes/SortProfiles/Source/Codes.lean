import Mettapedia.OSLF.NativeTypes.SortProfiles.Source.Syntax
import Mettapedia.OSLF.NativeTypes.Generation.StructuralCodes
import Mettapedia.OSLF.NativeTypes.Generation.EquationAdmission

open Mettapedia.OSLF.Framework

/-!
# Code-bearing outputs of the generated structural system

The code compiler consumes actual native input codes and generated constructor
expression. It checks carrier and universe formation before returning the semantic
code together with that expression, both formation witnesses, and an exact readout
comparison. Selected equation and directed-law admission are both consumed.
An unresolved law check and a rejected code have different result constructors.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Source

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation (Generated)
open Mettapedia.OSLF.NativeTypes.Modal.Rules (TypeCode)
open Mettapedia.OSLF.NativeTypes.Structural (ConstructorValue)
open ModalHypercube (HSort)

abbrev LeafCodes (generated : Generated) (bound : List TypeExpr) :=
  Nat → Σ carrier : TypeExpr, Σ sort : HSort, TypeCode generated.plan bound carrier sort

def leafCarriers {generated : Generated} {bound : List TypeExpr}
    (leaves : LeafCodes generated bound) : Nat → TypeExpr := fun index => (leaves index).1

def leafSorts {generated : Generated} {bound : List TypeExpr}
    (leaves : LeafCodes generated bound) : Nat → HSort := fun index => (leaves index).2.1

def meaning (generated : Generated) (bound : List TypeExpr) (leaves : LeafCodes generated bound) :
    Code generated.snapshot.language → Pattern → Prop
  | .variableCode index, term => (leaves index).2.2.meaning term
  | .constructor index arguments, term =>
      HasType generated.snapshot.language generated.snapshot.free bound term
        (.base (declaration generated.snapshot.language index).category) ∧
      ∃ value : ConstructorValue generated.snapshot.language generated.snapshot.free bound
          (declaration generated.snapshot.language index),
        Relation.EqvGen (Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics.Equation generated.plan bound
          (.base (declaration generated.snapshot.language index).category)) term value.pattern ∧
        ∀ position, meaning generated bound leaves (arguments position)
          (value.arguments[position.val]'(by rw [value.arguments_length]; exact position.isLt))

theorem meaning_typed {generated : Generated} {bound : List TypeExpr}
    {leaves : LeafCodes generated bound} {expression : Code generated.snapshot.language} {carrier : TypeExpr}
    (formed : Carries (leafCarriers leaves) expression carrier) {term : Pattern}
    (inhabited : meaning generated bound leaves expression term) :
    HasType generated.snapshot.language generated.snapshot.free bound term carrier := by
  cases formed with
  | variableCode index => exact (leaves index).2.2.bounded term inhabited
  | constructor index arguments children => exact inhabited.1

structure ClassifiedCode (generated : Generated) (bound : List TypeExpr)
    (leaves : LeafCodes generated bound) (carrier : TypeExpr) (sort : HSort) where
  expression : Code generated.snapshot.language
  carrierFormation : Carries (leafCarriers leaves) expression carrier
  universeFormation : Kinded generated.vertex.2 (leafSorts leaves) expression sort
  code : TypeCode generated.plan bound carrier sort
  meaningComparison : ∀ term, code.meaning term ↔ meaning generated bound leaves expression term

def classify {generated : Generated} {bound : List TypeExpr}
    {leaves : LeafCodes generated bound} (expression : Code generated.snapshot.language)
    {carrier : TypeExpr} {sort : HSort}
    (carrierFormation : Carries (leafCarriers leaves) expression carrier)
    (universeFormation : Kinded generated.vertex.2 (leafSorts leaves) expression sort) :
    ClassifiedCode generated bound leaves carrier sort where
  expression := expression
  carrierFormation := carrierFormation
  universeFormation := universeFormation
  code := {
    meaning := meaning generated bound leaves expression
    bounded := fun _ inhabited => meaning_typed carrierFormation inhabited}
  meaningComparison _ := Iff.rfl

/-- Both checked law systems are required by the code-preserving contract.
The E-only center remains a separate construction. -/
def jointAdmission (generated : Generated) : Option Bool :=
  match generated.equationAdmission, generated.rewriteAdmission with
  | some false, _ => some false
  | _, some false => some false
  | some true, some true => some true
  | _, _ => none

theorem joint_admission_exact (generated : Generated) :
    jointAdmission generated = some true ↔
      generated.equationAdmission = some true ∧ generated.rewriteAdmission = some true := by
  cases first : generated.equationAdmission with
  | none =>
      cases second : generated.rewriteAdmission with
      | none => simp [jointAdmission, first, second]
      | some truth => cases truth <;> simp [jointAdmission, first, second]
  | some firstTruth =>
      cases second : generated.rewriteAdmission with
      | none => cases firstTruth <;> simp [jointAdmission, first, second]
      | some secondTruth =>
          cases firstTruth <;> cases secondTruth <;> simp [jointAdmission, first, second]

inductive Failure where
  | disabledStructuralFragment
  | rejectedLawProfile
  | malformedCarrier
  | malformedUniverse
  deriving DecidableEq, Repr

inductive Compilation (generated : Generated) (bound : List TypeExpr)
    (leaves : LeafCodes generated bound) where
  | unresolved
  | refused (reason : Failure)
  | accepted (result : Σ carrier : TypeExpr, Σ sort : HSort,
      ClassifiedCode generated bound leaves carrier sort)

def compileNativeCode (generated : Generated) (bound : List TypeExpr)
    (leaves : LeafCodes generated bound) (expression : Code generated.snapshot.language) :
    Compilation generated bound leaves :=
  if generated.logicFragment.core.structural then
    match jointAdmission generated with
    | none => .unresolved
    | some false => .refused .rejectedLawProfile
    | some true =>
        match carrierRead : expression.carrier? (leafCarriers leaves) with
        | none => .refused .malformedCarrier
        | some carrier =>
            match universeRead : expression.kind? generated.vertex.2 (leafSorts leaves) with
            | none => .refused .malformedUniverse
            | some sort => .accepted ⟨carrier, sort, classify expression
                ((carrier_read_exact _ _ _).mp carrierRead)
                ((kind_read_exact _ _ _ _).mp universeRead)⟩
  else .refused .disabledStructuralFragment

theorem compile_native_code_accepts {generated : Generated} {bound : List TypeExpr}
    {leaves : LeafCodes generated bound} {expression : Code generated.snapshot.language}
    {carrier : TypeExpr} {sort : HSort}
    (enabled : generated.logicFragment.core.structural = true)
    (admitted : jointAdmission generated = some true)
    (carrierFormation : Carries (leafCarriers leaves) expression carrier)
    (universeFormation : Kinded generated.vertex.2 (leafSorts leaves) expression sort) :
    compileNativeCode generated bound leaves expression = .accepted
      ⟨carrier, sort, classify expression carrierFormation universeFormation⟩ := by
  simp only [compileNativeCode, enabled, if_true, admitted]
  split
  · rename_i missing
    have present := carries_read carrierFormation
    rw [missing] at present
    cases present
  · rename_i actualCarrier readCarrier
    have agrees : actualCarrier = carrier := Option.some.inj
      (readCarrier.symm.trans (carries_read carrierFormation))
    subst actualCarrier
    split
    · rename_i missing
      have present := kinded_read universeFormation
      rw [missing] at present
      cases present
    · rename_i actualSort readSort
      have agrees : actualSort = sort := Option.some.inj
        (readSort.symm.trans (kinded_read universeFormation))
      subst actualSort
      rfl

theorem accepted_native_code_retains_syntax {generated : Generated} {bound : List TypeExpr}
    {leaves : LeafCodes generated bound} {expression : Code generated.snapshot.language}
    {result : Σ carrier : TypeExpr, Σ sort : HSort, ClassifiedCode generated bound leaves carrier sort}
    (accepted : compileNativeCode generated bound leaves expression = .accepted result) :
    result.2.2.expression = expression := by
  unfold compileNativeCode at accepted
  split at accepted
  · split at accepted
    · cases accepted
    · cases accepted
    · split at accepted
      · cases accepted
      · split at accepted
        · cases accepted
        · cases accepted
          rfl
  · cases accepted

theorem accepted_native_code_consumes_laws {generated : Generated} {bound : List TypeExpr}
    {leaves : LeafCodes generated bound} {expression : Code generated.snapshot.language}
    {result : Σ carrier : TypeExpr, Σ sort : HSort, ClassifiedCode generated bound leaves carrier sort}
    (accepted : compileNativeCode generated bound leaves expression = .accepted result) :
    generated.logicFragment.core.structural = true ∧
      generated.equationAdmission = some true ∧ generated.rewriteAdmission = some true := by
  unfold compileNativeCode at accepted
  split at accepted
  · rename_i enabled
    refine ⟨enabled, ?_⟩
    apply (joint_admission_exact generated).mp
    cases lawStatus : jointAdmission generated with
    | none => rw [lawStatus] at accepted; cases accepted
    | some truth =>
        cases truth with
        | false => rw [lawStatus] at accepted; cases accepted
        | true => rfl
  · cases accepted

theorem unfinished_laws_remain_unresolved {generated : Generated} {bound : List TypeExpr}
    (leaves : LeafCodes generated bound) (expression : Code generated.snapshot.language)
    (enabled : generated.logicFragment.core.structural = true)
    (unfinished : jointAdmission generated = none) :
    compileNativeCode generated bound leaves expression = .unresolved := by
  simp [compileNativeCode, enabled, unfinished]

theorem wrong_universe_is_refused {generated : Generated} {bound : List TypeExpr}
    (leaves : LeafCodes generated bound) (expression : Code generated.snapshot.language)
    (enabled : generated.logicFragment.core.structural = true)
    (admitted : jointAdmission generated = some true) {carrier : TypeExpr}
    (formed : Carries (leafCarriers leaves) expression carrier)
    (wrong : expression.kind? generated.vertex.2 (leafSorts leaves) = none) :
    compileNativeCode generated bound leaves expression = .refused .malformedUniverse := by
  simp only [compileNativeCode, enabled, if_true, admitted]
  split
  · rename_i missing
    have present := carries_read formed
    rw [missing] at present
    cases present
  · split
    · rfl
    · rename_i actualSort readSort
      rw [wrong] at readSort
      cases readSort

/-- The generated constructor expression and its semantic output agree with the
existing structural former, at all argument positions and every carrier. -/
theorem constructor_meaning_exact (generated : Generated) (bound : List TypeExpr)
    (leaves : LeafCodes generated bound)
    (index : Fin generated.snapshot.language.terms.length)
    (children : (position : Fin (declaration generated.snapshot.language index).params.length) →
      ClassifiedCode generated bound leaves
        (declaration generated.snapshot.language index).params[position].typeExpr
        (Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.input generated.vertex.2 (operation generated.snapshot.language index) position))
    (term : Pattern) :
    meaning generated bound leaves (.constructor index (fun position => (children position).expression)) term ↔
      (Mettapedia.OSLF.NativeTypes.Generation.structuralCode generated bound index (fun position => (children position).code)).meaning term := by
  change (_ ∧ ∃ value, _ ∧ ∀ position, _) ↔ (_ ∧ ∃ value, _ ∧ ∀ position, _)
  constructor
  · rintro ⟨typed, value, conversion, arguments⟩
    exact ⟨typed, value, conversion,
      fun position => ((children position).meaningComparison _).mpr (arguments position)⟩
  · rintro ⟨typed, value, conversion, arguments⟩
    exact ⟨typed, value, conversion,
      fun position => ((children position).meaningComparison _).mp (arguments position)⟩

def constructorCode (generated : Generated) (bound : List TypeExpr)
    (leaves : LeafCodes generated bound) (index : Fin generated.snapshot.language.terms.length)
    (children : (position : Fin (declaration generated.snapshot.language index).params.length) →
      ClassifiedCode generated bound leaves
        (declaration generated.snapshot.language index).params[position].typeExpr
        (Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.input generated.vertex.2 (operation generated.snapshot.language index) position)) :
    ClassifiedCode generated bound leaves (.base (declaration generated.snapshot.language index).category)
      (Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.output generated.vertex.2 (operation generated.snapshot.language index)) where
  expression := .constructor index (fun position => (children position).expression)
  carrierFormation := .constructor index _ (fun position => (children position).carrierFormation)
  universeFormation := .constructor index _ (fun position => (children position).universeFormation)
  code := Mettapedia.OSLF.NativeTypes.Generation.structuralCode generated bound index (fun position => (children position).code)
  meaningComparison term := (constructor_meaning_exact generated bound leaves index children term).symm

end Mettapedia.OSLF.NativeTypes.SortProfiles.Source
