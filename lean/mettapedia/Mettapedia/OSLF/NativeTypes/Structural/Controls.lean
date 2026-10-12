import Mettapedia.OSLF.NativeTypes.Structural.Execution
import Mettapedia.OSLF.NativeTypes.Structural.AC
import Mettapedia.OSLF.MeTTaIL.GeneralEquationSeparators

open Mettapedia.OSLF.Framework

/-!
# Structural generation and fragment controls

These controls distinguish a representative root from an equation-class
structural type, positional splitting from commutative splitting, unsupported
logical vocabulary from falsehood, and actual abstraction parameters from
ordinary arguments of the same apparent carrier.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Structural.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.OSLF.MeTTaIL.GeneralEquationSeparators

private def unitFormer : Former := ⟨2, unitLanguage.terms[2]'(by decide)⟩
private def atomTerm : Pattern := .apply "Atom" []
private def zeroTerm : Pattern := .apply "Zero" []

private theorem unitFormer_member : unitFormer ∈ structuralFormers unitLanguage := by
  apply (mem_structuralFormers_iff _ _).mpr
  decide

private theorem atom_typed (bound : List TypeExpr) :
    HasType unitLanguage FreeTypeContext.empty bound atomTerm (.base "Proc") := by
  exact .constructor (rule := unitLanguage.terms[0]'(by decide))
    (by simp [unitLanguage]) (by simp [unitLanguage, UsesBareCollection]) .nil

private theorem zero_typed (bound : List TypeExpr) :
    HasType unitLanguage FreeTypeContext.empty bound zeroTerm (.base "Proc") := by
  exact .constructor (rule := unitLanguage.terms[1]'(by decide))
    (by simp [unitLanguage]) (by simp [unitLanguage, UsesBareCollection]) .nil

/-- The generated parallel type contains an atom representative through the
actual authored unit equation. It is not a test of a hidden root flag. -/
theorem authored_equation_changes_representative_root
    (base : BasePremiseEvaluator) (bound : List TypeExpr) :
    StructuralHolds unitLanguage FreeTypeContext.empty bound
        (EquationEquiv base unitLanguage) unitFormer atomTerm ∧
      ¬ ∃ arguments, atomTerm = .apply unitFormer.declaration.label arguments := by
  constructor
  · refine ⟨unitFormer_member,
      .ordinary [atomTerm, zeroTerm] (by simp [unitFormer, unitLanguage, UsesBareCollection])
        (.cons trivial rfl (atom_typed bound) (.cons trivial rfl (zero_typed bound) .nil)), ?_⟩
    exact .rel _ _ (unit_generator base atomTerm)
  · rintro ⟨arguments, equal⟩
    simp [atomTerm, unitFormer, unitLanguage] at equal

/-- The same constructor with free equality keeps the two positions distinct. -/
theorem free_split_is_positional (bound : List TypeExpr) :
    SplitHolds unitLanguage FreeTypeContext.empty bound Eq unitFormer
        (fun value => value = atomTerm) (fun value => value = zeroTerm)
        (.apply "Parallel" [atomTerm, zeroTerm]) ∧
      ¬ SplitHolds unitLanguage FreeTypeContext.empty bound Eq unitFormer
        (fun value => value = zeroTerm) (fun value => value = atomTerm)
        (.apply "Parallel" [atomTerm, zeroTerm]) := by
  have ordinary : ¬ UsesBareCollection unitFormer.declaration := by
    simp [unitFormer, unitLanguage, UsesBareCollection]
  constructor
  · exact ⟨unitFormer_member,
      .ordinary [atomTerm, zeroTerm] ordinary
        (.cons trivial rfl (atom_typed bound) (.cons trivial rfl (zero_typed bound) .nil)),
      rfl, atomTerm, zeroTerm, rfl, rfl, rfl⟩
  · intro swapped
    obtain ⟨left, right, same, _, first, second⟩ :=
      (free_positional_split unitFormer_member ordinary _ _ _).mp swapped
    subst left
    subst right
    simp [unitFormer, unitLanguage, atomTerm, zeroTerm] at same

private def noAtoms : Nat → Option TypeExpr := fun _ => none

/-- A true proposition can fail to elaborate because negation is outside the
chosen finite-limit fragment. -/
theorem unsupported_true_formula_refused (term : Pattern) :
    Holds unitLanguage FreeTypeContext.empty [] (fun _ => Eq)
        (fun _ _ _ => False) (.base "Proc") (.neg .bottom) term ∧
      elaborate unitLanguage noAtoms finiteLimitFragment (.base "Proc") (.neg .bottom) =
        .error (.unsupportedConnective .negation) := by
  constructor
  · exact fun falsehood => falsehood
  · decide

/-- An admitted false formula is a successful elaboration, a different result
from an unsupported connective. -/
theorem admitted_false_formula (term : Pattern) :
    (∃ judgment, elaborate unitLanguage noAtoms heytingFragment (.base "Proc") .bottom =
      .ok judgment) ∧
      ¬ Holds unitLanguage FreeTypeContext.empty [] (fun _ => Eq)
        (fun _ _ _ => False) (.base "Proc") .bottom term := by
  constructor
  · apply (elaborate_success_iff _ _ _ _ _).mpr
    exact .bottom _ (by decide)
  · exact formed_bottom_is_false _ _

private def bindingLanguage : LanguageDef where
  name := "BindingStructural"
  types := [TypeDecl.plain "Name", TypeDecl.plain "Proc"]
  terms := [
    { label := "Token", category := "Name", params := [], syntaxPattern := [] },
    { label := "Use", category := "Proc", params := [.simple "name" (.base "Name")],
      syntaxPattern := [] },
    { label := "BindPair", category := "Proc",
      params := [.simple "name" (.base "Name"),
        .abstractionNamed none "body" (.arrow (.base "Name") (.base "Proc"))],
      syntaxPattern := [] }]
  equations := []
  rewrites := []

private def token : Pattern := .apply "Token" []
private def binder : Pattern := .lambda none (.apply "Use" [.bvar 0])
private def bindingFormer : Former := ⟨2, bindingLanguage.terms[2]'(by decide)⟩

private theorem token_typed (bound : List TypeExpr) :
    HasType bindingLanguage FreeTypeContext.empty bound token (.base "Name") := by
  exact .constructor (rule := bindingLanguage.terms[0]'(by decide))
    (by simp [bindingLanguage]) (by simp [bindingLanguage, UsesBareCollection]) .nil

private theorem binder_typed (bound : List TypeExpr) :
    HasType bindingLanguage FreeTypeContext.empty bound binder
      (.arrow (.base "Name") (.base "Proc")) := by
  apply HasType.lambda
  exact .constructor (rule := bindingLanguage.terms[1]'(by decide))
    (by simp [bindingLanguage])
    (by simp [bindingLanguage, UsesBareCollection]) (.cons trivial rfl (.bvar rfl) .nil)

/-- Both argument carriers, including the abstraction carrier, are recovered
from the declaration by the one elaborator. -/
theorem binder_split_elaborates :
    ∃ judgment, elaborate bindingLanguage noAtoms finiteLimitFragment (.base "Proc")
      (.split 2 .top .top) = .ok judgment := by
  apply (elaborate_success_iff _ _ _ _ _).mpr
  apply (checkFormation_iff _ _ _ _ _).mp
  decide

theorem binder_root_executes (bound : List TypeExpr) :
    constructorArguments? bindingLanguage FreeTypeContext.empty bound bindingFormer.declaration
        (.apply "BindPair" [token, binder]) = some [token, binder] := by
  let typed : ArgumentsHaveTypes bindingLanguage FreeTypeContext.empty bound [token, binder]
      bindingFormer.declaration.params :=
    .cons trivial rfl (token_typed bound) (.cons trivial rfl (binder_typed bound) .nil)
  let value : ConstructorValue bindingLanguage FreeTypeContext.empty bound bindingFormer.declaration :=
    .ordinary [token, binder] (by simp [bindingFormer, bindingLanguage, UsesBareCollection]) typed
  exact constructorArguments?_complete value (by
    change isObjectPattern (.apply "BindPair" [token, binder]) = true
    decide)

/-- A term of the binder's arrow carrier is not sufficient: the declared
abstraction representation itself must be present. -/
theorem binder_representation_rejected (bound : List TypeExpr) :
    constructorArguments? bindingLanguage FreeTypeContext.empty bound bindingFormer.declaration
        (.apply "BindPair" [token, .fvar "pretendBinder"]) = none := by
  simp [constructorArguments?, bindingFormer, bindingLanguage, usesBareCollection?,
    checkArgumentsHaveTypes, matchesParameterRepresentation?, parameterType?, token, checkHasType]

private def commEquation : Equation where
  name := "comm"
  typeContext := [("P", .base "Proc"), ("Q", .base "Proc")]
  premises := []
  left := commLeft "Parallel"
  right := commRight "Parallel"

private def assocEquation : Equation where
  name := "assoc"
  typeContext := [("P", .base "Proc"), ("Q", .base "Proc"), ("R", .base "Proc")]
  premises := []
  left := assocLeft "Parallel"
  right := assocRight "Parallel"

private def acLanguage : LanguageDef :=
  { unitLanguage with name := "ACStructural", equations := [commEquation, assocEquation] }

private def acFormer : Former := ⟨2, acLanguage.terms[2]'(by decide)⟩

/-- Both separating laws come from detected authored equations, for all
inhabitants and every ambient binding context. -/
theorem detected_ac_separating_laws (base : BasePremiseEvaluator) (bound : List TypeExpr)
    (first second third : Pattern → Prop) (term : Pattern) :
    (SplitHolds acLanguage FreeTypeContext.empty bound (EquationEquiv base acLanguage)
        acFormer first second term ↔
      SplitHolds acLanguage FreeTypeContext.empty bound (EquationEquiv base acLanguage)
        acFormer second first term) ∧
    (SplitHolds acLanguage FreeTypeContext.empty bound (EquationEquiv base acLanguage)
        acFormer first (SplitHolds acLanguage FreeTypeContext.empty bound
          (EquationEquiv base acLanguage) acFormer second third) term ↔
      SplitHolds acLanguage FreeTypeContext.empty bound (EquationEquiv base acLanguage)
        acFormer (SplitHolds acLanguage FreeTypeContext.empty bound
          (EquationEquiv base acLanguage) acFormer first second) third term) := by
  constructor
  · apply authored_ac_split_commutative base (firstName := "P") (secondName := "Q")
      (equation := commEquation)
    · rfl
    · rfl
  · apply authored_ac_split_associative base (firstName := "P") (secondName := "Q")
      (equation := assocEquation)
    · apply (mem_structuralFormers_iff _ _).mpr
      decide
    · rfl
    · rfl

/-- Authored unit expansion is not silently treated as a commutativity law. -/
theorem absent_ac_law_is_not_detected : findCommutativity unitLanguage "Parallel" = none := by
  rfl

end Mettapedia.OSLF.NativeTypes.Structural.Controls
