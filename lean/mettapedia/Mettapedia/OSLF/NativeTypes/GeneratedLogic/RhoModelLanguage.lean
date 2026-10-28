import Mettapedia.OSLF.NativeTypes.Instances.Normalized.RhoProfile
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Reference
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep

/-!
# ρ's runtime model, written as a language

The normalized ρ profile (`Instances.Normalized.RhoProfile`) runs ρ's compiled plan modulo a model of its own: the
parallel laws (permutation, flattening of a bag inside a bag, removal of `0`) and the name equation `@(*n) = n`. The
model keeps the wrappers apart: `{P}` is not `P` and `{}` is not `0`. ρ's declared algebra identifies them, since a
flattening algebra derives the singleton law and a unit derives the empty law. So the model is written as a language
of its own (`language`): ρ's constructors and rules, without the declared algebra, with the model's laws authored as
equations.

- **Flattening, one member at a time** (`flattenHead`, `flattenEmpty`): `{{x, ...inner}, ...rest} = {x, {...inner},
  ...rest}` and `{{}, ...rest} = {...rest}`. Matching a bag picks its members anywhere, so the first equation also moves
  any member to the front.
- **The unit** (`unitLaw`): `{0, ...rest} = {...rest}`.
- **The name equation**: ρ's `QuoteDrop`.

Its rules are ρ's, read as the plan reads them (`reading`): a rule fires at a process of ρ's carrier, closed,
well-sorted in the plan's sorting and sealed by its quotations, matching syntactically and substituting by ρ's
reflective substitution.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoModel

open Mettapedia.OSLF.MeTTaIL Syntax Match
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep (RuleInterpretation)
open Mettapedia.GSLT.LanguageDef.ReflectionExtension (rhoReflectionProfile)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (applyBindingsForRuleUsing)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep (rhoBasePremises)
open Mettapedia.OSLF.NativeTypes.Instances.Normalized

/-! ## The language -/

/-- A constructor without a declared collection algebra. -/
def withoutAlgebra (rule : GrammarRule) : GrammarRule := {rule with algebra? := none}

/-- A parallel composition, with a rest variable or none. -/
abbrev bag (elements : List Pattern) (rest : Option String := none) : Pattern := .collection .hashBag elements rest

/-- **Flattening one member**: `{{x, ...inner}, ...rest} = {x, {...inner}, ...rest}`. -/
def flattenHead : Equation where
  name := "FlattenHead"
  typeContext := [("x", TypeExpr.proc)]
  premises := []
  left := bag [bag [.fvar "x"] (some "inner")] (some "rest")
  right := bag [.fvar "x", bag [] (some "inner")] (some "rest")

/-- **Flattening the empty bag**: `{{}, ...rest} = {...rest}`. -/
def flattenEmpty : Equation where
  name := "FlattenEmpty"
  typeContext := []
  premises := []
  left := bag [bag []] (some "rest")
  right := bag [] (some "rest")

/-- **The unit**: `{0, ...rest} = {...rest}`. -/
def unitLaw : Equation where
  name := "Unit"
  typeContext := []
  premises := []
  left := bag [.apply "PZero" []] (some "rest")
  right := bag [] (some "rest")

/-- **ρ's runtime model as a language**: ρ's constructors without the declared algebra, its rules, and the model's
laws as equations. -/
def language : LanguageDef :=
  { rhoCalc with
    name := "RhoModel"
    terms := rhoCalc.terms.map withoutAlgebra
    equations := rhoCalc.equations ++ [flattenHead, flattenEmpty, unitLaw] }

-- The model passes the language validation gate.
#guard language.validate.isEmpty

theorem rewrites_eq : language.rewrites = [rhoCommRewrite, rhoParCongRewrite] := rfl

theorem equations_eq : language.equations =
    [rhoCalc.equations[0], flattenHead, flattenEmpty, unitLaw] := rfl

/-- No constructor of the model declares an algebra. -/
theorem no_algebra {rule : GrammarRule} (member : rule ∈ language.terms) : rule.algebra? = none := by
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  rfl

/-! ## The reading -/

abbrev proc : TypeExpr := .base "Proc"

/-- **A closed process in the plan's sorting**, where the plan fires. -/
def sorted (term : Pattern) : Bool :=
  checkOpenPatternWellSorted RhoPrimitive.plan.snapshot.language RhoPrimitive.plan.snapshot.free [] proc term

theorem sorted_iff {term : Pattern} : sorted term = true ↔ RhoPrimitive.Source term :=
  checkOpenPatternWellSorted_eq_true_iff _ _ _ _ _

/-- **A process sealed by its quotations**: a quoted process mentions no variable bound outside it. -/
def sealed (term : Pattern) : Bool := ScopedPattern.binderSafeAt "NQuote" 0 term

/-- **ρ's carrier**: closed processes sorted in the plan's sorting and sealed by their quotations. -/
def carrier (term : Pattern) : Bool := sorted term && sealed term

/-- **How the plan reads ρ's rules**: at a process of ρ's carrier, syntactic matching, and ρ's reflective
substitution. -/
def interpretation : RuleInterpretation where
  matchRule := fun _ rule term => if carrier term then matchPattern rule.left term else []
  instantiateRule := fun _ rule bindings => applyBindingsForRuleUsing rhoReflectionProfile rule bindings

/-- **The model's reading**: its equations as the syntax theory, its rules as the plan reads them. -/
def reading : LanguageReading where
  rules := .interpreted interpretation rhoBasePremises

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoModel
