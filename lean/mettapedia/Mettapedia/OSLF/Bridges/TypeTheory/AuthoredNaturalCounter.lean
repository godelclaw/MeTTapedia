import Mettapedia.GSLT.LanguageDef.Examples.NativeNaturalCounter
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorFamilies

/-!
# The authored natural fragment in the existing dependent signature

Numerals inhabit the established natural-number family in every context.
The authored eliminator's two root rules produce that signature's iota
evidence and computation steps. The interpretation is parameterized by the
meaning of open leaves; no dependent formation judgment is inferred from raw
root execution. A concrete negative example preserves this distinction.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Bridges.TypeTheory.AuthoredNaturalCounter

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

open Mettapedia.GSLT.LanguageDef.Examples
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

def numeral {scope : Nat} : Nat → Tower.Tm scope
  | 0 => NativeNaturalVectorFamilies.zeroTm
  | count + 1 => NativeNaturalVectorFamilies.succApp (numeral count)

theorem numeral_hasType {scope : Nat} (context : Tower.Ctx scope) (count : Nat) :
    NativeNaturalVectorFamilies.HasType context (numeral count) NativeNaturalVectorFamilies.natTm := by
  induction count with
  | zero => exact NativeNaturalVectorFamilies.zeroTm_hasType
  | succ count ih => exact NativeNaturalVectorFamilies.succApp_hasType ih

theorem numeral_injective {scope : Nat} : Function.Injective (numeral (scope := scope)) := by
  intro first
  induction first with
  | zero => intro second equal; cases second <;> simp_all [numeral, NativeNaturalVectorFamilies.zeroTm, NativeNaturalVectorFamilies.succApp]
  | succ first ih =>
    intro second equal
    cases second with
    | zero => simp [numeral, NativeNaturalVectorFamilies.zeroTm, NativeNaturalVectorFamilies.succApp] at equal
    | succ second =>
      have inner : numeral first = numeral (scope := scope) second := by
        simpa only [numeral, NativeNaturalVectorFamilies.succApp, Tm.app.injEq, true_and] using equal
      exact congrArg Nat.succ (ih inner)

/-- The same natural data has both authored-pattern and dependent-term views. -/
theorem numeral_views_agree {scope : Nat} (first second : Nat) :
    NativeNaturalCounter.numeral first = NativeNaturalCounter.numeral second ↔
      numeral (scope := scope) first = numeral second := by
  rw [NativeNaturalCounter.numeral_injective.eq_iff, numeral_injective.eq_iff]

def interpret {scope : Nat} (environment : String → Tower.Tm scope) : NativeNaturalCounter.Term → Tower.Tm scope
  | .leaf atom => environment atom
  | .number count => numeral count
  | .app fn arg => .app (interpret environment fn) (interpret environment arg)
  | .eliminate motive zeroCase succCase count =>
      NativeNaturalVectorFamilies.natEliminateApp (interpret environment motive) (interpret environment zeroCase)
        (interpret environment succCase) (numeral count)

theorem iota_evidence {scope : Nat} (environment : String → Tower.Tm scope)
    {source target : NativeNaturalCounter.Term} (step : NativeNaturalCounter.Iota source target) :
    Nonempty (NativeNaturalVectorFamilies.IotaEvidence scope (interpret environment source) (interpret environment target)) := by
  cases step with
  | zero motive zeroCase succCase => exact ⟨.natZero _ _ _⟩
  | succ motive zeroCase succCase count => exact ⟨.natSucc _ _ _ _⟩

/-- Actual `.module` execution supplies raw dependent-calculus computation. -/
theorem authored_computation {scope : Nat} (environment : String → Tower.Tm scope)
    (base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator)
    {source target : NativeNaturalCounter.Term}
    (executed : Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base Mettapedia.GSLT.LanguageDef.Examples.NativeNaturalCounter.language
      source.encode target.encode) :
    NativeNaturalVectorFamilies.rules.computation.step (interpret environment source) (interpret environment target) := by
  have sourceStep := (NativeNaturalCounter.iota_step_iff base source target).mp executed
  cases sourceStep with
  | zero motive zeroCase succCase => exact NativeNaturalVectorFamilies.iota_natZero
  | succ motive zeroCase succCase count => exact NativeNaturalVectorFamilies.iota_natSucc

def untypedSource : NativeNaturalCounter.Term :=
  .eliminate (.number 0) (.number 0) (.leaf "undeclared") 0

def untypedEnvironment : String → Tower.Tm 0 := fun _ => NativeNaturalVectorFamilies.undeclaredCase

theorem untyped_source_executes (base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base Mettapedia.GSLT.LanguageDef.Examples.NativeNaturalCounter.language
      untypedSource.encode (NativeNaturalCounter.Term.number 0).encode := by
  rw [NativeNaturalCounter.iota_step_iff]
  exact .zero _ _ _

theorem untyped_source_has_no_type (type : Tower.Tm 0) :
    ¬ NativeNaturalVectorFamilies.HasType (.nil : Tower.Ctx 0) (interpret untypedEnvironment untypedSource) type :=
  NativeNaturalVectorFamilies.untypedNatZeroLeft_not_hasType type

/-- Raw iota execution remains available for an ill-formed submitted instance;
it must not be mistaken for acceptance by the dependent type checker. -/
theorem execution_does_not_grant_typing
    (base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base Mettapedia.GSLT.LanguageDef.Examples.NativeNaturalCounter.language
      untypedSource.encode (NativeNaturalCounter.Term.number 0).encode ∧
      ∀ type : Tower.Tm 0,
        ¬ NativeNaturalVectorFamilies.HasType (.nil : Tower.Ctx 0) (interpret untypedEnvironment untypedSource) type :=
  ⟨untyped_source_executes base, untyped_source_has_no_type⟩

end Mettapedia.OSLF.Bridges.TypeTheory.AuthoredNaturalCounter
