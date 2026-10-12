import Mettapedia.OSLF.MeTTaIL.AuthoredEquationOccurrenceSearch
import Mettapedia.OSLF.Framework.ResumableEquationCoverage

/-!
# Authored occurrence search and its independent typed instance judgments

An authored origin refers to a declaration position, an indexed scoped match,
an ordered finite-premise derivation and its instantiated target. The queue
algorithm is compared with these judgments rather than used to define them.
Every partial run has a sound equation trace and a sound primitive firing.

Supported finite queries earn root-instance completeness. Full equation-class
coverage additionally needs reversibility of the admitted typed instances;
an arbitrary binding declaration is not assumed to have that property.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.AuthoredEquationOccurrenceSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax Engine
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)
open ScopedEquationExecution (Orientation)


def Equation (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (origin : ConditionalEquationExecution.EquationReceipt) (source target : Pattern) : Prop :=
  ∃ equation index orientation,
    (equation, index) ∈ language.equations.zipIdx ∧
      ConditionalEquationExecution.EquationInstance relEnv language free bound expected
        index equation orientation source origin ∧ target = origin.target

def Firing (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (source : Pattern) (origin : AuthoredEquationOccurrenceSearch.RuleOrigin) (target : Pattern) : Prop :=
  ∃ rule, (rule, origin.ruleIndex) ∈ language.rewrites.zipIdx ∧
    ConditionalEquationExecution.RuleInstance relEnv language free bound expected
      rule source origin.toReceipt ∧ target = origin.target

def Conversion (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (source target : Pattern) : Prop :=
  ∃ origin, Equation relEnv language free bound expected origin source target

def Primitive (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (source : Pattern) (answer : AuthoredEquationOccurrenceSearch.RuleOrigin × Pattern) : Prop :=
  Firing relEnv language free bound expected source answer.1 answer.2

/-- The admitted scoped presentation generates an actual equation-saturated GSLT.
Comparison with an untyped raw presentation is a separate admission theorem. -/
def gslt (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr) :=
  Mettapedia.OSLF.Framework.FiniteEquationCoverage.moduloGSLT (Conversion relEnv language free bound expected)
    (Primitive relEnv language free bound expected) Prod.snd

theorem equations_sound (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (source target : Pattern) (origin : ConditionalEquationExecution.EquationReceipt)
    (present : (origin, target) ∈
      (AuthoredEquationOccurrenceSearch.equationBatch relEnv language free bound expected source).answers) :
    Equation relEnv language free bound expected origin source target := by
  obtain ⟨equation, index, orientation, declared, actual, readout⟩ :=
    AuthoredEquationOccurrenceSearch.equationBatch_readout relEnv language free bound expected source target origin present
  exact ⟨equation, index, orientation, declared,
    ConditionalEquationExecution.applyAt_sound relEnv language free bound expected
      index equation orientation source origin actual, readout⟩

theorem firings_sound (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (source target : Pattern) (origin : AuthoredEquationOccurrenceSearch.RuleOrigin)
    (present : (origin, target) ∈
      (AuthoredEquationOccurrenceSearch.firingBatch relEnv language free bound expected source).answers) :
    Firing relEnv language free bound expected source origin target := by
  obtain ⟨rule, index, receipt, declared, actual, retained, position, readout⟩ :=
    AuthoredEquationOccurrenceSearch.firingBatch_readout relEnv language free bound expected source target origin present
  rw [← position] at declared
  exact ⟨rule, declared, retained ▸
    ConditionalEquationExecution.applyRuleAtOutcome_sound relEnv language free bound expected
      rule source receipt actual, retained ▸ readout⟩

def RulesSupported (language : LanguageDef) : Prop :=
  ∀ rule ∈ language.rewrites, ∀ spec, rule.bindings = some spec →
    ConditionalEquationExecution.queriesSupported spec 0 rule.premises = true

def EquationsSupported (language : LanguageDef) : Prop :=
  ∀ equation ∈ language.equations, ∀ orientation spec,
    (ScopedEquationExecution.orientedRule equation orientation).bindings = some spec →
      ConditionalEquationExecution.queriesSupported spec 0 equation.premises = true

theorem firings_complete (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (supported : RulesSupported language)
    (source target : Pattern) (origin : AuthoredEquationOccurrenceSearch.RuleOrigin)
    (fire : Firing relEnv language free bound expected source origin target) :
    (origin, target) ∈
      (AuthoredEquationOccurrenceSearch.firingBatch relEnv language free bound expected source).answers := by
  obtain ⟨rule, declared, fire, readout⟩ := fire
  have actual := ConditionalEquationExecution.applyRuleAtOutcome_complete relEnv language free bound expected
    rule source origin.toReceipt (supported rule (List.fst_mem_of_mem_zipIdx declared)) fire
  simp only [AuthoredEquationOccurrenceSearch.firingBatch, List.mem_flatMap, List.mem_map]
  refine ⟨(rule, origin.ruleIndex), declared, origin.toReceipt, actual, ?_⟩
  cases origin
  simp_all

theorem equations_complete (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (supported : EquationsSupported language)
    (source target : Pattern) (origin : ConditionalEquationExecution.EquationReceipt)
    (convert : Equation relEnv language free bound expected origin source target) :
    (origin, target) ∈
      (AuthoredEquationOccurrenceSearch.equationBatch relEnv language free bound expected source).answers := by
  obtain ⟨equation, index, orientation, declared, convert, readout⟩ := convert
  have actual := ConditionalEquationExecution.applyAt_complete relEnv language free bound expected
    index equation orientation source origin
    (supported equation (List.fst_mem_of_mem_zipIdx declared) orientation) convert
  simp only [AuthoredEquationOccurrenceSearch.equationBatch, List.mem_flatMap, List.mem_map]
  exact ⟨(equation, index, orientation),
    (AuthoredEquationOccurrenceSearch.equationCases_spec language equation index orientation).mpr declared,
    origin, actual, by simp [readout]⟩

/-- Soundness does not require an exhausted frontier or an exhaustive provider. -/
theorem run_sound (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (source : Pattern) (fuel : Nat) :
    Mettapedia.OSLF.Framework.ResumableEquationOccurrenceFrontier.Snapshot.Valid (Equation relEnv language free bound expected)
      (Firing relEnv language free bound expected) source
      (Mettapedia.OSLF.Framework.ResumableEquationOccurrenceFrontier.run (AuthoredEquationOccurrenceSearch.model relEnv language free bound expected) fuel (Mettapedia.OSLF.Framework.ResumableEquationOccurrenceFrontier.initial source)) := by
  exact Mettapedia.OSLF.Framework.ResumableEquationOccurrenceFrontier.run_valid (AuthoredEquationOccurrenceSearch.model relEnv language free bound expected)
    (Equation relEnv language free bound expected) (Firing relEnv language free bound expected)
    (fun node edge present => equations_sound relEnv language free bound expected
      node edge.2 edge.1 present)
    (fun node answer present => firings_sound relEnv language free bound expected
      node answer.2 answer.1 present) source fuel _
    (Mettapedia.OSLF.Framework.ResumableEquationOccurrenceFrontier.initial_valid _ _ source)

/-- Every returned receipt supplies an actual step of the independently
generated scoped GSLT, while its equation trace remains separate. -/
theorem emitted_gslt_step (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (source : Pattern) (fuel : Nat)
    (receipt : Mettapedia.OSLF.Framework.ResumableEquationOccurrenceFrontier.Receipt Pattern ConditionalEquationExecution.EquationReceipt AuthoredEquationOccurrenceSearch.RuleOrigin)
    (present : receipt ∈
      (Mettapedia.OSLF.Framework.ResumableEquationOccurrenceFrontier.run (AuthoredEquationOccurrenceSearch.model relEnv language free bound expected) fuel
        (Mettapedia.OSLF.Framework.ResumableEquationOccurrenceFrontier.initial source)).receipts) :
    (gslt relEnv language free bound expected).Step source receipt.target := by
  have valid := (run_sound relEnv language free bound expected source fuel).receipts receipt present
  refine ⟨receipt.representative.state, (receipt.origin, receipt.target), ?_, valid.2, .refl _⟩
  exact Mettapedia.OSLF.Framework.ResumableEquationOccurrenceFrontier.TraceValid.equivalent
    (Equation relEnv language free bound expected) source receipt.representative.state
    receipt.representative.conversions valid.1

end Mettapedia.OSLF.MeTTaIL.AuthoredEquationOccurrenceSemantics
