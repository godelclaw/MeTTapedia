import Mettapedia.GSLT.Causality.DoCalculus.AdjustCounts
import Mettapedia.GSLT.Causality.DoCalculus.BowBound
import Mettapedia.GSLT.Causality.DoCalculus.LanguageDef

/-!
# Revise the interventional truth value from observation

The premise is the identification sequent: the interventional query equals an
observational expression. The checker that discharges it is
`identificationDischarged`, which is `identify` returning `.doFree`. On the
bow that checker returns false. Where it returns true, for the front door and
the back door, pooling an experimental count is `Counts.revise` of the
interventional state derived from the adjustment counts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ContextualInference
open Mettapedia.Logic.EvidenceStateInsufficiency
open Mettapedia.ProbabilityTheory.BayesianNetworks

def reviseId : String := "$do:revise-from-observation"

/-- The observational expression identified for the interventional query,
revised by one experimental count. -/
def reviseTerm : GrammarRule where
  label := "$do:revise-interventional"
  category := exprType.name
  params :=
    [ .simple "identified" (.base exprType.name)
    , .simple "experiment" (.base exprType.name) ]
  syntaxPattern := []

def reviseFromObservationRule : Rule where
  id := ⟨reviseId⟩
  metavariables :=
    [("Gamma", 0), ("Delta", 0), ("Outcome", 0), ("Intervention", 0),
      ("Identified", 0), ("Experiment", 0)]
  premises :=
    [{ variableContext := .hole "Gamma"
       relationContext := .hole "Delta"
       conclusion :=
        .apply eqTerm.label
          [ .apply queryTerm.label
              [.fvar "Outcome", .fvar "Intervention", .apply emptySetTerm.label []]
          , .fvar "Identified" ] }]
  conclusion :=
    { variableContext := .hole "Gamma"
      relationContext := .hole "Delta"
      conclusion :=
        .apply eqTerm.label
          [ .apply queryTerm.label
              [.fvar "Outcome", .fvar "Intervention", .apply emptySetTerm.label []]
          , .apply reviseTerm.label [.fvar "Identified", .fvar "Experiment"] ] }

/-- One rule and one constructor, appended to the authored do-calculus. -/
def reviseExtension : CalculusLanguageExtension where
  newTerms := [reviseTerm]
  newRules := [lowerRule reviseFromObservationRule]

theorem revise_rule_id :
    (lowerRule reviseFromObservationRule).id.value = reviseId := by
  rfl

theorem revise_rule_id_fresh :
    reviseId ∉ [rule1Id, rule2Id, rule3Id, chainId, bayesId, emptyDoId, marginalId] := by
  decide

theorem revise_extension_appends :
    (reviseExtension.apply definition).rules =
      definition.rules ++ [lowerRule reviseFromObservationRule] ∧
      (reviseExtension.apply definition).terms = definition.terms ++ [reviseTerm] := by
  simp [reviseExtension, CalculusLanguageExtension.apply_rules,
    CalculusLanguageExtension.apply_terms]

/-- The identification sequent is discharged when `identify` returns a do-free
expression. -/
def identificationDischarged {V : Type} [Fintype V] [DecidableEq V]
    (graph : DirectedGraph V) [DecidableRel graph.edges]
    (fuel : Nat) (enum : List V) (L outcome intervention conditioning : Finset V) : Bool :=
  match identify graph fuel enum L outcome intervention conditioning with
  | .doFree _ => true
  | .hedge _ => false

theorem revise_rule_misses_bow :
    identificationDischarged bowGraph 2 bowEnum {Bow.u} {Bow.y} {Bow.x}
      (∅ : Finset Bow) = false := by
  have hhedge := bow_id_returns_hedge
  cases hrun : identify bowGraph 2 bowEnum {Bow.u} {Bow.y} {Bow.x} (∅ : Finset Bow) with
  | doFree _ =>
      simp [hrun] at hhedge
  | hedge _ =>
      simp [identificationDischarged, hrun]

theorem revise_rule_sound_front (experiment : Bool)
    (hprem : identificationDischarged smokeGraph 2 smokeEnum {Smoke.u} {Smoke.c} smokeS
      (∅ : Finset Smoke) = true) :
    (poolInterventional frontDoorState experiment).interventional =
      frontDoorCounts.revise experiment ∧
    (poolInterventional frontDoorState experiment).observational = smokeObsCounts := by
  cases hrun : identify smokeGraph 2 smokeEnum {Smoke.u} {Smoke.c} smokeS (∅ : Finset Smoke) with
  | hedge _ =>
      simp [identificationDischarged, hrun] at hprem
  | doFree _ =>
      exact front_door_pool_is_one_revision experiment

theorem revise_rule_sound_back (experiment : Bool)
    (hprem : identificationDischarged doorGraph 2 doorEnum (∅ : Finset Door) doorY doorX
      (∅ : Finset Door) = true) :
    (poolInterventional backDoorState experiment).interventional =
      backDoorCounts.revise experiment ∧
    (poolInterventional backDoorState experiment).observational = doorObsCounts := by
  cases hrun : identify doorGraph 2 doorEnum (∅ : Finset Door) doorY doorX (∅ : Finset Door) with
  | hedge _ =>
      simp [identificationDischarged, hrun] at hprem
  | doFree _ =>
      exact back_door_pool_is_one_revision experiment

end Mettapedia.GSLT.Causality.DoCalculus
