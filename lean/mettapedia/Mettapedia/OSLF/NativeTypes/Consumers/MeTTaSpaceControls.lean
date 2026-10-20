import Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpace

/-! # Executable controls at the Zero / PeTTa reflective-space boundary -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpace.Controls

open Mettapedia.Languages.MeTTa
open Mettapedia.OSLF.MeTTaIL.Syntax
open PeTTa.MeTTaZeroExtension.NativeControls
open Mettapedia.OSLF.MeTTaIL.Match

def spaceTerm : Pattern := .apply "&self" []
def equation : Pattern := .apply "=" [a, b]
def pattern : Pattern := .apply "=" [a, .fvar "result"]
def template : Pattern := .fvar "result"
def absent : Pattern := .apply "absent" []

def article (copy : Nat) : MeTTaZeroStagedAdequacy.ObservationProof :=
  .produced (.query ⟨equation, copy, [("result", b)], 0⟩)

theorem duplicate_query : duplicateRules.spaceMatch pattern template = [b, b] := by
  simp [PeTTa.PeTTaSpace.spaceMatch, PeTTa.PeTTaSpace.storedAtoms,
    PeTTa.PeTTaSpace.storedRuleAtoms, PeTTa.PeTTaSpace.storedRuleAtom?,
    duplicateRules, ordinaryFact, rule, pattern, template, a, b,
    matchPattern, matchArgs, mergeBindings, applyBindings]

theorem duplicate_copies_decided :
    checkOccurrence duplicateRules pattern template b 0 = true ∧
    checkOccurrence duplicateRules pattern template b 1 = true ∧
    checkOccurrence duplicateRules pattern template b 2 = false ∧
    checkOccurrence duplicateRules pattern template a 0 = false := by
  simp [checkOccurrence, duplicate_query, a, b]

theorem complete_packet_decided :
    checkPacket duplicateRules pattern template [b, b] = true ∧
    checkPacket duplicateRules pattern template [b] = false ∧
    checkPacket duplicateRules pattern template [b, b, b] = false ∧
    checkPacket duplicateRules pattern template [a, b] = false := by
  simp [checkPacket, duplicate_query, a, b]
  decide

theorem duplicate_native_types :
    QueryMember duplicateRules pattern template b 0 ∧
    QueryMember duplicateRules pattern template b 1 ∧
    ¬ QueryMember duplicateRules pattern template b 2 :=
  ⟨(checkOccurrence_exact _ _ _ _ _).mp duplicate_copies_decided.1,
    (checkOccurrence_exact _ _ _ _ _).mp duplicate_copies_decided.2.1,
    (checkOccurrence_refutes _ _ _ _ _).mp duplicate_copies_decided.2.2.1⟩

/-- A payload-only packet is incomplete despite every supplied value being
an actual answer. The missing occurrence has its own source-derived type. -/
theorem value_membership_does_not_certify_packet :
    (∀ value ∈ [b], ∃ occurrence, QueryMember duplicateRules pattern template value occurrence) ∧
    checkPacket duplicateRules pattern template [b] = false := by
  constructor
  · intro value member
    simp only [List.mem_singleton] at member
    subst value
    exact ⟨0, duplicate_native_types.1⟩
  · exact complete_packet_decided.2.1

theorem article_checks :
    checkArticle duplicateRules spaceTerm pattern template b (article 0) = true ∧
    checkArticle duplicateRules spaceTerm pattern template b (article 1) = true ∧
    checkArticle duplicateRules spaceTerm pattern template b (article 2) = false ∧
    checkArticle duplicateRules spaceTerm pattern template a (article 0) = false := by
  simp [checkArticle, queryClaim, MeTTaZeroNativeKernel.proofKernel,
    MeTTaZeroStagedAdequacy.checkObservationProof,
    MeTTaZeroStagedAdequacy.checkProductionProof,
    MeTTaZeroStagedAdequacy.checkQueryProof,
    MeTTaZeroStagedAdequacy.classifiedRequest,
    PeTTa.MeTTaZeroExtension.model, PeTTa.PeTTaSpace.storedAtoms,
    PeTTa.PeTTaSpace.storedRuleAtoms, PeTTa.PeTTaSpace.storedRuleAtom?,
    duplicateRules, ordinaryFact, rule, article, equation, pattern, template,
    a, b, matchPattern, matchArgs, mergeBindings, applyBindings]

theorem article_origins_distinct : article 0 ≠ article 1 := by decide

theorem rejected_article_does_not_refute :
    checkArticle duplicateRules spaceTerm pattern template b (article 2) = false ∧
    QueryMember duplicateRules pattern template b 0 :=
  ⟨article_checks.2.2.1, duplicate_native_types.1⟩

theorem empty_query_decided :
    checkPacket duplicateRules absent template [] = true ∧
    checkOccurrence duplicateRules absent template b 0 = false := by
  simp [checkPacket, checkOccurrence, PeTTa.PeTTaSpace.spaceMatch,
    PeTTa.PeTTaSpace.storedAtoms, PeTTa.PeTTaSpace.storedRuleAtoms,
    PeTTa.PeTTaSpace.storedRuleAtom?, duplicateRules, ordinaryFact, rule,
    absent, template, a, b, matchPattern]

def distinctFacts : PeTTa.PeTTaSpace := { facts := [a, b], rules := [] }

theorem bag_observation_ignores_enumeration_order :
    checkPacket distinctFacts (.fvar "x") (.fvar "x") [a, b] = true ∧
    checkPacket distinctFacts (.fvar "x") (.fvar "x") [b, a] = true := by
  simp [checkPacket, PeTTa.PeTTaSpace.spaceMatch, PeTTa.PeTTaSpace.storedAtoms,
    PeTTa.PeTTaSpace.storedRuleAtoms, distinctFacts, matchPattern, applyBindings]
  decide

/-- The same public query sees equation-shaped data and selected rules. -/
theorem reflected_equation_is_queryable :
    checkOccurrence factEquationOnly pattern template b 0 = true := by
  simp [checkOccurrence, PeTTa.PeTTaSpace.spaceMatch, PeTTa.PeTTaSpace.storedAtoms,
    PeTTa.PeTTaSpace.storedRuleAtoms, factEquationOnly, pattern, template, a, b,
    matchPattern, matchArgs, mergeBindings, applyBindings]

def reflectiveEvaluation : MeTTaZeroNativeKernel.Claim PeTTa.MeTTaZeroExtension.model :=
  ⟨.evaluate factEquationOnly spaceTerm a, b⟩

/-- Zero uses its reflective medium for evaluation; the actual PeTTa selected
rule table is empty here. This is a semantic boundary, not an execution bug. -/
theorem reflected_evaluation_is_not_selected_rule :
    (MeTTaZeroNativeKernel.decisionKernel PeTTa.MeTTaZeroExtension.model).decide
      reflectiveEvaluation = true ∧
    PeTTa.MeTTaZeroExtension.premiseFreeRuleResults factEquationOnly a = [] := by
  constructor
  · change decide (b ∈ MeTTaZeroStagedAdequacy.run PeTTa.MeTTaZeroExtension.model
      (.evaluate factEquationOnly a)) = true
    rw [decide_eq_true_eq, MeTTaZeroStagedAdequacy.run_evaluate,
      MeTTaZero.evaluateOne, MeTTaZero.interpretedResults,
      fact_equation_is_not_selected_rule.1]
    simp
  · exact fact_equation_is_not_selected_rule.2

theorem reflected_evaluation_has_authored_step : reflectiveEvaluation.Meaning :=
  (MeTTaZeroNativeKernel.decisionKernel PeTTa.MeTTaZeroExtension.model).correct
    reflectiveEvaluation |>.mp reflected_evaluation_is_not_selected_rule.1

theorem fact_equation_breaks_authority_condition :
    ¬ PeTTa.MeTTaZeroExtension.NoFactEquations factEquationOnly := by
  intro authority
  have rejected := authority equation (by decide)
  simp [equation, MeTTaZero.viewEquation?] at rejected

/-- Executable regression controls used by the shared consumer runner. -/
def verdicts : List (String × Bool) :=
  [("first occurrence", checkOccurrence duplicateRules pattern template b 0),
   ("second equal occurrence", checkOccurrence duplicateRules pattern template b 1),
   ("no third occurrence", !checkOccurrence duplicateRules pattern template b 2),
   ("wrong value", !checkOccurrence duplicateRules pattern template a 0),
   ("exact packet", checkPacket duplicateRules pattern template [b, b]),
   ("missing copy", !checkPacket duplicateRules pattern template [b]),
   ("extra copy", !checkPacket duplicateRules pattern template [b, b, b]),
   ("wrong packet", !checkPacket duplicateRules pattern template [a, b]),
   ("first article", checkArticle duplicateRules spaceTerm pattern template b (article 0)),
   ("second article", checkArticle duplicateRules spaceTerm pattern template b (article 1)),
   ("invalid article for true claim", !checkArticle duplicateRules spaceTerm pattern template b (article 2)),
   ("wrong article target", !checkArticle duplicateRules spaceTerm pattern template a (article 0)),
   ("origins stay distinct", decide (article 0 ≠ article 1)),
   ("empty packet", checkPacket duplicateRules absent template []),
   ("empty query has no occurrence", !checkOccurrence duplicateRules absent template b 0),
   ("ordered presentation", checkPacket distinctFacts (.fvar "x") (.fvar "x") [a, b]),
   ("permuted presentation", checkPacket distinctFacts (.fvar "x") (.fvar "x") [b, a]),
   ("equation data is queryable", checkOccurrence factEquationOnly pattern template b 0)]

end Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpace.Controls
