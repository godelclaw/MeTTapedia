import Mettapedia.PLN.Bridges.GSLT.EvidenceTermSettings

/-!
# Semantic soundness of instantiated evidence-calculus proofs

The shared nine-rule definition has one recursive interpretation indexed by
its four semantic settings. Checking an open proof implies its interpreted
conclusion whenever the external context judgments are true. This includes
arbitrarily nested rule arguments, not only the original variable schemas.

No interpretation translates counts into likelihoods or identifies the
settings' world carriers. Bridges between settings remain explicit theorems.
-/

namespace Mettapedia.PLN.Bridges.GSLT.EvidenceTermComposition

open Mettapedia.GSLT.LanguageDef.FirstOrderCalculus
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.SemanticSettings
open Mettapedia.PLN.Bridges.GSLT.EvidenceCalculusModule

def ModelAt : SemanticSetting → Type 1
  | .ledger => LedgerTermSemantics.Model
  | .samples => EvidenceTermSettings.Samples.Model
  | .reports => EvidenceTermSettings.Reports.Model
  | .population => EvidenceTermSettings.Population.Model

def reading : (setting : SemanticSetting) → ModelAt setting → Pattern → Prop
  | .ledger => LedgerTermSemantics.Model.holds
  | .samples => EvidenceTermSettings.Samples.Model.holds
  | .reports => EvidenceTermSettings.Reports.Model.holds
  | .population => EvidenceTermSettings.Population.Model.holds

abbrev Models := (setting : SemanticSetting) → ModelAt setting

noncomputable def meaning : Models → Pattern → Prop := combinedHolds settingOf reading

private theorem arguments_seven {arguments : List Pattern} (length : arguments.length = 7) :
    ∃ a b c d e f g, arguments = [a, b, c, d, e, f, g] := by
  let [a, b, c, d, e, f, g] := arguments
  exact ⟨a, b, c, d, e, f, g, rfl⟩

/-- Each actual admitted application preserves the combined interpretation.
Its semantic contracts remain ordinary, externally established premises. -/
theorem rule_application_sound (models : Models) (ruleInstance : RuleInstance)
    (premises : List Pattern) (conclusion : Pattern)
    (application : RuleApplication evidenceCalculusValidated ruleInstance premises conclusion)
    (premisesSound : ∀ premise ∈ premises, meaning models premise) : meaning models conclusion := by
  rcases ruleInstance with ⟨id, arguments⟩
  cases application with
  | intro schema lookup valid _ premisesInstantiate conclusionInstantiates =>
    have member := List.mem_of_find?_eq_some lookup
    change schema ∈ evidenceRules at member
    simp only [evidenceRules, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have length : arguments.length = 3 := (argumentsValidAt_length valid).symm
      obtain ⟨q, first, second, argumentsEq⟩ := List.length_eq_three.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [rule, fv, app, observationCounts, observationLowerBound, ledgerHolds,
        countReadout, sampleCounts, sampleHolds, reportLikelihoods, reportHolds,
        populationReadout, populationHolds] at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      have hypotheses := premisesSound
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hypotheses
      dsimp only [meaning, combinedHolds, settingOf, reading, observationCounts,
        observationLowerBound, ledgerHolds, countReadout, sampleCounts, sampleHolds,
        reportLikelihoods, reportHolds, populationReadout, populationHolds, app] at hypotheses ⊢
      exact LedgerTermSemantics.Model.revise (models .ledger) q first second hypotheses.1 hypotheses.2.1 hypotheses.2.2
    · have length : arguments.length = 3 := (argumentsValidAt_length valid).symm
      obtain ⟨q, first, second, argumentsEq⟩ := List.length_eq_three.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [rule, fv, app, observationCounts, observationLowerBound, ledgerHolds,
        countReadout, sampleCounts, sampleHolds, reportLikelihoods, reportHolds,
        populationReadout, populationHolds] at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      have hypotheses := premisesSound
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hypotheses
      dsimp only [meaning, combinedHolds, settingOf, reading, observationCounts,
        observationLowerBound, ledgerHolds, countReadout, sampleCounts, sampleHolds,
        reportLikelihoods, reportHolds, populationReadout, populationHolds, app] at hypotheses ⊢
      exact LedgerTermSemantics.Model.revise_unknown_overlap (models .ledger) q first second hypotheses.1 hypotheses.2
    · have length : arguments.length = 2 := (argumentsValidAt_length valid).symm
      obtain ⟨q, e, argumentsEq⟩ := List.length_eq_two.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [rule, fv, app, observationCounts, observationLowerBound, ledgerHolds,
        countReadout, sampleCounts, sampleHolds, reportLikelihoods, reportHolds,
        populationReadout, populationHolds] at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      have hypotheses := premisesSound
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hypotheses
      dsimp only [meaning, combinedHolds, settingOf, reading, observationCounts,
        observationLowerBound, ledgerHolds, countReadout, sampleCounts, sampleHolds,
        reportLikelihoods, reportHolds, populationReadout, populationHolds, app] at hypotheses ⊢
      exact LedgerTermSemantics.Model.negate (models .ledger) q e hypotheses
    · have length : arguments.length = 3 := (argumentsValidAt_length valid).symm
      obtain ⟨q, first, second, argumentsEq⟩ := List.length_eq_three.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [rule, fv, app, observationCounts, observationLowerBound, ledgerHolds,
        countReadout, sampleCounts, sampleHolds, reportLikelihoods, reportHolds,
        populationReadout, populationHolds] at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      have hypotheses := premisesSound
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hypotheses
      dsimp only [meaning, combinedHolds, settingOf, reading, observationCounts,
        observationLowerBound, ledgerHolds, countReadout, sampleCounts, sampleHolds,
        reportLikelihoods, reportHolds, populationReadout, populationHolds, app] at hypotheses ⊢
      exact EvidenceTermSettings.Reports.Model.fuse (models .reports) q first second hypotheses.1 hypotheses.2.1 hypotheses.2.2
    · have length : arguments.length = 4 := (argumentsValidAt_length valid).symm
      obtain ⟨a, b, first, second, argumentsEq⟩ := List.length_eq_four.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [rule, fv, app, observationCounts, observationLowerBound, ledgerHolds,
        countReadout, sampleCounts, sampleHolds, reportLikelihoods, reportHolds,
        populationReadout, populationHolds] at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      have hypotheses := premisesSound
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hypotheses
      dsimp only [meaning, combinedHolds, settingOf, reading, observationCounts,
        observationLowerBound, ledgerHolds, countReadout, sampleCounts, sampleHolds,
        reportLikelihoods, reportHolds, populationReadout, populationHolds, app] at hypotheses ⊢
      exact EvidenceTermSettings.Samples.Model.conjoin (models .samples) a b first second hypotheses.1 hypotheses.2.1 hypotheses.2.2
    · have length : arguments.length = 4 := (argumentsValidAt_length valid).symm
      obtain ⟨a, b, first, second, argumentsEq⟩ := List.length_eq_four.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [rule, fv, app, observationCounts, observationLowerBound, ledgerHolds,
        countReadout, sampleCounts, sampleHolds, reportLikelihoods, reportHolds,
        populationReadout, populationHolds] at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      have hypotheses := premisesSound
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hypotheses
      dsimp only [meaning, combinedHolds, settingOf, reading, observationCounts,
        observationLowerBound, ledgerHolds, countReadout, sampleCounts, sampleHolds,
        reportLikelihoods, reportHolds, populationReadout, populationHolds, app] at hypotheses ⊢
      exact LedgerTermSemantics.Model.conjoin_one_world (models .ledger) a b first second hypotheses.1 hypotheses.2.1 hypotheses.2.2
    · have length : arguments.length = 7 := (argumentsValidAt_length valid).symm
      obtain ⟨a, b, c, s1, s2, s3, s4, argumentsEq⟩ := arguments_seven length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [rule, fv, app, observationCounts, observationLowerBound, ledgerHolds,
        countReadout, sampleCounts, sampleHolds, reportLikelihoods, reportHolds,
        populationReadout, populationHolds] at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      have hypotheses := premisesSound
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hypotheses
      dsimp only [meaning, combinedHolds, settingOf, reading, observationCounts,
        observationLowerBound, ledgerHolds, countReadout, sampleCounts, sampleHolds,
        reportLikelihoods, reportHolds, populationReadout, populationHolds, app] at hypotheses ⊢
      exact EvidenceTermSettings.Population.Model.deduce (models .population) a b c s1 s2 s3 s4 hypotheses.1 hypotheses.2.1 hypotheses.2.2.1 hypotheses.2.2.2.1 hypotheses.2.2.2.2
    · have length : arguments.length = 2 := (argumentsValidAt_length valid).symm
      obtain ⟨q, e, argumentsEq⟩ := List.length_eq_two.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [rule, fv, app, observationCounts, observationLowerBound, ledgerHolds,
        countReadout, sampleCounts, sampleHolds, reportLikelihoods, reportHolds,
        populationReadout, populationHolds] at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      have hypotheses := premisesSound
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hypotheses
      dsimp only [meaning, combinedHolds, settingOf, reading, observationCounts,
        observationLowerBound, ledgerHolds, countReadout, sampleCounts, sampleHolds,
        reportLikelihoods, reportHolds, populationReadout, populationHolds, app] at hypotheses ⊢
      exact LedgerTermSemantics.Model.read_strength (models .ledger) q e hypotheses
    · have length : arguments.length = 2 := (argumentsValidAt_length valid).symm
      obtain ⟨q, e, argumentsEq⟩ := List.length_eq_two.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [rule, fv, app, observationCounts, observationLowerBound, ledgerHolds,
        countReadout, sampleCounts, sampleHolds, reportLikelihoods, reportHolds,
        populationReadout, populationHolds] at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      have hypotheses := premisesSound
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hypotheses
      dsimp only [meaning, combinedHolds, settingOf, reading, observationCounts,
        observationLowerBound, ledgerHolds, countReadout, sampleCounts, sampleHolds,
        reportLikelihoods, reportHolds, populationReadout, populationHolds, app] at hypotheses ⊢
      exact LedgerTermSemantics.Model.read_interval (models .ledger) q e hypotheses

/-- End-to-end semantic soundness of the actual open proof checker. -/
theorem checked_proof_sound (models : Models) (context : List Pattern) (goal : Pattern)
    (proof : RawOpenProof)
    (checked : checkOpenRaw evidenceCalculusValidated context goal proof = true)
    (contextSound : ∀ premise ∈ context, meaning models premise) : meaning models goal := by
  obtain ⟨derivation, _⟩ := checkOpenRaw_exact_derivation checked
  exact derivation.sound_of_ruleApplications (meaning models)
    (rule_application_sound models) contextSound

end Mettapedia.PLN.Bridges.GSLT.EvidenceTermComposition
