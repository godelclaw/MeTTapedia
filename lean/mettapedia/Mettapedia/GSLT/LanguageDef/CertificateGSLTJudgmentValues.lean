import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenApplicationWire

/-!
# Requests, rule programs and derivation data

These three physical constructors describe existing checker inputs. None is
a seal. A derivation value answers a request only when the selected catalog,
ordered context and exact conclusion agree, and its submitted proof checks.
The catalog is the existing checker-facing projection; source interpretation
and admission remain with the chosen calculus and its semantic interface.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.InferenceCettaWire

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceLanguageWire
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

def judgmentRequestData (definition : ValidatedCalculusLanguageDef)
    (context : List Pattern) (goal : Pattern) : CettaTerm :=
  .application "GJudgmentRequest" [encodeDefinition definition.1, encodePatterns context, encodePattern goal]

def ruleProgramData (definition : ValidatedCalculusLanguageDef)
    (premises : List Pattern) (goal : Pattern) (program : RawOpenProof) : CettaTerm :=
  .application "GRuleProgram"
    [encodeDefinition definition.1, encodePatterns premises, encodePattern goal, encodeOpenProof program]

def derivationData (definition : ValidatedCalculusLanguageDef)
    (context : List Pattern) (goal : Pattern) (proof : RawOpenProof) : CettaTerm :=
  .application "GDerivation"
    [encodeDefinition definition.1, encodePatterns context, encodePattern goal, encodeOpenProof proof]

def checkDerivationValue (definition : ValidatedCalculusLanguageDef)
    (context : List Pattern) (goal : Pattern) : CettaTerm → Bool
  | .application "GDerivation" [language, contextTerm, goalTerm, proofTerm] =>
    match decodeRuntimeInferenceLanguage language, decodePatterns contextTerm,
        decodePattern goalTerm, decodeOpenProof proofTerm with
    | some catalog, some actualContext, some actualGoal, some proof =>
        decide (catalog = RuntimeInferenceLanguage.ofDefinition definition.1 ∧
          actualContext = context ∧ actualGoal = goal) && checkOpenRaw definition context goal proof
    | _, _, _, _ => false
  | _ => false

theorem checkDerivationValue_derivationData (definition : ValidatedCalculusLanguageDef)
    (context : List Pattern) (goal : Pattern) (proof : RawOpenProof) :
    checkDerivationValue definition context goal (derivationData definition context goal proof) =
      checkOpenRaw definition context goal proof := by
  simp [checkDerivationValue, derivationData]

theorem checkDerivationValue_exact (definition : ValidatedCalculusLanguageDef)
    (context : List Pattern) (goal : Pattern) (value : CettaTerm)
    (accepted : checkDerivationValue definition context goal value = true) :
    ∃ language contextTerm goalTerm proofTerm proof,
      value = .application "GDerivation" [language, contextTerm, goalTerm, proofTerm] ∧
      decodeRuntimeInferenceLanguage language = some (RuntimeInferenceLanguage.ofDefinition definition.1) ∧
      decodePatterns contextTerm = some context ∧ decodePattern goalTerm = some goal ∧
      decodeOpenProof proofTerm = some proof ∧
      ∃ derivation : OpenDerivation definition context goal, derivation.eraseOpen = proof := by
  unfold checkDerivationValue at accepted
  split at accepted
  next _ language contextTerm goalTerm proofTerm =>
    cases hl : decodeRuntimeInferenceLanguage language with
    | none => simp [hl] at accepted
    | some catalog =>
      cases hc : decodePatterns contextTerm with
      | none => simp [hl, hc] at accepted
      | some actualContext =>
        cases hg : decodePattern goalTerm with
        | none => simp [hl, hc, hg] at accepted
        | some actualGoal =>
          cases hp : decodeOpenProof proofTerm with
          | none => simp [hl, hc, hg, hp] at accepted
          | some proof =>
            simp only [hl, hc, hg, hp, Bool.and_eq_true, decide_eq_true_eq] at accepted
            obtain ⟨⟨catalogEq, contextEq, goalEq⟩, checked⟩ := accepted
            exact ⟨language, contextTerm, goalTerm, proofTerm, proof, rfl,
              hl.trans (congrArg some catalogEq), hc.trans (congrArg some contextEq),
              hg.trans (congrArg some goalEq), hp, checkOpenRaw_exact_derivation checked⟩
  next => simp_all

theorem request_data_is_not_derivation (definition : ValidatedCalculusLanguageDef)
    (context : List Pattern) (goal : Pattern) :
    checkDerivationValue definition context goal (judgmentRequestData definition context goal) = false := by
  simp [checkDerivationValue, judgmentRequestData]

theorem rule_data_is_not_derivation (definition : ValidatedCalculusLanguageDef)
    (context : List Pattern) (goal : Pattern) (program : RawOpenProof) :
    checkDerivationValue definition context goal (ruleProgramData definition context goal program) = false := by
  simp [checkDerivationValue, ruleProgramData]

/-- A separately valid proof of a different statement still does not answer
this request. -/
theorem different_claim_refused (definition : ValidatedCalculusLanguageDef)
    (context : List Pattern) (goal other : Pattern) (different : other ≠ goal) (proof : RawOpenProof) :
    checkDerivationValue definition context goal (derivationData definition context other proof) = false := by
  simp [checkDerivationValue, derivationData, different]

#print axioms checkDerivationValue_exact
#print axioms different_claim_refused

end Mettapedia.GSLT.LanguageDef.InferenceCettaWire
