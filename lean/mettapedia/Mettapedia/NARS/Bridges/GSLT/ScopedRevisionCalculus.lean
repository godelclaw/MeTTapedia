import Mettapedia.NARS.Bridges.PLN.RevisionSemantics
import Mettapedia.GSLT.LanguageDef.FirstOrderCalculus
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Portable
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenChecker

/-!
# Checked NARS revision and choice with retained evidence paths

Belief expressions retain statements, truth values, source sets, and complete
rule histories. Binary count readouts are separate terms. Revision uses the
evidence-additive core under an explicit source-disjointness contract; overlap
uses confidence choice and retains a complete input occurrence.

Soundness covers instantiated applications with nested expressions and actual
checked open proofs. A checker accepts the proof structure; the external
statement, validity, and source-scope contracts still need to be true.
-/

set_option autoImplicit false

namespace Mettapedia.NARS.Bridges.GSLT.ScopedRevisionCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.FirstOrderCalculus
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.NARS.Evidence.EvidenceScopeIncoherence
open Mettapedia.NARS.Evidence.EvidenceScopeIncoherence.PathScopedBelief
open Mettapedia.NARS.Bridges.PLN.RevisionSemantics
open Mettapedia.NARS.Bridges.PLN.SecondOrderProbability
open Mettapedia.NARS.Bridges.PLN
open Mettapedia.PLN.Evidence

def revision (first second : Pattern) : Pattern := app "RevisionCandidate" [first, second]
def choice (first second : Pattern) : Pattern := app "ConfidenceChoice" [first, second]
def countSum (first second : Pattern) : Pattern := app "CountSum" [first, second]
def sameStatement (first second : Pattern) : Pattern := app "SameStatement" [first, second]
def disjoint (first second : Pattern) : Pattern := app "SourceDisjoint" [first, second]
def overlap (first second : Pattern) : Pattern := app "SourceOverlap" [first, second]
def confidenceLe (first second : Pattern) : Pattern := app "ConfidenceLe" [first, second]
def confidenceLt (first second : Pattern) : Pattern := app "ConfidenceLt" [first, second]
def validBelief (belief : Pattern) : Pattern := app "ValidBelief" [belief]
def counts (belief summary : Pattern) : Pattern := app "EvidenceCounts" [belief, summary]

structure Model where
  Statement : Type
  Source : Type
  sourceDecidableEq : DecidableEq Source
  atomBelief : Pattern → @PathScopedBelief Statement Source sourceDecidableEq
  atomCounts : Pattern → BinaryEvidence

attribute [instance] Model.sourceDecidableEq

namespace Model

noncomputable def belief (model : Model) : Pattern → PathScopedBelief model.Statement model.Source
  | .apply "RevisionCandidate" [first, second] =>
      revisionCandidate (model.belief first) (model.belief second)
  | .apply "ConfidenceChoice" [first, second] =>
      choiceCandidate (model.belief first) (model.belief second)
  | other => model.atomBelief other
termination_by pattern => sizeOf pattern

noncomputable def summary (model : Model) : Pattern → BinaryEvidence
  | .apply "CountSum" [first, second] => model.summary first + model.summary second
  | other => model.atomCounts other
termination_by pattern => sizeOf pattern

@[simp] theorem belief_revision (model : Model) (first second : Pattern) :
    model.belief (.apply "RevisionCandidate" [first, second]) =
      revisionCandidate (model.belief first) (model.belief second) := by
  rw [belief]

@[simp] theorem belief_choice (model : Model) (first second : Pattern) :
    model.belief (.apply "ConfidenceChoice" [first, second]) =
      choiceCandidate (model.belief first) (model.belief second) := by
  rw [belief]

@[simp] theorem summary_sum (model : Model) (first second : Pattern) :
    model.summary (.apply "CountSum" [first, second]) = model.summary first + model.summary second := by
  rw [summary]

noncomputable def meaning (model : Model) : Pattern → Prop
  | .apply "SameStatement" [first, second] =>
      (model.belief first).statement = (model.belief second).statement
  | .apply "SourceDisjoint" [first, second] =>
      Disjoint (model.belief first).scope (model.belief second).scope
  | .apply "SourceOverlap" [first, second] =>
      ¬ Disjoint (model.belief first).scope (model.belief second).scope
  | .apply "ConfidenceLe" [first, second] =>
      (model.belief first).truth.c ≤ (model.belief second).truth.c
  | .apply "ConfidenceLt" [first, second] =>
      (model.belief first).truth.c < (model.belief second).truth.c
  | .apply "ValidBelief" [value] => IsProbTV (model.belief value).truth
  | .apply "EvidenceCounts" [value, count] =>
      EvidenceTranslation.TV.toEvidence (model.belief value).truth = model.summary count
  | _ => False

end Model

def rules : List RuleSchema :=
  [rule "revise-counts" ["a", "b", "e", "f"]
      [sameStatement (fv "a") (fv "b"), disjoint (fv "a") (fv "b"), validBelief (fv "a"), validBelief (fv "b"), counts (fv "a") (fv "e"), counts (fv "b") (fv "f")]
      (counts (revision (fv "a") (fv "b")) (countSum (fv "e") (fv "f"))),
    rule "revise-valid" ["a", "b"]
      [sameStatement (fv "a") (fv "b"), disjoint (fv "a") (fv "b"), validBelief (fv "a"), validBelief (fv "b")]
      (validBelief (revision (fv "a") (fv "b"))),
    rule "choose-left" ["a", "b", "e"]
      [sameStatement (fv "a") (fv "b"), overlap (fv "a") (fv "b"), confidenceLe (fv "b") (fv "a"), counts (fv "a") (fv "e")]
      (counts (choice (fv "a") (fv "b")) (fv "e")),
    rule "choose-right" ["a", "b", "e"]
      [sameStatement (fv "a") (fv "b"), overlap (fv "a") (fv "b"), confidenceLt (fv "a") (fv "b"), counts (fv "b") (fv "e")]
      (counts (choice (fv "a") (fv "b")) (fv "e"))]

def calculus : CalculusLanguageDef where
  name := "nars-scoped-revision"
  types := [TypeDecl.plain "Belief", TypeDecl.plain "Counts"]
  terms := [term "RevisionCandidate" "Belief" [("first", "Belief"), ("second", "Belief")],
    term "ConfidenceChoice" "Belief" [("first", "Belief"), ("second", "Belief")],
    term "CountSum" "Counts" [("first", "Counts"), ("second", "Counts")]]
  judgments := [⟨"SameStatement", 2⟩, ⟨"SourceDisjoint", 2⟩, ⟨"SourceOverlap", 2⟩,
    ⟨"ConfidenceLe", 2⟩, ⟨"ConfidenceLt", 2⟩, ⟨"ValidBelief", 1⟩, ⟨"EvidenceCounts", 2⟩]
  rules := rules
  equations := []
  rewrites := []

theorem calculus_admitted : calculus.isAdmitted = true := by decide +kernel

def validated : ValidatedCalculusLanguageDef := calculus.validated calculus_admitted

def moduleText : String := ModuleFormat.Portable.renderCalculus validated.val

theorem moduleText_read : ModuleFormat.Portable.readValidatedCalculus? moduleText = some validated :=
  ModuleFormat.Portable.readValidatedCalculus_renderCalculus _

/-- Soundness of arbitrary instantiated rule arguments, including nested
revision and count-sum expressions. External source contracts are retained. -/
theorem rule_application_sound (model : Model) (ruleInstance : RuleInstance)
    (premises : List Pattern) (conclusion : Pattern)
    (application : RuleApplication validated ruleInstance premises conclusion)
    (premisesSound : ∀ premise ∈ premises, model.meaning premise) : model.meaning conclusion := by
  rcases ruleInstance with ⟨id, arguments⟩
  cases application with
  | intro schema lookup valid _ premisesInstantiate conclusionInstantiates =>
    have member := List.mem_of_find?_eq_some lookup
    change schema ∈ rules at member
    simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · have length : arguments.length = 4 := (argumentsValidAt_length valid).symm
      obtain ⟨a, b, e, f, argumentsEq⟩ := List.length_eq_four.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [rule, fv, app, revision, choice, countSum, sameStatement, disjoint, overlap,
        confidenceLe, confidenceLt, validBelief, counts]
        at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      have hypotheses := premisesSound
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hypotheses
      simp only [Model.meaning] at hypotheses ⊢
      simp only [Model.belief_revision, Model.summary_sum]
      change EvidenceTranslation.TV.toEvidence
        (Mettapedia.NARS.TruthFunctions.truthRevisionCore (model.belief a).truth (model.belief b).truth) = _
      rw [core_counts _ _ hypotheses.2.2.1 hypotheses.2.2.2.1,
        hypotheses.2.2.2.2.1, hypotheses.2.2.2.2.2]
    · have length : arguments.length = 2 := (argumentsValidAt_length valid).symm
      obtain ⟨a, b, argumentsEq⟩ := List.length_eq_two.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [rule, fv, app, revision, choice, countSum, sameStatement, disjoint, overlap,
        confidenceLe, confidenceLt, validBelief, counts]
        at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      have hypotheses := premisesSound
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hypotheses
      simp only [Model.meaning] at hypotheses ⊢
      rw [Model.belief_revision]
      exact core_valid _ _ hypotheses.2.2.1 hypotheses.2.2.2
    · have length : arguments.length = 3 := (argumentsValidAt_length valid).symm
      obtain ⟨a, b, e, argumentsEq⟩ := List.length_eq_three.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [rule, fv, app, revision, choice, countSum, sameStatement, disjoint, overlap,
        confidenceLe, confidenceLt, validBelief, counts]
        at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      have hypotheses := premisesSound
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hypotheses
      simp only [Model.meaning] at hypotheses ⊢
      rw [Model.belief_choice, choiceCandidate_left _ _ hypotheses.2.2.1]
      exact hypotheses.2.2.2
    · have length : arguments.length = 3 := (argumentsValidAt_length valid).symm
      obtain ⟨a, b, e, argumentsEq⟩ := List.length_eq_three.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [rule, fv, app, revision, choice, countSum, sameStatement, disjoint, overlap,
        confidenceLe, confidenceLt, validBelief, counts]
        at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      have hypotheses := premisesSound
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hypotheses
      simp only [Model.meaning] at hypotheses ⊢
      rw [Model.belief_choice, choiceCandidate_right _ _ hypotheses.2.2.1]
      exact hypotheses.2.2.2

/-- Structural proof checking composes the established semantic rule laws. -/
theorem checked_proof_sound (model : Model) (context : List Pattern) (conclusion : Pattern)
    (proof : RawOpenProof) (checked : checkOpenRaw validated context conclusion proof = true)
    (contextSound : ∀ premise ∈ context, model.meaning premise) : model.meaning conclusion := by
  obtain ⟨derivation, _⟩ := checkOpenRaw_exact_derivation checked
  exact derivation.sound_of_ruleApplications model.meaning (rule_application_sound model) contextSound

end Mettapedia.NARS.Bridges.GSLT.ScopedRevisionCalculus
