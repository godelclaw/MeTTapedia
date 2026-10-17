import Mettapedia.Languages.HOLLight.InferenceCompiler

/-!
# Concrete controls for the HOL Light inference compiler

The controls reuse the existing modus-ponens and canonical-data presentations.
Shared source proofs compile through the actual rule emitter and chronological
driver, then replay with the original HOL Light checker. Malformed supplied
proofs are rejected even when their requested claim has another valid proof.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.InferenceCompiler.Controls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayPresentation
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
open Mettapedia.Languages.HOLLight.FirstOrder.InferenceTranslation
open Mettapedia.Languages.HOLLight.InferenceHosting
open Mettapedia.Logic.HOL.Embedding.InferenceRules

/-- The two axioms are saved once and used as ordered shared parents. -/
def sharedModusPonens : LemmaCertificate :=
  ([(judgmentP formulaA, .node ⟨⟨"a"⟩, []⟩ []),
    (judgmentP (implication formulaA formulaB), .node ⟨⟨"i"⟩, []⟩ [])],
    .node ⟨⟨"m"⟩, [formulaA, formulaB]⟩ [.premise 0, .premise 1])

theorem shared_modus_ponens_source :
    sharedSourceCheck mpValidated (judgmentP formulaB) sharedModusPonens = true := by
  decide +kernel

/-- The literal shared source certificate generates an accepted primitive
graph with the exact encoded claim and no residual hypotheses. -/
theorem shared_modus_ponens_compiled :
    ∃ (certificate : ProofSystem.Certificate) (out : Theorem),
      compileShared mpValidated (judgmentP formulaB) sharedModusPonens = some certificate ∧
      (ProofSystem.checker (policy (inferenceRules mpValidated.1))).check out certificate = true ∧
      out.sequent.hyp = ∅ ∧ out.sequent.concl = compileClaim (judgmentP formulaB) := by
  obtain ⟨certificate, compiled⟩ := compileShared_preserves mpValidated
    Mettapedia.Languages.MM0.Translation.CalculusSimulation.Controls.mp_firstOrder _ _ shared_modus_ponens_source
  obtain ⟨out, checked, hypotheses, conclusion⟩ := compileShared_checked mpValidated _ _ compiled
  exact ⟨certificate, out, compiled, checked, hypotheses, conclusion⟩

/-- A generated graph checks directly against its source judgment. The same
physical root refuses the separately provable axiom judgment. -/
theorem shared_modus_ponens_claim_checked :
    ∃ certificate,
      compileShared mpValidated (judgmentP formulaB) sharedModusPonens = some certificate ∧
      (compiledChecker mpValidated.1).check (judgmentP formulaB) certificate = true ∧
      (compiledChecker mpValidated.1).check (judgmentP formulaA) certificate = false := by
  obtain ⟨certificate, compiled⟩ := compileShared_preserves mpValidated
    Mettapedia.Languages.MM0.Translation.CalculusSimulation.Controls.mp_firstOrder _ _
    shared_modus_ponens_source
  have valid : argumentValidAt 0 (judgmentP formulaB) = true := by decide +kernel
  have accepted := compileShared_claim_checked mpValidated _ _ valid compiled
  refine ⟨certificate, compiled, accepted, ?_⟩
  apply compiledChecker_wrong_claim _ _ _ _ accepted
  decide +kernel

def repeatedPremise : Theorem := Theorem.emptyResult ∅ (compileClaim (judgmentP formulaA))

/-- Two source holes retain two ordered parent occurrences pointing to the
same physical proof, while the receipt and cache vectors remain unchanged. -/
theorem repeated_holes_keep_physical_root (origin : ProofExecution.Origin) :
    compileChildrenWith mpValidated (InferenceRuleExpansion.emitRule? mpValidated) [0] origin
      [judgmentP formulaA, judgmentP formulaA] [.premise 0, .premise 0]
      (GraphExpansion.start [repeatedPremise]) =
        some (GraphExpansion.start [repeatedPremise], [0, 0]) := by
  apply compileChildrenWith_repeated_premise _ _ _ _ _ _ 0 0 repeatedPremise rfl rfl
  simp [hasClaim, repeatedPremise, Theorem.emptyResult]

def sharedData (arguments : List Pattern) : LemmaCertificate :=
  ([], .node ⟨FirstOrder.InferenceTranslation.Controls.dataRule.id, arguments⟩ [])

theorem binder_shared_source :
    sharedSourceCheck FirstOrder.InferenceTranslation.Controls.dataCalculus
      (judgmentP FirstOrder.InferenceTranslation.Controls.binderValue)
      (sharedData [FirstOrder.InferenceTranslation.Controls.binderValue]) = true := by
  decide +kernel

/-- Closed binding structure remains opaque source data throughout actual
compilation and checking; the source schema itself remains first-order. -/
theorem binder_shared_compiled :
    ∃ (certificate : ProofSystem.Certificate) (out : Theorem),
      compileShared FirstOrder.InferenceTranslation.Controls.dataCalculus
        (judgmentP FirstOrder.InferenceTranslation.Controls.binderValue)
        (sharedData [FirstOrder.InferenceTranslation.Controls.binderValue]) = some certificate ∧
      (ProofSystem.checker (policy (inferenceRules FirstOrder.InferenceTranslation.Controls.dataCalculus.1))).check
        out certificate = true ∧ out.sequent.hyp = ∅ ∧
      out.sequent.concl = compileClaim (judgmentP FirstOrder.InferenceTranslation.Controls.binderValue) := by
  obtain ⟨certificate, compiled⟩ := compileShared_preserves
    FirstOrder.InferenceTranslation.Controls.dataCalculus
    FirstOrder.InferenceTranslation.Controls.dataCalculus_firstOrder _ _ binder_shared_source
  obtain ⟨out, checked, hypotheses, conclusion⟩ := compileShared_checked
    FirstOrder.InferenceTranslation.Controls.dataCalculus _ _ compiled
  exact ⟨certificate, out, compiled, checked, hypotheses, conclusion⟩

theorem wrong_argument_count_refused :
    compileShared FirstOrder.InferenceTranslation.Controls.dataCalculus
      (judgmentP FirstOrder.InferenceTranslation.Controls.binderValue) (sharedData []) = none ∧
    compileShared FirstOrder.InferenceTranslation.Controls.dataCalculus
      (judgmentP FirstOrder.InferenceTranslation.Controls.binderValue)
      (sharedData [FirstOrder.InferenceTranslation.Controls.binderValue,
        FirstOrder.InferenceTranslation.Controls.binderValue]) = none := by
  constructor <;> apply compileShared_refused <;> decide +kernel

theorem escaping_argument_refused :
    compileShared FirstOrder.InferenceTranslation.Controls.dataCalculus
      (judgmentP (.lambda none (.bvar 1))) (sharedData [.lambda none (.bvar 1)]) = none := by
  apply compileShared_refused
  decide +kernel

/-- Canonical source-claim admission is checked at the independent target
interface too, for every supplied graph. -/
theorem escaping_claim_refused (certificate : ProofSystem.Certificate) :
    (compiledChecker FirstOrder.InferenceTranslation.Controls.dataCalculus.1).check
      (judgmentP (.lambda none (.bvar 1))) certificate = false := by
  apply compiledChecker_invalid_claim
  decide +kernel

theorem noncanonical_argument_refused :
    compileShared FirstOrder.InferenceTranslation.Controls.dataCalculus
      (judgmentP (.lambda (some "x") (.bvar 0))) (sharedData [.lambda (some "x") (.bvar 0)]) = none := by
  apply compileShared_refused
  decide +kernel

/-- The source theory proves `P(A)`, but the supplied certificate proves
`P(B)`. It must not be accepted as a certificate of `P(A)`. -/
theorem wrong_goal_refused : compileShared mpValidated (judgmentP formulaA) sharedModusPonens = none := by
  apply compileShared_refused
  decide +kernel

def futureLemma : LemmaCertificate := ([(judgmentP formulaA, .premise 0)], .premise 0)

/-- A lemma cannot cite itself before it is stored, even when an independent
axiom proves the same claim. -/
theorem future_lemma_refused : compileShared mpValidated (judgmentP formulaA) futureLemma = none := by
  apply compileShared_refused
  decide +kernel

def unusedFutureLemma : LemmaCertificate :=
  ([(judgmentP formulaA, .premise 0)], .node ⟨⟨"a"⟩, []⟩ [])

/-- A valid independent root does not license skipping a malformed saved
declaration earlier in the supplied certificate. -/
theorem unused_future_lemma_refused :
    compileShared mpValidated (judgmentP formulaA) unusedFutureLemma = none := by
  apply compileShared_refused
  decide +kernel

/-- Equal lemma conclusions remain separate chronological declarations. The
root selects the second physical declaration, without collapsing its origin. -/
def duplicateLemmas : LemmaCertificate :=
  ([(judgmentP formulaA, .node ⟨⟨"a"⟩, []⟩ []),
    (judgmentP formulaA, .node ⟨⟨"a"⟩, []⟩ [])], .premise 1)

theorem duplicate_lemmas_source :
    sharedSourceCheck mpValidated (judgmentP formulaA) duplicateLemmas = true := by
  decide +kernel

theorem duplicate_lemmas_compiled :
    ∃ certificate,
      compileShared mpValidated (judgmentP formulaA) duplicateLemmas = some certificate ∧
      (compiledChecker mpValidated.1).check (judgmentP formulaA) certificate = true := by
  obtain ⟨certificate, computed⟩ := compileShared_preserves mpValidated
    Mettapedia.Languages.MM0.Translation.CalculusSimulation.Controls.mp_firstOrder _ _
    duplicate_lemmas_source
  exact ⟨certificate, computed, compileShared_claim_checked mpValidated _ _ (by decide +kernel) computed⟩

theorem missing_child_refused :
    compileShared mpValidated (judgmentP formulaB)
      ([], .node ⟨⟨"m"⟩, [formulaA, formulaB]⟩ []) = none := by
  apply compileShared_refused
  decide +kernel

theorem unknown_rule_refused :
    compileShared mpValidated (judgmentP formulaA) ([], .node ⟨⟨"missing"⟩, []⟩ []) = none := by
  apply compileShared_refused
  decide +kernel

theorem unavailable_root_refused :
    compileShared mpValidated (judgmentP formulaA) ([], .premise 0) = none := by
  apply compileShared_refused
  decide +kernel

end Mettapedia.Languages.HOLLight.InferenceCompiler.Controls
