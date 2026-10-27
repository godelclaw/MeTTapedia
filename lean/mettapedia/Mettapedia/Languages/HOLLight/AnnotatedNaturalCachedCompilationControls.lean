import Mettapedia.Languages.HOLLight.AnnotatedNaturalCachedCompilation
import Mettapedia.Languages.HOLLight.AnnotatedNaturalCompilationControls

/-!
# Cached received-equality controls

The beta cache contains a genuinely compiled hypothesis-free beta proof.
A separate declared-premise fixture exercises source-premise discharge while
retaining both declarations in its axiom set. Native replay supplies the
derived selection and recursion facts from the qualified source history.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.AnnotatedNaturalCachedCompilation.Controls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies
open NativeNaturalPredicateReading AnnotatedConversion CertificateInterpretation
open ReverseTranslation GraphExpansion
open AnnotatedNaturalCompilation.Controls (operations profile betaReceived)

def bareBeta : RetainedCompilation.Compiled emptyAxiomPolicy Naming.empty []
    (.eq (.app (.lam (.var HOL.Var.vz)) operations.zero) operations.zero) :=
  RetainedCompilation.Compiled.betaRule operations.zero (.var HOL.Var.vz) ("cached-beta", 0)

def betaCache : ProofExecution.State := start [bareBeta.proof.result]

theorem bare_beta_accepted : (ProofSystem.checker emptyAxiomPolicy).check bareBeta.proof.result bareBeta.proof.certificate = true :=
  bareBeta.proof.accepted

theorem exact_beta_reused : reuse? betaReceived Naming.empty betaCache 0 = some bareBeta.proof.result := by
  apply (reuse_iff betaReceived Naming.empty betaCache 0 bareBeta.proof.result).mpr
  exact ⟨rfl, bareBeta.hypotheses_exact, bareBeta.conclusion_exact⟩

theorem cached_beta_checked :
    BlockChecked emptyAxiomPolicy [bareBeta.proof.result] bareBeta.proof.result (finish betaCache 0) :=
  (reuse_checked betaReceived Naming.empty (start_checked emptyAxiomPolicy [bareBeta.proof.result]) exact_beta_reused).1

def declaredSources : Sources operations [] Naming.empty where
  selection := Theorem.axiomResult ⟨∅, reverseCanonical Naming.empty (HOL.ImpredicativeConnectives.expand
    (HOL.SelectionProofs.principle operations.selection))⟩
    ⟨reverseCanonical_isBool Naming.empty _, by simp⟩
  recursion := Theorem.axiomResult ⟨∅, reverseCanonical Naming.empty (HOL.ImpredicativeConnectives.expand
    (HOL.NaturalRecursionProofs.statement operations.zero operations.successor operations.result))⟩
    ⟨reverseCanonical_isBool Naming.empty _, by simp⟩
  selection_exact := by simp only [HOL.weakenCtx_nil]; rfl
  recursion_exact := by simp only [HOL.weakenCtx_nil]; rfl
  selection_closed := rfl
  recursion_closed := rfl

def sourceCache : ProofExecution.State := start [declaredSources.selection, declaredSources.recursion]

theorem declared_premises_close :
    ∃ after root fact,
      compileAndClose? betaReceived Naming.empty ("source-close", 0) sourceCache 0 1 = some (after, root) ∧
      BuildChecked emptyAxiomPolicy [declaredSources.selection, declaredSources.recursion] after ∧
      after.cache[root]? = some fact ∧ fact.sequent.hyp = ∅ ∧
      fact.axioms = declaredSources.recursion.axioms ∪ declaredSources.selection.axioms := by
  obtain ⟨after, root, fact, computed, checked, found, _, closed, dependencies, _, _⟩ :=
    compileAndClose_checked betaReceived Naming.empty ("source-close", 0) declaredSources
      (selectionRoot := 0) (recursionRoot := 1)
      (start_checked emptyAxiomPolicy [declaredSources.selection, declaredSources.recursion]) rfl rfl
  exact ⟨after, root, fact, computed, checked, found, closed, dependencies⟩

theorem declared_dependencies_nonempty :
    declaredSources.recursion.axioms ∪ declaredSources.selection.axioms ≠ ∅ := by
  simp [declaredSources, Theorem.axiomResult]

def wrongFact : Theorem := EqualityExpansion.reflexivity DerivedRules.truthTerm
def wrongCache : ProofExecution.State := start [wrongFact]

theorem changed_claim_refused : reuse? betaReceived Naming.empty wrongCache 0 = none := by
  simp [reuse?, wrongCache, start, wrongFact, EqualityExpansion.reflexivity,
    Theorem.emptyResult]
  intro same
  have termsEqual := congrArg CanonicalTerm.term same
  change CanonicalTerm.equalityDB Ty.bool _ _ =
    CanonicalTerm.equalityDB (reverseTy betaReceived.reading.1) _ _ at termsEqual
  have carrier : reverseTy betaReceived.reading.1 = Ty.var (Name.global "SourceNumber") :=
    reverseTy_toHOL (Ty.var (Name.global "SourceNumber"))
  rw [carrier] at termsEqual
  cases termsEqual

theorem missing_cache_refused : reuse? betaReceived Naming.empty betaCache 1 = none := by
  simp [reuse?, betaCache, start]

def conditionalFact := AnnotatedNaturalCompilation.Controls.betaCompiled.proof.result
def conditionalCache : ProofExecution.State := start [conditionalFact]

theorem beta_compiled_axioms_empty : conditionalFact.axioms = ∅ :=
  compilation_axioms_empty betaReceived Naming.empty ("annotated-beta", 0)

theorem conditional_not_published : CachedHypothesisDischarge.requireClosed? conditionalCache 0 = none := by
  apply CachedHypothesisDischarge.requireClosed_hypothesis_refused _ _ conditionalFact rfl
  rw [show conditionalFact.sequent.hyp = {declaredSources.selection.sequent.concl, declaredSources.recursion.sequent.concl}
    from compilation_covered betaReceived Naming.empty ("annotated-beta", 0) declaredSources]
  simp

def wrongSourceResult := compileAndClose? betaReceived Naming.empty ("wrong-source", 0) sourceCache 0 0
def missingSourceResult := compileAndClose? betaReceived Naming.empty ("missing-source", 0) sourceCache 0 20

def malformedSourceResult := checkAndReuse? operations profile [] .nil
  CertificateInterpretation.Controls.betaLeft CertificateInterpretation.Controls.betaLeft (.const natName)
  .nil CertificateInterpretation.Controls.badMiddle Naming.empty betaCache 0

#eval if wrongSourceResult.isNone && missingSourceResult.isNone then true else panic! "source closure refusal failed"
#eval if (reuse? betaReceived Naming.empty betaCache 0).isSome then true else panic! "cached beta refused"
#eval if malformedSourceResult.isNone then true else panic! "malformed source certificate reused a cached proof"

#print axioms bare_beta_accepted
#print axioms exact_beta_reused
#print axioms cached_beta_checked
#print axioms declared_premises_close
#print axioms declared_dependencies_nonempty
#print axioms changed_claim_refused
#print axioms conditional_not_published
#print axioms beta_compiled_axioms_empty

end Mettapedia.Languages.HOLLight.AnnotatedNaturalCachedCompilation.Controls
