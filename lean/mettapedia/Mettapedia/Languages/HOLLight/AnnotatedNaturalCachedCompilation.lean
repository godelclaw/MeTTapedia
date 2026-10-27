import Mettapedia.Languages.HOLLight.AnnotatedNaturalCompilation
import Mettapedia.Languages.HOLLight.CachedHypothesisDischarge

/-!
# Received source equalities with cached source-premise discharge

The selected natural predicate interpretation has two ambient hypotheses:
selection and natural recursion. Their actual cached proofs discharge those
hypotheses after compilation. This operation preserves the earlier cache,
adds four discharge nodes, and retains precisely the source proofs' axiom
dependencies. A source replay must supply the stated cache readings.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.AnnotatedNaturalCachedCompilation

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Logic.DerivationGraph
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies
open NativeNaturalPredicateReading AnnotatedConversion CertificateInterpretation
open ReverseTranslation GraphExpansion

variable {operations : Operations AtomicTy Symbol} {profile : Programs.ComputationProfiles.Selection}
    {Γ : HOL.Ctx AtomicTy} {context : CCtx Tower.Head Γ.length} {source target type : CTm Tower.Head Γ.length}

structure Sources (operations : Operations AtomicTy Symbol) (Γ : HOL.Ctx AtomicTy) (names : Naming Γ) where
  selection : Theorem
  recursion : Theorem
  selection_exact : selection.sequent.concl = reverseCanonical names (HOL.ImpredicativeConnectives.expand
    (HOL.SelectionProofs.principle (HOL.weakenCtx Γ operations.selection)))
  recursion_exact : recursion.sequent.concl = reverseCanonical names (HOL.ImpredicativeConnectives.expand
    (HOL.NaturalRecursionProofs.statement (HOL.weakenCtx Γ operations.zero)
      (HOL.weakenCtx Γ operations.successor) operations.result))
  selection_closed : selection.sequent.hyp = ∅
  recursion_closed : recursion.sequent.hyp = ∅

/-- Reuse requires the exact interpreted conclusion and no remaining
hypotheses. Axiom dependencies stay attached to the returned theorem. -/
def reuse? (received : CheckedEquality operations profile Γ context source target type)
    (names : Naming Γ) (state : ProofExecution.State) (root : Nat) : Option Theorem := do
  let fact ← state.cache[root]?
  if fact.sequent.concl.same (reverseCanonical names (HOL.ImpredicativeConnectives.expand
      (.eq received.sourceState.code received.targetState.code))) && (fact.sequent.hyp.card == 0)
  then some fact else none

theorem reuse_iff (received : CheckedEquality operations profile Γ context source target type)
    (names : Naming Γ) (state : ProofExecution.State) (root : Nat) (fact : Theorem) :
    reuse? received names state root = some fact ↔
      state.cache[root]? = some fact ∧ fact.sequent.hyp = ∅ ∧
      fact.sequent.concl = reverseCanonical names (HOL.ImpredicativeConnectives.expand
        (.eq received.sourceState.code received.targetState.code)) := by
  cases found : state.cache[root]? with
  | none => simp [reuse?, found]
  | some actual =>
      simp only [reuse?, found, Option.bind_eq_bind, Option.bind_some, Bool.and_eq_true,
        CanonicalTerm.same_eq_true_iff, beq_iff_eq, Finset.card_eq_zero]
      split <;> simp_all [and_comm]
      all_goals rintro rfl; assumption

theorem reuse_checked (received : CheckedEquality operations profile Γ context source target type)
    (names : Naming Γ) {policy : AxiomPolicy} [DecidablePred policy]
    {premises : List Theorem} {state : ProofExecution.State} {root : Nat} {fact : Theorem}
    (earlier : BuildChecked policy premises state)
    (reused : reuse? received names state root = some fact) :
    BlockChecked policy premises fact (finish state root) ∧ fact.sequent.hyp = ∅ ∧
      fact.sequent.concl = reverseCanonical names (HOL.ImpredicativeConnectives.expand
        (.eq received.sourceState.code received.targetState.code)) := by
  obtain ⟨found, closed, exactClaim⟩ := (reuse_iff received names state root fact).mp reused
  exact ⟨finish_checked earlier found, closed, exactClaim⟩

def checkAndReuse? [DecidableEq AtomicTy]
    (operations : Operations AtomicTy Symbol) (profile : Programs.ComputationProfiles.Selection)
    (Γ : HOL.Ctx AtomicTy) (context : CCtx Tower.Head Γ.length) (source target type : CTm Tower.Head Γ.length)
    (contextCertificate : Programs.Annotated.JudgmentReplay.ContextCertificate profile Γ.length)
    (certificate : Programs.Annotated.JudgmentReplay.Certificate profile)
    (names : Naming Γ) (state : ProofExecution.State) (root : Nat) : Option Theorem := do
  let received ← CertificateInterpretation.check? operations profile Γ context source target type contextCertificate certificate
  reuse? received names state root

def compileAndClose? (received : CheckedEquality operations profile Γ context source target type)
    (names : Naming Γ) (origin : ProofExecution.Origin) (state : ProofExecution.State)
    (selectionRoot recursionRoot : Nat) : Option (ProofExecution.State × Nat) := do
  let compiled := AnnotatedNaturalCompilation.compile received names origin
  let (after, root) ← emitBlock emptyAxiomPolicy [] compiled.proof.certificate state
  let (closed, finalRoot) ← CachedHypothesisDischarge.close? emptyAxiomPolicy after selectionRoot recursionRoot root origin
  CachedHypothesisDischarge.requireClosed? closed finalRoot

theorem compilation_axioms_empty (received : CheckedEquality operations profile Γ context source target type)
    (names : Naming Γ) (origin : ProofExecution.Origin) :
    (AnnotatedNaturalCompilation.compile received names origin).proof.result.axioms = ∅ :=
  axioms_eq_empty_of_emptyAxiomPolicy (derives_shared emptyAxiomPolicy
    ((ProofSystem.checker_authority emptyAxiomPolicy).sound _ _
      (AnnotatedNaturalCompilation.compile_accepted received names origin)))

theorem compilation_covered (received : CheckedEquality operations profile Γ context source target type)
    (names : Naming Γ) (origin : ProofExecution.Origin) (sources : Sources operations Γ names) :
    (AnnotatedNaturalCompilation.compile received names origin).proof.result.sequent.hyp =
      {sources.selection.sequent.concl, sources.recursion.sequent.concl} := by
  rw [(AnnotatedNaturalCompilation.compile received names origin).hypotheses_exact]
  simp only [assumptions, List.map_cons, List.map_nil, reverseHypotheses_cons, reverseHypotheses_nil,
    sources.selection_exact, sources.recursion_exact, Finset.insert_empty]

theorem compileAndClose_checked (received : CheckedEquality operations profile Γ context source target type)
    (names : Naming Γ) (origin : ProofExecution.Origin) (sources : Sources operations Γ names)
    {premises : List Theorem} {state : ProofExecution.State} {selectionRoot recursionRoot : Nat}
    (earlier : BuildChecked emptyAxiomPolicy premises state)
    (selectionFound : state.cache[selectionRoot]? = some sources.selection)
    (recursionFound : state.cache[recursionRoot]? = some sources.recursion) :
    ∃ after root fact, compileAndClose? received names origin state selectionRoot recursionRoot = some (after, root) ∧
      BuildChecked emptyAxiomPolicy premises after ∧ after.cache[root]? = some fact ∧
      fact.sequent.concl = reverseCanonical names (HOL.ImpredicativeConnectives.expand
        (.eq received.sourceState.code received.targetState.code)) ∧
      fact.sequent.hyp = ∅ ∧ fact.axioms = sources.recursion.axioms ∪ sources.selection.axioms ∧
      after.receipts.size = state.receipts.size +
        (AnnotatedNaturalCompilation.compile received names origin).proof.certificate.1.length + 4 ∧
      ∀ (index : Nat) (old : Theorem), state.cache[index]? = some old → after.cache[index]? = some old := by
  let compiled := AnnotatedNaturalCompilation.compile received names origin
  have selectionBool : sources.selection.sequent.concl.IsBool := by
    rw [sources.selection_exact]
    exact reverseCanonical_isBool names _
  have recursionBool : sources.recursion.sequent.concl.IsBool := by
    rw [sources.recursion_exact]
    exact reverseCanonical_isBool names _
  have selected : lookupPremises state.cache [] = some ([] : List Theorem) := rfl
  obtain ⟨middle, compiledRoot, emitted, middleChecked, rootFound, _, firstPreserved⟩ :=
    emitBlock_checked earlier selected compiled.proof.blockChecked
  obtain ⟨after, root, closed, afterChecked, finalFound, closeSize, secondPreserved⟩ :=
    CachedHypothesisDischarge.close_checked middleChecked
      (firstPreserved selectionRoot sources.selection selectionFound)
      (firstPreserved recursionRoot sources.recursion recursionFound) rootFound
      (selectionBool.trans compiled.boolean.symm) (recursionBool.trans compiled.boolean.symm) origin
  let fact := CachedHypothesisDischarge.result sources.selection sources.recursion compiled.proof.result
  have covered : compiled.proof.result.sequent.hyp ⊆ {sources.selection.sequent.concl, sources.recursion.sequent.concl} :=
    (compilation_covered received names origin sources).le
  have noHypotheses : fact.sequent.hyp = ∅ :=
    CachedHypothesisDischarge.result_hypotheses_empty _ _ _
      sources.selection_closed sources.recursion_closed covered
  have publish := (CachedHypothesisDischarge.requireClosed_iff after root).mpr ⟨fact, finalFound, noHypotheses⟩
  refine ⟨after, root, fact, ?_, afterChecked, finalFound, compiled.conclusion_exact, ?_, ?_, ?_, ?_⟩
  · change ((emitBlock emptyAxiomPolicy [] compiled.proof.certificate state).bind fun intermediate =>
      (CachedHypothesisDischarge.close? emptyAxiomPolicy intermediate.1 selectionRoot recursionRoot intermediate.2 origin).bind
        fun final => CachedHypothesisDischarge.requireClosed? final.1 final.2) = some (after, root)
    rw [emitted]
    change ((CachedHypothesisDischarge.close? emptyAxiomPolicy middle selectionRoot recursionRoot compiledRoot origin).bind
      fun final => CachedHypothesisDischarge.requireClosed? final.1 final.2) = some (after, root)
    rw [closed]
    exact publish
  · exact noHypotheses
  · rw [CachedHypothesisDischarge.result_axioms, compilation_axioms_empty received names origin, Finset.union_empty]
  · have compileSize := (emitBlock_size emitted).2
    change after.receipts.size = state.receipts.size + compiled.proof.certificate.1.length + 4
    omega
  · intro index old found
    exact secondPreserved index old (firstPreserved index old found)

#print axioms compilation_axioms_empty
#print axioms compilation_covered
#print axioms compileAndClose_checked
#print axioms reuse_checked

end Mettapedia.Languages.HOLLight.AnnotatedNaturalCachedCompilation
