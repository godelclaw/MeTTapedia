import Mettapedia.Languages.Megalodon.NativeSessionControls
import Mettapedia.Languages.Megalodon.NativePublication
import Mettapedia.Languages.Megalodon.CursorEnvironment
import Mettapedia.Languages.Megalodon.SealedInference
import Mettapedia.Languages.Megalodon.SourceBinderRefinement
import Mettapedia.Languages.Megalodon.OpenTypeParameters
import Mettapedia.Languages.Megalodon.BorrowedProofCursorControls
import Mettapedia.Languages.Megalodon.SourceCursor
import Mettapedia.Languages.Megalodon.SourcePublication
import Mettapedia.Languages.Megalodon.SourceGraph

/-!
# Native Megalodon integration

Ordinary stored mathematical data is decoded to local proof rows. A retained
session checks them against an immutable selected environment; full contexts
are part of every judgment. Publication requires a completed batch, a closed
root and a formed source claim. No serialization to a generic proof article is
required. All profiles use this infrastructure with their actual primitive,
definition and known-proposition inventories.

`checkStored` is the assembled one-batch entry point. `NativeSession.begin`,
`resume` and `finish` expose its resumable form, with independent row and
normalization bounds. The bounds are supplied observations, not default
language limits. `BudgetIndependent` identifies the same finite derivations
without selecting a global default bound.

The exact inference reference is the existing Lean Mathdata kernel.
`checkSource` additionally enforces the source binding invariant, preserved
through imported definitions, normalization, inference and resumption. On
this fragment the publication substitution and the shared all-sort binder
operation agree, including after internal type abstractions appear during
expansion. Source type parameters may remain open in an enclosing type scope.
Accepted source sessions reconstruct protected proofs accepted by an independent
publication-style algorithm, even after resumption with changed bounds.
These results do not identify unrestricted mixed-binder Mathdata with that
fragment, or prove the entire OCaml `.mg` elaborator and lazy converter.

Opaque host values, retained owners, frozen helper resolution and atomic
storage publication remain native refinement obligations. The logical seal
and transaction results express their required invariants; decoding syntax
or printing a profile name does not establish them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.NativeIntegration
open MathdataKernel ProofJudgment BorrowedProofCursor
open NativeSession
open Mettapedia.Logic.DerivationGraph.BorrowedCursor

def checkStored (environment : Environment) (revision : Nat)
    (read : Nat → Option NativeSyntaxWire.Wire)
    (normalizationBound rowBound : Nat) (schedule : List Nat)
    (root goalBound : Nat) (proposition : Tm) : Publication environment :=
  finish (resume (NativeSession.begin environment (sourceOfWire revision read))
    normalizationBound rowBound schedule) root goalBound proposition

/-- Every published value has a formed, closed proof in the original checker
at a finite bound. A wire claim alone never mints such a value. -/
theorem checked_original {environment : Environment} {revision normalizationBound rowBound root goalBound : Nat}
    {read : Nat → Option NativeSyntaxWire.Wire} {schedule : List Nat} {proposition : Tm}
    {theorem_ : NativeSession.Theorem environment}
    (accepted : checkStored environment revision read normalizationBound rowBound schedule root goalBound proposition =
      .accepted theorem_) :
    theorem_.proposition = proposition ∧ checkProposition environment 0 [] proposition = true ∧
      ∃ fuel proof, checkProof environment fuel 0 [] [] proof proposition = true := by
  unfold checkStored at accepted
  have finished := finish_checks_whole_suffix accepted
  unfold finish at accepted
  rw [if_pos ⟨finished.1, finished.2.1⟩] at accepted
  obtain ⟨same, fuel, formed, proof, checked⟩ := publish_correct accepted
  exact ⟨same, formed, fuel, proof, checked⟩

/-- The assembled entry point cannot accept a convenient root while ignoring
an invalid or resource-limited tail of its submitted schedule. -/
theorem whole_batch_required {environment : Environment} {revision normalizationBound rowBound root goalBound : Nat}
    {read : Nat → Option NativeSyntaxWire.Wire} {schedule : List Nat} {proposition : Tm}
    {theorem_ : NativeSession.Theorem environment}
    (accepted : checkStored environment revision read normalizationBound rowBound schedule root goalBound proposition =
      .accepted theorem_) :
    let result := resume (NativeSession.begin environment (sourceOfWire revision read))
      normalizationBound rowBound schedule
    result.status = .finished ∧ result.pending = [] := by
  have completed := finish_checks_whole_suffix accepted
  exact ⟨completed.1, completed.2.1⟩

/-- Complete characterization of acceptance for this wire store and schedule.
Resource exhaustion remains a separate observation of the same operation. -/
theorem checkStored_accepts_iff (environment : Environment) (revision : Nat)
    (read : Nat → Option NativeSyntaxWire.Wire)
    (normalizationBound rowBound : Nat) (schedule : List Nat)
    (root goalBound : Nat) (proposition : Tm) :
    (checkStored environment revision read normalizationBound rowBound schedule root goalBound proposition).isAccepted = true ↔
      let result := resume (NativeSession.begin environment (sourceOfWire revision read))
        normalizationBound rowBound schedule
      result.status = .finished ∧ result.pending = [] ∧
        ∃ judgment, rootAt result.session.state root = some judgment ∧ judgment.context = ⟨0, [], []⟩ ∧
          checkProposition environment 0 [] proposition = true ∧
          normalize environment goalBound proposition = some judgment.proposition :=
  finish_accepts_iff _ _ _ _

/-- The source-facing entry point. Environment admission and row decoding
enforce protected polymorphic regions before the shared worker runs. The
environment check may be retained on an immutable admitted environment. -/
def checkSource (environment : Environment) (revision : Nat)
    (read : Nat → Option NativeSyntaxWire.Wire)
    (normalizationBound rowBound : Nat) (schedule : List Nat)
    (root goalBound : Nat) (proposition : Tm) : Publication environment :=
  if safe : SourceAdmission.environmentCheck environment = true then
    SourceCursor.finish (SourceCursor.resume
      (SourceCursor.begin environment (SourceAdmission.environmentCheck_sound safe) revision read)
      normalizationBound rowBound schedule) root goalBound proposition
  else .malformed

theorem source_checked_original {environment : Environment}
    {revision normalizationBound rowBound root goalBound : Nat}
    {read : Nat → Option NativeSyntaxWire.Wire} {schedule : List Nat} {proposition : Tm}
    {theorem_ : NativeSession.Theorem environment}
    (accepted : checkSource environment revision read normalizationBound rowBound schedule root goalBound proposition =
      .accepted theorem_) :
    SourceAdmission.EnvironmentSafe environment ∧ SourceScopeInvariant.Protected proposition ∧
      theorem_.proposition = proposition ∧ checkProposition environment 0 [] proposition = true ∧
      ∃ fuel proof, checkProof environment fuel 0 [] [] proof proposition = true := by
  unfold checkSource at accepted
  split at accepted
  · obtain ⟨safeEnvironment, safeClaim, _, _, same, fuel, formed, proof, checked⟩ :=
      SourceCursor.finish_correct accepted
    exact ⟨safeEnvironment, safeClaim, same, formed, fuel, proof, checked⟩
  · cases accepted

theorem source_checked_normalization_uses_all_sorts {environment : Environment}
    {revision normalizationBound rowBound root goalBound : Nat}
    {read : Nat → Option NativeSyntaxWire.Wire} {schedule : List Nat} {proposition normal : Tm}
    {theorem_ : NativeSession.Theorem environment}
    (accepted : checkSource environment revision read normalizationBound rowBound schedule root goalBound proposition =
      .accepted theorem_) (fuel : Nat) (normalized : normalize environment fuel proposition = some normal)
    (replacement : Tm) :
    Mettapedia.GSLT.LanguageDef.SortedSignatureIndexedABT.Term.substituteTop
      SortedABTRefinement.VarSort.term (SortedABTRefinement.encode replacement)
      (SortedABTRefinement.encode normal) =
        SortedABTRefinement.encode (SourceTermFragment.publicationSubstitute 0 replacement normal) := by
  have acceptedSource := source_checked_original accepted
  exact SourceBinderRefinement.normalized_publication_uses_all_sorts
    acceptedSource.1.1 acceptedSource.2.1 fuel normalized replacement

/-- End-to-end correspondence from ordinary stored mathematical data to the
publication-style proof algorithm, including formation of the closed claim. -/
theorem source_checked_publication {environment : Environment}
    {revision normalizationBound rowBound root goalBound : Nat}
    {read : Nat → Option NativeSyntaxWire.Wire} {schedule : List Nat} {proposition : Tm}
    {theorem_ : NativeSession.Theorem environment}
    (accepted : checkSource environment revision read normalizationBound rowBound schedule root goalBound proposition =
      .accepted theorem_) :
    theorem_.proposition = proposition ∧ checkProposition environment 0 [] proposition = true ∧
      ∃ fuel proof, SourceScopeInvariant.ProofPayload proof ∧
        PublicationProofRefinement.check environment fuel 0 [] [] proof proposition = true := by
  unfold checkSource at accepted
  split at accepted
  · exact SourcePublication.finished_has_publication_proof accepted
  · cases accepted

end Mettapedia.Languages.Megalodon.NativeIntegration
