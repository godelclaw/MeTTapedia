import Mettapedia.Languages.Megalodon.SourceCursor
import Mettapedia.Languages.Megalodon.PublicationProofRefinement

/-!
# Stored source proofs and publication checking

A completed retained session publishes only formed closed claims checked by
the independent publication-style proof algorithm. The proof's source-payload
invariant comes from the actual decoded rows and survives every resumption.
The common finite bound is existential: no default resource cutoff is added.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.SourcePublication
open MathdataKernel ProofJudgment BorrowedProofCursor SourceScopeInvariant
open Mettapedia.Logic.DerivationGraph.BorrowedCursor

theorem finished_has_publication_proof {environment : Environment} {revision : Nat}
    {read : NodeId → Option NativeSyntaxWire.Wire} {result : SourceCursor.Resumed environment revision read}
    {root goalBound : Nat} {proposition : Tm} {theorem_ : NativeSession.Theorem environment}
    (accepted : SourceCursor.finish result root goalBound proposition = .accepted theorem_) :
    theorem_.proposition = proposition ∧ checkProposition environment 0 [] proposition = true ∧
      ∃ fuel proof, ProofPayload proof ∧
        PublicationProofRefinement.check environment fuel 0 [] [] proof proposition = true := by
  have isAccepted : (SourceCursor.finish result root goalBound proposition).isAccepted = true := by
    rw [accepted]
    rfl
  obtain ⟨safeClaim, _, _, judgment, found, closed, formed, normalized⟩ :=
    (SourceCursor.finish_accepts_iff result root goalBound proposition).mp isAccepted
  obtain ⟨proofFuel, proof, payload, derived⟩ := SourceCursor.root_supported result.cachedSupported found
  have lifted := SourceCursor.proof_mono (Nat.le_max_left proofFuel goalBound) derived
  have liftedNormal := FuelledConversionProfile.normalize_mono environment proposition judgment.proposition
    (Nat.le_max_right proofFuel goalBound) normalized
  rw [closed] at lifted
  have native : checkProof environment (max proofFuel goalBound) 0 [] [] proof proposition = true :=
    (ProofJudgment.check_iff environment _ ⟨0, [], []⟩ proof proposition).mpr
      ⟨judgment.proposition, liftedNormal, lifted⟩
  have checked := (PublicationProofRefinement.closed_check_agrees result.environmentSafe.1
    result.environmentSafe.2 (max proofFuel goalBound) payload safeClaim).trans native
  exact ⟨(SourceCursor.finish_correct accepted).2.2.2.2.1, formed,
    max proofFuel goalBound, proof, payload, checked⟩

/-- This conclusion applies to any retained session, including sessions
constructed by several resumptions with different normalization bounds. -/
theorem publication_forgery_excluded {environment : Environment} {revision : Nat}
    {read : NodeId → Option NativeSyntaxWire.Wire} (result : SourceCursor.Resumed environment revision read)
    (root goalBound : Nat) (proposition : Tm)
    (impossible : ∀ fuel proof, ProofPayload proof →
      PublicationProofRefinement.check environment fuel 0 [] [] proof proposition ≠ true) :
    ∀ theorem_, SourceCursor.finish result root goalBound proposition ≠ .accepted theorem_ := by
  intro theorem_ accepted
  obtain ⟨_, _, fuel, proof, payload, checked⟩ := finished_has_publication_proof accepted
  exact impossible fuel proof payload checked

end Mettapedia.Languages.Megalodon.SourcePublication
