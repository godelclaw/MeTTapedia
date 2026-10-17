import Mettapedia.Languages.Megalodon.BorrowedProofCursor
import Mettapedia.Languages.Megalodon.MathdataProofFormation
import Mettapedia.Languages.Megalodon.NativeProofEnvironment

/-!
# Formed Megalodon theorems, LCF construction and explicit reuse

Intermediate proof judgments may have open contexts. Published library
theorems are formed, closed propositions checked under one retained environment.
Inspection returns the retained proposition without instantiation. A theorem
is not an authority to mutate a theory, import axioms or run foreign code.

Private Lean construction proves the logical invariant only. Native sealing
must additionally hide the constructor, retain payload owners and keep every
helper used by minting outside client-redefinable equation resolution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.NativeTheorem

open MathdataKernel ProofJudgment
open Mettapedia.Logic Mettapedia.Logic.DerivationGraph

def ClosedValid (environment : Environment) (fuel : Nat) (proposition : Tm) : Prop :=
  checkProposition environment 0 [] proposition = true ∧
    ∃ proof, checkProof environment fuel 0 [] [] proof proposition = true

structure Theorem (environment : Environment) (fuel : Nat) where
  private mk ::
  proposition : Tm
  valid : ClosedValid environment fuel proposition

/-- A source proof is checked before a closed theorem is minted. -/
def check (environment : Environment) (fuel : Nat) (proof : Pf) (proposition : Tm) :
    Option (Theorem environment fuel) :=
  if formed : checkProposition environment 0 [] proposition = true then
    if accepted : checkProof environment fuel 0 [] [] proof proposition = true then
      some ⟨proposition, formed, proof, accepted⟩
    else none
  else none

theorem check_iff (environment : Environment) (fuel : Nat) (proof : Pf) (proposition : Tm) :
    (check environment fuel proof proposition).map Theorem.proposition = some proposition ↔
      checkProposition environment 0 [] proposition = true ∧
        checkProof environment fuel 0 [] [] proof proposition = true := by
  unfold check
  split <;> simp_all

/-- Publish a checked row only after checking the user's closed source claim.
The row may use a normalized representative; the source proposition is retained. -/
def publish {environment : Environment} {fuel : Nat}
    (checked : CheckedJudgment (BorrowedProofCursor.Rules environment fuel))
    (proposition : Tm) : Option (Theorem environment fuel) :=
  if context : checked.judgment.context = ⟨0, [], []⟩ then
    if formed : checkProposition environment 0 [] proposition = true then
      if normalized : normalize environment fuel proposition = some checked.judgment.proposition then
        some ⟨proposition, formed, by
          obtain ⟨proof, inferred⟩ := (BorrowedProofCursor.derives_iff_original environment fuel
            checked.judgment).mp checked.valid
          rw [context] at inferred
          exact ⟨proof, (ProofJudgment.check_iff environment fuel ⟨0, [], []⟩ proof proposition).mpr
            ⟨checked.judgment.proposition, normalized, proves_of_infer inferred⟩⟩⟩
      else none
    else none
  else none

theorem publish_isSome_iff {environment : Environment} {fuel : Nat}
    (checked : CheckedJudgment (BorrowedProofCursor.Rules environment fuel)) (proposition : Tm) :
    (publish checked proposition).isSome = true ↔
      checked.judgment.context = ⟨0, [], []⟩ ∧
      checkProposition environment 0 [] proposition = true ∧
      normalize environment fuel proposition = some checked.judgment.proposition := by
  unfold publish
  by_cases context : checked.judgment.context = ⟨0, [], []⟩ <;>
    by_cases formed : checkProposition environment 0 [] proposition = true <;>
    by_cases normalized : normalize environment fuel proposition = some checked.judgment.proposition <;>
    simp [context, formed, normalized]

/-- Every formed theorem has a finite local-row certificate that publishes it.
The construction does not require changing the foundation or adding axioms. -/
theorem valid_iff_publishable (environment : Environment) (fuel : Nat) (proposition : Tm) :
    ClosedValid environment fuel proposition ↔
      ∃ checked : CheckedJudgment (BorrowedProofCursor.Rules environment fuel),
        (publish checked proposition).isSome = true := by
  constructor
  · rintro ⟨formed, proof, accepted⟩
    obtain ⟨normal, normalized, proved⟩ :=
      (ProofJudgment.check_iff environment fuel ⟨0, [], []⟩ proof proposition).mp accepted
    have derived := BorrowedProofCursor.proof_derives proved
    obtain ⟨nodes, root, minted⟩ :=
      (CheckedJudgment.exists_mint_iff (BorrowedProofCursor.interface environment fuel) (0 : Nat)
        ⟨⟨0, [], []⟩, normal⟩).mpr derived
    obtain ⟨checked, _, same⟩ := Option.map_eq_some_iff.mp minted
    exact ⟨checked, (publish_isSome_iff checked proposition).mpr
      ⟨congrArg BorrowedProofCursor.Judgment.context same, formed,
        by simpa only [same] using normalized⟩⟩
  · rintro ⟨checked, accepted⟩
    cases result : publish checked proposition with
    | none => simp [result] at accepted
    | some theorem_ =>
        have same : theorem_.proposition = proposition := by
          unfold publish at result
          split at result <;> try contradiction
          split at result <;> try contradiction
          split at result <;> try contradiction
          exact congrArg Theorem.proposition (Option.some.inj result.symm)
        exact same ▸ theorem_.valid

/-- Reuse checks the original proof and all its transitive declaration reads,
including negative lookups. It is not a comparison of profile names or hashes. -/
theorem checked_reuse {source target : Environment} {fuel : Nat} {proof : Pf} {proposition : Tm}
    (accepted : checkProof source fuel 0 [] [] proof proposition = true)
    (agreement : NativeProofEnvironment.requestFrameCheck source target [] proof proposition = true) :
    checkProof target fuel 0 [] [] proof proposition = true := by
  rw [NativeProofEnvironment.checkProof_eq_of_requestFrameCheck agreement]
  exact accepted

namespace Controls
open MathdataProofFormation

theorem ordinary_theorem_published :
    (check {} 8 identity (.imp ordinary ordinary)).isSome = true := by
  have formed : checkProposition {} 0 [] (.imp ordinary ordinary) = true := by decide
  simp only [check, formed, ordinary_identity_accepted, ↓reduceDIte, Option.isSome_some]

theorem legitimate_polymorphism_published :
    (check {} 8 polymorphicIdentity (.typeAll (.imp ordinary ordinary))).isSome = true := by
  have formed : checkProposition {} 0 [] (.typeAll (.imp ordinary ordinary)) = true := by decide
  simp only [check, formed, polymorphic_identity_accepted, ↓reduceDIte, Option.isSome_some]

theorem unscoped_specialization_cannot_publish :
    check {} 8 (.typeApp predicateIdentityProof (.var 0))
      (Tm.typeInstantiate (.var 0) predicateIdentityBody) = none := by decide +kernel

theorem known_prefix_cannot_escape_formation :
    check prefixKnownEnvironment 8 (.proofLam ordinary (.known "predicate-identity"))
      (.imp ordinary (.typeAll predicateIdentityBody)) = none := by decide +kernel

end Controls
end Mettapedia.Languages.Megalodon.NativeTheorem
