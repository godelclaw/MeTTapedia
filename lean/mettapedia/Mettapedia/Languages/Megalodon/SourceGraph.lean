import Mettapedia.Languages.Megalodon.SourceCursor

/-!
# Complete local graphs for protected source proofs

The local admission relation records the executable source guard. Its meaning
is established separately: protected proofs of the original inductive judgment
produce admitted graphs, and admitted graphs reconstruct those original proofs.
The guard is therefore a representation boundary, not a replacement logic.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.SourceGraph
open MathdataKernel ProofJudgment BorrowedProofCursor SourceScopeInvariant SourceCursor
open Mettapedia.Logic Mettapedia.Logic.DerivationGraph

def LocalAdmission (environment : Environment) (fuel : Nat)
    (premises : List Judgment) (conclusion : Judgment) : Prop :=
  ∃ witness, WitnessSafe witness ∧ JudgmentSafe conclusion ∧
    requirements environment fuel witness conclusion = some premises

def interface (environment : Environment) (fuel : Nat) : RuleWitness (LocalAdmission environment fuel) where
  W := Witness
  isInstance witness premises conclusion := decide
    (WitnessSafe witness ∧ JudgmentSafe conclusion ∧ requirements environment fuel witness conclusion = some premises)
  sound witness _ _ checked := ⟨witness, of_decide_eq_true checked⟩
  complete _ _ admitted := by
    obtain ⟨witness, checked⟩ := admitted
    exact ⟨witness, by simp [checked]⟩

theorem derives_protected_proof {environment : Environment} {fuel : Nat} {judgment : Judgment}
    (derived : Derives (LocalAdmission environment fuel) judgment) :
    ∃ proof, ProofPayload proof ∧ Proves environment fuel judgment.context proof judgment.proposition := by
  induction derived with
  | node premises conclusion admitted _ ih =>
      obtain ⟨witness, safe, _, checked⟩ := admitted
      exact requirements_proof (Nat.le_refl _) safe checked ih

private theorem safe_judgment {environment : Environment} (definitions : Definitions environment)
    (known : Known environment) {fuel : Nat} {context : Context} {proof : Pf} {proposition : Tm}
    (derived : Proves environment fuel context proof proposition) (safeContext : ContextSafe context)
    (payload : ProofPayload proof) : JudgmentSafe ⟨context, proposition⟩ :=
  ⟨safeContext, proof_invariants definitions known derived safeContext payload⟩

private theorem singleton {rules : List Judgment → Judgment → Prop} {judgment : Judgment}
    (derived : Derives rules judgment) : ∀ parent ∈ [judgment], Derives rules parent := by
  intro parent member
  simpa only [List.mem_singleton.mp member] using derived

theorem protected_proof_derives {environment : Environment} (definitions : Definitions environment)
    (known : Known environment) {fuel : Nat} {context : Context} {proof : Pf} {proposition : Tm}
    (derived : Proves environment fuel context proof proposition) (safeContext : ContextSafe context)
    (payload : ProofPayload proof) : Derives (LocalAdmission environment fuel) ⟨context, proposition⟩ := by
  induction derived with
  | @hyp context index proposition found =>
      exact .node [] _ ⟨.hyp index, trivial,
        safe_judgment definitions known (fuel := fuel) (.hyp found) safeContext payload,
        by simp [requirements, found]⟩ (by simp)
  | @known context name source proposition found normalized =>
      exact .node [] _ ⟨.known name, trivial,
        safe_judgment definitions known (.known found normalized) safeContext payload,
        by simp [requirements, found, normalized]⟩ (by simp)
  | @termApp context proof argument body normalized proposition domain parent typed unfolded converted ih =>
      have bodySafe := (proof_invariants definitions known parent safeContext payload.1).2
      exact .node _ _ ⟨.termApp argument domain body, ⟨payload.2, bodySafe⟩,
        safe_judgment definitions known (.termApp parent typed unfolded converted) safeContext payload,
        by simp [requirements, typed, unfolded, converted]⟩ (singleton (ih safeContext payload.1))
  | @proofApp context function argument domain codomain functionProof argumentProof ihf iha =>
      have domainSafe := (proof_invariants definitions known functionProof safeContext payload.1).2.1
      refine .node _ _ ⟨.proofApp domain, domainSafe,
        safe_judgment definitions known (.proofApp functionProof argumentProof) safeContext payload, rfl⟩ ?_
      intro parent member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ihf safeContext payload.1
      · exact iha safeContext payload.2
  | @termLam context type proof body formed parent ih =>
      exact .node _ _ ⟨.termLam, trivial,
        safe_judgment definitions known (.termLam formed parent) safeContext payload,
        by simp [requirements, formed]⟩ (singleton (ih (safeContext.termBinder type) payload))
  | @proofLam context proposition normalized body proof typed converted parent ih =>
      obtain ⟨scope, safe⟩ := full_normalize_invariants definitions fuel converted
      have nextSafe := safeContext.proofBinder (scope _ (inferTerm_scoped typed)) (safe payload.1)
      exact .node _ _ ⟨.proofLam proposition, payload.1,
        safe_judgment definitions known (.proofLam typed converted parent) safeContext payload,
        by simp [requirements, typed, converted]⟩ (singleton (ih nextSafe payload.2))
  | @typeApp context proof type body parent ih =>
      have bodySafe := (proof_invariants definitions known parent safeContext payload).2.2
      exact .node _ _ ⟨.typeApp type body, bodySafe,
        safe_judgment definitions known (.typeApp parent) safeContext payload,
        by simp [requirements]⟩ (singleton (ih safeContext payload))
  | @typeLam context proof body terms hypotheses parent ih =>
      exact .node _ _ ⟨.typeLam, trivial,
        safe_judgment definitions known (.typeLam terms hypotheses parent) safeContext payload,
        by simp [requirements, terms, hypotheses]⟩ (singleton (ih (ContextSafe.typeBinder context) payload))

/-- Both directions refer to the independently defined proof judgment.
Existence of a graph does not claim a polynomial expanded-tree encoding. -/
theorem protected_proof_iff_graph {environment : Environment} (definitions : Definitions environment)
    (known : Known environment) (fuel : Nat) (judgment : Judgment) (safeContext : ContextSafe judgment.context) :
    (∃ proof, ProofPayload proof ∧ inferProof environment fuel judgment.context.typeDepth judgment.context.terms
      judgment.context.hypotheses proof = some judgment.proposition) ↔
    ∃ (nodes : List (Node Judgment Witness Nat)) (cache : Array Judgment) (index : Nat),
      replay (interface environment fuel) nodes = some cache ∧ cache[index]? = some judgment := by
  constructor
  · rintro ⟨proof, payload, inferred⟩
    exact exists_replay_of_derives (interface environment fuel) (0 : Nat)
      (protected_proof_derives definitions known (proves_of_infer inferred) safeContext payload)
  · rintro ⟨nodes, cache, index, replayed, found⟩
    obtain ⟨proof, payload, derived⟩ := derives_protected_proof
      (root_sound (interface environment fuel) replayed found)
    exact ⟨proof, payload, derived.infer⟩

/-- The graph guard agrees with the borrowed worker's local rule on every
node admitted by the actual wire decoder. -/
theorem guarded_instance_eq {environment : Environment} {fuel : Nat} {node : SourceNode}
    (safe : NodeSafe node) (premises : List Judgment) :
    (interface environment fuel).isInstance node.request premises node.conclusion =
      (BorrowedProofCursor.interface environment fuel).isInstance node.request premises node.conclusion := by
  simp [interface, BorrowedProofCursor.interface, safe.1, safe.2]

end Mettapedia.Languages.Megalodon.SourceGraph
