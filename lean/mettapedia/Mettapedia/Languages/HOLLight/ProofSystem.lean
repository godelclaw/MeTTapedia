import Mettapedia.Languages.HOLLight.ProofExecution
import Mettapedia.Languages.OpenTheory.ExtensionalHOLInterpretation
import Mettapedia.GSLT.LanguageDef.KernelAuthority

/-!
# HOL Light's proof graphs as an exact checker

HOL Light's kernel admits a theorem by one of its ten inference rules, or as an axiom of
its theory. A certificate here is a proof graph: a list of nodes, each naming a rule
instance and citing earlier nodes as its premises, together with the position of the
claimed theorem. Definitions and type definitions extend the theory itself; they are
replayed by `ExportReplay`, and this checker works within one theory.

* **Exact.** The checker accepts a theorem exactly when the rules derive it
  (`checker_authority`). Soundness and completeness come from the replay of finite
  derivation graphs (`DerivationGraph.root_sound`, `DerivationGraph.exists_replay_of_derives`).
* **Sound in models.** For the kernel without axioms, the translated conclusion of an
  accepted theorem holds in every extensional Henkin model in which its translated
  hypotheses hold (`checker_models`).
* **Every step is explicit.** A node is accepted exactly when its cited premises are the
  premises of its rule request and the rule computes the node's conclusion from them
  (`node_replay_iff`). Terms are compared by their canonical representation, so alpha
  equivalence is equality, and `BETA` contracts only the trivial redex `(λx. t) x`. The
  checker computes each step's unique result and compares; it never searches for a
  conversion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ProofSystem

open Mettapedia.Languages.OpenTheory Mettapedia.Logic
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open ProofExecution (Receipt Origin)

/-- A proof graph and the position of its root. -/
abbrev Certificate := List Receipt × Nat

section Checker

variable (policy : AxiomPolicy) [DecidablePred policy]

/-- Replay the graph, then compare the theorem at the root with the claim. -/
def checker : Checker Theorem Certificate where
  check claim certificate :=
    match DerivationGraph.replay (ruleWitness policy) certificate.1 with
    | some cache => decide (cache[certificate.2]? = some claim)
    | none => false

theorem checker_check_iff (claim : Theorem) (certificate : Certificate) :
    (checker policy).check claim certificate = true ↔
      ∃ cache, DerivationGraph.replay (ruleWitness policy) certificate.1 = some cache ∧
        cache[certificate.2]? = some claim := by
  simp only [checker]
  cases DerivationGraph.replay (ruleWitness policy) certificate.1 with
  | none => simp
  | some cache => simp

/-- **HOL Light's proof graphs check exactly the theorems its rules derive.** -/
theorem checker_authority : (checker policy).Authority (Derives (Rule policy)) where
  sound claim certificate accepted := by
    obtain ⟨cache, replayed, found⟩ := (checker_check_iff policy claim certificate).mp accepted
    exact DerivationGraph.root_sound (ruleWitness policy) replayed found
  complete claim derivation := by
    obtain ⟨nodes, cache, index, replayed, found⟩ :=
      DerivationGraph.exists_replay_of_derives (ruleWitness policy) (("authored", 0) : Origin)
        derivation
    exact ⟨(nodes, index), (checker_check_iff policy claim (nodes, index)).mpr
      ⟨cache, replayed, found⟩⟩

/-- **Each node is one explicit step.** It is accepted exactly when the cited premises are
those of its rule request and the rule computes the node's conclusion from them. -/
theorem node_replay_iff (cache result : Array Theorem) (node : Receipt) :
    node.replay (ruleWitness policy) cache = some result ↔
      DerivationGraph.lookupPremises cache node.parents = some node.witness.premises ∧
        node.witness.check policy = some node.conclusion ∧
          result = cache.push node.conclusion := by
  refine (DerivationGraph.Node.replay_eq_some_iff (ruleWitness policy) cache result node).trans ?_
  constructor
  · rintro ⟨premises, found, instance', shape⟩
    obtain ⟨same, semantics⟩ :=
      (RuleRequest.isInstance_eq_true_iff policy node.witness premises node.conclusion).mp instance'
    exact ⟨same ▸ found, (RuleRequest.check_eq_some_iff policy _ _).mpr semantics, shape⟩
  · rintro ⟨found, checked, shape⟩
    exact ⟨node.witness.premises, found,
      (RuleRequest.isInstance_eq_true_iff policy node.witness _ node.conclusion).mpr
        ⟨rfl, (RuleRequest.check_eq_some_iff policy _ _).mp checked⟩, shape⟩

end Checker

/-- **For the kernel without axioms, an accepted theorem holds in every extensional Henkin
model in which its hypotheses hold.** -/
theorem checker_models {claim : Theorem} {certificate : Certificate}
    (accepted : (checker emptyAxiomPolicy).check claim certificate = true)
    (model : HOL.HenkinModel AtomicTy Symbol) (extensional : model.FunctionsRespectEqv) :
    ∃ φ, Translates [] claim.sequent.concl.term .prop φ ∧
      ((∀ ψ ∈ translatedHypotheses claim.sequent.hyp, model.models ψ) → model.models φ) := by
  have derivation := derives_shared emptyAxiomPolicy
    ((checker_authority emptyAxiomPolicy).sound claim certificate accepted)
  exact derives_models variableFreeSubstitutionClosed_empty derivation
    (fun tagged member => by
      rw [axioms_eq_empty_of_emptyAxiomPolicy derivation] at member
      exact absurd member (Finset.notMem_empty _))
    model extensional (fun _ member => absurd member (Set.notMem_empty _))

/-! ## Controls -/

namespace Controls

open ProofExecution.Controls

/-- The one-node graph proving `p = p` by `REFL`. -/
def reflexivityCertificate : Certificate := ([reflexivity ("authored", 0)], 0)

theorem reflexivity_replay :
    DerivationGraph.replay (ruleWitness emptyAxiomPolicy) [reflexivity ("authored", 0)] =
      some #[reflexivityTheorem] := by
  have checked : checkRefl proposition = some reflexivityTheorem :=
    (checkRefl_eq_some_iff _ _).mpr
      ⟨equality, CanonicalTerm.equalityOfSameType_semantics _ _ rfl, rfl, rfl, rfl⟩
  have admitted :
      (RuleRequest.inference (.refl proposition)).isInstance emptyAxiomPolicy []
        reflexivityTheorem = true :=
    (RuleRequest.isInstance_eq_true_iff _ _ _ _).mpr
      ⟨rfl, (checkRefl_eq_some_iff _ _).mp checked⟩
  simp [DerivationGraph.replay, DerivationGraph.replayFrom, reflexivity,
    DerivationGraph.Node.replay, DerivationGraph.lookupPremises, ruleWitness, admitted]

theorem reflexivity_accepted :
    (checker emptyAxiomPolicy).check reflexivityTheorem reflexivityCertificate = true :=
  (checker_check_iff emptyAxiomPolicy _ _).mpr ⟨#[reflexivityTheorem], reflexivity_replay, rfl⟩

/-- The same graph does not certify a theorem at a position it does not have. -/
theorem reflexivity_wrong_root :
    (checker emptyAxiomPolicy).check reflexivityTheorem ([reflexivity ("authored", 0)], 1) =
      false := by
  rw [Bool.eq_false_iff]
  intro accepted
  obtain ⟨cache, replayed, found⟩ := (checker_check_iff emptyAxiomPolicy _ _).mp accepted
  have same : some cache = some #[reflexivityTheorem] := replayed.symm.trans reflexivity_replay
  cases Option.some.inj same
  simp at found

/-- A graph citing a premise that does not exist is rejected. -/
theorem forward_reference_rejected (claim : Theorem) :
    (checker emptyAxiomPolicy).check claim
      ([⟨reflexivityTheorem, .inference (.refl proposition), [0], ("authored", 0)⟩], 0) =
        false := by
  simp [checker, DerivationGraph.replay, DerivationGraph.replayFrom,
    DerivationGraph.Node.replay, DerivationGraph.lookupPremises]

end Controls

end Mettapedia.Languages.HOLLight.ProofSystem
