import Mettapedia.FoundationalMeaning.Basic
import Mettapedia.SetTheory.OpenTower.ConsistencyTower

/-!
# Reflection by evidence

The theory of foundational meaning concerns agents in the physical world;
reading formal knowledge through it is an extension made here.

An agent whose own checker is an arithmetic theory `K` can place sentences in
its knowledge graph. A causal model `a → b` between sentences is *licensed*
when `K` proves `a ➝ b`. Any other model carries a reliability held as graded
evidence: agreement of independent checkers, a model inside a stronger theory,
or long use. Evidence of this kind is not a proof in `K`.

Licensed chains prove their composite implication in `K`
(`Chain.proves_of_licensed`). Let `S` be the zoom-out of a sound stage `K`,
which adds `Con(K)`. `K` verifies that `S` proves `Con(K)`
(`ConsistencyTower.SoundStage.checks_next`) but cannot detach `Con(K)`. So
every chain from that verification to `Con(K)` contains an unlicensed model
(`detach_needs_evidence`). The chain is at most as strong as that model
(`detached_strength_le`). Grounding `Con(K)` at a threshold through the
verification needs evidence at that threshold (`grounded_detach_needs_evidence`).
For the agent, then, the theorem of the stronger system means no more than
its evidence for that system's soundness supports.

**Controls.** For the agent's own theorems detachment is licensed
(`licensed_reflection_of_proves`), so no evidence is needed. With an evidence
model for the stronger system, the theorem is grounded at the weaker of the
checker's and the evidence's reliabilities (`grounded_by_evidence`).
-/

set_option autoImplicit false

namespace Mettapedia.FoundationalMeaning.ReflectionByEvidence

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open Mettapedia.SetTheory.OpenTower.ConsistencyTower

universe uReliability

variable {R : Type uReliability}

/-- A model between sentences is licensed by `K` when `K` proves its implication. -/
def Licensed (K : ArithmeticTheory) (model : CausalModel ArithmeticSentence R) : Prop :=
  K ⊢ model.source ➝ model.target

/-- A chain of licensed models proves its composite implication. -/
theorem Chain.proves_of_licensed {K : ArithmeticTheory}
    {knowledge : Set (CausalModel ArithmeticSentence R)} {start finish : ArithmeticSentence}
    {chain : List (CausalModel ArithmeticSentence R)} (formed : Chain knowledge start finish chain)
    (licensed : ∀ model ∈ chain, Licensed K model) : K ⊢ start ➝ finish := by
  induction formed with
  | nil => exact C!_id
  | cons _ _ ih =>
      exact C!_trans (licensed _ (List.mem_cons_self ..))
        (ih fun model inRest => licensed model (List.mem_cons_of_mem _ inRest))

/-- Detaching an own theorem is licensed. -/
theorem licensed_reflection_of_proves {K : ArithmeticTheory} [K.Δ₁] {σ : ArithmeticSentence}
    (proved : K ⊢ σ) (reliability : R) :
    Licensed K (⟨K.standardProvability σ, σ, reliability⟩ : CausalModel ArithmeticSentence R) :=
  C!_of_conseq! proved

variable (S : SoundStage)

/-- The verification, inside the stage, that its zoom-out proves `Con` of the stage. -/
noncomputable abbrev verified : ArithmeticSentence :=
  S.next.theory.standardProvability ↑S.theory.consistent

/-- **Detaching a stronger theorem needs evidence.** Every chain from the
verification to `Con` of the stage contains a model the stage does not license. -/
theorem detach_needs_evidence {knowledge : Set (CausalModel ArithmeticSentence R)}
    {chain : List (CausalModel ArithmeticSentence R)}
    (formed : Chain knowledge (verified S) ↑S.theory.consistent chain) :
    ∃ model ∈ chain, ¬ Licensed S.theory model := by
  by_contra noneUnlicensed
  have allLicensed : ∀ model ∈ chain, Licensed S.theory model := by
    intro model inChain
    by_contra unlicensed
    exact noneUnlicensed ⟨model, inChain, unlicensed⟩
  exact S.not_detaches_next_consistency (Chain.proves_of_licensed formed allLicensed)

variable [LinearOrder R] [OrderTop R]

/-- The chain is at most as strong as an unlicensed model in it. -/
theorem detached_strength_le {knowledge : Set (CausalModel ArithmeticSentence R)}
    {chain : List (CausalModel ArithmeticSentence R)}
    (formed : Chain knowledge (verified S) ↑S.theory.consistent chain) :
    ∃ model ∈ chain, ¬ Licensed S.theory model ∧ strength chain ≤ model.reliability := by
  obtain ⟨model, inChain, unlicensed⟩ := detach_needs_evidence S formed
  exact ⟨model, inChain, unlicensed, (le_strength_iff _ chain).mp le_rfl model inChain⟩

/-- **Grounding a detached theorem needs evidence at the same threshold.** -/
theorem grounded_detach_needs_evidence {knowledge : Set (CausalModel ArithmeticSentence R)}
    {threshold : R} (grounded : GroundedAt knowledge threshold (verified S) ↑S.theory.consistent) :
    ∃ model ∈ knowledge, ¬ Licensed S.theory model ∧ threshold ≤ model.reliability := by
  obtain ⟨chain, formed, strong⟩ := grounded
  obtain ⟨model, inChain, unlicensed, bounded⟩ := detached_strength_le S formed
  exact ⟨model, formed.mem_knowledge inChain, unlicensed, strong.trans bounded⟩

/-- The checker's model: the stage verifies the zoom-out's proof of its consistency. -/
noncomputable def checkerModel (checker : R) : CausalModel ArithmeticSentence R :=
  ⟨⊤, verified S, checker⟩

omit [LinearOrder R] [OrderTop R] in
theorem checkerModel_licensed (checker : R) : Licensed S.theory (checkerModel S checker) :=
  C!_of_conseq! (S.checks_next S.next_proves_consistency)

/-- The evidence model: graded trust in the zoom-out's soundness at its consistency theorem. -/
noncomputable def evidenceModel (evidence : R) : CausalModel ArithmeticSentence R :=
  ⟨verified S, ↑S.theory.consistent, evidence⟩

omit [LinearOrder R] [OrderTop R] in
theorem evidenceModel_unlicensed (evidence : R) : ¬ Licensed S.theory (evidenceModel S evidence) :=
  S.not_detaches_next_consistency

/-- **Positive control.** With the checker's model and an evidence model, `Con`
of the stage is grounded at the weaker of their reliabilities. -/
theorem grounded_by_evidence (checker evidence : R) :
    GroundedAt ({checkerModel S checker, evidenceModel S evidence} :
        Set (CausalModel ArithmeticSentence R))
      (min checker evidence) ⊤ ↑S.theory.consistent :=
  ⟨[checkerModel S checker, evidenceModel S evidence],
    .cons (model := checkerModel S checker) (Or.inl rfl)
      (.cons (model := evidenceModel S evidence) (Or.inr rfl) (.nil _)),
    by simp [checkerModel, evidenceModel]⟩

/-- At `𝗣𝗔`: grounding `Con(𝗣𝗔)` through its verification in `𝗣𝗔 + Con(𝗣𝗔)` needs
evidence at the threshold. -/
theorem peano_grounded_detach_needs_evidence {knowledge : Set (CausalModel ArithmeticSentence R)}
    {threshold : R}
    (grounded : GroundedAt knowledge threshold (verified peano) ↑𝗣𝗔.consistent) :
    ∃ model ∈ knowledge, ¬ Licensed 𝗣𝗔 model ∧ threshold ≤ model.reliability :=
  grounded_detach_needs_evidence peano grounded

end Mettapedia.FoundationalMeaning.ReflectionByEvidence
