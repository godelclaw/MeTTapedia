import Mettapedia.CognitiveArchitecture.CollectiveAgency.InferenceHive
import Mettapedia.Cybernetics.ApproximateAdequacy.MemoryRecovery

/-!
# Exact authority and approximate collective decisions

The persistent knowledge readout may be sufficient for a task while being
insufficient for present authority. The Boolean safety-query family keeps
permissions, commitment status, responsibility and resource ownership exact.
It uses the existing policy-family realization interface.

Decision scores can separately use a recovered finite belief and an explicit
KL budget. The theorem combines exact eligibility from retained safety queries
with the existing recovery regret bound. Numerical approximation never grants
permission. These are finite belief profiles, not uniform laws on all histories.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.CollectiveAgency.DecisionMemory

open Lifecycle
open Mettapedia.GSLT.Core
open Mettapedia.CognitiveArchitecture.Agent.GoalCommitment
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV
open Mettapedia.InformationTheory.FiniteRecovery
open Mettapedia.Cybernetics.ApproximateAdequacy
open scoped BigOperators

inductive SafetyQuery (A Task Resource : Type*) where
  | authority (agent : A) (generation : Nat) (resource : Resource)
  | commitment (task : Task) (status : Status Nat)
  | responsible (task : Task) (agent : A)
  | owner (resource : Resource) (agent : A)

variable {A Task Resource Fact : Type*} [DecidableEq A]

abbrev safety : PolicyFamily (Body A Task Resource Fact) where
  Policy := SafetyQuery A Task Resource
  Result _ := Bool
  decide query s := match query with
    | .authority a epoch r => decide (Authorized s a epoch r)
    | .commitment task status => decide (s.commitments task = status)
    | .responsible task a => decide (s.responsible task = some a)
    | .owner r a => decide (s.owner r = a)

theorem exact_authority {Readout : Type*} {memory : Body A Task Resource Fact → Readout}
    (implementation : safety.ReadoutRealization memory) (s : Body A Task Resource Fact)
    (actor : A) (epoch : Nat) (resource : Resource) :
    implementation.run (.authority actor epoch resource) (memory s) = true ↔
      Authorized s actor epoch resource := by
  rw [implementation.agrees]
  exact decide_eq_true_iff

theorem exact_commitment {Readout : Type*} {memory : Body A Task Resource Fact → Readout}
    (implementation : safety.ReadoutRealization memory) (s : Body A Task Resource Fact)
    (task : Task) (status : Status Nat) :
    implementation.run (.commitment task status) (memory s) = true ↔
      s.commitments task = status := by
  rw [implementation.agrees]
  exact decide_eq_true_iff

section Decisions
variable {World Compressed Candidate Readout : Type*}
  [Fintype World] [Fintype Compressed] [DecidableEq Compressed]
  {memory : Body A Task Resource Fact → Readout}

/-- An exact permission readout and an approximate numeric belief serve
different purposes in one choice. The returned permission concerns the
actual current coalition state. -/
theorem authorized_regret
    (implementation : safety.ReadoutRealization memory) (current : Body A Task Resource Fact)
    (actor : Candidate → A) (resource : Candidate → Resource) (epoch : Nat)
    (p q : Prob World) (view : World → Compressed)
    (support : ∀ x, 0 < p.1 x → 0 < q.1 x)
    (score : Candidate → World → ℝ) {lo hi : ℝ} (ordered : lo ≤ hi)
    (lower : ∀ c, Authorized current (actor c) epoch (resource c) → ∀ x, lo ≤ score c x)
    (upper : ∀ c, Authorized current (actor c) epoch (resource c) → ∀ x, score c x ≤ hi)
    (selected : Candidate)
    (eligible : implementation.run (.authority (actor selected) epoch (resource selected)) (memory current) = true)
    (η : ℝ)
    (best : ∀ c, implementation.run (.authority (actor c) epoch (resource c)) (memory current) = true →
      (∑ x, (recover q view (Prob.coarsen p view)).1 x * score c x) ≤
        (∑ x, (recover q view (Prob.coarsen p view)).1 x * score selected x) + η)
    (alternative : Candidate)
    (available : implementation.run (.authority (actor alternative) epoch (resource alternative)) (memory current) = true) :
    Authorized current (actor selected) epoch (resource selected) ∧
      (∑ x, p.1 x * score alternative x) - (∑ x, p.1 x * score selected x) ≤
        (hi - lo) * Real.sqrt (2 * klLoss p q view) + η := by
  have permission := (exact_authority implementation current _ _ _).mp eligible
  refine ⟨permission, ?_⟩
  exact RecoveryDecision.regret_le p q view support score
    (fun c => Authorized current (actor c) epoch (resource c)) ordered lower upper
    selected permission η
    (fun c allowed => best c ((exact_authority implementation current _ _ _).mpr allowed))
    alternative ((exact_authority implementation current _ _ _).mp available)

theorem authorized_optimal_exists [Fintype Candidate]
    (implementation : safety.ReadoutRealization memory) (current : Body A Task Resource Fact)
    (actor : Candidate → A) (resource : Candidate → Resource) (epoch : Nat)
    (q : Prob World) (view : World → Compressed) (compressed : Prob Compressed)
    (score : Candidate → World → ℝ)
    (available : ∃ c, implementation.run (.authority (actor c) epoch (resource c)) (memory current) = true) :
    ∃ selected, Authorized current (actor selected) epoch (resource selected) ∧
      ∀ c, Authorized current (actor c) epoch (resource c) →
        (∑ x, (recover q view compressed).1 x * score c x) ≤
          ∑ x, (recover q view compressed).1 x * score selected x := by
  apply RecoveryDecision.optimal_exists q view compressed score
    (fun c => Authorized current (actor c) epoch (resource c))
  obtain ⟨c, allowed⟩ := available
  exact ⟨c, (exact_authority implementation current _ _ _).mp allowed⟩

end Decisions

namespace Controls

theorem durable_knowledge_does_not_recover_authority :
    ¬ (safety (A := Bool) (Task := Unit) (Resource := Unit) (Fact := InferenceHive.Fact)).SupportsReadout
      (fun s => s.knowledge) := by
  rintro ⟨reader⟩
  have same := InferenceHive.durable_report.2
  have a := reader.agrees (.authority false 1 ()) InferenceHive.retired.body
  have b := reader.agrees (.authority false 1 ()) InferenceHive.renewed.body
  have impossible : (false : Bool) = true := by
    calc
      false = reader.run (.authority false 1 ()) InferenceHive.retired.body.knowledge := a.symm
      _ = reader.run (.authority false 1 ()) InferenceHive.renewed.body.knowledge := by rw [same]
      _ = true := b
  cases impossible

theorem renewed_task_answers (family : PolicyFamily (Memory.Store (Bool × Nat) InferenceHive.Fact))
    (query : family.Policy) :
    family.decide query InferenceHive.renewed.body.knowledge =
      family.decide query InferenceHive.retired.body.knowledge := by
  rw [InferenceHive.durable_report.2]

end Controls

end Mettapedia.CognitiveArchitecture.CollectiveAgency.DecisionMemory
