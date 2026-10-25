import Mettapedia.Languages.HOLLight.ProofDataEncoding
import Mettapedia.OSLF.Bridges.TypeTheory.FiniteBranchingHypersetSemantics
import Mathlib.Logic.Encodable.Basic

/-!
# Material semantics of future HOL Light replay

An action supplies one complete proof receipt to the original replay checker.
It has zero or one successor. The full finite-alphabet receipt encoding gives
injective material labels, so hyperset equality is exactly labelled
bisimilarity of these future replay observations and factors through the
existing final coalgebra.

The state still retains its history. Future primitive replay reads its cache,
so equal caches are bisimilar even when past origins differ. An actual pair
of reachable states shows that the current-origin observer does not factor
through this behavioural reading. This observation boundary is explicit.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.HOLLight.HypersetReplay

open Mettapedia.Languages.OpenTheory
open Mettapedia.CategoryTheory _root_.CategoryTheory
open Mettapedia.OSLF.FiniteBranching
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ProofExecution

/-- End-of-script and unary receipt constructors fix the one-sort category. -/
def signature : Mettapedia.OSLF.DeterministicGSOS.Signature where
  Srt := Unit
  Operator _ := Option Receipt
  Position command := match command with | none => Empty | some _ => Unit
  argument _ _ := ()
  finite command := by cases command <;> infer_instance

abbrev actions (_ : signature.Srt) := Receipt

def advance (policy : AxiomPolicy) [DecidablePred policy] (before : State) (receipt : Receipt) : Option State :=
  (receipt.replay (ruleWitness policy) before.cache).map
    (fun cache => ⟨cache, before.receipts.push receipt⟩)

def successors (policy : AxiomPolicy) [DecidablePred policy] (before : State) (receipt : Receipt) : Finset State :=
  (advance policy before receipt).toFinset

def system (policy : AxiomPolicy) [DecidablePred policy] :
    Endofunctor.Coalgebra (behaviourFunctor signature actions) where
  V := fun _ _ => State
  str := fun _ _ => ↾(successors policy)

theorem advance_eq_some_iff (policy : AxiomPolicy) [DecidablePred policy]
    (before after : State) (receipt : Receipt) :
    advance policy before receipt = some after ↔
      receipt.replay (ruleWitness policy) before.cache = some after.cache ∧
      after.receipts = before.receipts.push receipt := by
  cases after with
  | mk cache receipts =>
      simp only [advance, Option.map_eq_some_iff, State.mk.injEq]
      constructor
      · rintro ⟨found, replayed, rfl, same⟩
        exact ⟨replayed, same.symm⟩
      · rintro ⟨replayed, rfl⟩
        exact ⟨cache, replayed, rfl, rfl⟩

theorem mem_successors_iff (policy : AxiomPolicy) [DecidablePred policy]
    (before after : State) (receipt : Receipt) :
    after ∈ successors policy before receipt ↔
      receipt.replay (ruleWitness policy) before.cache = some after.cache ∧
      after.receipts = before.receipts.push receipt := by
  simpa [successors] using advance_eq_some_iff policy before after receipt

/-- The coalgebra contains exactly the source model's proof-execution steps. -/
theorem step_iff_successor (policy : AxiomPolicy) [DecidablePred policy] (before after : State) :
    ProofExecution.Step policy before after ↔ ∃ receipt, after ∈ successors policy before receipt := by
  constructor
  · rintro ⟨receipt, replayed, retained⟩
    exact ⟨receipt, (mem_successors_iff policy before after receipt).mpr ⟨replayed, retained⟩⟩
  · rintro ⟨receipt, member⟩
    exact ⟨receipt, (mem_successors_iff policy before after receipt).mp member⟩

theorem successor_valid (policy : AxiomPolicy) [DecidablePred policy]
    {before after : State} (receipt : Receipt) (member : after ∈ successors policy before receipt)
    (valid : ProofExecution.Valid policy before) : ProofExecution.Valid policy after :=
  ProofExecution.step_preserves_derivations policy
    ((step_iff_successor policy before after).mpr ⟨receipt, member⟩) valid

/-- Labels retain every request field, origin, ordered parent and conclusion. -/
def labels (_ : signature.Srt) (receipt : Receipt) : HSet.{0} :=
  HSet.numeralLabel (Encodable.encode
    (Mettapedia.OSLF.Binding.WireCodec.Binary.encodeWith ProofDataEncoding.receiptCodec receipt))

theorem labels_injective (sort : signature.Srt) : Function.Injective (labels sort) :=
  HSet.numeralLabel_injective.comp
    (Encodable.encode_injective.comp
      (Mettapedia.OSLF.Binding.WireCodec.Binary.encodeWith_injective ProofDataEncoding.receiptCodec))

def meaning (policy : AxiomPolicy) [DecidablePred policy] (state : State) : HSet.{0} :=
  Mettapedia.OSLF.FiniteBranching.HypersetSemantics.readout (system policy) labels PUnit.unit () state

theorem meaning_via_final (policy : AxiomPolicy) [DecidablePred policy] (state : State) :
    Mettapedia.OSLF.FiniteBranching.HypersetSemantics.readout
      (FinalSemantics.finalObject signature actions) labels PUnit.unit ()
      ((FinalSemantics.observe signature actions (system policy)).f PUnit.unit () state) =
      meaning policy state :=
  Mettapedia.OSLF.FiniteBranching.HypersetSemantics.readout_observe (system policy) labels PUnit.unit () state

theorem meaning_eq_iff_bisimilar (policy : AxiomPolicy) [DecidablePred policy] (left right : State) :
    meaning policy left = meaning policy right ↔
      Bisimulation.Bisimilar (system policy) (system policy) PUnit.unit () left right :=
  Mettapedia.OSLF.FiniteBranching.HypersetSemantics.readout_eq_iff_bisimilar
    (system policy) (system policy) labels labels_injective PUnit.unit () left right

/-- Future source primitive replay depends on the cache, not prior receipt origins. -/
theorem sameCache_bisimulation (policy : AxiomPolicy) [DecidablePred policy] :
    Bisimulation.Admitted (system policy) (system policy)
      (fun _ _ left right => left.cache = right.cache) := by
  classical
  intro base sort left right same receipt
  change FinitePowerset.Related (fun first second : State => first.cache = second.cache)
    (successors policy left receipt) (successors policy right receipt)
  cases replayed : receipt.replay (ruleWitness policy) left.cache with
  | none =>
      have other : receipt.replay (ruleWitness policy) right.cache = none := same ▸ replayed
      simp [successors, advance, replayed, other, FinitePowerset.Related]
  | some cache =>
      have other : receipt.replay (ruleWitness policy) right.cache = some cache := same ▸ replayed
      simp [successors, advance, replayed, other, FinitePowerset.Related]

theorem meaning_of_same_cache (policy : AxiomPolicy) [DecidablePred policy]
    {left right : State} (same : left.cache = right.cache) : meaning policy left = meaning policy right :=
  (meaning_eq_iff_bisimilar policy left right).mpr ⟨_, sameCache_bisimulation policy, same⟩

/-- Two actually reachable histories have the same complete future replay
behaviour while the retained-origin query distinguishes them. -/
theorem origin_not_determined_by_meaning :
    ¬ ∃ observer : HSet.{0} → Prop, ∀ state : State,
      (gslt emptyAxiomPolicy).MultiStep empty state →
      (observer (meaning emptyAxiomPolicy state) ↔ Nonempty (ReceiptAtOrigin state ("source", 0))) := by
  rintro ⟨observer, agrees⟩
  have same : meaning emptyAxiomPolicy (Controls.once ("source", 0)) =
      meaning emptyAxiomPolicy (Controls.once ("other", 0)) := meaning_of_same_cache _ rfl
  have first := (agrees _ (Controls.once_reachable ("source", 0))).mpr
    (Controls.retained_origin_available ("source", 0))
  rw [same] at first
  exact Controls.different_origin_refused (first := ("other", 0)) (second := ("source", 0))
    (by decide) ((agrees _ (Controls.once_reachable ("other", 0))).mp first)


/-! ## Cache occurrences can affect future checking -/

/-- This future command uses the second physical cached occurrence twice. -/
def referenceSecond : Receipt :=
  { Controls.sharedTransitivity ("future", 0) with parents := [1, 1] }

theorem referenceSecond_refused (origin : Origin) :
    referenceSecond.replay (ruleWitness emptyAxiomPolicy) (Controls.once origin).cache = none := by
  simp [referenceSecond, Controls.sharedTransitivity, Controls.once,
    Mettapedia.Logic.DerivationGraph.Node.replay, Mettapedia.Logic.DerivationGraph.lookupPremises]

theorem referenceSecond_replayed (first second : Origin) :
    referenceSecond.replay (ruleWitness emptyAxiomPolicy) (Controls.twice first second).cache =
      some ((Controls.twice first second).cache.push Controls.reflexivityTheorem) := by
  have primitive := ((ProofSystem.node_replay_iff emptyAxiomPolicy
    (Controls.once first).cache (Controls.twice first second).cache (Controls.sharedTransitivity second)).mp
    (Controls.shared_transitivity_replayed first second)).2.1
  apply (ProofSystem.node_replay_iff emptyAxiomPolicy _ _ _).mpr
  exact ⟨rfl, primitive, rfl⟩

/-- Equal theorem support does not imply equal future replay behaviour.
The same second-position lookup succeeds only in the two-occurrence cache. -/
theorem repeated_cache_entry_changes_meaning (first second : Origin) :
    meaning emptyAxiomPolicy (Controls.once first) ≠
      meaning emptyAxiomPolicy (Controls.twice first second) := by
  intro same
  obtain ⟨relation, admitted, related⟩ := (meaning_eq_iff_bisimilar emptyAxiomPolicy _ _).mp same
  let after : State := ⟨(Controls.twice first second).cache.push Controls.reflexivityTheorem,
    (Controls.twice first second).receipts.push referenceSecond⟩
  have present : after ∈ successors emptyAxiomPolicy (Controls.twice first second) referenceSecond :=
    (mem_successors_iff emptyAxiomPolicy _ _ _).mpr ⟨referenceSecond_replayed first second, rfl⟩
  obtain ⟨before, member, _⟩ :=
    (admitted PUnit.unit () _ _ related referenceSecond).2 after present
  change before ∈ successors emptyAxiomPolicy (Controls.once first) referenceSecond at member
  simp [successors, advance, referenceSecond_refused] at member
  exact Finset.notMem_empty _ member

theorem support_agrees_but_meaning_differs (first second : Origin) :
    ProofExecution.support (Controls.once first) = ProofExecution.support (Controls.twice first second) ∧
      meaning emptyAxiomPolicy (Controls.once first) ≠ meaning emptyAxiomPolicy (Controls.twice first second) :=
  ⟨Controls.extra_inference_same_support first second, repeated_cache_entry_changes_meaning first second⟩

end Mettapedia.Languages.HOLLight.HypersetReplay
