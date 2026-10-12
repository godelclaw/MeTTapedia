import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ResourcePredation
import Mathlib.Data.List.Nodup

/-!
# Complete firing histories and exclusive resource claims

Finite executions retain the actual firing selected at every intermediate
configuration. Their claim ledger retains the full receiver and resource
occurrences, including their activation origins. A uniquely keyed output can
be consumed at most once in any such execution, even when a continuation
reissues an equal message. Fresh reissues are different occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.ResourceClaimHistory

open ResourcePredation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness

/-- A proof-relevant finite execution in the occurrence semantics. -/
inductive Execution : Configuration → Configuration → Type where
  | done (source : Configuration) : Execution source source
  | next {source target : Configuration} (firing : Firing source)
      (rest : Execution firing.target target) : Execution source target

namespace Execution

variable {source target : Configuration}

def length : {source target : Configuration} → Execution source target → Nat
  | _, _, .done _ => 0
  | _, _, .next _ rest => 1 + rest.length

/-- Every entry retains its intermediate configuration and complete firing. -/
def claims : {source target : Configuration} →
    Execution source target → List (Σ current : Configuration, Firing current)
  | _, _, .done _ => []
  | _, _, .next firing rest => ⟨_, firing⟩ :: rest.claims

def claimedKeys (execution : Execution source target) : List Nat :=
  execution.claims.map fun entry => entry.2.resource.key

@[simp] theorem claims_length (execution : Execution source target) :
    execution.claims.length = execution.length := by
  induction execution with
  | done => rfl
  | next firing rest ih => simp only [claims, List.length_cons, length, ih]; omega

@[simp] theorem claimedKeys_done (current : Configuration) :
    (Execution.done current).claimedKeys = [] := rfl

@[simp] theorem claimedKeys_next (firing : Firing source)
    (rest : Execution firing.target target) :
    (Execution.next firing rest).claimedKeys = firing.resource.key :: rest.claimedKeys := rfl

theorem history : {source target : Configuration} → Execution source target → History source target
  | _, _, .done _ => .refl
  | _, _, .next firing rest =>
      (Relation.ReflTransGen.single ⟨firing, rfl⟩).trans rest.history

theorem public_history (execution : Execution source target) :
    Relation.ReflTransGen rhoLanguageDefGSLT.Step (readout source) (readout target) :=
  execution.history.public

theorem distinct (execution : Execution source target) (initial : Distinct source) :
    Distinct target := execution.history.distinct initial

def append : {first middle last : Configuration} → Execution first middle →
    Execution middle last → Execution first last
  | _, _, _, .done _, second => second
  | _, _, _, .next firing rest, second => .next firing (rest.append second)

theorem claims_append {last : Configuration} (first : Execution source target)
    (second : Execution target last) :
    (first.append second).claims = first.claims ++ second.claims := by
  induction first with
  | done => rfl
  | next firing rest ih => simp only [append, claims, List.cons_append, ih]

theorem append_length {last : Configuration} (first : Execution source target)
    (second : Execution target last) :
    (first.append second).length = first.length + second.length := by
  have equal := congrArg List.length (claims_append first second)
  simpa only [claims_length, List.length_append] using equal

theorem append_assoc {middle last : Configuration} (first : Execution source target)
    (second : Execution target middle) (third : Execution middle last) :
    (first.append second).append third = first.append (second.append third) := by
  induction first with
  | done => rfl
  | next firing rest ih => exact congrArg (Execution.next firing) (ih second)

/-- A ledger entry comes from an actual firing at a reachable configuration. -/
theorem claim_reaches (execution : Execution source target) {key : Nat}
    (membership : key ∈ execution.claimedKeys) :
    ∃ current, History source current ∧ ∃ firing : Firing current, firing.resource.key = key := by
  induction execution with
  | done => simp at membership
  | @next source target firing rest ih =>
      rcases List.mem_cons.mp membership with first | later
      · exact ⟨source, .refl, firing, first.symm⟩
      · obtain ⟨current, prior, claim, equal⟩ := ih later
        exact ⟨current, (Relation.ReflTransGen.single ⟨firing, rfl⟩).trans prior,
          claim, equal⟩

/-- Any subsequent claim must consume an occurrence still present then. -/
theorem consumed_not_claimed_later (firing : Firing source) (initial : Distinct source)
    (rest : Execution firing.target target) :
    firing.resource.key ∉ rest.claimedKeys := by
  intro membership
  obtain ⟨current, prior, claim, equal⟩ := rest.claim_reaches membership
  exact firing.consumed_key_never_reappears initial prior claim.resource
    (List.mem_of_mem_eraseIdx (List.getElem_mem claim.outputIndex.isLt)) equal

/-- The complete ledger contains no repeated consumed occurrence key. -/
theorem claimedKeys_nodup (execution : Execution source target) (initial : Distinct source) :
    execution.claimedKeys.Nodup := by
  induction execution with
  | done => exact List.nodup_nil
  | next firing rest ih =>
      exact List.nodup_cons.mpr
        ⟨consumed_not_claimed_later firing initial rest, ih (firing.distinct_target initial)⟩

theorem claim_count_le_one (execution : Execution source target) (initial : Distinct source)
    (key : Nat) : execution.claimedKeys.count key ≤ 1 :=
  List.nodup_iff_count_le_one.mp (execution.claimedKeys_nodup initial) key

theorem claimed_exactly_once (execution : Execution source target) (initial : Distinct source)
    {key : Nat} (membership : key ∈ execution.claimedKeys) :
    execution.claimedKeys.count key = 1 :=
  List.count_eq_one_of_mem (execution.claimedKeys_nodup initial) membership

end Execution

/-- Independently supplied public executions lift to complete firing histories,
including every intermediate occurrence inventory. -/
theorem public_execution_lifts (initial : Configuration) {target : RhoProcess}
    (history : Relation.ReflTransGen rhoLanguageDefGSLT.Step (readout initial) target) :
    ∃ final, ∃ _execution : Execution initial final, inventory final = fromProcess target := by
  induction history with
  | refl => exact ⟨initial, .done initial, (fromProcess_toProcess _).symm⟩
  | @tail middle target history step ih =>
      obtain ⟨current, execution, currentEqual⟩ := ih
      have currentStep : rhoLanguageDefGSLT.Step (readout current) target := by
        apply (CanonicalReaction.publicStep_iff _ _).mpr
        rw [readout, fromProcess_toProcess, currentEqual]
        exact (CanonicalReaction.publicStep_iff _ _).mp step
      obtain ⟨firing, finalEqual⟩ := publicStep_lifts currentStep
      exact ⟨firing.target, execution.append (.next firing (.done firing.target)), finalEqual⟩

/-- The no-double-claim law covers every public finite execution, including
equation transport and arbitrary choices of enabled communications. -/
theorem public_execution_exclusive_claims (initial : Configuration)
    (distinct : Distinct initial) {target : RhoProcess}
    (history : Relation.ReflTransGen rhoLanguageDefGSLT.Step (readout initial) target) :
    ∃ final, ∃ execution : Execution initial final,
      inventory final = fromProcess target ∧ execution.claimedKeys.Nodup ∧
        ∀ key, execution.claimedKeys.count key ≤ 1 := by
  obtain ⟨final, execution, equal⟩ := public_execution_lifts initial history
  exact ⟨final, execution, equal, execution.claimedKeys_nodup distinct,
    execution.claim_count_le_one distinct⟩

/-- A race consists of two independently enabled receivers for the same output.
The origin conditions distinguish owner spending from contextual harvesting. -/
structure Race (source : Configuration) where
  distinct : Distinct source
  owner : Firing source
  competitor : Firing source
  sameResource : owner.resource = competitor.resource
  computationResource : owner.resource.origin = .computation
  ownerOrigin : owner.receiver.origin = .computation
  competitorOrigin : competitor.receiver.origin = .context

namespace Race

variable {source : Configuration}

theorem different_receivers (race : Race source) :
    race.owner.receiver ≠ race.competitor.receiver := by
  intro equal
  have impossible := congrArg Occurrence.origin equal
  rw [race.ownerOrigin, race.competitorOrigin] at impossible
  cases impossible

theorem owner_spending (race : Race source) :
    rhoLanguageDefGSLT.Step (readout source) (readout race.owner.target) ∧
      ¬ HarvestAt race.owner.resource.key race.owner := by
  refine ⟨race.owner.public_step, ?_⟩
  rintro ⟨_, _, contextual⟩
  rw [race.ownerOrigin] at contextual
  cases contextual

theorem competitor_harvesting (race : Race source) :
    HarvestAt race.owner.resource.key race.competitor ∧
      rhoLanguageDefGSLT.Step (readout source) (readout race.competitor.target) := by
  refine ⟨⟨?_, ?_, race.competitorOrigin⟩, race.competitor.public_step⟩
  · exact congrArg Occurrence.key race.sameResource.symm
  · rw [← race.sameResource]
    exact race.computationResource

/-- After the owner wins, no later context can harvest this original occurrence. -/
theorem owner_excludes_original_harvest (race : Race source)
    {future : Configuration} (history : History race.owner.target future)
    (claim : Firing future) : ¬ HarvestAt race.owner.resource.key claim := by
  rintro ⟨equal, _, _⟩
  exact race.owner.consumed_key_never_reappears race.distinct history claim.resource
    (List.mem_of_mem_eraseIdx (List.getElem_mem claim.outputIndex.isLt)) equal

/-- After the competitor wins, the owner cannot spend this original occurrence. -/
theorem competitor_excludes_original_spend (race : Race source)
    {future : Configuration} (history : History race.competitor.target future)
    (claim : Firing future) : claim.resource.key ≠ race.owner.resource.key := by
  rw [race.sameResource]
  exact race.competitor.consumed_key_never_reappears race.distinct history claim.resource
    (List.mem_of_mem_eraseIdx (List.getElem_mem claim.outputIndex.isLt))

/-- Reissued resources carry keys strictly newer than the consumed occurrence. -/
theorem reissued_resource_is_new (race : Race source) {occurrence : Occurrence}
    (membership : occurrence ∈ race.owner.spawned) :
    race.owner.resource.key < occurrence.key := by
  have old := source.reserved race.owner.resource
    (List.mem_of_mem_eraseIdx (List.getElem_mem race.owner.outputIndex.isLt))
  have fresh := race.owner.spawned_fresh membership
  unfold ResourcePredation.fresh at fresh
  omega

end Race

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.ResourceClaimHistory
