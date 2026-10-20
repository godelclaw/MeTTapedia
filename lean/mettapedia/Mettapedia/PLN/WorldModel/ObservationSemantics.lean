import Mettapedia.Logic.WorldModel.Observation
import Mettapedia.PLN.WorldModel.EvidenceContracts

/-!
# Observation identities, sample counts and report likelihoods

An identified ledger and its bag of recorded worlds give the same count
observations. Their native revisions differ on overlapping ledgers. Report
likelihoods require joint information about the hypothesis and the report;
the marginal count pair of the report cannot determine them.
-/

namespace Mettapedia.PLN.WorldModel.ObservationSemantics

open Mettapedia.Logic.WorldModel
open Mettapedia.PLN.WorldModel.EvidenceSpaces
open Mettapedia.PLN.WorldModel.EvidenceContracts

variable {Id W : Type} [DecidableEq Id]

/-- Retained observation identities are merged by set union. -/
@[instance_reducible] def ledgerModel (world : Id → W) :
    WorldModel (Finset Id) (W → Bool) (Evidence ℕ) where
  revise := (· ∪ ·)
  empty := ∅
  extract ledger query := ledgerEvidence world query ledger

/-- Sample bags are pooled with multiplicity. -/
@[instance_reducible] def sampleModel :
    WorldModel (Multiset W) (W → Bool) (Evidence ℕ) where
  revise := (· + ·)
  empty := 0
  extract samples query := ofSamples query samples

/-- Forgetting identity retains the complete query-wise count pair. -/
def ledgerToSamples (world : Id → W) :
    @ObservationMap (Finset Id) (W → Bool) (Evidence ℕ)
      (Multiset W) (W → Bool) (Evidence ℕ) (ledgerModel world) sampleModel := by
  letI := ledgerModel world
  letI := sampleModel (W := W)
  exact {
   state ledger := ledger.val.map world
   query := id
   value := id
   observe ledger query := (ledgerEvidence_eq_ofSamples world query ledger).symm }

theorem disjoint_revision_counts (world : Id → W) (query : W → Bool)
    {first second : Finset Id} (disjoint : Disjoint first second) :
    ledgerEvidence world query (first ∪ second) =
      ofSamples query (first.val.map world + second.val.map world) := by
  rw [ofSamples_add, ← ledgerEvidence_eq_ofSamples, ← ledgerEvidence_eq_ofSamples]
  exact ledgerEvidence_union_of_disjoint world query disjoint

/-- Report likelihoods are conditional frequencies in a joint population.
Zero denominators use the same division convention as the existing finite
query interface; a probabilistic consumer must retain their possibility. -/
def likelihoodsOfSamples (hypothesis report : W → Bool) (samples : Multiset W) : Evidence ℚ :=
  ⟨(count samples (fun w => hypothesis w && report w) : ℚ) / count samples hypothesis,
    (count samples (fun w => !hypothesis w && report w) : ℚ) /
      count samples (fun w => !hypothesis w)⟩

namespace Controls

def same : Multiset (Bool × Bool) := {(true, true), (false, false)}
def opposite : Multiset (Bool × Bool) := {(true, false), (false, true)}

/-- Identical report marginals can encode opposite likelihoods. -/
theorem equal_counts_different_likelihoods :
    ofSamples Prod.snd same = ofSamples Prod.snd opposite ∧
      likelihoodsOfSamples Prod.fst Prod.snd same = (⟨1, 0⟩ : Evidence ℚ) ∧
      likelihoodsOfSamples Prod.fst Prod.snd opposite = (⟨0, 1⟩ : Evidence ℚ) := by
  constructor
  · ext <;> decide +kernel
  · constructor <;> ext <;> decide +kernel

/-- Consequently no function of the report's marginal counts can recover
these likelihoods for every population. -/
theorem likelihoods_not_determined_by_report_counts :
    ¬ ∃ recover : Evidence ℕ → Evidence ℚ,
      ∀ samples : Multiset (Bool × Bool),
        recover (ofSamples Prod.snd samples) = likelihoodsOfSamples Prod.fst Prod.snd samples := by
  rintro ⟨recover, correct⟩
  obtain ⟨sameCounts, first, second⟩ := equal_counts_different_likelihoods
  have equalLikelihoods := (correct same).symm.trans ((congrArg recover sameCounts).trans (correct opposite))
  rw [first, second] at equalLikelihoods
  have := congrArg Evidence.pos equalLikelihoods
  norm_num at this

/-- Observation preservation alone does not license translating union into
bag addition: one repeated observation would be counted twice. -/
theorem overlap_prevents_revision_map :
    ledgerEvidence (fun _ : Unit => true) id (({()} : Finset Unit) ∪ {()}) ≠
      ofSamples id ((({()} : Finset Unit).val.map (fun _ => true)) +
        (({()} : Finset Unit).val.map (fun _ => true))) := by
  intro equal
  have := congrArg Evidence.pos equal
  norm_num [ledgerEvidence, ofSamples, sampleEvidence, Evidence.positive] at this

end Controls

end Mettapedia.PLN.WorldModel.ObservationSemantics
