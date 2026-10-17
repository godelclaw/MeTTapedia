import Mettapedia.CognitiveArchitecture.Attention.Spreading
import Mettapedia.PLN.WorldModel.WorldModelOverlap
import Mettapedia.PLN.InferenceControl.PremiseSelection.RankingStability

/-!
# Attention, stamped observations and world-model evidence

Attention is a relevance view, not an evidence-revision operation. The bridge
uses the canonical PLN evidence carrier and world-model extraction. Stamped
observations replace the same keyed contribution; they are not added twice.
An explicit replacement may change a contribution, while repeated delivery of
the identical observation is idempotent. Unrelated stamps commute.

Uniform evidence attenuation is monotone but is generally not idempotent. It
is therefore not an instance of the idempotent `ForgettingLayer` interface.
The strength view is invariant under positive finite uniform attenuation;
confidence-weighted routing need not be. Co-use is an observation about a
link's usefulness, not evidence that either memory's factual claim is true.

The coordinate commutation results hold for the explicitly supplied, fixed
kernel. They do not authorize resuming a world-dependent producer under a new
world without rebuilding or validating that producer. Score-order robustness
is conditional on actual error bounds, not a floating-point certification.
-/

noncomputable section

namespace Mettapedia.PLN.Bridges.CognitiveArchitecture.AttentionEvidence

open scoped BigOperators ENNReal Classical
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric
open Mettapedia.CognitiveArchitecture.Attention
open Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport

/-- This state deliberately separates factual evidence from association evidence. -/
structure State (ι World : Type*) where
  attention : ThreeTimescale.Bank ι
  links : ι → ι → BinaryEvidence
  world : World

variable {ι World : Type*}

def spreadAttention [Fintype ι] (P : Kernel ι) (d : ℝ) (s : State ι World) : State ι World :=
  { s with attention := Spreading.spreadBank P d s.attention }

def reviseWorld [Add World] (s : State ι World) (delta : World) : State ι World :=
  { s with world := s.world + delta }

def replaceLinks (s : State ι World) (links : ι → ι → BinaryEvidence) : State ι World :=
  { s with links := links }

theorem spreading_preserves_evidence [Fintype ι] (P : Kernel ι) (d : ℝ) (s : State ι World) :
    (spreadAttention P d s).world = s.world ∧
      (spreadAttention P d s).links = s.links := ⟨rfl, rfl⟩

theorem link_learning_preserves_world (s : State ι World)
    (links : ι → ι → BinaryEvidence) : (replaceLinks s links).world = s.world := rfl

theorem revision_preserves_attention [Add World] (s : State ι World) (delta : World) :
    (reviseWorld s delta).attention = s.attention ∧
      (reviseWorld s delta).links = s.links := ⟨rfl, rfl⟩

theorem spreading_revision_commute [Fintype ι] [Add World] (P : Kernel ι) (d : ℝ)
    (s : State ι World) (delta : World) :
    spreadAttention P d (reviseWorld s delta) = reviseWorld (spreadAttention P d s) delta := rfl

/-- Current-world extraction inherits the upstream additive WM law. It never
reads the attention balance as factual support. -/
theorem extract_after_revision {Query Ev : Type*} [EvidenceType World]
    [AddCommMonoid Ev] [AdditiveWorldModel World Query Ev]
    (s : State ι World) (delta : World) (q : Query) :
    AdditiveWorldModel.extract (State := World) (Query := Query) (Ev := Ev)
        (reviseWorld s delta).world q =
      AdditiveWorldModel.extract (State := World) (Query := Query) (Ev := Ev) s.world q +
      AdditiveWorldModel.extract (State := World) (Query := Query) (Ev := Ev) delta q :=
  AdditiveWorldModel.extract_add _ _ _

section Stamps

variable {Stamp : Type*}

/-- The event identity owns a contribution. A repeated ID is not a new sample. -/
abbrev Observations (Stamp ι : Type*) := Stamp → Option (ι → ι → BinaryEvidence)

def record (log : Observations Stamp ι) (stamp : Stamp) (e : ι → ι → BinaryEvidence) :
    Observations Stamp ι := Function.update log stamp (some e)

theorem record_idempotent (log : Observations Stamp ι) (stamp : Stamp)
    (e : ι → ι → BinaryEvidence) : record (record log stamp e) stamp e = record log stamp e := by
  simp [record]

theorem records_commute (log : Observations Stamp ι) (a b : Stamp) (hab : a ≠ b)
    (ea eb : ι → ι → BinaryEvidence) :
    record (record log a ea) b eb = record (record log b eb) a ea := by
  exact Function.update_comm hab (some ea) (some eb) log

def contribution (log : Observations Stamp ι) (stamp : Stamp) (i j : ι) : BinaryEvidence :=
  match log stamp with | none => 0 | some e => e i j

def aggregate [Fintype Stamp] (log : Observations Stamp ι) (i j : ι) : BinaryEvidence :=
  ∑ stamp, contribution log stamp i j

theorem replay_does_not_add_evidence [Fintype Stamp]
    (log : Observations Stamp ι) (stamp : Stamp) (e : ι → ι → BinaryEvidence) (i j : ι) :
    aggregate (record (record log stamp e) stamp e) i j = aggregate (record log stamp e) i j := by
  rw [record_idempotent]

def deleteObservations (log : Observations Stamp ι) (deleted : Set Stamp) :
    Observations Stamp ι := fun stamp => if stamp ∈ deleted then none else log stamp

theorem deletion_idempotent (log : Observations Stamp ι) (deleted : Set Stamp) :
    deleteObservations (deleteObservations log deleted) deleted = deleteObservations log deleted := by
  funext stamp
  by_cases h : stamp ∈ deleted <;> simp [deleteObservations, h]

theorem deletion_preserves_outside (log : Observations Stamp ι) (deleted : Set Stamp)
    (stamp : Stamp) (h : stamp ∉ deleted) : deleteObservations log deleted stamp = log stamp := by
  simp [deleteObservations, h]

/-- Delete all stamped support of an edge and its aggregate vanishes. Recompute
the view from retained observations instead of leaving a dangling count. -/
theorem deletion_removes_supported_edge [Fintype Stamp]
    (log : Observations Stamp ι) (deleted : Set Stamp) (i j : ι)
    (hsupport : ∀ stamp, stamp ∉ deleted → contribution log stamp i j = 0) :
    aggregate (deleteObservations log deleted) i j = 0 := by
  apply Finset.sum_eq_zero
  intro stamp _
  by_cases h : stamp ∈ deleted
  · simp [contribution, deleteObservations, h]
  · simpa [contribution, deleteObservations, h] using hsupport stamp h

end Stamps

def attenuate (a : ℝ≥0∞) (e : BinaryEvidence) : BinaryEvidence := ⟨a * e.pos, a * e.neg⟩

theorem attenuation_total (a : ℝ≥0∞) (e : BinaryEvidence) :
    (attenuate a e).total = a * e.total := by
  simp [attenuate, BinaryEvidence.total, mul_add]

theorem attenuation_le (a : ℝ≥0∞) (ha : a ≤ 1) (e : BinaryEvidence) : attenuate a e ≤ e := by
  constructor
  · simpa [attenuate] using mul_le_mul' ha (le_refl e.pos)
  · simpa [attenuate] using mul_le_mul' ha (le_refl e.neg)

theorem attenuation_total_le (a : ℝ≥0∞) (ha : a ≤ 1) (e : BinaryEvidence) :
    (attenuate a e).total ≤ e.total := by
  exact add_le_add (attenuation_le a ha e).1 (attenuation_le a ha e).2

theorem attenuation_confidence_le (a k : ℝ≥0∞) (ha : a ≤ 1)
    (hk0 : k ≠ 0) (hktop : k ≠ ⊤) (e : BinaryEvidence) (hetop : e.total ≠ ⊤) :
    BinaryEvidence.toConfidence k (attenuate a e) ≤ BinaryEvidence.toConfidence k e :=
  BinaryEvidence.confidence_monotone_in_total k _ e hk0 hktop hetop (attenuation_total_le a ha e)

theorem attenuation_strength (a : ℝ≥0∞) (ha0 : a ≠ 0) (hatop : a ≠ ⊤)
    (e : BinaryEvidence) : BinaryEvidence.toStrength (attenuate a e) = BinaryEvidence.toStrength e := by
  by_cases ht : e.total = 0
  · simp [BinaryEvidence.toStrength, attenuation_total, ht]
  · have hscaled : (attenuate a e).total ≠ 0 := by
      rw [attenuation_total]
      exact mul_ne_zero ha0 ht
    rw [BinaryEvidence.toStrength, if_neg hscaled, BinaryEvidence.toStrength, if_neg ht,
      attenuation_total]
    change a * e.pos / (a * e.total) = e.pos / e.total
    exact ENNReal.mul_div_mul_left _ _ ha0 hatop

/-- Evidence decay is not deletion's idempotent operation. -/
theorem attenuation_not_idempotent :
    attenuate (1 / 2) (attenuate (1 / 2) (⟨1, 0⟩ : BinaryEvidence)) ≠
      attenuate (1 / 2) (⟨1, 0⟩ : BinaryEvidence) := by
  intro h
  have hp := congrArg BinaryEvidence.pos h
  have hr := congrArg (fun x : ℝ≥0∞ => x.toReal) hp
  norm_num [attenuate, ENNReal.toReal_mul, ENNReal.toReal_div] at hr

/-- Finite-count strength times confidence at prior size one. -/
def supportedScore (positive negative : ℝ) : ℝ := positive / (positive + negative + 1)

/-- Uniform attenuation of all observations changes confidence-weighted shares
when edges have different evidence totals. Strength invariance does not imply this. -/
theorem confidence_weighted_share_changes :
    supportedScore 1 0 / (supportedScore 1 0 + supportedScore 9 1) = (11 / 29 : ℝ) ∧
    supportedScore (1 / 2) 0 /
      (supportedScore (1 / 2) 0 + supportedScore (9 / 2) (1 / 2)) = (4 / 13 : ℝ) ∧
    (11 / 29 : ℝ) ≠ 4 / 13 := by
  norm_num [supportedScore]

/-- Reuse upstream's ranking-margin result for any mixture of relevance and
attention scores. The approximation error must be established separately. -/
theorem ranking_stable {Item : Type*} (score error : Item → ℝ)
    (x y : Item) (epsilon : ℝ) (hgap : score y - score x > 2 * epsilon)
    (hx : |error x| ≤ epsilon) (hy : |error y| ≤ epsilon) :
    score x + error x < score y + error y :=
  Mettapedia.PLN.InferenceControl.PremiseSelection.Optimality.pairwise_lt_stable_of_margin
    score error x y epsilon hgap hx hy

/-- The complement route is a genuine part of PLN deduction, not path attention. -/
theorem direct_product_not_full_deduction :
    Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.simpleDeductionStrengthFormula
      (1 / 2) (1 / 2) (1 / 2) 0 0 = 1 := by
  norm_num [Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.simpleDeductionStrengthFormula,
    Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.conditionalProbabilityConsistency,
    Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.smallestIntersectionProbability,
    Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.largestIntersectionProbability]


end Mettapedia.PLN.Bridges.CognitiveArchitecture.AttentionEvidence
