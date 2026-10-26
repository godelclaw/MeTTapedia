import Mettapedia.GSLT.Logic.TaskRelativeMemory
import Mettapedia.Logic.EvidenceStateInsufficiency
import Mettapedia.PLN.WorldModel.EvidenceContracts
import Mettapedia.PLN.Evidence.CountRegimes
import Mathlib.Tactic

/-!
# Minimal memory for two evidence-revision contracts

For fresh observations, future strength readouts determine exactly the two
natural counts. In fact the positive and negative one-step probes suffice,
including at zero evidence. Counts forget observation order.

For identified observations with replay-safe insertion, the declared readout
is the complete evidence pair. Future delivery probes determine the entire
finite ledger, although its current aggregate counts can coincide with those
of another ledger. These contracts have different observations and updates;
count minimality does not authorize forgetting provenance under replay.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Evidence.RevisionMemory

open Mettapedia.GSLT.TaskRelativeMemory
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.Logic.EvidenceStateInsufficiency
open Mettapedia.PLN.WorldModel.EvidenceSpaces
open Mettapedia.PLN.WorldModel.EvidenceContracts

namespace Fresh

def observe (_ : Unit) (counts : Counts) : ℚ := counts.strength

def family := futureFamily Counts.revise observe

theorem revised_strength (counts : Counts) (positive : Bool) :
    (counts.revise positive).strength =
      (if positive then (counts.pos : ℚ) + 1 else counts.pos) / ((counts.total : ℚ) + 1) := by
  cases positive <;>
    simp only [Counts.revise, Bool.false_eq_true, if_false, if_true, Counts.strength,
      Counts.total, Nat.cast_add, Nat.cast_one] <;> ring

/-- The separation of two one-step probes recovers the evidence total. -/
theorem probe_gap (counts : Counts) :
    (counts.revise true).strength - (counts.revise false).strength =
      1 / ((counts.total : ℚ) + 1) := by
  rw [revised_strength, revised_strength]
  simp only [Bool.false_eq_true, if_false, if_true]
  ring

theorem probes_injective : Function.Injective
    (fun counts : Counts => ((counts.revise true).strength, (counts.revise false).strength)) := by
  intro first second same
  have positive := congrArg Prod.fst same
  have negative := congrArg Prod.snd same
  dsimp only at positive negative
  have gap : 1 / ((first.total : ℚ) + 1) = 1 / ((second.total : ℚ) + 1) := by
    rw [← probe_gap, ← probe_gap, positive, negative]
  have totals : first.total = second.total := by
    have denominator : (first.total : ℚ) + 1 = (second.total : ℚ) + 1 := by
      simpa only [one_div, inv_inj] using gap
    exact_mod_cast (add_right_cancel denominator : (first.total : ℚ) = second.total)
  have totalNonzero : (first.total : ℚ) + 1 ≠ 0 := by positivity
  rw [revised_strength, revised_strength, ← totals] at negative
  simp only [Bool.false_eq_true, if_false] at negative
  have positives : first.pos = second.pos := by
    exact_mod_cast (div_left_inj' totalNonzero).mp negative
  have negatives : first.neg = second.neg := by
    dsimp [Counts.total] at totals
    omega
  cases first
  cases second
  simp_all

/-- All continuations distinguish exactly the count pairs. -/
theorem profile_eq_iff_counts (first second : Counts) :
    profile Counts.revise observe first = profile Counts.revise observe second ↔ first = second := by
  constructor
  · intro same
    apply probes_injective
    exact Prod.ext (congrFun (congrFun same [true]) ()) (congrFun (congrFun same [false]) ())
  · rintro rfl
    rfl

/-- Every sufficient fresh-revision memory retains both counts, up to encoding. -/
theorem sufficient_memory_injective {Memory : Type*} (memory : Counts → Memory)
    (sufficient : ConstantOnFibers memory (profile Counts.revise observe)) :
    Function.Injective memory :=
  fun first second same => (profile_eq_iff_counts first second).mp (sufficient first second same)

/-- Counts themselves present the minimal fresh-revision quotient. -/
noncomputable def quotientEquivCounts : MemoryQuotient Counts.revise observe ≃ Counts :=
  (Equiv.ofBijective (classify Counts.revise observe)
    ⟨fun _ _ same => (profile_eq_iff_counts _ _).mp ((classify_eq_iff _ _ _ _).mp same),
      Quotient.mk_surjective⟩).symm

def historyCounts (history : List Bool) : Counts := history.foldl Counts.revise ⟨0, 0⟩

theorem historyCounts_coordinates (history : List Bool) (initial : Counts) :
    history.foldl Counts.revise initial =
      ⟨initial.pos + history.count true, initial.neg + history.count false⟩ := by
  induction history generalizing initial with
  | nil => simp
  | cons observation history ih =>
    cases observation <;>
      simp only [List.foldl_cons, Counts.revise, Bool.false_eq_true, if_true, if_false, ih,
        List.count_cons_self, List.count_cons_of_ne Bool.false_ne_true,
        List.count_cons_of_ne (by decide : true ≠ false)] <;>
      congr 1 <;> omega

theorem histories_equivalent_iff (first second : List Bool) :
    profile Counts.revise observe (historyCounts first) =
        profile Counts.revise observe (historyCounts second) ↔
      first.count true = second.count true ∧ first.count false = second.count false := by
  rw [profile_eq_iff_counts]
  simp [historyCounts, historyCounts_coordinates, Counts.mk.injEq]

theorem historyCounts_surjective : Function.Surjective historyCounts := by
  intro counts
  refine ⟨List.replicate counts.pos true ++ List.replicate counts.neg false, ?_⟩
  cases counts
  simp only [historyCounts, historyCounts_coordinates, List.count_append, List.count_replicate,
    beq_self_eq_true, (show (false == true) = false from rfl),
    (show (true == false) = false from rfl), Bool.false_eq_true, if_true, if_false, zero_add, add_zero]

/-- Interpret the historical rational fixture in the shared sample-count carrier. -/
def sampleCounts (counts : Counts) : Evidence ℕ := ⟨counts.pos, counts.neg⟩

def countsEquiv : Counts ≃ Evidence ℕ where
  toFun := sampleCounts
  invFun counts := ⟨counts.pos, counts.neg⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sampleCounts_total (counts : Counts) : (sampleCounts counts).total = counts.total := rfl

/-- The rational fixture agrees with the established binary-evidence strength. -/
theorem binary_strength (counts : Counts) :
    (BinaryEvidence.toStrength (CountRegimes.sampleEmbedding (sampleCounts counts))).toReal =
      (counts.strength : ℝ) := by
  rw [BinaryEvidence.toStrength, CountRegimes.sampleEmbedding_total, sampleCounts_total]
  by_cases empty : counts.total = 0
  · have posZero : counts.pos = 0 := by dsimp [Counts.total] at empty; omega
    simp [empty, Counts.strength, posZero]
  · have nonzero : (counts.total : ENNReal) ≠ 0 := by exact_mod_cast empty
    simp only [nonzero, if_false, CountRegimes.sampleEmbedding_pos,
      ENNReal.toReal_div, ENNReal.toReal_natCast, sampleCounts, Counts.strength]
    push_cast
    rfl

theorem sampleCounts_revise (counts : Counts) (positive : Bool) :
    sampleCounts (counts.revise positive) =
      sampleCounts counts + sampleEvidence id positive := by
  cases positive <;> rfl

theorem strength_only_refused :
    ¬ ConstantOnFibers Counts.strength (profile Counts.revise observe) := by
  intro sufficient
  have same := sufficient light heavy (revision_separates_equal_strengths.1)
  exact revision_separates_equal_strengths.2 (congrFun (congrFun same [true]) ())

theorem reordered_history : historyCounts [true, false] = historyCounts [false, true] := by decide

theorem zero_probes :
    ((⟨0, 0⟩ : Counts).revise true).strength = 1 ∧
      ((⟨0, 0⟩ : Counts).revise false).strength = 0 := by
  norm_num [revised_strength, Counts.total]

end Fresh

namespace Identified

variable {Id W : Type*} [DecidableEq Id]

def deliver (ledger : Finset Id) (identity : Id) : Finset Id := insert identity ledger

def observe (world : Id → W) (query : W → Bool) (_ : Unit) (ledger : Finset Id) : Evidence ℕ :=
  ledgerEvidence world query ledger

/-- Current counts and all one-delivery count probes determine the ledger. -/
theorem probes_separate (world : Id → W) (query : W → Bool) (first second : Finset Id)
    (current : ledgerEvidence world query first = ledgerEvidence world query second)
    (probes : ∀ identity,
      ledgerEvidence world query (deliver first identity) =
        ledgerEvidence world query (deliver second identity)) : first = second := by
  have cards : first.card = second.card := by
    simpa only [ledgerEvidence_total] using congrArg Evidence.total current
  ext identity
  have inserted : (insert identity first).card = (insert identity second).card := by
    simpa only [ledgerEvidence_total, deliver] using congrArg Evidence.total (probes identity)
  by_cases inFirst : identity ∈ first <;> by_cases inSecond : identity ∈ second
  · exact iff_of_true inFirst inSecond
  · simp [Finset.insert_eq_of_mem inFirst, Finset.card_insert_of_notMem inSecond, cards] at inserted
  · simp [Finset.card_insert_of_notMem inFirst, Finset.insert_eq_of_mem inSecond, cards] at inserted
  · exact iff_of_false inFirst inSecond

theorem profile_eq_iff_ledger (world : Id → W) (query : W → Bool) (first second : Finset Id) :
    profile deliver (observe world query) first = profile deliver (observe world query) second ↔
      first = second := by
  constructor
  · intro same
    exact probes_separate world query first second (congrFun (congrFun same []) ())
      (fun identity => congrFun (congrFun same [identity]) ())
  · rintro rfl
    rfl

theorem sufficient_memory_injective (world : Id → W) (query : W → Bool)
    {Memory : Type*} (memory : Finset Id → Memory)
    (sufficient : ConstantOnFibers memory (profile deliver (observe world query))) :
    Function.Injective memory :=
  fun first second same => (profile_eq_iff_ledger world query first second).mp
    (sufficient first second same)

noncomputable def quotientEquivLedgers (world : Id → W) (query : W → Bool) :
    MemoryQuotient deliver (observe world query) ≃ Finset Id :=
  (Equiv.ofBijective (classify deliver (observe world query))
    ⟨fun _ _ same => (profile_eq_iff_ledger world query _ _).mp
      ((classify_eq_iff _ _ _ _).mp same), Quotient.mk_surjective⟩).symm

theorem deliveries_compute_union (history : List Id) (initial : Finset Id) :
    history.foldl deliver initial = initial ∪ history.toFinset := by
  induction history generalizing initial with
  | nil => simp
  | cons identity history ih =>
    simpa only [List.foldl_cons, deliver, List.toFinset_cons, Finset.insert_union,
      Finset.union_insert] using ih (insert identity initial)

theorem histories_equivalent_iff (world : Id → W) (query : W → Bool) (first second : List Id) :
    profile deliver (observe world query) (first.foldl deliver ∅) =
        profile deliver (observe world query) (second.foldl deliver ∅) ↔
      first.toFinset = second.toFinset := by
  rw [profile_eq_iff_ledger]
  simp only [deliveries_compute_union, Finset.empty_union]

theorem replay_idempotent (ledger : Finset Id) (identity : Id) :
    deliver (deliver ledger identity) identity = deliver ledger identity := Finset.insert_idem _ _

namespace Controls

private def positive (_ : Bool) : Bool := true

/-- Even equal complete count readouts can react differently to replay. -/
theorem equal_counts_different_replay :
    ledgerEvidence id positive ({true} : Finset Bool) = ledgerEvidence id positive {false} ∧
      ledgerEvidence id positive (deliver {true} true) ≠
      ledgerEvidence id positive (deliver {false} true) := by
  simp only [deliver, ledgerEvidence, Finset.insert_eq_of_mem (Finset.mem_singleton_self true),
    Finset.sum_singleton, Finset.sum_insert (by decide : true ∉ ({false} : Finset Bool)),
    sampleEvidence, positive, if_true]
  constructor
  · trivial
  · intro equal
    have impossible := congrArg Evidence.pos equal
    norm_num [Evidence.positive] at impossible

theorem counts_only_refused : ¬ ConstantOnFibers
    (ledgerEvidence (id : Bool → Bool) positive) (profile deliver (observe id positive)) := by
  intro sufficient
  exact equal_counts_different_replay.2
    (congrFun (congrFun (sufficient _ _ equal_counts_different_replay.1) [true]) ())

end Controls
end Identified

end Mettapedia.PLN.Evidence.RevisionMemory
