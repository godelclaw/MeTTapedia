import Mathlib.Computability.Halting
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.NormNum

/-!
# Finite semantic image does not give an effective generating-base cutoff

An attempted shortcut to the source's finite-image proposal enumerates objects
of unbounded size and deduplicates profiles. This generic audit uses a two-element
observation carrier and a primitive recursive bounded evaluator. Every such
image has a finite complete prefix, but there is no total computable procedure
returning a complete-prefix cutoff from the program.

This does not prove that any fixed graph class or the Four-Color base problem
is undecidable. A finite, fully specified generator algebra with proved
coverage and computable semantic operations has additional structure and is
not refuted. No graph-realization or physical-alphabet hypothesis is supplied
by this module. The proof reuses mathlib's halting theorem.

This exact-image obstruction does not obstruct a sound finite overapproximation.
The spherical base-reflection consumer already permits such overapproximations:
coverage of actual traces and exclusion of their necessary bad condition suffice.
Computing the exact realizable image is not an extra prerequisite for that base.
Nor does the obstruction apply to exhausting a proved complete finite encoding
of graphs below an already supplied explicit size bound.
-/

namespace Mettapedia.GraphTheory.FourColor.FiniteImageBaseAudit

open Nat.Partrec Nat.Partrec.Code

/-- Whether the bounded evaluator has found an output on input zero.
The bound is the evaluator's parameter, not elapsed running time. -/
def observed (c : Code) (k : Nat) : Bool := (evaln k c 0).isSome

/-- All observations made up to and including the proposed cutoff. -/
def seen (c : Code) (k : Nat) : Finset Bool :=
  (Finset.range (k + 1)).image (observed c)

/-- No later object produces an observation absent from this prefix. -/
def CompleteAt (c : Code) (k : Nat) : Prop :=
  ∀ n, observed c n ∈ seen c k

theorem observed_iff (c : Code) (k : Nat) :
    observed c k = true ↔ ∃ v, v ∈ evaln k c 0 := by
  cases h : evaln k c 0 <;> simp [observed, h]

@[simp] theorem observed_zero (c : Code) : observed c 0 = false := by
  simp [observed, evaln]

theorem observed_mono (c : Code) {i j : Nat} (hij : i ≤ j)
    (hi : observed c i = true) : observed c j = true := by
  obtain ⟨v, hv⟩ := (observed_iff c i).1 hi
  exact (observed_iff c j).2 ⟨v, evaln_mono hij hv⟩

theorem eventually_observed_iff (c : Code) :
    (∃ k, observed c k = true) ↔ (eval c 0).Dom := by
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨v, hv⟩ := (observed_iff c k).1 hk
    exact ⟨v, evaln_sound hv⟩
  · rintro ⟨v, hv⟩
    obtain ⟨k, hk⟩ := evaln_complete.1 hv
    exact ⟨k, (observed_iff c k).2 ⟨v, hk⟩⟩

theorem primrec_observed : Primrec fun p : Code × Nat => observed p.1 p.2 :=
  Primrec.option_isSome.comp (primrec_evaln.comp
    ((Primrec.snd.pair Primrec.fst).pair (Primrec.const 0)))

theorem seen_card_le_two (c : Code) (k : Nat) : (seen c k).card ≤ 2 := by
  simpa using Finset.card_le_univ (seen c k)

theorem mem_seen_iff (c : Code) (k : Nat) (b : Bool) :
    b ∈ seen c k ↔ ∃ m, m ≤ k ∧ observed c m = b := by
  simp [seen, Nat.lt_succ_iff]

theorem seen_eq_singleton_of_false (c : Code) (k : Nat)
    (hk : observed c k = false) : seen c k = {false} := by
  ext b
  cases b
  · simp only [Finset.mem_singleton, iff_true]
    exact (mem_seen_iff c k false).2 ⟨0, Nat.zero_le _, observed_zero c⟩
  · simp only [Finset.mem_singleton]
    constructor
    · intro hb
      obtain ⟨m, hm, he⟩ := (mem_seen_iff c k true).1 hb
      exact (Bool.false_ne_true (hk.symm.trans (observed_mono c hm he))).elim
    · intro he
      cases he

theorem completeAt_iff (c : Code) (k : Nat) :
    CompleteAt c k ↔ ((eval c 0).Dom → observed c k = true) := by
  constructor
  · intro h hc
    obtain ⟨n, hn⟩ := (eventually_observed_iff c).2 hc
    obtain ⟨m, hm, he⟩ := (mem_seen_iff c k (observed c n)).1 (h n)
    exact observed_mono c hm (he.trans hn)
  · intro h n
    apply (mem_seen_iff c k _).2
    cases hn : observed c n
    · exact ⟨0, Nat.zero_le _, by simp⟩
    · exact ⟨k, le_rfl, h ((eventually_observed_iff c).1 ⟨n, hn⟩)⟩

/-- There is always a finite complete prefix. This is an existence theorem,
not a computable method for selecting that prefix. -/
theorem exists_complete_cutoff (c : Code) : ∃ k, CompleteAt c k := by
  classical
  by_cases hc : (eval c 0).Dom
  · obtain ⟨k, hk⟩ := (eventually_observed_iff c).2 hc
    exact ⟨k, (completeAt_iff c k).2 (fun _ => hk)⟩
  · exact ⟨0, (completeAt_iff c 0).2 (fun h => (hc h).elim)⟩

/-- Even a program-dependent cutoff cannot be selected by a total algorithm.
Such an algorithm, followed by bounded evaluation, would decide halting. -/
theorem no_computable_complete_cutoff :
    ¬ ∃ bound : Code → Nat, Computable bound ∧ ∀ c, CompleteAt c (bound c) := by
  rintro ⟨bound, hb, hcomplete⟩
  have ho : Computable fun c => observed c (bound c) :=
    primrec_observed.to_comp.comp (Computable.id.pair hb)
  have hp : ComputablePred fun c => observed c (bound c) = true :=
    ⟨inferInstance, by simpa using ho⟩
  apply ComputablePred.halting_problem 0
  exact hp.of_eq fun c => ⟨
    fun h => (eventually_observed_iff c).1 ⟨bound c, h⟩,
    (completeAt_iff c (bound c)).1 (hcomplete c)⟩

/-- In particular, the two-element observation carrier gives no uniform
number of enumeration stages after which its image is complete. -/
theorem no_state_cardinality_cutoff : ¬ ∃ k, ∀ c, CompleteAt c k := by
  rintro ⟨k, hk⟩
  exact no_computable_complete_cutoff ⟨fun _ => k, Computable.const k, hk⟩

/-- Kernel-checked plateau control: an unchanged observed image later grows. -/
theorem plateau_control :
    seen (Code.const 8) 1 = seen (Code.const 8) 7 ∧
      observed (Code.const 8) 8 = true ∧ ¬ CompleteAt (Code.const 8) 1 := by
  have h8 : observed (Code.const 8) 8 = true := by
    norm_num [observed, Code.const, evaln]
  have h1 : seen (Code.const 8) 1 = {false} := by
    apply seen_eq_singleton_of_false
    norm_num [observed, Code.const, evaln]
  have h7 : seen (Code.const 8) 7 = {false} := by
    apply seen_eq_singleton_of_false
    norm_num [observed, Code.const, evaln]
  refine ⟨h1.trans h7.symm, h8, ?_⟩
  intro h
  have he := h 8
  simp [h1, h8] at he

/-- The finite observation is not an autonomous state of the enumerator.
Equal observations do not determine the observation after one more step. -/
theorem plateau_has_no_observation_transition :
    ¬ ∃ step : Bool → Bool, ∀ k,
      observed (Code.const 8) (k + 1) = step (observed (Code.const 8) k) := by
  rintro ⟨step, h⟩
  have h0 := h 0
  have h7 := h 7
  norm_num [observed, Code.const, evaln] at h0 h7
  exact Bool.false_ne_true (h0.symm.trans h7)

end Mettapedia.GraphTheory.FourColor.FiniteImageBaseAudit
