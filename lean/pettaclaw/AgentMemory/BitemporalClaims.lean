import Mathlib.Data.Finset.Max
import Mathlib.Data.Prod.Lex
import Mathlib.Order.Interval.Finset.Nat

/-!
# Bitemporal claims with derived invalidation

A memory slot `k`, such as a person's home city, receives claims. A claim states
a value from an event-time `start`, optionally until a declared `stop`, and
cites the episode that supports it. Claims and retractions are appended to a
log. An entry's position in the log is its knowledge time. No entry is ever
changed or removed.

Invalidation is derived from the log instead of being stored. At knowledge time
`τ`, a live claim determines its slot at event time `t` when three conditions
hold. It has started by `t`. It has not reached its declared stop. No live claim
of the same slot with higher priority has started by `t`. Priority orders claims
by event start and breaks ties by knowledge time.

Zep (arXiv 2501.13956) invalidates fact edges by this rule, with an LLM deciding
which facts contradict each other. A newer contradicting fact closes an older
one at its own start. The paper states this half; the edge resolution of its
open-source Graphiti engine also implements the other half, in which an older
fact about later events closes a newly learned fact about earlier ones. Here a
slot plays the role of the contradiction test. The rule becomes a view over an
append-only log instead of an in-place update of stored timestamps.

Main results:
* `asOf_stable`: later operations never change the view at an earlier knowledge
  time, so the beliefs held at any past moment can be reconstructed exactly.
* `believes_functional`: a slot has at most one value at each pair of event and
  knowledge times.
* `holds_provenance`: every belief comes from a logged, unretracted claim, which
  carries its supporting episode.
* `assert_visible` and `holds_after_assert_iff` (liveness): a new claim takes
  effect immediately on exactly its derived interval.
* `loss_has_cause`: a claim stops determining its slot only through a logged
  retraction or a logged claim of higher priority.
* `retract_permanent` (liveness): a retracted claim never determines its slot
  again.
* `assert_cuts_at_most_one`, `retract_restores_at_most_one` and
  `assert_preserves_other_slots` (quantitative): each operation changes the
  derived interval of at most one other claim, always in its own slot.
* `invalidation_monotone`: without retractions, new knowledge only shortens
  derived intervals. `retraction_restores` shows that a retraction undoes an
  earlier cut.
* `covers_iff_of_distinct_starts`: when starts differ, the timeline does not
  depend on the order in which claims were learned.
* `inplace_stamps_lose_history`: when validity stamps are overwritten in place,
  as in Graphiti's edge invalidation, either reading of the stamps loses
  something. One loses the history before a change, the other a past view.
-/

set_option autoImplicit false

namespace AgentMemory.Bitemporal

/-! ## Event-time order -/

/-- Event time `t` lies before the end point `e`; `none` is an open end. -/
def Before (t : ℕ) : Option ℕ → Prop
  | none => True
  | some e => t < e

instance (t : ℕ) (e : Option ℕ) : Decidable (Before t e) := by
  cases e <;> simp only [Before] <;> infer_instance

/-- Claim `j` has priority over claim `i`: it starts later in event time, or it
starts at the same time and was recorded later. -/
def Later (start : ℕ → ℕ) (i j : ℕ) : Prop :=
  start i < start j ∨ (start i = start j ∧ i < j)

instance (start : ℕ → ℕ) (i j : ℕ) : Decidable (Later start i j) := by
  unfold Later; infer_instance

section Order

variable {start : ℕ → ℕ} {i j : ℕ}

theorem later_irrefl : ¬ Later start i i := by
  unfold Later; omega

theorem later_asymm (h : Later start i j) : ¬ Later start j i := by
  unfold Later at *; omega

theorem later_total (h : i ≠ j) : Later start i j ∨ Later start j i := by
  unfold Later; omega

theorem start_le_of_later (h : Later start i j) : start i ≤ start j := by
  unfold Later at h; omega

end Order

/-! ## Derived intervals over a finite set of live claims -/

section Timeline

variable (S : Finset ℕ) (start : ℕ → ℕ) (stop : ℕ → Option ℕ)

/-- Live claim `i` determines its slot at event time `t`: it has started, has not
reached its declared stop, and no live claim of higher priority has started. -/
def Covers (i t : ℕ) : Prop :=
  i ∈ S ∧ start i ≤ t ∧ Before t (stop i) ∧ ∀ j ∈ S, Later start i j → t < start j

instance (i t : ℕ) : Decidable (Covers S start stop i t) := by
  unfold Covers; infer_instance

/-- `i` is the live claim of highest priority among those started by `t`. -/
def Latest (i t : ℕ) : Prop :=
  i ∈ S ∧ start i ≤ t ∧ ∀ j ∈ S, start j ≤ t → j = i ∨ Later start j i

/-- Adding claim `n` shortens the derived interval of claim `i`. -/
def Cut (n i : ℕ) : Prop :=
  ∃ t, Covers S start stop i t ∧ ¬ Covers (insert n S) start stop i t

variable {S start stop}

/-- At most one claim determines the slot at any event time. -/
theorem covers_unique {i j t : ℕ} (hi : Covers S start stop i t)
    (hj : Covers S start stop j t) : i = j := by
  by_contra hne
  rcases later_total (start := start) hne with h | h
  · exact absurd (hi.2.2.2 j hj.1 h) (not_lt.mpr hj.2.1)
  · exact absurd (hj.2.2.2 i hi.1 h) (not_lt.mpr hi.2.1)

/-- The derived interval agrees with the rule "the latest claim that has started
wins, unless it has reached its declared stop". -/
theorem covers_iff_latest {i t : ℕ} :
    Covers S start stop i t ↔ Latest S start i t ∧ Before t (stop i) := by
  constructor
  · rintro ⟨hS, ht, hb, hcut⟩
    refine ⟨⟨hS, ht, fun j hj hjt => ?_⟩, hb⟩
    by_cases hji : j = i
    · exact Or.inl hji
    · rcases later_total (start := start) hji with h | h
      · exact Or.inr h
      · exact absurd (hcut j hj h) (not_lt.mpr hjt)
  · rintro ⟨⟨hS, ht, hmax⟩, hb⟩
    refine ⟨hS, ht, hb, fun j hj hij => ?_⟩
    by_contra hle
    rcases hmax j hj (not_lt.mp hle) with rfl | h
    · exact later_irrefl hij
    · exact later_asymm hij h

theorem exists_latest {t : ℕ} (h : ∃ j ∈ S, start j ≤ t) : ∃ i, Latest S start i t := by
  obtain ⟨j, hjS, hjt⟩ := h
  have hne : (S.filter (fun j => start j ≤ t)).Nonempty :=
    ⟨j, Finset.mem_filter.mpr ⟨hjS, hjt⟩⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image _ (fun j => toLex (start j, j)) hne
  rw [Finset.mem_filter] at hi
  refine ⟨i, hi.1, hi.2, fun j hj hjt => ?_⟩
  have hle := hmax j (Finset.mem_filter.mpr ⟨hj, hjt⟩)
  rw [Prod.Lex.toLex_le_toLex] at hle
  simp only at hle
  unfold Later
  omega

/-- The view is decided at every event time: a unique claim covers `t`, or no
live claim has started, or the latest claim that has started has reached its
declared stop and the value is explicitly unknown. -/
theorem covers_or_unknown (t : ℕ) :
    (∃ i, Covers S start stop i t) ∨ (∀ j ∈ S, t < start j) ∨
      (∃ i, Latest S start i t ∧ ¬ Before t (stop i)) := by
  by_cases h : ∃ j ∈ S, start j ≤ t
  · obtain ⟨i, hi⟩ := exists_latest h
    by_cases hb : Before t (stop i)
    · exact Or.inl ⟨i, covers_iff_latest.mpr ⟨hi, hb⟩⟩
    · exact Or.inr (Or.inr ⟨i, hi, hb⟩)
  · push Not at h
    exact Or.inr (Or.inl h)

/-- More live claims can only shorten a derived interval. -/
theorem covers_mono {T : Finset ℕ} {i t : ℕ} (hST : S ⊆ T) (hi : i ∈ S)
    (h : Covers T start stop i t) : Covers S start stop i t :=
  ⟨hi, h.2.1, h.2.2.1, fun j hj hij => h.2.2.2 j (hST hj) hij⟩

theorem covers_congr {start' : ℕ → ℕ} {stop' : ℕ → Option ℕ}
    (hs : ∀ j ∈ S, start' j = start j) (hp : ∀ j ∈ S, stop' j = stop j) {i t : ℕ} :
    Covers S start' stop' i t ↔ Covers S start stop i t := by
  constructor
  · rintro ⟨hi, ht, hb, hcut⟩
    refine ⟨hi, by rwa [hs i hi] at ht, by rwa [hp i hi] at hb, fun j hj hl => ?_⟩
    have hl' : Later start' i j := by
      unfold Later at hl ⊢; rw [hs i hi, hs j hj]; exact hl
    have := hcut j hj hl'
    rwa [hs j hj] at this
  · rintro ⟨hi, ht, hb, hcut⟩
    refine ⟨hi, by rwa [hs i hi], by rwa [hp i hi], fun j hj hl => ?_⟩
    have hl' : Later start i j := by
      unfold Later at hl ⊢; rw [hs i hi, hs j hj] at hl; exact hl
    have := hcut j hj hl'
    rwa [hs j hj]

theorem covers_insert_iff {n i t : ℕ} (hin : i ≠ n) :
    Covers (insert n S) start stop i t ↔
      Covers S start stop i t ∧ (Later start i n → t < start n) := by
  simp only [Covers, Finset.mem_insert, hin, false_or, forall_eq_or_imp]
  tauto

theorem cut_iff {n i : ℕ} (hin : i ≠ n) :
    Cut S start stop n i ↔ Later start i n ∧ ∃ t, Covers S start stop i t ∧ start n ≤ t := by
  unfold Cut
  simp only [covers_insert_iff hin]
  constructor
  · rintro ⟨t, hc, hn⟩
    by_cases hl : Later start i n
    · by_cases ht : start n ≤ t
      · exact ⟨hl, t, hc, ht⟩
      · exact absurd ⟨hc, fun _ => not_le.mp ht⟩ hn
    · exact absurd ⟨hc, fun h => absurd h hl⟩ hn
  · rintro ⟨hl, t, hc, ht⟩
    exact ⟨t, hc, fun h => absurd (h.2 hl) (not_lt.mpr ht)⟩

/-- Adding a claim shortens the derived interval of at most one existing claim:
its immediate predecessor in priority order. -/
theorem cut_at_most_one {n i j : ℕ} (hn : n ∉ S) (hi : i ∈ S) (hj : j ∈ S)
    (ci : Cut S start stop n i) (cj : Cut S start stop n j) : i = j := by
  have hin : i ≠ n := fun h => hn (h ▸ hi)
  have hjn : j ≠ n := fun h => hn (h ▸ hj)
  obtain ⟨hli, t₁, hc₁, ht₁⟩ := (cut_iff hin).mp ci
  obtain ⟨hlj, t₂, hc₂, ht₂⟩ := (cut_iff hjn).mp cj
  by_contra hij
  rcases later_total (start := start) hij with h | h
  · have h₁ := hc₁.2.2.2 j hj h
    have h₂ := start_le_of_later hlj
    omega
  · have h₁ := hc₂.2.2.2 i hi h
    have h₂ := start_le_of_later hli
    omega

/-- The derived interval of the most recently learned claim. -/
theorem covers_insert_newest {n t : ℕ} (hn : ∀ j ∈ S, j < n) :
    Covers (insert n S) start stop n t ↔
      start n ≤ t ∧ Before t (stop n) ∧ ∀ j ∈ S, start n < start j → t < start j := by
  constructor
  · rintro ⟨-, ht, hb, hcut⟩
    exact ⟨ht, hb, fun j hj hlt => hcut j (Finset.mem_insert_of_mem hj) (Or.inl hlt)⟩
  · rintro ⟨ht, hb, hcut⟩
    refine ⟨Finset.mem_insert_self n S, ht, hb, fun j hj hl => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact absurd hl later_irrefl
    · rcases hl with hl | ⟨_, hl⟩
      · exact hcut j hj hl
      · exact absurd (hn j hj) (not_lt.mpr hl.le)

/-- With pairwise distinct starts, knowledge order plays no role: the timeline
is the same whatever order the claims were learned in. -/
theorem covers_iff_of_distinct_starts
    (hd : ∀ i ∈ S, ∀ j ∈ S, start i = start j → i = j) {i t : ℕ} :
    Covers S start stop i t ↔
      i ∈ S ∧ start i ≤ t ∧ Before t (stop i) ∧ ∀ j ∈ S, start i < start j → t < start j := by
  constructor
  · rintro ⟨hi, ht, hb, hcut⟩
    exact ⟨hi, ht, hb, fun j hj hlt => hcut j hj (Or.inl hlt)⟩
  · rintro ⟨hi, ht, hb, hcut⟩
    refine ⟨hi, ht, hb, fun j hj hl => ?_⟩
    rcases hl with hl | ⟨heq, hlt⟩
    · exact hcut j hj hl
    · exact absurd (hd i hi j hj heq) (Nat.ne_of_lt hlt)

end Timeline

/-! ## The append-only claim log -/

/-- A claim about slot `key`: `val` holds from event time `start` until `stop`
(open when `none`), supported by the episode `source`. -/
structure Claim (K V : Type) where
  key : K
  val : V
  start : ℕ
  stop : Option ℕ
  source : ℕ
  deriving DecidableEq, Repr

/-- A log entry. A retraction names the knowledge time of the claim it withdraws. -/
inductive Entry (K V : Type) where
  | assert (c : Claim K V)
  | retract (target : ℕ)
  deriving DecidableEq, Repr

/-- The append-only log. The position of an entry is its knowledge time. -/
abbrev Log (K V : Type) := List (Entry K V)

variable {K V : Type}

def Entry.claim? : Entry K V → Option (Claim K V)
  | .assert c => some c
  | .retract _ => none

def Entry.target? : Entry K V → Option ℕ
  | .assert _ => none
  | .retract i => some i

def claimAt (log : Log K V) (i : ℕ) : Option (Claim K V) := log[i]?.bind Entry.claim?

def keyAt (log : Log K V) (i : ℕ) : Option K := (claimAt log i).map Claim.key

def startAt (log : Log K V) (i : ℕ) : ℕ := ((claimAt log i).map Claim.start).getD 0

def stopAt (log : Log K V) (i : ℕ) : Option ℕ := (claimAt log i).bind Claim.stop

/-- Claim `i` was withdrawn by a retraction recorded after it and no later than `τ`. -/
def Retracted (log : Log K V) (τ i : ℕ) : Prop :=
  ∃ p ∈ Finset.Ioc i τ, log[p]?.bind Entry.target? = some i

instance (log : Log K V) (τ i : ℕ) : Decidable (Retracted log τ i) := by
  unfold Retracted; infer_instance

/-! ### Basic facts about positions -/

theorem claimAt_eq_some {log : Log K V} {i : ℕ} {c : Claim K V} :
    claimAt log i = some c ↔ log[i]? = some (.assert c) := by
  unfold claimAt
  cases h : log[i]? with
  | none => simp
  | some e => cases e <;> simp [Entry.claim?]

theorem claimAt_append_left {log ext : Log K V} {i : ℕ} (h : i < log.length) :
    claimAt (log ++ ext) i = claimAt log i := by
  simp [claimAt, List.getElem?_append_left h]

theorem claimAt_of_le_length {log : Log K V} {i : ℕ} (h : log.length ≤ i) :
    claimAt log i = none := by
  simp [claimAt, List.getElem?_eq_none h]

theorem retracted_mono {log : Log K V} {τ τ' i : ℕ} (hττ' : τ ≤ τ')
    (h : Retracted log τ i) : Retracted log τ' i := by
  obtain ⟨p, hp, hpt⟩ := h
  rw [Finset.mem_Ioc] at hp
  exact ⟨p, Finset.mem_Ioc.mpr ⟨hp.1, le_trans hp.2 hττ'⟩, hpt⟩

/-! ### Appending preserves recorded entries -/

/-- History is never lost: every operation appends, so each earlier log is a
prefix of every later one. -/
theorem history_never_lost (log ext : Log K V) : log <+: log ++ ext :=
  List.prefix_append log ext

/-- Recorded entries never change, because every operation appends. -/
theorem entry_stable (log ext : Log K V) {i : ℕ} (h : i < log.length) :
    (log ++ ext)[i]? = log[i]? :=
  List.getElem?_append_left h

theorem retracted_stable (log ext : Log K V) {τ i : ℕ} (hτ : τ < log.length) :
    Retracted (log ++ ext) τ i ↔ Retracted log τ i := by
  unfold Retracted
  constructor
  · rintro ⟨p, hp, h⟩
    have hpl : p < log.length := lt_of_le_of_lt (Finset.mem_Ioc.mp hp).2 hτ
    exact ⟨p, hp, by rwa [List.getElem?_append_left hpl] at h⟩
  · rintro ⟨p, hp, h⟩
    have hpl : p < log.length := lt_of_le_of_lt (Finset.mem_Ioc.mp hp).2 hτ
    exact ⟨p, hp, by rwa [List.getElem?_append_left hpl]⟩

theorem startAt_append_left {log ext : Log K V} {i : ℕ} (h : i < log.length) :
    startAt (log ++ ext) i = startAt log i := by
  simp [startAt, claimAt_append_left h]

theorem stopAt_append_left {log ext : Log K V} {i : ℕ} (h : i < log.length) :
    stopAt (log ++ ext) i = stopAt log i := by
  simp [stopAt, claimAt_append_left h]

section Log

variable [DecidableEq K]

/-- The claims of slot `k` that are known and not withdrawn at knowledge time `τ`. -/
def live (log : Log K V) (τ : ℕ) (k : K) : Finset ℕ :=
  (Finset.range (τ + 1)).filter (fun i => keyAt log i = some k ∧ ¬ Retracted log τ i)

/-- At knowledge time `τ`, claim `i` determines slot `k` at event time `t`. -/
def Holds (log : Log K V) (k : K) (t τ i : ℕ) : Prop :=
  Covers (live log τ k) (startAt log) (stopAt log) i t

instance (log : Log K V) (k : K) (t τ i : ℕ) : Decidable (Holds log k t τ i) := by
  unfold Holds; infer_instance

/-- At knowledge time `τ`, the agent believes that slot `k` had value `v` at event
time `t`. -/
def Believes (log : Log K V) (k : K) (t τ : ℕ) (v : V) : Prop :=
  ∃ i, Holds log k t τ i ∧ (claimAt log i).map Claim.val = some v

theorem mem_live {log : Log K V} {τ i : ℕ} {k : K} :
    i ∈ live log τ k ↔ i ≤ τ ∧ keyAt log i = some k ∧ ¬ Retracted log τ i := by
  simp [live, Nat.lt_succ_iff]

theorem lt_length_of_mem_live {log : Log K V} {τ i : ℕ} {k : K} (h : i ∈ live log τ k) :
    i < log.length := by
  by_contra hge
  have := (mem_live.mp h).2.1
  simp [keyAt, claimAt_of_le_length (not_lt.mp hge)] at this

/-! ### History and past views -/

theorem live_stable (log ext : Log K V) {τ : ℕ} (k : K) (hτ : τ < log.length) :
    live (log ++ ext) τ k = live log τ k := by
  unfold live
  apply Finset.filter_congr
  intro i hi
  have hil : i < log.length := lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hτ
  simp only [keyAt, claimAt_append_left hil, retracted_stable log ext hτ]

/-- Stability: no later operation changes the view at an earlier knowledge time.
The beliefs held at knowledge time `τ` can be reconstructed exactly. -/
theorem asOf_stable (log ext : Log K V) {τ : ℕ} (hτ : τ < log.length) (k : K) (t i : ℕ) :
    Holds (log ++ ext) k t τ i ↔ Holds log k t τ i := by
  unfold Holds
  rw [live_stable log ext k hτ]
  apply covers_congr
  · intro j hj
    simp only [startAt, claimAt_append_left (lt_length_of_mem_live hj)]
  · intro j hj
    simp only [stopAt, claimAt_append_left (lt_length_of_mem_live hj)]

theorem believes_stable (log ext : Log K V) {τ : ℕ} (hτ : τ < log.length) (k : K) (t : ℕ)
    (v : V) : Believes (log ++ ext) k t τ v ↔ Believes log k t τ v := by
  unfold Believes
  constructor
  · rintro ⟨i, hi, hv⟩
    have hil := lt_length_of_mem_live
      (by have := hi.1; rwa [live_stable log ext k hτ] at this)
    exact ⟨i, (asOf_stable log ext hτ k t i).mp hi, by rwa [claimAt_append_left hil] at hv⟩
  · rintro ⟨i, hi, hv⟩
    exact ⟨i, (asOf_stable log ext hτ k t i).mpr hi,
      by rwa [claimAt_append_left (lt_length_of_mem_live hi.1)]⟩

/-! ### Provenance and functionality -/

/-- Every belief is backed by a logged claim that is not withdrawn. The claim
carries its supporting episode. -/
theorem holds_provenance {log : Log K V} {k : K} {t τ i : ℕ} (h : Holds log k t τ i) :
    ∃ c, log[i]? = some (.assert c) ∧ c.key = k ∧ c.start ≤ t ∧ Before t c.stop ∧
      i ≤ τ ∧ ¬ Retracted log τ i := by
  obtain ⟨hi, ht, hb, -⟩ := h
  obtain ⟨hiτ, hkey, hret⟩ := mem_live.mp hi
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hkey
  refine ⟨c, claimAt_eq_some.mp hc, rfl, ?_, ?_, hiτ, hret⟩
  · simpa [startAt, hc] using ht
  · simpa [stopAt, hc] using hb

/-- A slot has at most one value at each event time and knowledge time. -/
theorem believes_functional {log : Log K V} {k : K} {t τ : ℕ} {v w : V}
    (hv : Believes log k t τ v) (hw : Believes log k t τ w) : v = w := by
  obtain ⟨i, hi, hiv⟩ := hv
  obtain ⟨j, hj, hjw⟩ := hw
  obtain rfl := covers_unique hi hj
  rw [hiv] at hjw
  exact Option.some_injective _ hjw

/-! ### Operations at the current knowledge time -/

theorem live_after_assert (log : Log K V) (c : Claim K V) (k : K) :
    live (log ++ [.assert c]) log.length k =
      if c.key = k then insert log.length (live log log.length k)
      else live log log.length k := by
  have hret : ∀ i, i < log.length →
      (Retracted (log ++ [.assert c]) log.length i ↔ Retracted log log.length i) := by
    intro i _
    unfold Retracted
    constructor
    · rintro ⟨p, hp, h⟩
      rcases lt_or_eq_of_le (Finset.mem_Ioc.mp hp).2 with hpl | rfl
      · exact ⟨p, hp, by rwa [List.getElem?_append_left hpl] at h⟩
      · simp [Entry.target?] at h
    · rintro ⟨p, hp, h⟩
      rcases lt_or_eq_of_le (Finset.mem_Ioc.mp hp).2 with hpl | rfl
      · exact ⟨p, hp, by rwa [List.getElem?_append_left hpl]⟩
      · simp at h
  ext i
  rcases lt_trichotomy i log.length with hi | rfl | hi
  · have hne : i ≠ log.length := Nat.ne_of_lt hi
    split_ifs <;>
      simp only [Finset.mem_insert, hne, false_or, mem_live, keyAt,
        claimAt_append_left hi, hret i hi]
  · have hnot : ¬ Retracted (log ++ [.assert c]) log.length log.length := by
      rintro ⟨p, hp, -⟩
      rw [Finset.mem_Ioc] at hp
      omega
    have hk : keyAt (log ++ [.assert c]) log.length = some c.key := by
      simp [keyAt, claimAt, Entry.claim?]
    have hn : log.length ∉ live log log.length k := fun h =>
      Nat.lt_irrefl _ (lt_length_of_mem_live h)
    split_ifs with hck
    · simp [mem_live, hk, hnot, hck]
    · simp only [mem_live, hk, hnot, hn, iff_false]
      simp [hck]
  · have h1 : i ∉ live (log ++ [.assert c]) log.length k := fun h => by
      have := lt_length_of_mem_live h
      simp at this
      omega
    have h2 : i ∉ live log log.length k := fun h =>
      absurd (lt_length_of_mem_live h) (by omega)
    split_ifs <;> simp [h1, h2, Nat.ne_of_gt hi]

theorem live_after_retract (log : Log K V) (r : ℕ) (k : K) :
    live (log ++ [.retract r]) log.length k = (live log log.length k).erase r := by
  ext i
  rcases lt_or_ge i log.length with hi | hi
  · have hret : Retracted (log ++ [.retract r]) log.length i ↔
        Retracted log log.length i ∨ i = r := by
      unfold Retracted
      constructor
      · rintro ⟨p, hp, h⟩
        rcases lt_or_eq_of_le (Finset.mem_Ioc.mp hp).2 with hpl | rfl
        · exact Or.inl ⟨p, hp, by rwa [List.getElem?_append_left hpl] at h⟩
        · simp [Entry.target?] at h
          exact Or.inr h.symm
      · rintro (⟨p, hp, h⟩ | rfl)
        · have hpl : p < log.length := by
            rcases lt_or_eq_of_le (Finset.mem_Ioc.mp hp).2 with hpl | rfl
            · exact hpl
            · simp at h
          exact ⟨p, hp, by rwa [List.getElem?_append_left hpl]⟩
        · exact ⟨log.length, Finset.mem_Ioc.mpr ⟨hi, le_rfl⟩, by simp [Entry.target?]⟩
    simp only [Finset.mem_erase, mem_live, keyAt, claimAt_append_left hi, hret]
    tauto
  · have h1 : i ∉ live (log ++ [.retract r]) log.length k := fun h => by
      have hlt := lt_length_of_mem_live h
      have hk := (mem_live.mp h).2.1
      rcases lt_or_eq_of_le hi with hgt | rfl
      · simp at hlt; omega
      · simp [keyAt, claimAt, Entry.claim?] at hk
    have h2 : i ∉ live log log.length k := fun h =>
      absurd (lt_length_of_mem_live h) (not_lt.mpr hi)
    simp [h1, h2]

/-- Read your writes (liveness): a new claim with a nonempty declared interval
determines its slot at its own start, immediately after it is recorded. -/
theorem assert_visible (log : Log K V) (c : Claim K V) (hb : Before c.start c.stop) :
    Holds (log ++ [.assert c]) c.key c.start log.length log.length := by
  unfold Holds
  rw [live_after_assert, if_pos rfl]
  refine (covers_insert_newest (fun j hj => lt_length_of_mem_live hj)).mpr ⟨?_, ?_, ?_⟩
  · simp [startAt, claimAt, Entry.claim?]
  · simpa [stopAt, claimAt, Entry.claim?] using hb
  · intro j _ h
    simpa [startAt, claimAt, Entry.claim?] using h

/-- The exact derived interval of a new claim. It runs from its start to the
earlier of its declared stop and the next known start in its slot. A late report
about the past is closed by facts already known about later events. -/
theorem holds_after_assert_iff (log : Log K V) (c : Claim K V) (t : ℕ) :
    Holds (log ++ [.assert c]) c.key t log.length log.length ↔
      c.start ≤ t ∧ Before t c.stop ∧
        ∀ j ∈ live log log.length c.key, c.start < startAt log j → t < startAt log j := by
  unfold Holds
  rw [live_after_assert, if_pos rfl,
    covers_insert_newest (fun j hj => lt_length_of_mem_live hj)]
  have hs : startAt (log ++ [.assert c]) log.length = c.start := by
    simp [startAt, claimAt, Entry.claim?]
  have hp : stopAt (log ++ [.assert c]) log.length = c.stop := by
    simp [stopAt, claimAt, Entry.claim?]
  rw [hs, hp]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun j hj hlt => ?_⟩
    have := h3 j hj (by rwa [startAt_append_left (lt_length_of_mem_live hj)])
    rwa [startAt_append_left (lt_length_of_mem_live hj)] at this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun j hj hlt => ?_⟩
    rw [startAt_append_left (lt_length_of_mem_live hj)] at hlt ⊢
    exact h3 j hj hlt

/-- A claim stops determining its slot only for a recorded reason: its own
retraction, or a live claim of higher priority in the same slot that has started. -/
theorem loss_has_cause {log : Log K V} {c : Claim K V} {n τ t : ℕ}
    (hn : log[n]? = some (.assert c)) (hτ : n ≤ τ) (ht : c.start ≤ t)
    (hb : Before t c.stop) (hlost : ¬ Holds log c.key t τ n) :
    Retracted log τ n ∨
      ∃ j ∈ live log τ c.key, Later (startAt log) n j ∧ startAt log j ≤ t := by
  have hc : claimAt log n = some c := claimAt_eq_some.mpr hn
  by_contra hno
  push Not at hno
  obtain ⟨hret, hcut⟩ := hno
  apply hlost
  refine ⟨mem_live.mpr ⟨hτ, by simp [keyAt, hc], hret⟩, by simp [startAt, hc, ht],
    by simpa [stopAt, hc] using hb, fun j hj hl => hcut j hj hl⟩

/-- A retracted claim never determines its slot again. -/
theorem retract_permanent {log : Log K V} {p r τ : ℕ} (hp : log[p]? = some (.retract r))
    (hrp : r < p) (hpτ : p ≤ τ) (k : K) (t : ℕ) : ¬ Holds log k t τ r := by
  rintro ⟨hr, -⟩
  exact (mem_live.mp hr).2.2 ⟨p, Finset.mem_Ioc.mpr ⟨hrp, hpτ⟩, by simp [hp, Entry.target?]⟩

/-- Liveness of retraction: once recorded, a retraction holds at every later
knowledge time, whatever is appended afterwards. -/
theorem retracted_never_holds_again (log ext : Log K V) {r τ : ℕ} (hr : r < log.length)
    (hτ : log.length ≤ τ) (k : K) (t : ℕ) : ¬ Holds (log ++ .retract r :: ext) k t τ r :=
  retract_permanent (p := log.length) (by simp) hr hτ k t

/-! ### Bounded work per operation -/

/-- An assertion never changes the view of another slot. -/
theorem assert_preserves_other_slots (log : Log K V) (c : Claim K V) {k : K}
    (hk : c.key ≠ k) (t i : ℕ) :
    Holds (log ++ [.assert c]) k t log.length i ↔ Holds log k t log.length i := by
  unfold Holds
  rw [live_after_assert, if_neg hk]
  exact covers_congr (fun j hj => startAt_append_left (lt_length_of_mem_live hj))
    (fun j hj => stopAt_append_left (lt_length_of_mem_live hj))

/-- An assertion shortens the derived interval of at most one existing claim. A
cache of materialized interval ends therefore needs at most two updates per
assertion: the new claim and its predecessor. -/
theorem assert_cuts_at_most_one (log : Log K V) (c : Claim K V) {i j t₁ t₂ : ℕ}
    (hi : Holds log c.key t₁ log.length i)
    (hi' : ¬ Holds (log ++ [.assert c]) c.key t₁ log.length i)
    (hj : Holds log c.key t₂ log.length j)
    (hj' : ¬ Holds (log ++ [.assert c]) c.key t₂ log.length j) : i = j := by
  unfold Holds at hi hi' hj hj'
  rw [live_after_assert, if_pos rfl] at hi' hj'
  set S := live log log.length c.key
  have hs : ∀ x ∈ S, startAt (log ++ [.assert c]) x = startAt log x :=
    fun x hx => startAt_append_left (lt_length_of_mem_live hx)
  have hp : ∀ x ∈ S, stopAt (log ++ [.assert c]) x = stopAt log x :=
    fun x hx => stopAt_append_left (lt_length_of_mem_live hx)
  have hn : log.length ∉ S := fun h => Nat.lt_irrefl _ (lt_length_of_mem_live h)
  exact cut_at_most_one hn hi.1 hj.1 ⟨t₁, (covers_congr hs hp).mpr hi, hi'⟩
    ⟨t₂, (covers_congr hs hp).mpr hj, hj'⟩

/-- A retraction lengthens the derived interval of at most one other claim. -/
theorem retract_restores_at_most_one (log : Log K V) (r : ℕ) (k : K) {i j t₁ t₂ : ℕ}
    (hi : Holds (log ++ [.retract r]) k t₁ log.length i) (hi' : ¬ Holds log k t₁ log.length i)
    (hj : Holds (log ++ [.retract r]) k t₂ log.length j) (hj' : ¬ Holds log k t₂ log.length j) :
    i = j := by
  unfold Holds at hi hi' hj hj'
  rw [live_after_retract] at hi hj
  set S := live log log.length k
  have hs : ∀ x ∈ S, startAt (log ++ [.retract r]) x = startAt log x :=
    fun x hx => startAt_append_left (lt_length_of_mem_live hx)
  have hp : ∀ x ∈ S, stopAt (log ++ [.retract r]) x = stopAt log x :=
    fun x hx => stopAt_append_left (lt_length_of_mem_live hx)
  have hs' : ∀ x ∈ S.erase r, startAt (log ++ [.retract r]) x = startAt log x :=
    fun x hx => hs x (Finset.mem_of_mem_erase hx)
  have hp' : ∀ x ∈ S.erase r, stopAt (log ++ [.retract r]) x = stopAt log x :=
    fun x hx => hp x (Finset.mem_of_mem_erase hx)
  rw [covers_congr hs' hp'] at hi hj
  by_cases hr : r ∈ S
  · rw [← Finset.insert_erase hr] at hi' hj'
    exact cut_at_most_one (Finset.notMem_erase r S) hi.1 hj.1 ⟨t₁, hi, hi'⟩ ⟨t₂, hj, hj'⟩
  · rw [Finset.erase_eq_of_notMem hr] at hi
    exact absurd hi hi'

/-- Without retractions, new knowledge only shortens derived intervals: once a
claim is cut at some event time, it stays cut. -/
theorem invalidation_monotone {log : Log K V} {k : K} {t τ τ' i : ℕ} (hττ' : τ ≤ τ')
    (hnone : ∀ p, τ < p → p ≤ τ' → log[p]?.bind Entry.target? = none)
    (hiτ : i ≤ τ) (h : Holds log k t τ' i) : Holds log k t τ i := by
  have hsub : live log τ k ⊆ live log τ' k := by
    intro j hj
    obtain ⟨hjτ, hjk, hjr⟩ := mem_live.mp hj
    refine mem_live.mpr ⟨le_trans hjτ hττ', hjk, fun ⟨p, hp, hpt⟩ => ?_⟩
    rw [Finset.mem_Ioc] at hp
    by_cases hpτ : p ≤ τ
    · exact hjr ⟨p, Finset.mem_Ioc.mpr ⟨hp.1, hpτ⟩, hpt⟩
    · rw [hnone p (not_le.mp hpτ) hp.2] at hpt
      cases hpt
  obtain ⟨_, hik, hir⟩ := mem_live.mp h.1
  exact covers_mono hsub
    (mem_live.mpr ⟨hiτ, hik, fun hr => hir (retracted_mono hττ' hr)⟩) h

/-! ### Examples -/

/-- Slot 0 is a home city. Value 1 is claimed from event time 0, value 2 from
event time 5, and the second claim is later withdrawn. -/
def moveLog : Log ℕ ℕ :=
  [.assert ⟨0, 1, 0, none, 10⟩, .assert ⟨0, 2, 5, none, 11⟩, .retract 1]

/-- A retraction undoes the cut that the withdrawn claim made. Invalidation is
therefore not monotone once retractions are allowed, and stored invalidation
stamps would have to be recomputed. -/
theorem retraction_restores :
    Holds moveLog 0 7 0 0 ∧ ¬ Holds moveLog 0 7 1 0 ∧ Holds moveLog 0 7 1 1 ∧
      Holds moveLog 0 7 2 0 ∧ Holds moveLog 0 3 1 0 := by
  decide

/-- Claims learned in reverse event order give the same timeline. -/
def lateRecollection : Log ℕ ℕ :=
  [.assert ⟨0, 2, 5, none, 11⟩, .assert ⟨0, 1, 0, none, 10⟩]

example : Holds lateRecollection 0 3 1 1 ∧ Holds lateRecollection 0 7 1 0 ∧
    ¬ Holds lateRecollection 0 7 1 1 := by
  decide

/-- A claim with a declared stop closes the earlier claim at its start and does
not revive it after the stop. The value is unknown there. A temporary exception
belongs in its own slot. -/
def closedLog : Log ℕ ℕ :=
  [.assert ⟨0, 1, 0, none, 10⟩, .assert ⟨0, 2, 5, some 8, 11⟩]

example : Holds closedLog 0 6 1 1 ∧ ¬ Holds closedLog 0 9 1 0 ∧ ¬ Holds closedLog 0 9 1 1 := by
  decide

/-! ## Why stored stamps must be derived -/

/-- A stored fact whose event-time end and expiry are overwritten in place. -/
structure StampRow where
  key : ℕ
  val : ℕ
  validAt : ℕ
  invalidAt : Option ℕ
  createdAt : ℕ
  expiredAt : Option ℕ
  deriving DecidableEq, Repr

/-- In-place ingestion of an open-ended fact at knowledge time `now`, following
the invalidation step of the Graphiti engine. Each contradicting row (same key,
other value) that started earlier and is still valid at the new start is closed
at that start and stamped as expired. -/
def ingestInPlace (rows : List StampRow) (k v s now : ℕ) : List StampRow :=
  rows.map (fun r =>
      if r.key = k ∧ r.val ≠ v ∧ r.validAt < s ∧ Before s r.invalidAt then
        { r with invalidAt := some s, expiredAt := some (r.expiredAt.getD now) }
      else r) ++
    [⟨k, v, s, none, now, none⟩]

/-- Reading the expiry stamp as the end of belief. -/
def visibleByExpiry (rows : List StampRow) (k t τ : ℕ) : List ℕ :=
  (rows.filter (fun r => decide (r.key = k ∧ r.createdAt ≤ τ ∧ Before τ r.expiredAt ∧
    r.validAt ≤ t ∧ Before t r.invalidAt))).map StampRow.val

/-- Ignoring the expiry stamp and reading the stored validity at any knowledge time. -/
def visibleIgnoringExpiry (rows : List StampRow) (k t τ : ℕ) : List ℕ :=
  (rows.filter (fun r => decide (r.key = k ∧ r.createdAt ≤ τ ∧ r.validAt ≤ t ∧
    Before t r.invalidAt))).map StampRow.val

def stampsBefore : List StampRow := ingestInPlace [] 0 1 0 0

def stampsAfter : List StampRow := ingestInPlace stampsBefore 0 2 5 1

def moveClaims : Log ℕ ℕ := [.assert ⟨0, 1, 0, none, 10⟩, .assert ⟨0, 2, 5, none, 11⟩]

/-- Value 1 holds from event time 0. At knowledge time 1 the agent learns that
value 2 holds from event time 5. The append-only log keeps value 1 at event time
3 in the current view, and keeps value 1 at event time 7 in the view held at
knowledge time 0. Stored stamps lose one of the two, depending on how they are
read: reading expiry as the end of belief erases the history before the move,
and ignoring expiry rewrites the past view. -/
theorem inplace_stamps_lose_history :
    Believes moveClaims 0 3 1 1 ∧ Believes moveClaims 0 7 0 1 ∧
      visibleByExpiry stampsAfter 0 3 1 = [] ∧
      visibleIgnoringExpiry stampsBefore 0 7 0 = [1] ∧
      visibleIgnoringExpiry stampsAfter 0 7 0 = [] := by
  refine ⟨⟨0, by decide, rfl⟩, ⟨0, by decide, rfl⟩, by decide, by decide, by decide⟩

end Log

end AgentMemory.Bitemporal
