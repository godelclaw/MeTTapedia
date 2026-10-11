import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# A bounded working memory with attention and forgetting

`bgoertzel-sing/iter` adds WMTM, a working medium-term memory between the
prompt and the long-term journal (master `3399366`, live branch
`agent/protocosmo2-wmtm-live-20261005` at `4564185`). A bounded store holds
items recalled from the journal or derived by inference. Each item carries
ECAN-style short- and long-term importance (STI, LTI). STI decays by a factor
of `0.9` per tick, items below an STI floor are evicted, and a full store
evicts its lowest-STI item to admit a new one. A forgetting log records
evicted contents and blocks their re-derivation. Long-lived, useful items are
written back to the journal.

This file isolates what that design guarantees and where it fails.

Store and admission:
* `admitU_length_le`: the upstream admission keeps the store within capacity.
* `admitU_evicts_better`: it admits every newcomer, so an item of higher
  attention can be evicted for a newcomer of lower attention.
  `admitG_evicts_only_worse` is the guarded alternative: it evicts only an
  item of minimal attention, and only for a strictly better newcomer.
* `eviction_ignores_long_term_importance`: eviction compares STI only, while
  the attentional focus is ordered by STI plus LTI, so the item at the top of
  the focus can be evicted first.

Attention dynamics:
* `unboosted_falls_below_floor`, `floor_eviction_tick` (liveness, bound): an
  item that is never boosted falls below the eviction floor; with the upstream
  constants, an item admitted at STI 100 is evicted at tick 88.
* `sti_bounded` (bound): with boosts bounded by `B`, STI stays below
  `max s₀ (B / (1 - d))`.
* `shown_dominates_forever`: the live branch boosts every item it shows to the
  model. Without outside stimulus, an item shown once keeps dominating every
  item that is not shown.
* `displayed_derived_is_promoted`: showing an item counts as using it, so a
  derived item shown for 15 cycles meets the writeback threshold although the
  model never referred to it.

Forgetting and writeback:
* `pln_forgotten_is_exiled`: a forgotten content is re-derived only with
  initial STI of at least 500. A PLN-derived candidate starts at `s · c ≤ 1`,
  so once forgotten it never returns, whatever new evidence arrives.
* `recordAll_eq`, `forgotten_stays_barred`, `forgotten_returns_after`: the live
  branch caps the log at `N` records (oldest first out). A forgotten content
  stays barred for fewer than `N` further evictions and returns after `N`.
* `recall_writeback_launders` and `recallP_writeback`: a derived belief written
  back to the journal is recalled as an ordinary recalled item, losing its
  derived status and its premises. Keeping provenance in the stored atom
  makes the round trip the identity.

A CeTTa-native working memory keeps attention apart from truth. The space holds
claims and evidence; the working set is a derived, budgeted selection whose
admission compares the newcomer against the current minimum. Forgetting
removes items from the working set, never from the space; a forgetting record
names the evidential base of the forgotten conclusion, so the conclusion can
return when that base changes. Writeback is an event that keeps the derived
status and the premises of the belief.
-/

set_option autoImplicit false

namespace AgentMemory.WorkingMemory

/-! ## The store -/

/-- A working-memory item: identity, short-term importance and long-term
importance. -/
structure Item (V : Type) where
  id : ℕ
  sti : V
  lti : V
  deriving DecidableEq

section Store

variable {V : Type} [LinearOrder V]

/-- The item the upstream store evicts: one of lowest STI. -/
def lowest (s : List (Item V)) : Option (Item V) := s.argmin Item.sti

/-- `WMTMStore.admit` for a new identity: when the store is full, evict a
lowest-STI item, then insert the newcomer without comparing it. A present
identity is refreshed in place. -/
def admitU (cap : ℕ) (s : List (Item V)) (x : Item V) : List (Item V) :=
  if x.id ∈ s.map Item.id then s
  else if s.length < cap then x :: s
  else match lowest s with
    | some m => x :: s.erase m
    | none => [x]

/-- Guarded admission: a full store admits a newcomer only when it beats the
current minimum. -/
def admitG (cap : ℕ) (s : List (Item V)) (x : Item V) : List (Item V) :=
  if x.id ∈ s.map Item.id then s
  else if s.length < cap then x :: s
  else match lowest s with
    | some m => if m.sti < x.sti then x :: s.erase m else s
    | none => [x]

/-- Admission keeps the store within its capacity. -/
theorem admitU_length_le (cap : ℕ) (hcap : 0 < cap) (s : List (Item V)) (x : Item V)
    (hs : s.length ≤ cap) : (admitU cap s x).length ≤ cap := by
  unfold admitU
  split_ifs with h1 h2
  · exact hs
  · simp only [List.length_cons]
    omega
  · split
    · rename_i m hm
      have hmem : m ∈ s := List.argmin_mem hm
      simp only [List.length_cons, List.length_erase_of_mem hmem]
      omega
    · simp only [List.length_cons, List.length_nil]
      omega

/-- Guarded admission also keeps the store within its capacity. -/
theorem admitG_length_le (cap : ℕ) (hcap : 0 < cap) (s : List (Item V)) (x : Item V)
    (hs : s.length ≤ cap) : (admitG cap s x).length ≤ cap := by
  unfold admitG
  split_ifs with h1 h2
  · exact hs
  · simp only [List.length_cons]
    omega
  · split
    · rename_i m hm
      have hmem : m ∈ s := List.argmin_mem hm
      split_ifs
      · simp only [List.length_cons, List.length_erase_of_mem hmem]
        omega
      · exact hs
    · simp only [List.length_cons, List.length_nil]
      omega

/-- Guarded admission evicts only an item of minimal attention, and only for a
newcomer of strictly higher attention. -/
theorem admitG_evicts_only_worse (cap : ℕ) (s : List (Item V)) (x y : Item V)
    (hy : y ∈ s) (hout : y ∉ admitG cap s x) :
    y.sti < x.sti ∧ ∀ z ∈ s, y.sti ≤ z.sti := by
  unfold admitG at hout
  split_ifs at hout with h1 h2
  · exact absurd hy hout
  · exact absurd (List.mem_cons_of_mem _ hy) hout
  · split at hout
    · rename_i m hm
      split_ifs at hout with h3
      · have hym : y = m := by
          by_contra hne
          exact hout (List.mem_cons_of_mem _ ((List.mem_erase_of_ne hne).mpr hy))
        subst hym
        exact ⟨h3, fun z hz => List.le_of_mem_argmin hz hm⟩
      · exact absurd hy hout
    · rename_i hm
      simp [List.argmin_eq_none.mp hm] at hy

end Store

/-- The upstream rule evicts an item of attention 90 for a newcomer of attention
1; the guarded rule refuses the newcomer. -/
theorem admitU_evicts_better :
    let a : Item ℕ := ⟨1, 100, 0⟩
    let b : Item ℕ := ⟨2, 90, 0⟩
    let c : Item ℕ := ⟨3, 1, 0⟩
    admitU 2 [a, b] c = [c, a] ∧ c.sti < b.sti ∧ admitG 2 [a, b] c = [a, b] := by
  decide

/-- The attentional focus orders items by STI plus a fifth of LTI (here scaled
by 5). -/
def total (x : Item ℕ) : ℕ := 5 * x.sti + x.lti

/-- Eviction compares STI only: an item with large long-term importance, first in
the attentional focus, is evicted before an item of lower total importance. -/
theorem eviction_ignores_long_term_importance :
    let p : Item ℕ := ⟨1, 1, 100⟩
    let q : Item ℕ := ⟨2, 2, 0⟩
    let r : Item ℕ := ⟨3, 3, 0⟩
    admitU 2 [p, q] r = [r, q] ∧ total q < total p := by
  decide

/-! ## Attention dynamics -/

/-- An item that is never boosted falls below any positive eviction floor. -/
theorem unboosted_falls_below_floor (d floor s : ℚ) (hd1 : d < 1) (hf : 0 < floor) :
    ∃ k : ℕ, d ^ k * s < floor := by
  rcases le_or_gt s 0 with hs | hs
  · exact ⟨0, by simp; linarith⟩
  · obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hf hs) hd1
    refine ⟨k, ?_⟩
    calc d ^ k * s < floor / s * s := by
          exact mul_lt_mul_of_pos_right hk hs
      _ = floor := by field_simp

/-- With the upstream constants (decay `0.9`, floor `0.01`), an item admitted at
STI 100 and never boosted is evicted at tick 88 and not earlier. -/
theorem floor_eviction_tick :
    (9 / 10 : ℚ) ^ 88 * 100 < 1 / 100 ∧ 1 / 100 ≤ (9 / 10 : ℚ) ^ 87 * 100 := by
  norm_num

/-- Boosts of at most `B` per tick keep STI below any `M` with `s₀ ≤ M` and
`B ≤ (1 - d) M`, for example `max s₀ (B / (1 - d))`. -/
theorem sti_bounded (d B M : ℚ) (s b : ℕ → ℚ) (hrec : ∀ k, s (k + 1) = d * s k + b k)
    (hd0 : 0 ≤ d) (hb : ∀ k, b k ≤ B) (h0 : s 0 ≤ M) (hMB : B ≤ (1 - d) * M) :
    ∀ k, s k ≤ M := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
    rw [hrec k]
    have := hb k
    nlinarith [mul_le_mul_of_nonneg_left ih hd0]

/-- The live branch records every item shown to the model as used, and each full
cycle boosts the used items by `b` while every item decays by `d`. An item
shown once dominates every item that is not shown, for every later cycle
without outside stimulus. -/
theorem shown_dominates_forever (d b : ℚ) (x y : ℕ → ℚ) (hd : 0 ≤ d) (hb : 0 ≤ b)
    (hx : ∀ k, x (k + 1) = d * x k + b) (hy : ∀ k, y (k + 1) = d * y k)
    (h0 : y 0 ≤ x 0) : ∀ k, y k ≤ x k := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
    rw [hx k, hy k]
    nlinarith [mul_le_mul_of_nonneg_left ih hd]

/-- Utility on the live branch: two per use, one and a half per derivation the
item contributed to, minus three tenths per cycle in which it was present but
unused, clamped at zero. -/
def utility (uses inferred misses : ℕ) : ℚ :=
  max 0 (2 * uses + 3 / 2 * inferred - 3 / 10 * misses)

/-- Writeback threshold for a derived item: age at least 15 cycles and utility
at least `3/2`. -/
def promotesDerived (age : ℕ) (u : ℚ) : Prop := 15 ≤ age ∧ 3 / 2 ≤ u

/-- Every item shown to the model is recorded as used and is not counted as a
miss. A derived item shown in each of its first 15 cycles is written back,
whether or not the model used it. -/
theorem displayed_derived_is_promoted (n : ℕ) (hn : 15 ≤ n) :
    promotesDerived n (utility n 0 0) := by
  refine ⟨hn, ?_⟩
  have h : (15 : ℚ) ≤ n := by exact_mod_cast hn
  simp only [utility]
  apply le_max_of_le_right
  push_cast
  linarith

/-! ## The forgetting log -/

section Forgetting

variable {C : Type}

/-- The upstream skip rule for a derived candidate: its content was forgotten
and its initial STI is below the override threshold. -/
def skipped (override : ℚ) (log : List C) (c : C) (sti : ℚ) : Prop :=
  c ∈ log ∧ sti < override

/-- A PLN-derived candidate enters with STI `s · c`, where `s` and `c` are its
strength and confidence. Once its content is forgotten it is skipped for
every truth value, so new evidence can never bring it back. -/
theorem pln_forgotten_is_exiled (log : List C) (c : C) (hc : c ∈ log) (s conf : ℚ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hc1 : conf ≤ 1) :
    skipped 500 log c (s * conf) := by
  refine ⟨hc, ?_⟩
  nlinarith

/-- The live branch keeps the newest `N` records (newest first). -/
def record (N : ℕ) (log : List C) (c : C) : List C := (c :: log).take N

/-- Recording several evictions in order. -/
def recordAll (N : ℕ) (log : List C) (cs : List C) : List C := cs.foldl (record N) log

private theorem take_append_take (N : ℕ) (A B : List C) :
    (A ++ B.take N).take N = (A ++ B).take N := by
  rw [List.take_append, List.take_append, List.take_take]
  congr 2
  omega

/-- A log that starts within the cap holds the newest `N` records. -/
theorem recordAll_eq (N : ℕ) (cs log : List C) (hlog : log.length ≤ N) :
    recordAll N log cs = (cs.reverse ++ log).take N := by
  induction cs generalizing log with
  | nil => simp [recordAll, List.take_of_length_le hlog]
  | cons c cs ih =>
    have hlen : (record N log c).length ≤ N := by simp [record]
    simp only [recordAll, List.foldl_cons] at ih ⊢
    rw [ih (record N log c) hlen, record, take_append_take]
    simp

/-- A forgotten content stays barred while fewer than `N` later evictions are
recorded. -/
theorem forgotten_stays_barred (N : ℕ) (log cs : List C) (c : C) (hlog : log.length ≤ N)
    (hfew : cs.length < N) : c ∈ recordAll N log (c :: cs) := by
  rw [recordAll_eq N (c :: cs) log hlog, List.reverse_cons, List.append_assoc]
  apply List.mem_take_iff_getElem.mpr
  refine ⟨cs.reverse.length, ?_, ?_⟩
  · simp
    omega
  · simp

/-- After `N` later evictions of other contents, the forgotten content is no
longer barred and may be derived again. -/
theorem forgotten_returns_after (N : ℕ) (log cs : List C) (c : C) (hN : cs.length = N) (hc : c ∉ cs) : c ∉ recordAll N (record N log c) cs := by
  have hlen : (record N log c).length ≤ N := by simp [record]
  rw [recordAll_eq N cs _ hlen, List.take_append]
  have h0 : N - cs.reverse.length = 0 := by simp [hN]
  rw [h0, List.take_zero, List.append_nil, List.take_of_length_le (by simp [hN])]
  simpa using hc

end Forgetting

/-! ## Writeback and recall -/

/-- Where a belief came from. -/
inductive Origin
  | recalled
  | derived
  deriving DecidableEq

/-- A working-memory belief: content, origin and premises. -/
structure Belief where
  content : ℕ
  origin : Origin
  premises : List ℕ
  deriving DecidableEq

/-- A journal cluster written back by WMTM. It records whether the belief was
derived and from which items. -/
structure Cluster where
  content : ℕ
  derived : Bool
  derivedFrom : List ℕ
  deriving DecidableEq

/-- Writeback formats a derived belief with `ClusterType DerivedBelief` and its
`DerivedFrom` premises. -/
def writeback (b : Belief) : Cluster := ⟨b.content, b.origin = .derived, b.premises⟩

/-- Upstream recall admits every journal cluster as a recalled item. -/
def recallU (c : Cluster) : Belief := ⟨c.content, .recalled, []⟩

/-- Recall that reads back the recorded provenance. -/
def recallP (c : Cluster) : Belief :=
  ⟨c.content, if c.derived then .derived else .recalled, c.derivedFrom⟩

/-- A derived belief written back and recalled becomes an ordinary recalled
item: its derived status and premises are gone. -/
theorem recall_writeback_launders :
    recallU (writeback ⟨7, .derived, [1, 2]⟩) = ⟨7, .recalled, []⟩ := by
  decide

/-- Reading the recorded provenance makes the round trip the identity. -/
theorem recallP_writeback (b : Belief) : recallP (writeback b) = b := by
  obtain ⟨content, origin, premises⟩ := b
  cases origin <;> rfl

end AgentMemory.WorkingMemory
