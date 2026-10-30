import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum

/-!
# Range-based set reconciliation, with fingerprints that can collide

Two parties hold sets `S` (the server's) and `C` (the client's). Each item has a
position `key` in `[lo, hi)`. Range-based set reconciliation (Meyer, "Range-Based
Set Reconciliation", arXiv 2212.13567; Negentropy, NIP-77) compares a fingerprint
of each side's slice of a range. Equal fingerprints end the range. Different
ones split it in two, down to single positions, where the items are listed.
This file is the binary core. Negentropy's bucket counts and its exchange of
messages between two parties are a separate model.

Negentropy maps a set of 32-byte ids to a 16-byte fingerprint, so different sets
can share one (`not_collisionFree_of_card_lt`, `negentropy_not_collisionFree`).
Its fingerprint is computed from the sum of the ids and their count, and that
pair already collides on chosen ids (`fpSum_collision`), whatever hash follows
(`fingerprint_collision`). So nothing below assumes a fingerprint without
collisions:
- `rbsrDiff_sound`: with no assumption on `fp`, every item the run reports is in
  the server's slice and not in the client's.
- `rbsrDiff_complete`: when the fingerprints this run compares do not collide
  (`RunNoCollision`, defined by the run's own recursion), the report is exactly
  the server's slice minus the client's. `fpSum` meets that hypothesis on
  concrete different sets (the examples).
- `missed_in_colliding_range`: an item the run misses lies in a range where the
  run compared equal fingerprints of different slices. Every miss needs a
  collision there.
- `rbsrSplits_le`: with no assumption on `fp`, the run splits at most
  `|Δ| · ⌈log₂ (hi - lo)⌉` ranges, where `Δ` is the symmetric difference of the
  two slices. A range is split only when its fingerprints differ, which needs
  its slices to differ.
- `diffGo_fuel_stable`: the run's result does not depend on its fuel once the
  fuel covers the width, so `rbsrDiff`, which gives it `hi - lo`, is the full
  recursion.
- The dense second: items that share one timestamp are reconciled (example).

Mutants: a leaf that reports the server's slice without removing the client's
breaks soundness (`leafMutant_unsound`); a run that also splits ranges whose
fingerprints agree breaks the split bound (`splitMutant_exceeds`).

Not modelled here: the messages between the two parties, bucket counts other
than two, and frame limits.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Sync.Rbsr

open Finset
open scoped symmDiff

section Core

variable {α H : Type} [DecidableEq α] [DecidableEq H]

/-- The items of `S` at positions in `[lo, hi)`. -/
def sliceRange (key : α → Nat) (S : Finset α) (lo hi : Nat) : Finset α :=
  S.filter fun x => lo ≤ key x ∧ key x < hi

omit [DecidableEq α] in
theorem mem_sliceRange {key : α → Nat} {S : Finset α} {lo hi : Nat} {x : α} :
    x ∈ sliceRange key S lo hi ↔ x ∈ S ∧ lo ≤ key x ∧ key x < hi := by
  simp [sliceRange]

/-- The binary run with `fuel` levels of splitting left. -/
def diffGo (key : α → Nat) (fp : Finset α → H) (S C : Finset α) : Nat → Nat → Nat → Finset α
  | 0, lo, hi =>
    if fp (sliceRange key S lo hi) = fp (sliceRange key C lo hi) then ∅
    else sliceRange key S lo hi \ sliceRange key C lo hi
  | fuel + 1, lo, hi =>
    if fp (sliceRange key S lo hi) = fp (sliceRange key C lo hi) then ∅
    else if hi ≤ lo + 1 then sliceRange key S lo hi \ sliceRange key C lo hi
    else diffGo key fp S C fuel lo ((lo + hi) / 2) ∪ diffGo key fp S C fuel ((lo + hi) / 2) hi

/-- The items the server holds in `[lo, hi)` and the client lacks, as the run
reports them. -/
def rbsrDiff (key : α → Nat) (fp : Finset α → H) (S C : Finset α) (lo hi : Nat) : Finset α :=
  diffGo key fp S C (hi - lo) lo hi

/-- The number of ranges the run splits. -/
def splitsGo (key : α → Nat) (fp : Finset α → H) (S C : Finset α) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, lo, hi =>
    if fp (sliceRange key S lo hi) = fp (sliceRange key C lo hi) then 0
    else if hi ≤ lo + 1 then 0
    else 1 + splitsGo key fp S C fuel lo ((lo + hi) / 2) + splitsGo key fp S C fuel ((lo + hi) / 2) hi

def rbsrSplits (key : α → Nat) (fp : Finset α → H) (S C : Finset α) (lo hi : Nat) : Nat :=
  splitsGo key fp S C (hi - lo) lo hi

/-- At each range the run visits, equal fingerprints mean equal slices. -/
def noCollGo (key : α → Nat) (fp : Finset α → H) (S C : Finset α) : Nat → Nat → Nat → Bool
  | 0, lo, hi =>
    decide (fp (sliceRange key S lo hi) = fp (sliceRange key C lo hi) →
      sliceRange key S lo hi = sliceRange key C lo hi)
  | fuel + 1, lo, hi =>
    decide (fp (sliceRange key S lo hi) = fp (sliceRange key C lo hi) →
        sliceRange key S lo hi = sliceRange key C lo hi) &&
      (if fp (sliceRange key S lo hi) = fp (sliceRange key C lo hi) then true
      else if hi ≤ lo + 1 then true
      else noCollGo key fp S C fuel lo ((lo + hi) / 2) && noCollGo key fp S C fuel ((lo + hi) / 2) hi)

/-- The fingerprints compared by the run on `[lo, hi)` do not collide. -/
abbrev RunNoCollision (key : α → Nat) (fp : Finset α → H) (S C : Finset α) (lo hi : Nat) : Prop :=
  noCollGo key fp S C (hi - lo) lo hi = true

/-- The ranges where the run stopped on equal fingerprints. -/
def prunedGo (key : α → Nat) (fp : Finset α → H) (S C : Finset α) :
    Nat → Nat → Nat → List (Nat × Nat)
  | 0, lo, hi =>
    if fp (sliceRange key S lo hi) = fp (sliceRange key C lo hi) then [(lo, hi)] else []
  | fuel + 1, lo, hi =>
    if fp (sliceRange key S lo hi) = fp (sliceRange key C lo hi) then [(lo, hi)]
    else if hi ≤ lo + 1 then []
    else prunedGo key fp S C fuel lo ((lo + hi) / 2) ++ prunedGo key fp S C fuel ((lo + hi) / 2) hi

/-! ### Slices of halves -/

omit [DecidableEq α] in
theorem sliceRange_left {key : α → Nat} {S : Finset α} {lo mid hi : Nat} (h : mid ≤ hi) :
    sliceRange key S lo mid = (sliceRange key S lo hi).filter fun x => key x < mid := by
  ext x
  simp only [mem_filter, mem_sliceRange]
  constructor
  · rintro ⟨hs, h1, h2⟩
    exact ⟨⟨hs, h1, by omega⟩, h2⟩
  · rintro ⟨⟨hs, h1, _⟩, h3⟩
    exact ⟨hs, h1, h3⟩

omit [DecidableEq α] in
theorem sliceRange_right {key : α → Nat} {S : Finset α} {lo mid hi : Nat} (h : lo ≤ mid) :
    sliceRange key S mid hi = (sliceRange key S lo hi).filter fun x => ¬ key x < mid := by
  ext x
  simp only [mem_filter, mem_sliceRange]
  constructor
  · rintro ⟨hs, h1, h2⟩
    exact ⟨⟨hs, by omega, h2⟩, by omega⟩
  · rintro ⟨⟨hs, _, h2⟩, h3⟩
    exact ⟨hs, by omega, h2⟩

theorem sdiff_halves {key : α → Nat} {S C : Finset α} {lo mid hi : Nat} (h1 : lo ≤ mid)
    (h2 : mid ≤ hi) :
    (sliceRange key S lo mid \ sliceRange key C lo mid) ∪
        (sliceRange key S mid hi \ sliceRange key C mid hi) =
      sliceRange key S lo hi \ sliceRange key C lo hi := by
  ext x
  simp only [mem_union, mem_sdiff, mem_sliceRange]
  constructor
  · rintro (⟨⟨hs, ha, hb⟩, hc⟩ | ⟨⟨hs, ha, hb⟩, hc⟩)
    · exact ⟨⟨hs, ha, by omega⟩, fun ⟨hc', _, _⟩ => hc ⟨hc', ha, hb⟩⟩
    · exact ⟨⟨hs, by omega, hb⟩, fun ⟨hc', _, _⟩ => hc ⟨hc', ha, hb⟩⟩
  · rintro ⟨⟨hs, ha, hb⟩, hc⟩
    by_cases hm : key x < mid
    · exact Or.inl ⟨⟨hs, ha, hm⟩, fun ⟨hc', _, _⟩ => hc ⟨hc', ha, hb⟩⟩
    · exact Or.inr ⟨⟨hs, by omega, hb⟩, fun ⟨hc', _, _⟩ => hc ⟨hc', ha, hb⟩⟩

theorem filter_symmDiff' (p : α → Prop) [DecidablePred p] (s t : Finset α) :
    (s.filter p) ∆ (t.filter p) = (s ∆ t).filter p := by
  ext x
  simp only [mem_symmDiff, mem_filter]
  tauto

/-! ### Soundness, with no assumption on the fingerprint -/

theorem diffGo_sound (key : α → Nat) (fp : Finset α → H) (S C : Finset α) :
    ∀ fuel lo hi, diffGo key fp S C fuel lo hi ⊆
      sliceRange key S lo hi \ sliceRange key C lo hi
  | 0, lo, hi => by
    unfold diffGo
    split_ifs
    · exact empty_subset _
    · exact Subset.refl _
  | fuel + 1, lo, hi => by
    unfold diffGo
    split_ifs with h1 h2
    · exact empty_subset _
    · exact Subset.refl _
    · rw [← sdiff_halves (by omega : lo ≤ (lo + hi) / 2) (by omega : (lo + hi) / 2 ≤ hi)]
      exact union_subset_union (diffGo_sound key fp S C fuel lo _)
        (diffGo_sound key fp S C fuel _ hi)

/-- **A1.** Every item the run reports is in the server's slice and not in the
client's, whatever the fingerprint. -/
theorem rbsrDiff_sound (key : α → Nat) (fp : Finset α → H) (S C : Finset α) (lo hi : Nat) :
    rbsrDiff key fp S C lo hi ⊆ sliceRange key S lo hi \ sliceRange key C lo hi :=
  diffGo_sound key fp S C _ lo hi

/-! ### Completeness, when this run's fingerprints do not collide -/

theorem diffGo_complete (key : α → Nat) (fp : Finset α → H) (S C : Finset α) :
    ∀ fuel lo hi, noCollGo key fp S C fuel lo hi = true →
      diffGo key fp S C fuel lo hi = sliceRange key S lo hi \ sliceRange key C lo hi
  | 0, lo, hi, hnc => by
    unfold noCollGo at hnc
    unfold diffGo
    have hnc' := of_decide_eq_true hnc
    split_ifs with h
    · rw [hnc' h, sdiff_self, bot_eq_empty]
    · rfl
  | fuel + 1, lo, hi, hnc => by
    unfold noCollGo at hnc
    unfold diffGo
    rw [Bool.and_eq_true] at hnc
    obtain ⟨h0, hrest⟩ := hnc
    have h0' := of_decide_eq_true h0
    by_cases hfp : fp (sliceRange key S lo hi) = fp (sliceRange key C lo hi)
    · rw [if_pos hfp, h0' hfp, sdiff_self, bot_eq_empty]
    · rw [if_neg hfp]
      rw [if_neg hfp] at hrest
      by_cases hw : hi ≤ lo + 1
      · rw [if_pos hw]
      · rw [if_neg hw]
        rw [if_neg hw, Bool.and_eq_true] at hrest
        rw [diffGo_complete key fp S C fuel lo _ hrest.1,
          diffGo_complete key fp S C fuel _ hi hrest.2]
        exact sdiff_halves (by omega) (by omega)

/-- **A2.** When the fingerprints this run compares do not collide, the run
reports exactly the server's slice minus the client's. -/
theorem rbsrDiff_complete (key : α → Nat) (fp : Finset α → H) (S C : Finset α) (lo hi : Nat)
    (h : RunNoCollision key fp S C lo hi) :
    rbsrDiff key fp S C lo hi = sliceRange key S lo hi \ sliceRange key C lo hi :=
  diffGo_complete key fp S C _ lo hi h

/-! ### Where a miss can happen -/

theorem diffGo_missed (key : α → Nat) (fp : Finset α → H) (S C : Finset α) :
    ∀ fuel lo hi x, x ∈ sliceRange key S lo hi \ sliceRange key C lo hi →
      x ∉ diffGo key fp S C fuel lo hi →
      ∃ r ∈ prunedGo key fp S C fuel lo hi, r.1 ≤ key x ∧ key x < r.2 ∧
        fp (sliceRange key S r.1 r.2) = fp (sliceRange key C r.1 r.2) ∧
        sliceRange key S r.1 r.2 ≠ sliceRange key C r.1 r.2
  | 0, lo, hi, x, hx, hmiss => by
    unfold diffGo at hmiss
    unfold prunedGo
    have hx' := mem_sdiff.mp hx
    split_ifs at hmiss ⊢ with h
    · refine ⟨(lo, hi), List.mem_singleton_self _, (mem_sliceRange.mp hx'.1).2.1,
        (mem_sliceRange.mp hx'.1).2.2, h, fun heq => hx'.2 (heq ▸ hx'.1)⟩
    · exact absurd hx hmiss
  | fuel + 1, lo, hi, x, hx, hmiss => by
    unfold diffGo at hmiss
    unfold prunedGo
    have hx' := mem_sdiff.mp hx
    by_cases hfp : fp (sliceRange key S lo hi) = fp (sliceRange key C lo hi)
    · rw [if_pos hfp]
      exact ⟨(lo, hi), List.mem_singleton_self _, (mem_sliceRange.mp hx'.1).2.1,
        (mem_sliceRange.mp hx'.1).2.2, hfp, fun heq => hx'.2 (heq ▸ hx'.1)⟩
    · rw [if_neg hfp] at hmiss ⊢
      by_cases hw : hi ≤ lo + 1
      · rw [if_pos hw] at hmiss
        exact absurd hx hmiss
      · rw [if_neg hw] at hmiss ⊢
        rw [← sdiff_halves (by omega : lo ≤ (lo + hi) / 2) (by omega : (lo + hi) / 2 ≤ hi)] at hx
        rcases mem_union.mp hx with hl | hr
        · obtain ⟨r, hr, hrest⟩ := diffGo_missed key fp S C fuel lo _ x hl
            (fun h => hmiss (mem_union_left _ h))
          exact ⟨r, List.mem_append_left _ hr, hrest⟩
        · obtain ⟨r, hr', hrest⟩ := diffGo_missed key fp S C fuel _ hi x hr
            (fun h => hmiss (mem_union_right _ h))
          exact ⟨r, List.mem_append_right _ hr', hrest⟩

/-- **A6.** An item the run misses lies in a range where the run compared equal
fingerprints of different slices. -/
theorem missed_in_colliding_range (key : α → Nat) (fp : Finset α → H) (S C : Finset α)
    (lo hi : Nat) {x : α} (hx : x ∈ sliceRange key S lo hi \ sliceRange key C lo hi)
    (hmiss : x ∉ rbsrDiff key fp S C lo hi) :
    ∃ r ∈ prunedGo key fp S C (hi - lo) lo hi, r.1 ≤ key x ∧ key x < r.2 ∧
      fp (sliceRange key S r.1 r.2) = fp (sliceRange key C r.1 r.2) ∧
      sliceRange key S r.1 r.2 ≠ sliceRange key C r.1 r.2 :=
  diffGo_missed key fp S C _ lo hi x hx hmiss

/-! ### The number of splits -/

theorem symmDiff_card_halves {key : α → Nat} {S C : Finset α} {lo mid hi : Nat} (h1 : lo ≤ mid)
    (h2 : mid ≤ hi) :
    (sliceRange key S lo mid ∆ sliceRange key C lo mid).card +
        (sliceRange key S mid hi ∆ sliceRange key C mid hi).card =
      (sliceRange key S lo hi ∆ sliceRange key C lo hi).card := by
  rw [sliceRange_left h2, sliceRange_left h2, sliceRange_right h1, sliceRange_right h1,
    filter_symmDiff', filter_symmDiff']
  exact card_filter_add_card_filter_not _

theorem symmDiff_pos_of_ne {s t : Finset α} (h : s ≠ t) : 0 < (s ∆ t).card := by
  rw [card_pos]
  by_contra hne
  apply h
  ext x
  have hx : x ∉ s ∆ t := fun hx => hne ⟨x, hx⟩
  rw [mem_symmDiff] at hx
  tauto

theorem splitsGo_le (key : α → Nat) (fp : Finset α → H) (S C : Finset α) :
    ∀ fuel lo hi, splitsGo key fp S C fuel lo hi ≤
      (sliceRange key S lo hi ∆ sliceRange key C lo hi).card * Nat.clog 2 (hi - lo)
  | 0, _, _ => Nat.zero_le _
  | fuel + 1, lo, hi => by
    unfold splitsGo
    split_ifs with hfp hw
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · have hne : sliceRange key S lo hi ≠ sliceRange key C lo hi := fun h => hfp (by rw [h])
      have hpos := symmDiff_pos_of_ne hne
      have hL := splitsGo_le key fp S C fuel lo ((lo + hi) / 2)
      have hR := splitsGo_le key fp S C fuel ((lo + hi) / 2) hi
      have hcard := symmDiff_card_halves (key := key) (S := S) (C := C)
        (by omega : lo ≤ (lo + hi) / 2) (by omega : (lo + hi) / 2 ≤ hi)
      have hclog : Nat.clog 2 (hi - lo) = Nat.clog 2 ((hi - lo + 2 - 1) / 2) + 1 :=
        Nat.clog_of_two_le (by norm_num) (by omega)
      have hcl : Nat.clog 2 ((lo + hi) / 2 - lo) ≤ Nat.clog 2 ((hi - lo + 2 - 1) / 2) :=
        Nat.clog_mono_right 2 (by omega)
      have hcr : Nat.clog 2 (hi - (lo + hi) / 2) ≤ Nat.clog 2 ((hi - lo + 2 - 1) / 2) :=
        Nat.clog_mono_right 2 (by omega)
      rw [hclog, ← hcard]
      generalize (sliceRange key S lo ((lo + hi) / 2) ∆ sliceRange key C lo ((lo + hi) / 2)).card
        = dL at hL hcard
      generalize (sliceRange key S ((lo + hi) / 2) hi ∆ sliceRange key C ((lo + hi) / 2) hi).card
        = dR at hR hcard
      generalize Nat.clog 2 ((hi - lo + 2 - 1) / 2) = c at hcl hcr
      have hL' := hL.trans (Nat.mul_le_mul_left dL hcl)
      have hR' := hR.trans (Nat.mul_le_mul_left dR hcr)
      have hd : 1 ≤ dL + dR := by omega
      calc 1 + splitsGo key fp S C fuel lo ((lo + hi) / 2) +
            splitsGo key fp S C fuel ((lo + hi) / 2) hi
          ≤ 1 + dL * c + dR * c := by omega
        _ = 1 + (dL + dR) * c := by rw [Nat.add_mul, Nat.add_assoc]
        _ ≤ (dL + dR) * (c + 1) := by
          rw [Nat.mul_succ]
          generalize (dL + dR) * c = P
          omega

/-- **A5.** The run splits at most `|Δ| · ⌈log₂ (hi - lo)⌉` ranges, whatever the
fingerprint. -/
theorem rbsrSplits_le (key : α → Nat) (fp : Finset α → H) (S C : Finset α) (lo hi : Nat) :
    rbsrSplits key fp S C lo hi ≤
      (sliceRange key S lo hi ∆ sliceRange key C lo hi).card * Nat.clog 2 (hi - lo) :=
  splitsGo_le key fp S C _ lo hi

/-! ### The fuel covers the recursion -/

theorem diffGo_fuel_stable (key : α → Nat) (fp : Finset α → H) (S C : Finset α) :
    ∀ f g lo hi, hi - lo ≤ f + 1 → hi - lo ≤ g + 1 →
      diffGo key fp S C f lo hi = diffGo key fp S C g lo hi
  | 0, 0, _, _, _, _ => rfl
  | 0, g + 1, lo, hi, hf, _ => by
    unfold diffGo
    split_ifs with h1 h2 <;> first | rfl | omega
  | f + 1, 0, lo, hi, _, hg => by
    unfold diffGo
    split_ifs with h1 h2 <;> first | rfl | omega
  | f + 1, g + 1, lo, hi, hf, hg => by
    unfold diffGo
    split_ifs with h1 h2
    · rfl
    · rfl
    · rw [diffGo_fuel_stable key fp S C f g lo _ (by omega) (by omega),
        diffGo_fuel_stable key fp S C f g _ hi (by omega) (by omega)]

end Core

/-! ## Fingerprints collide -/

section Collisions

/-- A fingerprint without collisions: different sets have different
fingerprints. -/
def CollisionFreeFP {α H : Type} (fp : Finset α → H) : Prop :=
  ∀ A B : Finset α, fp A = fp B → A = B

/-- **A3.** A fingerprint with fewer values than there are sets collides. -/
theorem not_collisionFree_of_card_lt {α H : Type} [Fintype α] [Fintype H] [DecidableEq α]
    (fp : Finset α → H) (h : Fintype.card H < 2 ^ Fintype.card α) : ¬ CollisionFreeFP fp := by
  intro hcf
  have := Fintype.card_le_of_injective fp (fun A B hAB => hcf A B hAB)
  rw [Fintype.card_finset] at this
  omega

theorem not_collisionFree_fin {n m : Nat} (fp : Finset (Fin n) → Fin m) (h : m < 2 ^ n) :
    ¬ CollisionFreeFP fp :=
  not_collisionFree_of_card_lt fp (by rw [Fintype.card_fin, Fintype.card_fin]; exact h)

theorem two_pow_lt_two_pow {k j : Nat} (h : k < j) : 2 ^ k < 2 ^ j :=
  Nat.pow_lt_pow_right (by norm_num) h

/-- Negentropy's case: sets of 32-byte ids, 16-byte fingerprints. -/
theorem negentropy_not_collisionFree (fp : Finset (Fin (2 ^ 256)) → Fin (2 ^ 128)) :
    ¬ CollisionFreeFP fp :=
  not_collisionFree_fin fp (two_pow_lt_two_pow (by norm_num))

/-- The data Negentropy hashes for a set: the sum of its ids modulo `2^256`, and
its count. -/
def fpSum {α : Type} (val : α → Nat) (A : Finset α) : Nat × Nat :=
  ((∑ x ∈ A, val x) % 2 ^ 256, A.card)

/-- Two different sets with one sum and one count. -/
theorem fpSum_collision :
    fpSum id ({0, 3} : Finset Nat) = fpSum id {1, 2} ∧ ({0, 3} : Finset Nat) ≠ {1, 2} := by
  decide

/-- Whatever hash follows, a fingerprint computed from `fpSum` collides on those
two sets. -/
theorem fingerprint_collision {H : Type} (hash : Nat × Nat → H) :
    hash (fpSum id ({0, 3} : Finset Nat)) = hash (fpSum id {1, 2}) :=
  congrArg hash fpSum_collision.1

end Collisions

/-! ## Non-vacuity and mutants -/

section Examples

/-- **A4.** `RunNoCollision` holds for `fpSum` on concrete different sets, and the
run then reports the one missing item. -/
example : RunNoCollision id (fpSum id) ({1, 2, 3} : Finset Nat) {1, 2} 0 4 ∧
    ({1, 2, 3} : Finset Nat) ≠ {1, 2} := by
  decide

example : rbsrDiff id (fpSum id) ({1, 2, 3} : Finset Nat) {1, 2} 0 4 = {3} := by
  decide

/-- The dense second: three events in second `10`, the client holding two. With
positions `16 · time + id`, the run reports the third. Paging by `until` with a
page of two cannot reach it. -/
example : rbsrDiff (fun e : Nat × Nat => e.1 * 16 + e.2) (fpSum Prod.snd)
    ({(10, 1), (10, 2), (10, 3)} : Finset (Nat × Nat)) {(10, 1), (10, 2)} 0 256 = {(10, 3)} := by
  decide

/-- `missed_in_colliding_range` with its hypotheses met: on a colliding pair the
run misses `0` and `3`, and the range it stopped at shows equal fingerprints of
different slices. -/
example : (0 : Nat) ∈ sliceRange id ({0, 3} : Finset Nat) 0 4 \ sliceRange id ({1, 2} : Finset Nat) 0 4 ∧
    (0 : Nat) ∉ rbsrDiff id (fpSum id) ({0, 3} : Finset Nat) {1, 2} 0 4 := by
  decide

/-- A leaf that forgets to remove the client's items. -/
def leafMutant {α H : Type} [DecidableEq α] [DecidableEq H] (key : α → Nat)
    (fp : Finset α → H) (S C : Finset α) (lo hi : Nat) : Finset α :=
  if fp (sliceRange key S lo hi) = fp (sliceRange key C lo hi) then ∅
  else sliceRange key S lo hi

/-- The mutant of `rbsrDiff_sound`: two items at one position, the client holding
one, and the mutant reports both. -/
theorem leafMutant_unsound :
    ¬ leafMutant (fun _ : Nat => 0) Finset.card ({0, 1} : Finset Nat) {0} 0 1 ⊆
      sliceRange (fun _ : Nat => 0) ({0, 1} : Finset Nat) 0 1 \
        sliceRange (fun _ : Nat => 0) {0} 0 1 := by
  decide

/-- A run that splits whether or not the fingerprints agree. -/
def splitMutant {α : Type} : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then 0
    else 1 + splitMutant (α := α) fuel lo ((lo + hi) / 2) + splitMutant (α := α) fuel ((lo + hi) / 2) hi

/-- The mutant of `rbsrSplits_le`: on two equal sets the bound is `0`, and the
mutant splits once. -/
theorem splitMutant_exceeds :
    ((sliceRange id ({0, 1} : Finset Nat) 0 2 ∆ sliceRange id ({0, 1} : Finset Nat) 0 2).card *
        Nat.clog 2 (2 - 0) = 0) ∧ splitMutant (α := Nat) (2 - 0) 0 2 = 1 := by
  decide

end Examples

end Mettapedia.Protocols.Sync.Rbsr
