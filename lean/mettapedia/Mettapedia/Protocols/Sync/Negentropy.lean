import Mathlib.Data.Finset.Max
import Mettapedia.Protocols.Sync.Rbsr

/-!
# Negentropy V1 between two parties

Negentropy (NIP-77) reconciles two sets by exchanging ranges of a sorted id space. This file
models the reference implementation, `cpp/negentropy.h` of hoytech/negentropy at `b368765`,
range by range:
- `initiate` (lines 48–58) splits everything;
- `answerGo` is `reconcileAux` (80–205). A pending skip is written only before the next range
  that is not a skip (101–107). A fingerprint that differs is split (117–126). The initiator
  records an id list's differences (136–156). The responder answers with its own id list, cut
  short when the frame fills (157–183);
- `split` is `splitRange` (207–255): fewer than `2 * B` items go as an id list, otherwise `B`
  buckets of nearly equal size with their fingerprints;
- a message that would pass the frame limit ends with one fingerprint for the rest (188–195).

An item is its sort key, a timestamp and an id ordered lexicographically, written as one natural
number. A message is a list of ranges whose lower bound is the previous range's upper bound, as
on the wire. The fingerprint is any function of a set, and a frame's size is any cost per range.

**The cut.** When a frame fills, the reference drops the current range's output and fingerprints
the remaining items from the current range's upper bound (line 190). The receiver reads that
range as starting at the last bound written, which is lower when the current range, or skipped
ranges before it, were not written. With both sides frame-limited, a responder can so send the
fingerprint of nothing for a range where it holds items, to an initiator that holds nothing
there, and the two fingerprints agree. `refCut_misses` is such a run, with an injective
fingerprint. The fixed rule (`fixCut`) starts the fingerprint at the last bound written.

Theorems:
- **B2** `run_sound`: every id reported as had is in `I \ R`, and every id reported as needed is
  in `R \ I`. Nothing is assumed of the fingerprint, the frame limits or the cut rule.
- **B3, B4** `run_complete`: with the fixed cut rule, a run that ends reports exactly `I \ R` and
  `R \ I`, with any frame limits on either side or none. Equal fingerprints must have covered
  equal sets: the run records whether they did (`ok`), or the fingerprint is injective.
- **B5**: items within one second are reconciled like any others (examples). Paging by time is
  not (`Nostr.Paging.walk_stopping_misses`).
- Mutant: `refCut_misses`, the reference's cut rule. `fixCut_finds` is the same run with the
  fixed rule, and meets `run_complete`'s hypotheses.

Not proved here: termination (B1) with its round bound, and that each frame fits its byte limit,
which needs the byte encoding. Termination needs a lower bound on the frame limit, like the
reference's 4096 bytes, so that an answer always writes at least one range before it cuts. The
responder's shortened id list is modelled by its bound (`idBound`), the largest that fits, not by
the reference's byte count.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Sync.Negentropy

open Finset
open Mettapedia.Protocols.Sync.Rbsr

/-- The items of `X` in `[lo, hi)`. An item is its sort key, a timestamp and an id
ordered lexicographically, written as one natural number. -/
abbrev slice (X : Finset ℕ) (lo hi : ℕ) : Finset ℕ := sliceRange id X lo hi

/-- What a range carries: the modes Skip, Fingerprint and IdList. -/
inductive Pay (H : Type) where
  | skip
  | fp (h : H)
  | ids (l : Finset ℕ)
  deriving DecidableEq

/-- A range of a message: its upper bound and what it carries. Its lower bound is the
previous range's upper bound, or `0` for the first range. -/
structure Rng (H : Type) where
  hi : ℕ
  pay : Pay H
  deriving DecidableEq

/-- A message: ranges in order. -/
abbrev Msg (H : Type) := List (Rng H)

section Wire

variable {H : Type}

/-- The ranges of a message with the lower bounds a receiver reads. -/
def wl : ℕ → Msg H → List (ℕ × Rng H)
  | _, [] => []
  | lo, r :: rs => (lo, r) :: wl r.hi rs

/-- The upper bound of a message's last range, or `lo` for no range. -/
def lastB : ℕ → Msg H → ℕ
  | lo, [] => lo
  | _, r :: rs => lastB r.hi rs

end Wire

section Split

variable {H : Type}

/-- The item of rank `k` in `s`, counting from `0`; `⊤` if `s` has at most `k` items. -/
def kth (s : Finset ℕ) (k : ℕ) : WithTop ℕ :=
  (s.filter fun x => k < (s.filter (· ≤ x)).card).min

/-- Where bucket `j` of `B` ends among `n` items: each bucket holds `n / B` items, and the
first `n % B` hold one more (`negentropy.h:223–230`). -/
def bucketEnd (n B j : ℕ) : ℕ := j * (n / B) + min j (n % B)

/-- The upper bounds of the buckets: the first item of each next bucket, then `hi`. -/
def bucketBounds (B : ℕ) (s : Finset ℕ) (hi : ℕ) : List ℕ :=
  (List.range (B - 1)).map (fun j => WithTop.untopD hi (kth s (bucketEnd s.card B (j + 1)))) ++
    [hi]

/-- Fingerprinted ranges over a chain of bounds starting at `lo`. -/
def fpRanges (fp : Finset ℕ → H) (X : Finset ℕ) : ℕ → List ℕ → Msg H
  | _, [] => []
  | lo, b :: bs => ⟨b, .fp (fp (slice X lo b))⟩ :: fpRanges fp X b bs

/-- `splitRange` (`negentropy.h:207–255`): fewer than `2 * B` items go as an id list,
otherwise `B` fingerprinted buckets. -/
def split (B : ℕ) (fp : Finset ℕ → H) (X : Finset ℕ) (lo hi : ℕ) : Msg H :=
  if (slice X lo hi).card < 2 * B then [⟨hi, .ids (slice X lo hi)⟩]
  else fpRanges fp X lo (bucketBounds B (slice X lo hi) hi)

end Split

/-- One party's settings. -/
structure Cfg (H : Type) where
  /-- Buckets per split; the reference uses 16. -/
  B : ℕ
  /-- The fingerprint of a set of items. -/
  fp : Finset ℕ → H
  /-- The size of one range in a frame. -/
  rcost : Rng H → ℕ
  /-- The frame limit less the room kept for a last range; `none` for no limit. -/
  limit : Option ℕ
  /-- Where the remaining range's fingerprint starts, given the last bound written and the
  current range's upper bound. -/
  cut : ℕ → ℕ → ℕ
  /-- The infinite bound: every item lies below it. -/
  top : ℕ

/-- The reference starts the remaining range's fingerprint at the current range's upper
bound (`negentropy.h:190`). -/
def refCut (_emitted hi : ℕ) : ℕ := hi

/-- The fix starts it at the last bound written, where the receiver reads it to start. -/
def fixCut (emitted _hi : ℕ) : ℕ := emitted

section Answer

variable {H : Type} [DecidableEq H]

/-- The frame size of a message. -/
def Cfg.cost (c : Cfg H) (m : Msg H) : ℕ := (m.map c.rcost).sum

/-- Whether a message is over the frame limit. -/
def Cfg.over (c : Cfg H) (m : Msg H) : Bool :=
  match c.limit with
  | none => false
  | some L => decide (L < c.cost m)

/-- Where the responder's id list stops when the frame fills (`negentropy.h:160–174`):
`hi` when the whole list fits, otherwise the largest item below which the list fits,
otherwise the least item. -/
def idBound (c : Cfg H) (pre : Msg H) (X : Finset ℕ) (lo hi : ℕ) : ℕ :=
  let fits : ℕ → Bool := fun b => !c.over (pre ++ [⟨b, .ids (slice X lo b)⟩])
  if fits hi then hi
  else WithBot.unbotD (WithTop.untopD hi (slice X lo hi).min)
    ((slice X lo hi).filter fun b => fits b).max

/-- A pending skip, written just before the next range that is not a skip
(`negentropy.h:101–107`). -/
def flushOf (skipping : Bool) (prev : ℕ) : Msg H := if skipping then [⟨prev, .skip⟩] else []

/-- What answering a message gives: the reply, the ids found to be had and needed, and
whether every equal fingerprint covered equal sets. -/
structure Answer (H : Type) where
  msg : Msg H
  have_ : Finset ℕ
  need : Finset ℕ
  ok : Bool

/-- `reconcileAux` (`negentropy.h:80–205`), one range at a time. `prev` is the previous
range's upper bound, `skipping` says a skip is pending, and `emitted` is the last bound
written to `out`. `X` holds the answering party's items. `Y` holds the other party's and
is used only to record, in `ok`, whether an equal fingerprint covered different sets.
A range that writes nothing cannot fill the frame, so it is not checked against the
limit. -/
def answerGo (c : Cfg H) (init : Bool) (X Y : Finset ℕ) :
    ℕ → Bool → ℕ → Msg H → Finset ℕ → Finset ℕ → Bool → Msg H → Answer H
  | _, _, _, out, hv, nd, ok, [] => ⟨out, hv, nd, ok⟩
  | prev, skipping, emitted, out, hv, nd, ok, r :: rest =>
    let flush : Msg H := flushOf skipping prev
    match r.pay with
    | .skip => answerGo c init X Y r.hi true emitted out hv nd ok rest
    | .fp h =>
      if c.fp (slice X prev r.hi) = h then
        answerGo c init X Y r.hi true emitted out hv nd
          (ok && decide (slice X prev r.hi = slice Y prev r.hi)) rest
      else
        let o := flush ++ split c.B c.fp X prev r.hi
        if c.over (out ++ o) then
          ⟨out ++ [⟨c.top, .fp (c.fp (slice X (c.cut emitted r.hi) c.top))⟩], hv, nd, ok⟩
        else answerGo c init X Y r.hi false r.hi (out ++ o) hv nd ok rest
    | .ids l =>
      if init then
        answerGo c init X Y r.hi true emitted out
          (hv ∪ (slice X prev r.hi \ l)) (nd ∪ (l \ slice X prev r.hi)) ok rest
      else
        let b := idBound c (out ++ flush) X prev r.hi
        let out' := out ++ flush ++ [⟨b, .ids (slice X prev b)⟩]
        if b = r.hi ∧ c.over out' = false then
          answerGo c init X Y r.hi false r.hi out' hv nd ok rest
        else ⟨out' ++ [⟨c.top, .fp (c.fp (slice X (c.cut b b) c.top))⟩], hv, nd, ok⟩

/-- A party's answer to a message. -/
def answer (c : Cfg H) (init : Bool) (X Y : Finset ℕ) (m : Msg H) : Answer H :=
  answerGo c init X Y 0 false 0 [] ∅ ∅ true m

/-- The initiator's first message (`negentropy.h:48–58`): a split of everything. -/
def initiate (c : Cfg H) (I : Finset ℕ) : Msg H := split c.B c.fp I 0 c.top

/-- A party's settings with its own frame limit. -/
def Cfg.withLimit (c : Cfg H) (L : Option ℕ) : Cfg H := { c with limit := L }

/-- Rounds between the initiator `I` and the responder `R`. It ends when the initiator's
answer is empty, with the ids had and needed and the no-collision record. -/
def runGo (c : Cfg H) (lI lR : Option ℕ) (I R : Finset ℕ) :
    ℕ → Msg H → Finset ℕ → Finset ℕ → Bool → Option (Finset ℕ × Finset ℕ × Bool)
  | 0, _, _, _, _ => none
  | fuel + 1, m, hv, nd, ok =>
    let aR := answer (c.withLimit lR) false R I m
    let aI := answer (c.withLimit lI) true I R aR.msg
    if aI.msg = [] then some (hv ∪ aI.have_, nd ∪ aI.need, ok && aR.ok && aI.ok)
    else runGo c lI lR I R fuel aI.msg (hv ∪ aI.have_) (nd ∪ aI.need) (ok && aR.ok && aI.ok)

/-- A whole reconciliation within `fuel` rounds. -/
def run (c : Cfg H) (lI lR : Option ℕ) (I R : Finset ℕ) (fuel : ℕ) :
    Option (Finset ℕ × Finset ℕ × Bool) :=
  runGo c lI lR I R fuel (initiate (c.withLimit lI) I) ∅ ∅ true

end Answer

/-! ## Reading a message -/

section Reading

variable {H : Type}

@[simp] theorem wl_nil (lo : ℕ) : wl lo ([] : Msg H) = [] := rfl

@[simp] theorem wl_cons (lo : ℕ) (r : Rng H) (rs : Msg H) :
    wl lo (r :: rs) = (lo, r) :: wl r.hi rs := rfl

@[simp] theorem lastB_nil (lo : ℕ) : lastB lo ([] : Msg H) = lo := rfl

@[simp] theorem lastB_cons (lo : ℕ) (r : Rng H) (rs : Msg H) :
    lastB lo (r :: rs) = lastB r.hi rs := rfl

theorem wl_append (lo : ℕ) (a b : Msg H) : wl lo (a ++ b) = wl lo a ++ wl (lastB lo a) b := by
  induction a generalizing lo with
  | nil => rfl
  | cons r rs ih => simp [ih]

theorem lastB_append (lo : ℕ) (a b : Msg H) : lastB lo (a ++ b) = lastB (lastB lo a) b := by
  induction a generalizing lo with
  | nil => rfl
  | cons r rs ih => simp [ih]

/-- Each range's lower bound is at most its upper bound, which is at most `top`. -/
def Mono (top : ℕ) (ps : List (ℕ × Rng H)) : Prop := ∀ p ∈ ps, p.1 ≤ p.2.hi ∧ p.2.hi ≤ top

/-- Every id list names exactly the sender's items in its range. -/
def IdsHonest (Y : Finset ℕ) (ps : List (ℕ × Rng H)) : Prop :=
  ∀ p ∈ ps, ∀ l, p.2.pay = .ids l → l = slice Y p.1 p.2.hi

/-- Every id list and every fingerprint is of the sender's items in its range. -/
def Honest (fp : Finset ℕ → H) (Y : Finset ℕ) (ps : List (ℕ × Rng H)) : Prop :=
  IdsHonest Y ps ∧ ∀ p ∈ ps, ∀ h, p.2.pay = .fp h → h = fp (slice Y p.1 p.2.hi)

/-- Every item of `D` lies in a range that is not a skip. -/
def Covers (D : Finset ℕ) (ps : List (ℕ × Rng H)) : Prop :=
  ∀ x ∈ D, ∃ p ∈ ps, p.1 ≤ x ∧ x < p.2.hi ∧ p.2.pay ≠ .skip

theorem mem_slice {X : Finset ℕ} {lo hi x : ℕ} : x ∈ slice X lo hi ↔ x ∈ X ∧ lo ≤ x ∧ x < hi := by
  simp [slice, mem_sliceRange]

/-- In an ordered message, every range starts at or after where the message starts. -/
theorem lower_ge {top lo : ℕ} {rs : Msg H} (h : Mono top (wl lo rs)) :
    ∀ p ∈ wl lo rs, lo ≤ p.1 := by
  induction rs generalizing lo with
  | nil => simp
  | cons r rs ih =>
    intro p hp
    have hr := h (lo, r) (by simp)
    simp only [wl_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact le_rfl
    · exact le_trans hr.1 (ih (fun q hq => h q (by simp [hq])) p hp)

/-- An item at or above the first range's upper bound lies in a later range. -/
theorem mem_tail_of_ge {lo x : ℕ} {r : Rng H} {rs : Msg H} {p : ℕ × Rng H}
    (hp : p ∈ wl lo (r :: rs)) (hx : r.hi ≤ x) (hpx : x < p.2.hi) : p ∈ wl r.hi rs := by
  simp only [wl_cons, List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact absurd hpx (by simpa using hx)
  · exact hp

end Reading

/-! ## The split -/

section SplitFacts

variable {H : Type}

theorem fpRanges_honest (fp : Finset ℕ → H) (X : Finset ℕ) :
    ∀ (lo : ℕ) (bs : List ℕ), Honest fp X (wl lo (fpRanges fp X lo bs))
  | _, [] => by simp [Honest, IdsHonest, fpRanges]
  | lo, b :: bs => by
    obtain ⟨ih1, ih2⟩ := fpRanges_honest fp X b bs
    refine ⟨fun p hp l hl => ?_, fun p hp h hh => ?_⟩
    · simp only [fpRanges, wl_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp at hl
      · exact ih1 p hp l hl
    · simp only [fpRanges, wl_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp only [Pay.fp.injEq] at hh
        exact hh.symm
      · exact ih2 p hp h hh

theorem fpRanges_mono (fp : Finset ℕ → H) (X : Finset ℕ) (top : ℕ) :
    ∀ (lo : ℕ) (bs : List ℕ), (∀ b ∈ bs, lo ≤ b ∧ b ≤ top) → bs.Pairwise (· ≤ ·) →
      Mono top (wl lo (fpRanges fp X lo bs))
  | _, [], _, _ => by simp [Mono, fpRanges]
  | lo, b :: bs, hb, hs => by
    intro p hp
    simp only [fpRanges, wl_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hb b (by simp)
    · have hs' := List.pairwise_cons.1 hs
      exact fpRanges_mono fp X top b bs
        (fun b' hb' => ⟨hs'.1 b' hb', (hb b' (by simp [hb'])).2⟩) hs'.2 p hp

theorem fpRanges_covers (fp : Finset ℕ → H) (X : Finset ℕ) :
    ∀ (lo : ℕ) (bs : List ℕ) (x : ℕ), lo ≤ x → x < lastB lo (fpRanges fp X lo bs) →
      ∃ p ∈ wl lo (fpRanges fp X lo bs), p.1 ≤ x ∧ x < p.2.hi ∧ p.2.pay ≠ .skip
  | lo, [], x, h1, h2 => by simp [fpRanges] at h2; omega
  | lo, b :: bs, x, h1, h2 => by
    by_cases hx : x < b
    · exact ⟨(lo, ⟨b, .fp (fp (slice X lo b))⟩), by simp [fpRanges], h1, hx, by simp⟩
    · simp only [fpRanges, lastB_cons] at h2
      obtain ⟨p, hp, hp'⟩ := fpRanges_covers fp X b bs x (by omega) h2
      exact ⟨p, by simp [fpRanges, hp], hp'⟩

theorem lastB_fpRanges_concat (fp : Finset ℕ → H) (X : Finset ℕ) (hi : ℕ) :
    ∀ (lo : ℕ) (bs : List ℕ), lastB lo (fpRanges fp X lo (bs ++ [hi])) = hi
  | _, [] => by simp [fpRanges]
  | _, b :: bs => by simp [fpRanges, lastB_fpRanges_concat fp X hi b bs]

theorem kth_mem {s : Finset ℕ} {k x : ℕ} (h : kth s k = x) : x ∈ s :=
  (Finset.mem_filter.1 (Finset.mem_of_min h)).1

theorem kth_mono (s : Finset ℕ) {k k' : ℕ} (h : k ≤ k') : kth s k ≤ kth s k' := by
  unfold kth
  apply Finset.min_mono
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, lt_of_le_of_lt h hx.2⟩

theorem untopD_kth {s : Finset ℕ} {lo hi : ℕ} (hs : ∀ x ∈ s, lo ≤ x ∧ x < hi) (hlo : lo ≤ hi)
    (k : ℕ) : lo ≤ WithTop.untopD hi (kth s k) ∧ WithTop.untopD hi (kth s k) ≤ hi := by
  induction h : kth s k using WithTop.recTopCoe with
  | top => simp [hlo]
  | coe x =>
    have := hs x (kth_mem h)
    simp only [WithTop.untopD_coe]
    omega

theorem untopD_kth_mono {s : Finset ℕ} {hi : ℕ} (hs : ∀ x ∈ s, x < hi) {k k' : ℕ} (h : k ≤ k') :
    WithTop.untopD hi (kth s k) ≤ WithTop.untopD hi (kth s k') := by
  have hm := kth_mono s h
  induction h2 : kth s k' using WithTop.recTopCoe with
  | top =>
    have := (untopD_kth (lo := 0) (fun x hx => ⟨Nat.zero_le x, hs x hx⟩) (Nat.zero_le hi) k).2
    simpa using this
  | coe b =>
    rw [h2] at hm
    induction h1 : kth s k using WithTop.recTopCoe with
    | top => rw [h1] at hm; exact absurd hm (by simp)
    | coe a =>
      rw [h1] at hm
      simpa using WithTop.coe_le_coe.1 hm

theorem bucketEnd_mono (n B : ℕ) {j j' : ℕ} (h : j ≤ j') : bucketEnd n B j ≤ bucketEnd n B j' := by
  unfold bucketEnd
  have := Nat.mul_le_mul_right (n / B) h
  have := min_le_min_right (n % B) h
  omega

theorem bucketBounds_mem {B : ℕ} {s : Finset ℕ} {lo hi : ℕ} (hs : ∀ x ∈ s, lo ≤ x ∧ x < hi)
    (hlo : lo ≤ hi) : ∀ b ∈ bucketBounds B s hi, lo ≤ b ∧ b ≤ hi := by
  intro b hb
  simp only [bucketBounds, List.mem_append, List.mem_map, List.mem_range,
    List.mem_singleton] at hb
  rcases hb with ⟨j, _, rfl⟩ | rfl
  · exact untopD_kth hs hlo _
  · exact ⟨hlo, le_rfl⟩

theorem bucketBounds_sorted {B : ℕ} {s : Finset ℕ} {hi : ℕ} (hs : ∀ x ∈ s, x < hi) :
    (bucketBounds B s hi).Pairwise (· ≤ ·) := by
  unfold bucketBounds
  rw [List.pairwise_append]
  refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
  · exact List.Pairwise.map _
      (fun a b hab => untopD_kth_mono hs (bucketEnd_mono _ _ (by omega))) List.pairwise_lt_range
  · intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    simp only [List.mem_map] at ha
    obtain ⟨j, _, rfl⟩ := ha
    exact (untopD_kth (lo := 0) (fun x hx => ⟨Nat.zero_le x, hs x hx⟩) (Nat.zero_le _) _).2

variable (B : ℕ) (fp : Finset ℕ → H) (X : Finset ℕ)

theorem split_honest (lo hi : ℕ) : Honest fp X (wl lo (split B fp X lo hi)) := by
  unfold split
  split_ifs
  · refine ⟨fun p hp l hl => ?_, fun p hp h hh => ?_⟩ <;>
      simp only [wl_cons, wl_nil, List.mem_singleton] at hp <;> subst hp
    · simp only [Pay.ids.injEq] at hl
      exact hl.symm
    · simp at hh
  · exact fpRanges_honest fp X lo _

theorem lastB_split (lo hi : ℕ) : lastB lo (split B fp X lo hi) = hi := by
  unfold split
  split_ifs
  · simp
  · exact lastB_fpRanges_concat fp X hi lo _

theorem split_mono {lo hi top : ℕ} (hlo : lo ≤ hi) (htop : hi ≤ top) :
    Mono top (wl lo (split B fp X lo hi)) := by
  have hs : ∀ x ∈ slice X lo hi, lo ≤ x ∧ x < hi := fun x hx => (mem_slice.1 hx).2
  unfold split
  split_ifs
  · intro p hp
    simp only [wl_cons, wl_nil, List.mem_singleton] at hp
    subst hp
    exact ⟨hlo, htop⟩
  · apply fpRanges_mono
    · intro b hb
      have := bucketBounds_mem hs hlo b hb
      exact ⟨this.1, le_trans this.2 htop⟩
    · exact bucketBounds_sorted (fun x hx => (hs x hx).2)

theorem split_covers {lo hi x : ℕ} (h1 : lo ≤ x) (h2 : x < hi) :
    ∃ p ∈ wl lo (split B fp X lo hi), p.1 ≤ x ∧ x < p.2.hi ∧ p.2.pay ≠ .skip := by
  unfold split
  split_ifs
  · exact ⟨(lo, ⟨hi, .ids (slice X lo hi)⟩), by simp, h1, h2, by simp⟩
  · apply fpRanges_covers fp X lo _ x h1
    unfold bucketBounds
    rw [lastB_fpRanges_concat]
    exact h2

end SplitFacts

/-! ## Answering, range by range -/

section Fold

variable {H : Type}

theorem forall_append {P : ℕ × Rng H → Prop} {a b : List (ℕ × Rng H)} :
    (∀ p ∈ a ++ b, P p) ↔ (∀ p ∈ a, P p) ∧ (∀ p ∈ b, P p) := List.forall_mem_append

theorem lastB_flush (skipping : Bool) {emitted prev : ℕ} (h : skipping = false → emitted = prev) :
    lastB emitted (flushOf skipping prev : Msg H) = prev := by
  cases skipping
  · simp [flushOf, h rfl]
  · simp [flushOf]

theorem wl_flush (skipping : Bool) (emitted prev : ℕ) :
    wl emitted (flushOf skipping prev : Msg H) =
      if skipping then [(emitted, ⟨prev, .skip⟩)] else [] := by
  cases skipping <;> rfl

/-- Writing a pending skip and then `o`: the receiver reads `o` from `prev`. -/
theorem wl_emit {out : Msg H} {emitted prev : ℕ} (skipping : Bool) (hl : lastB 0 out = emitted)
    (hf : skipping = false → emitted = prev) (o : Msg H) :
    wl 0 (out ++ (flushOf skipping prev ++ o)) =
      wl 0 out ++ ((if skipping then [(emitted, ⟨prev, .skip⟩)] else []) ++ wl prev o) ∧
    lastB 0 (out ++ (flushOf skipping prev ++ o)) = lastB prev o := by
  rw [wl_append, wl_append, lastB_append, lastB_append, hl, wl_flush, lastB_flush skipping hf]
  exact ⟨rfl, rfl⟩

theorem flush_quiet (skipping : Bool) (emitted prev : ℕ) :
    ∀ p ∈ (if skipping then [(emitted, (⟨prev, .skip⟩ : Rng H))] else []), p.2.pay = .skip := by
  cases skipping <;> simp

variable [DecidableEq H] (c : Cfg H) (init : Bool) (X Y : Finset ℕ)

/-- The record of collisions only ever turns false. -/
theorem answerGo_ok : ∀ (rs : Msg H) (prev : ℕ) (skipping : Bool) (emitted : ℕ) (out : Msg H)
    (hv nd : Finset ℕ) (ok : Bool),
    (answerGo c init X Y prev skipping emitted out hv nd ok rs).ok = true → ok = true
  | [], _, _, _, _, _, _, _, h => h
  | ⟨hi, .skip⟩ :: rest, _, _, _, _, _, _, _, h => by
    simp only [answerGo] at h
    exact answerGo_ok rest _ _ _ _ _ _ _ h
  | ⟨hi, .fp f⟩ :: rest, _, _, _, _, _, _, _, h => by
    simp only [answerGo] at h
    split_ifs at h
    · have := answerGo_ok rest _ _ _ _ _ _ _ h
      simp only [Bool.and_eq_true] at this
      exact this.1
    · exact h
    · exact answerGo_ok rest _ _ _ _ _ _ _ h
  | ⟨hi, .ids l⟩ :: rest, _, _, _, _, _, _, _, h => by
    simp only [answerGo] at h
    split_ifs at h
    · exact answerGo_ok rest _ _ _ _ _ _ _ h
    · exact answerGo_ok rest _ _ _ _ _ _ _ h
    · exact h

/-- The responder finds nothing had or needed. -/
theorem answerGo_responder : ∀ (rs : Msg H) (prev : ℕ) (skipping : Bool) (emitted : ℕ)
    (out : Msg H) (hv nd : Finset ℕ) (ok : Bool),
    (answerGo c false X Y prev skipping emitted out hv nd ok rs).have_ = hv ∧
      (answerGo c false X Y prev skipping emitted out hv nd ok rs).need = nd
  | [], _, _, _, _, _, _, _ => ⟨rfl, rfl⟩
  | ⟨hi, .skip⟩ :: rest, _, _, _, _, _, _, _ => by
    simp only [answerGo]
    exact answerGo_responder rest _ _ _ _ _ _ _
  | ⟨hi, .fp f⟩ :: rest, _, _, _, _, _, _, _ => by
    simp only [answerGo]
    split_ifs
    · exact answerGo_responder rest _ _ _ _ _ _ _
    · exact ⟨rfl, rfl⟩
    · exact answerGo_responder rest _ _ _ _ _ _ _
  | ⟨hi, .ids l⟩ :: rest, _, _, _, _, _, _, _ => by
    simp only [answerGo, Bool.false_eq_true, if_false]
    split_ifs
    · exact answerGo_responder rest _ _ _ _ _ _ _
    · exact ⟨rfl, rfl⟩

/-- Every id list a party writes names exactly its items in the range the receiver reads,
whatever the cut rule. -/
theorem answerGo_idsHonest : ∀ (rs : Msg H) (prev : ℕ) (skipping : Bool) (emitted : ℕ)
    (out : Msg H) (hv nd : Finset ℕ) (ok : Bool),
    lastB 0 out = emitted → (skipping = false → emitted = prev) → IdsHonest X (wl 0 out) →
    IdsHonest X (wl 0 (answerGo c init X Y prev skipping emitted out hv nd ok rs).msg)
  | [], _, _, _, _, _, _, _, _, _, h => h
  | ⟨hi, .skip⟩ :: rest, _, _, _, out, _, _, _, hl, _, h => by
    simp only [answerGo]
    exact answerGo_idsHonest rest _ _ _ out _ _ _ hl (by simp) h
  | ⟨hi, .fp f⟩ :: rest, prev, skipping, emitted, out, hv, nd, ok, hl, hf, h => by
    simp only [answerGo]
    split_ifs
    · exact answerGo_idsHonest rest _ _ _ out _ _ _ hl (by simp) h
    · rw [wl_append]
      refine forall_append.2 ⟨h, ?_⟩
      intro p hp l hl'
      simp only [wl_cons, wl_nil, List.mem_singleton] at hp
      subst hp
      simp at hl'
    · obtain ⟨hw, hlast⟩ := wl_emit skipping hl hf (split c.B c.fp X prev hi)
      refine answerGo_idsHonest rest _ _ _ _ _ _ _ (by rw [hlast, lastB_split]) (by simp) ?_
      rw [hw]
      refine forall_append.2 ⟨h, forall_append.2 ⟨?_, (split_honest c.B c.fp X prev hi).1⟩⟩
      intro p hp l hl'
      rw [flush_quiet skipping emitted prev p hp] at hl'
      simp at hl'
  | ⟨hi, .ids l⟩ :: rest, prev, skipping, emitted, out, hv, nd, ok, hl, hf, h => by
    simp only [answerGo]
    set b := idBound c (out ++ flushOf skipping prev) X prev hi
    have hchunk := wl_emit skipping hl hf [⟨b, .ids (slice X prev b)⟩]
    have hc : IdsHonest X (wl 0 (out ++ (flushOf skipping prev ++
        [⟨b, .ids (slice X prev b)⟩]))) := by
      rw [hchunk.1]
      refine forall_append.2 ⟨h, forall_append.2 ⟨?_, ?_⟩⟩
      · intro p hp l hl'
        rw [flush_quiet skipping emitted prev p hp] at hl'
        simp at hl'
      · intro p hp l hl'
        simp only [wl_cons, wl_nil, List.mem_singleton] at hp
        subst hp
        simp only [Pay.ids.injEq] at hl'
        exact hl'.symm
    split_ifs with hi1 hi2
    · exact answerGo_idsHonest rest _ _ _ out _ _ _ hl (by simp) h
    · rw [List.append_assoc]
      refine answerGo_idsHonest rest _ _ _ _ _ _ _ ?_ (by simp) hc
      rw [hchunk.2]
      simp [hi2.1]
    · rw [wl_append, List.append_assoc]
      refine forall_append.2 ⟨hc, ?_⟩
      intro p hp l hl'
      simp only [wl_cons, wl_nil, List.mem_singleton] at hp
      subst hp
      simp at hl'

/-- The initiator records as had only items the responder lacks, and as needed only items
the responder holds and it lacks, given honest id lists. -/
theorem answerGo_sound : ∀ (rs : Msg H) (prev : ℕ) (skipping : Bool) (emitted : ℕ)
    (out : Msg H) (hv nd : Finset ℕ) (ok : Bool),
    IdsHonest Y (wl prev rs) → hv ⊆ X \ Y → nd ⊆ Y \ X →
    (answerGo c init X Y prev skipping emitted out hv nd ok rs).have_ ⊆ X \ Y ∧
      (answerGo c init X Y prev skipping emitted out hv nd ok rs).need ⊆ Y \ X
  | [], _, _, _, _, _, _, _, _, h1, h2 => ⟨h1, h2⟩
  | ⟨hi, .skip⟩ :: rest, _, _, _, _, _, _, _, hy, h1, h2 => by
    simp only [answerGo]
    exact answerGo_sound rest _ _ _ _ _ _ _ (fun p hp => hy p (by simp [hp])) h1 h2
  | ⟨hi, .fp f⟩ :: rest, _, _, _, _, _, _, _, hy, h1, h2 => by
    simp only [answerGo]
    split_ifs
    · exact answerGo_sound rest _ _ _ _ _ _ _ (fun p hp => hy p (by simp [hp])) h1 h2
    · exact ⟨h1, h2⟩
    · exact answerGo_sound rest _ _ _ _ _ _ _ (fun p hp => hy p (by simp [hp])) h1 h2
  | ⟨hi, .ids l⟩ :: rest, prev, _, _, _, hv, nd, _, hy, h1, h2 => by
    have hl : l = slice Y prev hi := hy (prev, ⟨hi, .ids l⟩) (by simp) l rfl
    simp only [answerGo]
    split_ifs
    · refine answerGo_sound rest _ _ _ _ _ _ _ (fun p hp => hy p (by simp [hp])) ?_ ?_
      · refine Finset.union_subset h1 (fun x hx => ?_)
        rw [Finset.mem_sdiff, hl, mem_slice, mem_slice] at hx
        exact Finset.mem_sdiff.2 ⟨hx.1.1, fun hy' => hx.2 ⟨hy', hx.1.2⟩⟩
      · refine Finset.union_subset h2 (fun x hx => ?_)
        rw [Finset.mem_sdiff, hl, mem_slice, mem_slice] at hx
        exact Finset.mem_sdiff.2 ⟨hx.1.1, fun hx' => hx.2 ⟨hx', hx.1.2⟩⟩
    · exact answerGo_sound rest _ _ _ _ _ _ _ (fun p hp => hy p (by simp [hp])) h1 h2
    · exact ⟨h1, h2⟩

end Fold

/-! ## B2: soundness, with no assumption on the fingerprint or the cut rule -/

section Soundness

variable {H : Type} [DecidableEq H]

theorem runGo_sound (c : Cfg H) (lI lR : Option ℕ) (I R : Finset ℕ) :
    ∀ (fuel : ℕ) (m : Msg H) (hv nd : Finset ℕ) (ok : Bool) (hv' nd' : Finset ℕ) (ok' : Bool),
    hv ⊆ I \ R → nd ⊆ R \ I → runGo c lI lR I R fuel m hv nd ok = some (hv', nd', ok') →
    hv' ⊆ I \ R ∧ nd' ⊆ R \ I
  | 0, _, _, _, _, _, _, _, _, _, h => by simp [runGo] at h
  | fuel + 1, m, hv, nd, ok, hv', nd', ok', h1, h2, h => by
    simp only [runGo] at h
    have hR := answerGo_idsHonest (c.withLimit lR) false R I m 0 false 0 [] ∅ ∅ true rfl
      (fun _ => rfl) (by simp [IdsHonest])
    obtain ⟨hs1, hs2⟩ := answerGo_sound (c.withLimit lI) true I R
      (answer (c.withLimit lR) false R I m).msg 0 false 0 [] ∅ ∅ true hR
      (Finset.empty_subset _) (Finset.empty_subset _)
    split_ifs at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨Finset.union_subset h1 hs1, Finset.union_subset h2 hs2⟩
    · exact runGo_sound c lI lR I R fuel _ _ _ _ hv' nd' ok'
        (Finset.union_subset h1 hs1) (Finset.union_subset h2 hs2) h

/-- **B2.** Every id the initiator reports as had is the initiator's and not the responder's,
and every id it reports as needed is the responder's and not the initiator's. Nothing is
assumed of the fingerprint, the frame limits or the cut rule. -/
theorem run_sound (c : Cfg H) (lI lR : Option ℕ) (I R : Finset ℕ) (fuel : ℕ)
    {hv nd : Finset ℕ} {ok : Bool} (h : run c lI lR I R fuel = some (hv, nd, ok)) :
    hv ⊆ I \ R ∧ nd ⊆ R \ I :=
  runGo_sound c lI lR I R fuel _ ∅ ∅ true hv nd ok (Finset.empty_subset _)
    (Finset.empty_subset _) h

end Soundness

/-! ## B3 and B4: completeness under the fixed cut rule, with or without frame limits -/

section Completeness

variable {H : Type}

theorem mono_tail {top lo : ℕ} {r : Rng H} {rs : Msg H} (h : Mono top (wl lo (r :: rs))) :
    Mono top (wl r.hi rs) := fun p hp => h p (by simp [hp])

theorem honest_tail {fp : Finset ℕ → H} {Y : Finset ℕ} {lo : ℕ} {r : Rng H} {rs : Msg H}
    (h : Honest fp Y (wl lo (r :: rs))) : Honest fp Y (wl r.hi rs) :=
  ⟨fun p hp => h.1 p (by simp [hp]), fun p hp => h.2 p (by simp [hp])⟩

theorem not_mem_symmDiff {X Y : Finset ℕ} {lo hi x : ℕ} (h : slice X lo hi = slice Y lo hi)
    (h1 : lo ≤ x) (h2 : x < hi) : x ∉ symmDiff X Y := by
  intro hx
  rw [Finset.mem_symmDiff] at hx
  rcases hx with ⟨a, b⟩ | ⟨a, b⟩
  · have : x ∈ slice Y lo hi := h ▸ mem_slice.2 ⟨a, h1, h2⟩
    exact b (mem_slice.1 this).1
  · have : x ∈ slice X lo hi := h.symm ▸ mem_slice.2 ⟨a, h1, h2⟩
    exact b (mem_slice.1 this).1

theorem sdiff_union_mono {D hv nd A B : Finset ℕ} {x : ℕ} (hx : x ∈ D \ (hv ∪ A ∪ (nd ∪ B))) :
    x ∈ D \ (hv ∪ nd) := by
  simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at hx ⊢
  exact ⟨hx.1, hx.2.1.1, hx.2.2.1⟩

variable [DecidableEq H] (c : Cfg H) (init : Bool) (X Y D : Finset ℕ)

omit [DecidableEq H] in
theorem idBound_mem (pre : Msg H) {lo hi : ℕ} (h : lo ≤ hi) :
    lo ≤ idBound c pre X lo hi ∧ idBound c pre X lo hi ≤ hi := by
  simp only [idBound]
  split_ifs
  · exact ⟨h, le_rfl⟩
  · induction hm : (Finset.filter (fun b => (!c.over (pre ++ [⟨b, .ids (slice X lo b)⟩])) = true)
        (slice X lo hi)).max using WithBot.recBotCoe with
    | bot =>
      simp only [WithBot.unbotD_bot]
      induction hn : (slice X lo hi).min using WithTop.recTopCoe with
      | top => simp [h]
      | coe n =>
        have := mem_slice.1 (Finset.mem_of_min hn)
        simp only [WithTop.untopD_coe]
        omega
    | coe m =>
      have := mem_slice.1 (Finset.mem_filter.1 (Finset.mem_of_max hm)).1
      simp only [WithBot.unbotD_coe]
      omega

/-- What holds while a party answers: `out` is written so far, `rs` is still to be read
from `prev`, and the items of `D` not yet recorded are still to be found. -/
structure Inv (prev : ℕ) (skipping : Bool) (emitted : ℕ) (out : Msg H) (hv nd : Finset ℕ)
    (rs : Msg H) : Prop where
  last : lastB 0 out = emitted
  le : emitted ≤ prev
  flush : skipping = false → emitted = prev
  ptop : prev ≤ c.top
  mono : Mono c.top (wl 0 out)
  honest : Honest c.fp X (wl 0 out)
  /-- Below the last bound written, every item still to be found lies in a written range
  that is not a skip. -/
  done : ∀ x ∈ D \ (hv ∪ nd), x < emitted →
    ∃ q ∈ wl 0 out, q.1 ≤ x ∧ x < q.2.hi ∧ q.2.pay ≠ .skip
  /-- Between the last bound written and `prev`, read and found equal, nothing is left. -/
  quiet : ∀ x ∈ D \ (hv ∪ nd), emitted ≤ x → x < prev → False
  rmono : Mono c.top (wl prev rs)
  rhonest : Honest c.fp Y (wl prev rs)
  /-- From `prev` on, every item still to be found lies in an unread range that is not a
  skip. -/
  todo : ∀ x ∈ D \ (hv ∪ nd), prev ≤ x →
    ∃ p ∈ wl prev rs, p.1 ≤ x ∧ x < p.2.hi ∧ p.2.pay ≠ .skip

/-- With the fixed cut rule, a party's answer to an honest, ordered message that covers what
is still to be found is honest, ordered, and covers what is still to be found after it.
Equal fingerprints must cover equal sets: either every one in this answer did (`ok`), or the
fingerprint is injective. -/
theorem answerGo_complete (hcut : ∀ e h, c.cut e h = e) (hD : D ⊆ symmDiff X Y)
    (htop : ∀ x ∈ D, x < c.top) :
    ∀ (rs : Msg H) (prev : ℕ) (skipping : Bool) (emitted : ℕ) (out : Msg H)
      (hv nd : Finset ℕ) (ok : Bool),
    ((answerGo c init X Y prev skipping emitted out hv nd ok rs).ok = true ∨
      Function.Injective c.fp) →
    Inv c X Y D prev skipping emitted out hv nd rs →
    Mono c.top (wl 0 (answerGo c init X Y prev skipping emitted out hv nd ok rs).msg) ∧
      Honest c.fp X (wl 0 (answerGo c init X Y prev skipping emitted out hv nd ok rs).msg) ∧
      Covers (D \ ((answerGo c init X Y prev skipping emitted out hv nd ok rs).have_ ∪
        (answerGo c init X Y prev skipping emitted out hv nd ok rs).need))
        (wl 0 (answerGo c init X Y prev skipping emitted out hv nd ok rs).msg)
  | [], prev, skipping, emitted, out, hv, nd, ok, _, inv => by
    simp only [answerGo]
    refine ⟨inv.mono, inv.honest, fun x hx => ?_⟩
    by_cases h1 : x < emitted
    · exact inv.done x hx h1
    · by_cases h2 : x < prev
      · exact (inv.quiet x hx (by omega) h2).elim
      · obtain ⟨p, hp, _⟩ := inv.todo x hx (by omega)
        simp at hp
  | ⟨hi, .skip⟩ :: rest, prev, skipping, emitted, out, hv, nd, ok, hcoll, inv => by
    have hh := inv.rmono (prev, ⟨hi, .skip⟩) (by simp)
    simp only [answerGo] at hcoll ⊢
    refine answerGo_complete hcut hD htop rest hi true emitted out hv nd ok hcoll
      { last := inv.last, le := le_trans inv.le hh.1, flush := by simp, ptop := hh.2,
        mono := inv.mono, honest := inv.honest, done := inv.done,
        quiet := fun x hx h1 h2 => ?_, rmono := mono_tail inv.rmono,
        rhonest := honest_tail inv.rhonest, todo := fun x hx h1 => ?_ }
    · by_cases h3 : x < prev
      · exact inv.quiet x hx h1 h3
      · obtain ⟨p, hp, hp1, hp2, hp3⟩ := inv.todo x hx (by omega)
        simp only [wl_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact hp3 rfl
        · have := lower_ge (mono_tail inv.rmono) p hp
          simp only at this
          omega
    · obtain ⟨p, hp, hp'⟩ := inv.todo x hx (le_trans hh.1 h1)
      exact ⟨p, mem_tail_of_ge hp h1 hp'.2.1, hp'⟩
  | ⟨hi, .fp f⟩ :: rest, prev, skipping, emitted, out, hv, nd, ok, hcoll, inv => by
    have hh := inv.rmono (prev, ⟨hi, .fp f⟩) (by simp)
    have hf : f = c.fp (slice Y prev hi) := inv.rhonest.2 (prev, ⟨hi, .fp f⟩) (by simp) f rfl
    simp only [answerGo] at hcoll ⊢
    split_ifs at hcoll ⊢ with heq hover
    · have hsl : slice X prev hi = slice Y prev hi := by
        rcases hcoll with hcoll | hinj
        · have := answerGo_ok c init X Y rest _ _ _ _ _ _ _ hcoll
          simp only [Bool.and_eq_true, decide_eq_true_eq] at this
          exact this.2
        · exact hinj (heq.trans hf)
      refine answerGo_complete hcut hD htop rest hi true emitted out hv nd _ hcoll
        { last := inv.last, le := le_trans inv.le hh.1, flush := by simp, ptop := hh.2,
          mono := inv.mono, honest := inv.honest, done := inv.done,
          quiet := fun x hx h1 h2 => ?_, rmono := mono_tail inv.rmono,
          rhonest := honest_tail inv.rhonest, todo := fun x hx h1 => ?_ }
      · by_cases h3 : x < prev
        · exact inv.quiet x hx h1 h3
        · exact not_mem_symmDiff hsl (by omega) h2 (hD (Finset.mem_sdiff.1 hx).1)
      · obtain ⟨p, hp, hp'⟩ := inv.todo x hx (le_trans hh.1 h1)
        exact ⟨p, mem_tail_of_ge hp h1 hp'.2.1, hp'⟩
    · rw [hcut]
      have hw : wl 0 (out ++ [⟨c.top, .fp (c.fp (slice X emitted c.top))⟩]) =
          wl 0 out ++ [(emitted, ⟨c.top, .fp (c.fp (slice X emitted c.top))⟩)] := by
        rw [wl_append, inv.last]
        rfl
      rw [hw]
      refine ⟨forall_append.2 ⟨inv.mono, ?_⟩,
        ⟨forall_append.2 ⟨inv.honest.1, ?_⟩, forall_append.2 ⟨inv.honest.2, ?_⟩⟩, ?_⟩
      · intro p hp
        simp only [List.mem_singleton] at hp
        subst hp
        exact ⟨le_trans inv.le inv.ptop, le_rfl⟩
      · intro p hp l hl
        simp only [List.mem_singleton] at hp
        subst hp
        simp at hl
      · intro p hp h' hh'
        simp only [List.mem_singleton] at hp
        subst hp
        simp only [Pay.fp.injEq] at hh'
        exact hh'.symm
      · intro x hx
        by_cases h1 : x < emitted
        · obtain ⟨q, hq, hq'⟩ := inv.done x hx h1
          exact ⟨q, by simp [hq], hq'⟩
        · exact ⟨(emitted, ⟨c.top, .fp (c.fp (slice X emitted c.top))⟩), by simp, by omega,
            htop x (Finset.mem_sdiff.1 hx).1, by simp⟩
    · obtain ⟨hw, hlast⟩ := wl_emit skipping inv.last inv.flush (split c.B c.fp X prev hi)
      refine answerGo_complete hcut hD htop rest hi false hi _ hv nd ok hcoll
        { last := by rw [hlast, lastB_split], le := le_rfl, flush := fun _ => rfl, ptop := hh.2,
          mono := ?_, honest := ?_, done := fun x hx h1 => ?_, quiet := fun x _ h1 h2 => by omega,
          rmono := mono_tail inv.rmono, rhonest := honest_tail inv.rhonest,
          todo := fun x hx h1 => ?_ }
      · rw [hw]
        refine forall_append.2 ⟨inv.mono, forall_append.2 ⟨?_, split_mono c.B c.fp X hh.1 hh.2⟩⟩
        intro p hp
        cases skipping
        · simp at hp
        · simp only [if_true, List.mem_singleton] at hp
          subst hp
          exact ⟨inv.le, inv.ptop⟩
      · rw [hw]
        refine ⟨forall_append.2 ⟨inv.honest.1, forall_append.2 ⟨?_,
          (split_honest c.B c.fp X prev hi).1⟩⟩, forall_append.2 ⟨inv.honest.2,
          forall_append.2 ⟨?_, (split_honest c.B c.fp X prev hi).2⟩⟩⟩
        · intro p hp l hl
          rw [flush_quiet skipping emitted prev p hp] at hl
          simp at hl
        · intro p hp h' hh'
          rw [flush_quiet skipping emitted prev p hp] at hh'
          simp at hh'
      · rw [hw]
        by_cases h2 : x < emitted
        · obtain ⟨q, hq, hq'⟩ := inv.done x hx h2
          exact ⟨q, by simp [hq], hq'⟩
        · by_cases h3 : x < prev
          · exact (inv.quiet x hx (by omega) h3).elim
          · obtain ⟨q, hq, hq'⟩ := split_covers c.B c.fp X (lo := prev) (by omega) h1
            exact ⟨q, by simp [hq], hq'⟩
      · obtain ⟨p, hp, hp'⟩ := inv.todo x hx (le_trans hh.1 h1)
        exact ⟨p, mem_tail_of_ge hp h1 hp'.2.1, hp'⟩
  | ⟨hi, .ids l⟩ :: rest, prev, skipping, emitted, out, hv, nd, ok, hcoll, inv => by
    have hh := inv.rmono (prev, ⟨hi, .ids l⟩) (by simp)
    have hl : l = slice Y prev hi := inv.rhonest.1 (prev, ⟨hi, .ids l⟩) (by simp) l rfl
    simp only [answerGo] at hcoll ⊢
    set b := idBound c (out ++ flushOf skipping prev) X prev hi with hb
    have hbm : prev ≤ b ∧ b ≤ hi := idBound_mem c X (out ++ flushOf skipping prev) hh.1
    have hchunk := wl_emit skipping inv.last inv.flush [⟨b, .ids (slice X prev b)⟩]
    have hmono : Mono c.top
        (wl 0 (out ++ (flushOf skipping prev ++ [⟨b, .ids (slice X prev b)⟩]))) := by
      rw [hchunk.1]
      refine forall_append.2 ⟨inv.mono, forall_append.2 ⟨?_, ?_⟩⟩
      · intro p hp
        cases skipping
        · simp at hp
        · simp only [if_true, List.mem_singleton] at hp
          subst hp
          exact ⟨inv.le, inv.ptop⟩
      · intro p hp
        simp only [wl_cons, wl_nil, List.mem_singleton] at hp
        subst hp
        exact ⟨hbm.1, le_trans hbm.2 hh.2⟩
    have hhon : Honest c.fp X
        (wl 0 (out ++ (flushOf skipping prev ++ [⟨b, .ids (slice X prev b)⟩]))) := by
      rw [hchunk.1]
      refine ⟨forall_append.2 ⟨inv.honest.1, forall_append.2 ⟨?_, ?_⟩⟩,
        forall_append.2 ⟨inv.honest.2, forall_append.2 ⟨?_, ?_⟩⟩⟩
      · intro p hp l' hl'
        rw [flush_quiet skipping emitted prev p hp] at hl'
        simp at hl'
      · intro p hp l' hl'
        simp only [wl_cons, wl_nil, List.mem_singleton] at hp
        subst hp
        simp only [Pay.ids.injEq] at hl'
        exact hl'.symm
      · intro p hp h' hh'
        rw [flush_quiet skipping emitted prev p hp] at hh'
        simp at hh'
      · intro p hp h' hh'
        simp only [wl_cons, wl_nil, List.mem_singleton] at hp
        subst hp
        simp at hh'
    have hdone : ∀ x ∈ D \ (hv ∪ nd), x < b →
        ∃ q ∈ wl 0 (out ++ (flushOf skipping prev ++ [⟨b, .ids (slice X prev b)⟩])),
          q.1 ≤ x ∧ x < q.2.hi ∧ q.2.pay ≠ .skip := by
      intro x hx h1
      rw [hchunk.1]
      by_cases h2 : x < emitted
      · obtain ⟨q, hq, hq'⟩ := inv.done x hx h2
        exact ⟨q, by simp [hq], hq'⟩
      · by_cases h3 : x < prev
        · exact (inv.quiet x hx (by omega) h3).elim
        · exact ⟨(prev, ⟨b, .ids (slice X prev b)⟩), by simp, by omega, h1, by simp⟩
    split_ifs at hcoll ⊢ with hinit hfit
    · refine answerGo_complete hcut hD htop rest hi true emitted out _ _ ok hcoll
        { last := inv.last, le := le_trans inv.le hh.1, flush := by simp, ptop := hh.2,
          mono := inv.mono, honest := inv.honest,
          done := fun x hx h1 => inv.done x (sdiff_union_mono hx) h1,
          quiet := fun x hx h1 h2 => ?_, rmono := mono_tail inv.rmono,
          rhonest := honest_tail inv.rhonest, todo := fun x hx h1 => ?_ }
      · by_cases h3 : x < prev
        · exact inv.quiet x (sdiff_union_mono hx) h1 h3
        · have hx' := Finset.mem_sdiff.1 hx
          have hsd := hD hx'.1
          apply hx'.2
          rw [Finset.mem_symmDiff] at hsd
          simp only [Finset.mem_union, Finset.mem_sdiff, hl, mem_slice]
          rcases hsd with ⟨a, a'⟩ | ⟨a, a'⟩
          · exact Or.inl (Or.inr ⟨⟨a, by omega, h2⟩, fun hy => a' hy.1⟩)
          · exact Or.inr (Or.inr ⟨⟨a, by omega, h2⟩, fun hx'' => a' hx''.1⟩)
      · obtain ⟨p, hp, hp'⟩ := inv.todo x (sdiff_union_mono hx) (le_trans hh.1 h1)
        exact ⟨p, mem_tail_of_ge hp h1 hp'.2.1, hp'⟩
    · rw [List.append_assoc] at hcoll ⊢
      refine answerGo_complete hcut hD htop rest hi false hi _ hv nd ok hcoll
        { last := by rw [hchunk.2]; simp [hfit.1], le := le_rfl, flush := fun _ => rfl,
          ptop := hh.2, mono := hmono, honest := hhon,
          done := fun x hx h1 => hdone x hx (by rw [hfit.1]; exact h1),
          quiet := fun x _ h1 h2 => by omega, rmono := mono_tail inv.rmono,
          rhonest := honest_tail inv.rhonest, todo := fun x hx h1 => ?_ }
      obtain ⟨p, hp, hp'⟩ := inv.todo x hx (le_trans hh.1 h1)
      exact ⟨p, mem_tail_of_ge hp h1 hp'.2.1, hp'⟩
    · rw [hcut]
      have hlast : lastB 0 (out ++ (flushOf skipping prev ++ [⟨b, .ids (slice X prev b)⟩])) = b := by
        rw [hchunk.2]
        rfl
      rw [wl_append, List.append_assoc, hlast]
      simp only [wl_cons, wl_nil]
      refine ⟨forall_append.2 ⟨hmono, ?_⟩,
        ⟨forall_append.2 ⟨hhon.1, ?_⟩, forall_append.2 ⟨hhon.2, ?_⟩⟩, fun x hx => ?_⟩
      · intro p hp
        simp only [List.mem_singleton] at hp
        subst hp
        exact ⟨le_trans hbm.2 hh.2, le_rfl⟩
      · intro p hp l' hl'
        simp only [List.mem_singleton] at hp
        subst hp
        simp at hl'
      · intro p hp h' hh'
        simp only [List.mem_singleton] at hp
        subst hp
        simp only [Pay.fp.injEq] at hh'
        exact hh'.symm
      · by_cases h1 : x < b
        · obtain ⟨q, hq, hq'⟩ := hdone x hx h1
          exact ⟨q, by simp [hq], hq'⟩
        · exact ⟨(b, ⟨c.top, .fp (c.fp (slice X b c.top))⟩), by simp, by omega,
            htop x (Finset.mem_sdiff.1 hx).1, by simp⟩

end Completeness

/-! ## The whole run -/

section Run

variable {H : Type} [DecidableEq H]

/-- A party's whole answer keeps the invariant: from an honest, ordered message covering `D`,
an honest, ordered answer covering what is still to be found. -/
theorem answer_complete (c : Cfg H) (init : Bool) (X Y D : Finset ℕ) (m : Msg H)
    (hcut : ∀ e h, c.cut e h = e) (hD : D ⊆ symmDiff X Y) (htop : ∀ x ∈ D, x < c.top)
    (hcoll : (answer c init X Y m).ok = true ∨ Function.Injective c.fp)
    (hmono : Mono c.top (wl 0 m)) (hhon : Honest c.fp Y (wl 0 m)) (hcov : Covers D (wl 0 m)) :
    Mono c.top (wl 0 (answer c init X Y m).msg) ∧ Honest c.fp X (wl 0 (answer c init X Y m).msg) ∧
      Covers (D \ ((answer c init X Y m).have_ ∪ (answer c init X Y m).need))
        (wl 0 (answer c init X Y m).msg) :=
  answerGo_complete c init X Y D hcut hD htop m 0 false 0 [] ∅ ∅ true hcoll
    { last := rfl, le := le_rfl, flush := fun _ => rfl, ptop := Nat.zero_le _,
      mono := by simp [Mono], honest := by simp [Honest, IdsHonest],
      done := fun x _ h => absurd h (Nat.not_lt_zero x),
      quiet := fun x _ h1 h2 => by omega,
      rmono := hmono, rhonest := hhon,
      todo := fun x hx _ => hcov x (by simpa using hx) }

/-- A run's final record of collisions is true only if it was true at the start. -/
theorem runGo_ok (c : Cfg H) (lI lR : Option ℕ) (I R : Finset ℕ) :
    ∀ (fuel : ℕ) (m : Msg H) (hv nd : Finset ℕ) (ok : Bool) (hv' nd' : Finset ℕ),
    runGo c lI lR I R fuel m hv nd ok = some (hv', nd', true) → ok = true
  | 0, _, _, _, _, _, _, h => by simp [runGo] at h
  | fuel + 1, m, hv, nd, ok, hv', nd', h => by
    simp only [runGo] at h
    split_ifs at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      have := h.2.2
      simp only [Bool.and_eq_true] at this
      exact this.1.1
    · have := runGo_ok c lI lR I R fuel _ _ _ _ hv' nd' h
      simp only [Bool.and_eq_true] at this
      exact this.1.1

theorem runGo_complete (c : Cfg H) (lI lR : Option ℕ) (I R : Finset ℕ)
    (hcut : ∀ e h, c.cut e h = e) (htop : ∀ x ∈ I ∪ R, x < c.top) :
    ∀ (fuel : ℕ) (m : Msg H) (hv nd : Finset ℕ) (ok : Bool) (hv' nd' : Finset ℕ) (ok' : Bool),
    runGo c lI lR I R fuel m hv nd ok = some (hv', nd', ok') →
    (ok' = true ∨ Function.Injective c.fp) →
    Mono c.top (wl 0 m) → Honest c.fp I (wl 0 m) → Covers (symmDiff I R \ (hv ∪ nd)) (wl 0 m) →
    symmDiff I R ⊆ hv' ∪ nd'
  | 0, _, _, _, _, _, _, _, h, _, _, _, _ => by simp [runGo] at h
  | fuel + 1, m, hv, nd, ok, hv', nd', ok', h, hcoll, hmono, hhon, hcov => by
    simp only [runGo] at h
    set aR := answer (c.withLimit lR) false R I m with haR
    set aI := answer (c.withLimit lI) true I R aR.msg with haI
    have hflags : ok' = true → aR.ok = true ∧ aI.ok = true := by
      intro hok
      split_ifs at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        have := h.2.2.trans hok
        simp only [Bool.and_eq_true] at this
        exact ⟨this.1.2, this.2⟩
      · rw [hok] at h
        have := runGo_ok c lI lR I R fuel _ _ _ _ hv' nd' h
        simp only [Bool.and_eq_true] at this
        exact ⟨this.1.2, this.2⟩
    set D := symmDiff I R \ (hv ∪ nd) with hD
    have hDI : D ⊆ symmDiff I R := fun x hx => (Finset.mem_sdiff.1 hx).1
    have hDR : D ⊆ symmDiff R I := fun x hx => by
      rw [symmDiff_comm]
      exact hDI hx
    have hDtop : ∀ x ∈ D, x < c.top := fun x hx => by
      apply htop x
      rcases Finset.mem_symmDiff.1 (hDI hx) with h' | h'
      · exact Finset.mem_union_left _ h'.1
      · exact Finset.mem_union_right _ h'.1
    obtain ⟨hR1, hR2, hR3⟩ := answer_complete (c.withLimit lR) false R I D m hcut hDR hDtop
      (hcoll.imp (fun h' => (hflags h').1) id) hmono hhon hcov
    have hRe := answerGo_responder (c.withLimit lR) R I m 0 false 0 [] ∅ ∅ true
    have hR3' : Covers D (wl 0 aR.msg) := by
      have := hR3
      simp only [answer] at this
      rwa [hRe.1, hRe.2, Finset.union_empty, Finset.sdiff_empty] at this
    obtain ⟨hI1, hI2, hI3⟩ := answer_complete (c.withLimit lI) true I R D aR.msg hcut hDI hDtop
      (hcoll.imp (fun h' => (hflags h').2) id) hR1 hR2 hR3'
    have hset : symmDiff I R \ ((hv ∪ aI.have_) ∪ (nd ∪ aI.need)) = D \ (aI.have_ ∪ aI.need) := by
      ext x
      simp only [hD, Finset.mem_sdiff, Finset.mem_union, not_or]
      tauto
    split_ifs at h with hempty
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      intro x hx
      by_contra hn
      have hx' : x ∈ D \ (aI.have_ ∪ aI.need) := by
        rw [← hset]
        exact Finset.mem_sdiff.2 ⟨hx, hn⟩
      obtain ⟨p, hp, _⟩ := hI3 x hx'
      rw [hempty] at hp
      simp at hp
    · exact runGo_complete c lI lR I R hcut htop fuel _ _ _ _ hv' nd' ok' h hcoll hI1 hI2
        (by rw [hset]; exact hI3)

/-- **B3 and B4.** With the fixed cut rule, a run that ends reports exactly what each side
lacks: the initiator's had ids are `I \ R` and its needed ids `R \ I`. This holds with any
frame limits on either side, or none. Equal fingerprints must have covered equal sets: either
the run recorded that (`ok`), or the fingerprint is injective. -/
theorem run_complete (c : Cfg H) (lI lR : Option ℕ) (I R : Finset ℕ) (fuel : ℕ)
    (hcut : ∀ e h, c.cut e h = e) (htop : ∀ x ∈ I ∪ R, x < c.top) {hv nd : Finset ℕ} {ok : Bool}
    (hrun : run c lI lR I R fuel = some (hv, nd, ok))
    (hcoll : ok = true ∨ Function.Injective c.fp) : hv = I \ R ∧ nd = R \ I := by
  obtain ⟨hs1, hs2⟩ := run_sound c lI lR I R fuel hrun
  have hc := runGo_complete c lI lR I R hcut htop fuel _ ∅ ∅ true hv nd ok hrun hcoll
    (split_mono c.B c.fp I (Nat.zero_le _) le_rfl) (split_honest c.B c.fp I 0 c.top)
    (fun x hx => by
      have hx' := (Finset.mem_sdiff.1 hx).1
      have : x ∈ I ∪ R := by
        rcases Finset.mem_symmDiff.1 hx' with h' | h'
        · exact Finset.mem_union_left _ h'.1
        · exact Finset.mem_union_right _ h'.1
      exact split_covers c.B c.fp I (Nat.zero_le x) (htop x this))
  constructor
  · refine Finset.Subset.antisymm hs1 (fun x hx => ?_)
    rcases Finset.mem_union.1 (hc (Finset.mem_symmDiff.2 (Or.inl (Finset.mem_sdiff.1 hx)))) with
      h | h
    · exact h
    · exact absurd (Finset.mem_sdiff.1 hx).1 (Finset.mem_sdiff.1 (hs2 h)).2
  · refine Finset.Subset.antisymm hs2 (fun x hx => ?_)
    rcases Finset.mem_union.1 (hc (Finset.mem_symmDiff.2 (Or.inr (Finset.mem_sdiff.1 hx)))) with
      h | h
    · exact absurd (Finset.mem_sdiff.1 hx).1 (Finset.mem_sdiff.1 (hs1 h)).2
    · exact h

end Run

/-! ## The reference's cut, and examples -/

section Examples

/-- A range costs one, and an id list one more per id. -/
def cost₀ : Rng (Finset ℕ) → ℕ
  | ⟨_, .ids l⟩ => 1 + l.card
  | _ => 1

/-- Two buckets, the set itself as its fingerprint, and items below 8. No two different sets
share a fingerprint. -/
def cfg₀ (cut : ℕ → ℕ → ℕ) : Cfg (Finset ℕ) := ⟨2, id, cost₀, none, cut, 8⟩

/-- **Mutant: the reference's cut.** With both sides frame-limited, the reference rule ends the
run with the responder's items 6 and 7 never found, although the fingerprint is injective.
The initiator's limit cuts its answer at a range it holds nothing in. The responder's limit
then cuts its answer at the initiator's remaining range: it drops its split of that range and
fingerprints only what lies above the range's upper bound, which is nothing. The initiator
reads that fingerprint as covering the range from the last bound written, where it also holds
nothing, finds the two equal, and stops. -/
theorem refCut_misses :
    Function.Injective (cfg₀ refCut).fp ∧
      run (cfg₀ refCut) (some 4) (some 6) {0, 1, 2, 5} {2, 4, 5, 6, 7} 10 =
        some ({0, 1}, {4}, false) ∧
      ({2, 4, 5, 6, 7} \ {0, 1, 2, 5} : Finset ℕ) = {4, 6, 7} :=
  ⟨Function.injective_id, by decide, by decide⟩

/-- The fixed rule finds them on the same run, which meets `run_complete`'s hypotheses. -/
theorem fixCut_finds :
    run (cfg₀ fixCut) (some 4) (some 6) {0, 1, 2, 5} {2, 4, 5, 6, 7} 10 =
      some ({0, 1}, {4, 6, 7}, true) := by decide

/-- `run_complete` applies to the fixed rule. -/
theorem fixCut_cut (e h : ℕ) : (cfg₀ fixCut).cut e h = e := rfl

/-- **B5.** Six and eight items within one second (keys `5 * 16 + i`) are reconciled exactly,
with or without frame limits. Paging by time cannot do this once a second holds more events
than a page (`Nostr.Paging.walk_stopping_misses`). -/
example : run { cfg₀ fixCut with top := 96 } none none {80, 81, 82, 83, 84, 85}
    {82, 83, 84, 85, 86, 87, 88, 89} 20 = some ({80, 81}, {86, 87, 88, 89}, true) := by decide

example : run { cfg₀ fixCut with top := 96 } (some 6) (some 6) {80, 81, 82, 83, 84, 85}
    {82, 83, 84, 85, 86, 87, 88, 89} 20 = some ({80, 81}, {86, 87, 88, 89}, true) := by decide

end Examples

end Mettapedia.Protocols.Sync.Negentropy
