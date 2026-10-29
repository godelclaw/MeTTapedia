import Mettapedia.Protocols.Nostr.Paging
import Mettapedia.Protocols.Nostr.Filter
import Mathlib.Logic.Function.Basic

/-!
# Resynchronising by state token, and paging by identifier

**Resync (M4).** A client that caches a server's records can catch up from a
token naming the state it holds.
- IMAP (RFC 9051 §2.3.1.1): a UID never names another message under the same
  UIDVALIDITY. When UIDs fail to persist, as when a mailbox is created again
  under its old name, UIDVALIDITY grows.
- CONDSTORE and QRESYNC (RFC 7162 §3.1, §3.2.5): changes get higher
  mod-sequences. Selecting with a known UIDVALIDITY and mod-sequence returns the
  changes since then, expunges included (`VANISHED`). A mismatched UIDVALIDITY
  returns no changes, and the client's cached UIDs no longer name the same
  messages. Expunges are reported from state kept about them (§5.3), or by
  listing every UID of the client's set that no longer exists (§5.1).
- JMAP (RFC 8620 §5.2): `Foo/changes` from `sinceState` returns the created,
  updated and destroyed ids. With `maxChanges` it may stop at an intermediate
  state and set `hasMoreChanges`. When it cannot calculate the changes, it
  answers `cannotCalculateChanges`, and the client must invalidate its cache.

The model: a server holds an epoch (UIDVALIDITY), the log of operations of that
epoch (puts and deletes of keyed records), and a horizon, the oldest state from
which it still computes changes. A token is an epoch and a position in the log
(a mod-sequence). `changes` returns, for every key the operations after the
token touched, its value at the new state, `none` for destroyed; with a page
limit it stops at an intermediate state. The client applies them, or on
`cannot` replaces its cache with the server's records.

**Paging (M6).** XMPP archives page by archive ids, not by time.
- XEP-0313 §3.1: order is the order received, and timestamps alone should not
  be relied on for it, as messages may share one. §6.2: archive ids are unique
  and never reused.
- XEP-0059 §2.2: the next page starts with the item that immediately follows
  the one named by `<after/>`. XEP-0313 §4.3.2 pages with the last id received,
  and the last page carries `complete='true'`.

The theorems:
- `sync_exact`: a client holding a state of the server reaches the server's
  current records and token exactly, by changes or by a full resync.
- `sync_page`, `rounds_exact`: with a page limit each round reaches a real
  intermediate state, and enough rounds reach the current state.
- `walkIds_complete`: paging by ids returns the archive, in order and exactly
  once, however many items share a timestamp.
- Mutants: a server that forgets deletions leaves a deleted record in the cache
  (`forgetful_keeps_deleted`). A server whose history was replaced without a new
  epoch leaves a cache that is wrong (`same_epoch_wrong`); a new epoch repairs
  it (`new_epoch_exact`). A read position kept as a creation time misses an
  event created earlier that arrives later (`creation_time_position_misses`).
  Paging after a timestamp skips the items that share the page's last one
  (`after_time_misses`). The until-walk of `Nostr.Paging` misses an event when
  one second holds more events than a page (`until_walk_misses`).

Not modelled: records changed during a client's paging, ids deleted between
pages (XEP-0059 §2.4), flags as values of their own, and the cost of keeping
history.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Mail.Sync

/-! ## Resync by state token -/

section Resync

variable {K V : Type} [DecidableEq K]

/-- An operation on keyed records. -/
inductive Op (K V : Type)
  | put (k : K) (v : V)
  | del (k : K)

/-- The key an operation touches. -/
def Op.key : Op K V → K
  | .put k _ => k
  | .del k => k

/-- Records by key. -/
abbrev Store (K V : Type) := K → Option V

/-- One operation applied to records. -/
def Op.apply (s : Store K V) : Op K V → Store K V
  | .put k v => Function.update s k (some v)
  | .del k => Function.update s k none

/-- The records after a sequence of operations, from none. -/
def replay (ops : List (Op K V)) : Store K V := ops.foldl Op.apply (fun _ => none)

/-- A server: its epoch, the operations of the epoch, and the oldest position
from which it computes changes. -/
structure Server (K V : Type) where
  epoch : Nat
  log : List (Op K V)
  horizon : Nat

/-- A state token: an epoch and a position in its log. -/
structure Token where
  epoch : Nat
  seq : Nat
deriving DecidableEq, Repr

namespace Server

/-- The records at position `n`. -/
def at_ (S : Server K V) (n : Nat) : Store K V := replay (S.log.take n)

/-- The current records. -/
def store (S : Server K V) : Store K V := replay S.log

/-- The current token. -/
def token (S : Server K V) : Token := ⟨S.epoch, S.log.length⟩

/-- A token the server can compute changes from. -/
def Covers (S : Server K V) (t : Token) : Prop :=
  t.epoch = S.epoch ∧ S.horizon ≤ t.seq ∧ t.seq ≤ S.log.length

instance (S : Server K V) (t : Token) : Decidable (S.Covers t) := by
  unfold Covers; infer_instance

end Server

/-- The answer to a request for changes. -/
inductive Changes (K V : Type)
  | changes (touched : List (K × Option V)) (newState : Token) (more : Bool)
  | cannot

/-- The changes since `t`, at most `max` operations' worth: every key the
operations touched, with its value at the new state. -/
def Server.changes (S : Server K V) (t : Token) (max : Nat) : Changes K V :=
  if S.Covers t then
    let upto := min S.log.length (t.seq + max)
    .changes (((S.log.drop t.seq).take (upto - t.seq)).map fun o => (o.key, S.at_ upto o.key))
      ⟨S.epoch, upto⟩ (decide (upto < S.log.length))
  else .cannot

/-- A client: its cached records and the token they are from. -/
structure Client (K V : Type) where
  cache : Store K V
  token : Token

/-- Write each touched key's value into the records. -/
def patch (s : Store K V) (touched : List (K × Option V)) : Store K V :=
  touched.foldl (fun s kv => Function.update s kv.1 kv.2) s

/-- One round: apply the changes, or replace the cache with the server's records. -/
def sync (S : Server K V) (max : Nat) (c : Client K V) : Client K V :=
  match S.changes c.token max with
  | .changes touched t _ => ⟨patch c.cache touched, t⟩
  | .cannot => ⟨S.store, S.token⟩

/-- The client holds a state of this server: if its token is of this epoch and
within the log, its cache is the server's records there. -/
def Holds (S : Server K V) (c : Client K V) : Prop :=
  c.token.epoch = S.epoch → c.token.seq ≤ S.log.length → c.cache = S.at_ c.token.seq

theorem patch_eq {α : Type} (f : α → K) (s target : Store K V) (xs : List α) (k : K) :
    patch s (xs.map fun x => (f x, target (f x))) k = if k ∈ xs.map f then target k else s k := by
  induction xs generalizing s with
  | nil => simp [patch]
  | cons x xs ih =>
    simp only [patch, List.map_cons, List.foldl_cons] at ih ⊢
    rw [ih]
    by_cases hx : k ∈ xs.map f
    · simp [hx]
    · by_cases hk : k = f x
      · subst hk; simp
      · simp [hx, hk]

theorem foldl_untouched (s : Store K V) (ops : List (Op K V)) (k : K) (h : k ∉ ops.map Op.key) :
    ops.foldl Op.apply s k = s k := by
  induction ops generalizing s with
  | nil => rfl
  | cons o os ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.foldl_cons]
    rw [ih _ h.2]
    cases o with
    | put x v => exact Function.update_of_ne (by simpa [Op.key] using h.1) _ _
    | del x => exact Function.update_of_ne (by simpa [Op.key] using h.1) _ _

/-- A key the operations between two positions leave alone keeps its value. -/
theorem at_untouched (S : Server K V) {n m : Nat} (hnm : n ≤ m) (k : K)
    (h : k ∉ ((S.log.drop n).take (m - n)).map Op.key) : S.at_ m k = S.at_ n k := by
  have : S.log.take m = S.log.take n ++ (S.log.drop n).take (m - n) := by
    rw [← List.take_add, Nat.add_sub_cancel' hnm]
  simp only [Server.at_, replay, this, List.foldl_append]
  exact foldl_untouched _ _ k h

/-- One round keeps the client holding a state of the server. -/
theorem sync_page (S : Server K V) (max : Nat) (c : Client K V) (hc : Holds S c) :
    Holds S (sync S max c) ∧ ((sync S max c).token.epoch = S.epoch ∧
      (sync S max c).token.seq ≤ S.log.length) := by
  unfold sync Server.changes
  split
  · next touched t more heq =>
    split at heq
    · next hcov =>
      simp only [Changes.changes.injEq] at heq
      obtain ⟨rfl, rfl, -⟩ := heq
      obtain ⟨he, -, hle⟩ := hcov
      have hm : c.token.seq ≤ min S.log.length (c.token.seq + max) := le_min hle (by omega)
      refine ⟨fun _ _ => ?_, rfl, min_le_left _ _⟩
      funext k
      dsimp only
      rw [patch_eq Op.key c.cache (S.at_ (min S.log.length (c.token.seq + max))), hc he hle]
      split
      · rfl
      · next hk => exact (at_untouched S hm k hk).symm
    · cases heq
  · exact ⟨fun _ _ => by simp [Server.store, Server.at_, Server.token], rfl, le_refl _⟩

/-- **Resync is exact**: a client holding a state of the server reaches its
current records and token in one round when the page limit covers the log, by
the changes when the server can compute them, by a full resync when not. -/
theorem sync_exact (S : Server K V) (c : Client K V) (hc : Holds S c) :
    (sync S S.log.length c).cache = S.store ∧ (sync S S.log.length c).token = S.token := by
  obtain ⟨hh, he, hle⟩ := sync_page S S.log.length c hc
  have hseq : (sync S S.log.length c).token.seq = S.log.length := by
    unfold sync Server.changes at hle ⊢
    split
    · next touched t more heq =>
      split at heq
      · simp only [Changes.changes.injEq] at heq
        obtain ⟨-, rfl, -⟩ := heq
        simp only
        omega
      · cases heq
    · rfl
  refine ⟨?_, ?_⟩
  · rw [hh he hle, hseq]; simp [Server.at_, Server.store]
  · cases ht : (sync S S.log.length c).token
    simp only [ht] at he hseq
    simp [Server.token, he, hseq]

/-- `n` rounds. -/
def rounds (S : Server K V) (max : Nat) : Nat → Client K V → Client K V
  | 0, c => c
  | n + 1, c => rounds S max n (sync S max c)

/-- Positions still to cover: the rest of the log from a covered token, and one
round more from any other. -/
def remaining (S : Server K V) (c : Client K V) : Nat :=
  if S.Covers c.token then S.log.length - c.token.seq else S.log.length + 1

theorem remaining_sync (S : Server K V) (hS : S.horizon ≤ S.log.length) (max : Nat) (hmax : 0 < max)
    (c : Client K V) (h : 0 < remaining S c) : remaining S (sync S max c) < remaining S c := by
  unfold remaining at h ⊢
  unfold sync Server.changes
  by_cases hcov : S.Covers c.token
  · simp only [hcov, if_true] at h ⊢
    obtain ⟨he, hh, hle⟩ := hcov
    have hc' : S.Covers ⟨S.epoch, min S.log.length (c.token.seq + max)⟩ :=
      ⟨rfl, le_trans hh (le_min hle (by omega)), min_le_left _ _⟩
    simp only [hc', if_true]
    omega
  · simp only [hcov, if_false]
    have hc' : S.Covers ⟨S.epoch, S.log.length⟩ := ⟨rfl, hS, le_refl _⟩
    simp only [Server.token, hc', if_true]
    omega

theorem remaining_le_of_zero (S : Server K V) (max : Nat) (c : Client K V) (h0 : remaining S c = 0) :
    remaining S (sync S max c) = 0 := by
  unfold remaining at h0 ⊢
  unfold sync Server.changes
  by_cases hcov : S.Covers c.token
  · simp only [hcov, if_true] at h0 ⊢
    obtain ⟨he, hh, hle⟩ := hcov
    have hc' : S.Covers ⟨S.epoch, min S.log.length (c.token.seq + max)⟩ :=
      ⟨rfl, le_trans hh (le_min hle (by omega)), min_le_left _ _⟩
    simp only [hc', if_true]
    omega
  · simp only [hcov, if_false] at h0; omega

theorem rounds_holds (S : Server K V) (max : Nat) :
    ∀ (n : Nat) (c : Client K V), Holds S c → Holds S (rounds S max n c)
  | 0, _, hc => hc
  | n + 1, c, hc => rounds_holds S max n _ (sync_page S max c hc).1

/-- **Paged resync is exact**: with any positive page limit, every round
reaches a state of the server, and after as many rounds as the log is long,
plus one, the client holds the current records and token. -/
theorem rounds_exact (S : Server K V) (hS : S.horizon ≤ S.log.length) (max : Nat) (hmax : 0 < max) :
    ∀ (n : Nat) (c : Client K V), Holds S c → remaining S c ≤ n →
      (rounds S max n c).cache = S.store ∧ (rounds S max n c).token = S.token
  | 0, c, hc, hr => by
    have h0 : remaining S c = 0 := by omega
    unfold remaining at h0
    split at h0
    · next hcov =>
      obtain ⟨he, -, hle⟩ := hcov
      have hseq : c.token.seq = S.log.length := by omega
      refine ⟨?_, ?_⟩
      · simp only [rounds]; rw [hc he hle, hseq]; simp [Server.at_, Server.store]
      · cases ht : c.token
        simp only [ht] at he hseq
        simp [rounds, ht, Server.token, he, hseq]
    · omega
  | n + 1, c, hc, hr => by
    by_cases h0 : remaining S c = 0
    · -- already current: a round changes nothing that matters
      have hp := sync_page S max c hc
      have := remaining_le_of_zero S max c h0
      exact rounds_exact S hS max hmax n _ hp.1 (by omega)
    · have := remaining_sync S hS max hmax c (by omega)
      exact rounds_exact S hS max hmax n _ (sync_page S max c hc).1 (by omega)

/-- A round that drops destroyed keys from the changes: a server that does not
remember deletions. -/
def syncDropping (S : Server K V) (max : Nat) (c : Client K V) : Client K V :=
  match S.changes c.token max with
  | .changes touched t _ => ⟨patch c.cache (touched.filter (·.2.isSome)), t⟩
  | .cannot => ⟨S.store, S.token⟩

end Resync

/-! ### Examples and mutants of resync -/

/-- Four operations in epoch 7; changes are kept from position 1. -/
def server : Server Nat String := ⟨7, [.put 1 "a", .put 2 "b", .del 1, .put 3 "c"], 1⟩

/-- A client holding position 2. -/
def atTwo : Client Nat String := ⟨server.at_ 2, ⟨7, 2⟩⟩

/-- The hypotheses meet with changes the server can compute: the client holds a
covered state, and resync ends at the current records, key 1 destroyed. -/
example : Holds server atTwo ∧ server.Covers atTwo.token ∧
    (sync server 4 atTwo).cache 1 = none ∧ (sync server 4 atTwo).cache 3 = some "c" :=
  ⟨fun _ _ => rfl, by decide, by decide, by decide⟩

/-- A token older than the horizon, or of another epoch, is not covered: the
client resynchronises in full, whatever its cache holds. -/
example : ¬ server.Covers ⟨7, 0⟩ ∧ ¬ server.Covers ⟨6, 2⟩ ∧
    (sync server 4 ⟨fun _ => some "stale", ⟨6, 2⟩⟩).cache = server.store :=
  ⟨by decide, by decide, (sync_exact server _ (fun h => by cases h)).1⟩

/-- Paged rounds, two operations at a time, from position 1. -/
example : (rounds server 2 3 ⟨server.at_ 1, ⟨7, 1⟩⟩).cache = server.store :=
  (rounds_exact server (by decide) 2 (by decide) 3 _ (fun _ _ => rfl) (by decide)).1

/-- A server that does not remember deletions leaves the destroyed key 1 in the
client's cache. -/
theorem forgetful_keeps_deleted :
    (syncDropping server 4 atTwo).cache 1 = some "a" ∧ server.store 1 = none := by decide

/-- The same epoch with a replaced history: the client's position is covered,
but its cache is of the old history. -/
def replaced : Server Nat String := ⟨7, [.put 1 "x", .put 4 "y"], 0⟩

/-- A server whose history was replaced without a new epoch leaves the client's
cache wrong. -/
theorem same_epoch_wrong : (sync replaced 2 atTwo).cache 1 = some "a" ∧ replaced.store 1 = some "x" := by
  decide

/-- With a new epoch the token is not covered, and resync is exact. -/
theorem new_epoch_exact : (sync { replaced with epoch := 8 } 2 atTwo).cache = replaced.store :=
  (sync_exact { replaced with epoch := 8 } atTwo (fun h => by cases h)).1

/-- Records keyed by creation time, in the order a relay received them: one
created at 1000, then one created at 5. -/
def arrivals : Server Nat String := ⟨1, [.put 1000 "first", .put 5 "late"], 0⟩

/-- A read position kept as a creation time is not a state token. After the
event created at 1000, a reader asking with `since` 1000 minus an overlap of
600 does not match the event created at 5 that arrived later (NIP-01's `since`
holds for stored and live events alike). The changes since the reader's
position in the relay's order include it. -/
theorem creation_time_position_misses :
    ({ since := some (1000 - 600) } : Nostr.Filter).accepts ⟨⟨"k", 5, 3838, [], ""⟩, "late", ""⟩ = false ∧
      (sync arrivals 2 ⟨arrivals.at_ 1, ⟨1, 1⟩⟩).cache 5 = some "late" := by
  decide

/-! ## Paging by archive id -/

/-- An archived item: its archive id and its timestamp. -/
structure Item where
  id : Nat
  stamp : Nat
deriving DecidableEq, Repr

/-- XEP-0059 §2.2: at most `max` items immediately following the item named by
`after`, or from the start. -/
def pageAfter (arch : List Item) (max : Nat) : Option Nat → List Item
  | none => arch.take max
  | some a => ((arch.dropWhile (fun x => x.id != a)).drop 1).take max

/-- Page forward with the last id received until a page is not full. -/
def walkIds (arch : List Item) (max : Nat) : Nat → Option Nat → List Item
  | 0, _ => []
  | fuel + 1, after =>
    if (pageAfter arch max after).length < max then pageAfter arch max after
    else pageAfter arch max after ++ walkIds arch max fuel ((pageAfter arch max after).getLast?.map (·.id))

/-- The cursor after the first `i` items. -/
def cursor (arch : List Item) (i : Nat) : Option Nat :=
  if i = 0 then none else (arch[i - 1]?).map (·.id)

theorem dropWhile_ne_id : ∀ (l : List Item) (j : Nat) (hj : j < l.length), (l.map Item.id).Nodup →
    l.dropWhile (fun x => x.id != l[j].id) = l.drop j
  | [], _, hj, _ => absurd hj (by simp)
  | x :: xs, 0, _, _ => by simp
  | x :: xs, j + 1, hj, hnd => by
    have hj' : j < xs.length := by simp only [List.length_cons] at hj; omega
    have hx : x.id ∉ xs.map Item.id := (List.nodup_cons.mp (by simpa using hnd)).1
    have hne : (x.id != (xs[j]'hj').id) = true := by
      have : (xs[j]'hj').id ∈ xs.map Item.id := List.mem_map_of_mem (List.getElem_mem _)
      simp only [bne_iff_ne, ne_eq]
      exact fun h => hx (h ▸ this)
    simp only [List.getElem_cons_succ, List.dropWhile_cons, hne, if_true, List.drop_succ_cons]
    exact dropWhile_ne_id xs j hj' (List.nodup_cons.mp (by simpa using hnd)).2

theorem pageAfter_cursor {arch : List Item} (hnd : (arch.map Item.id).Nodup) (max : Nat) {i : Nat}
    (hi : i ≤ arch.length) : pageAfter arch max (cursor arch i) = (arch.drop i).take max := by
  unfold cursor
  split
  · next h => subst h; rfl
  · next h =>
    have hlt : i - 1 < arch.length := by omega
    rw [List.getElem?_eq_getElem hlt]
    simp only [Option.map_some, pageAfter]
    rw [dropWhile_ne_id arch (i - 1) hlt hnd, List.drop_drop]
    congr 2
    omega

theorem walkIds_from {arch : List Item} (hnd : (arch.map Item.id).Nodup) {max : Nat} (hmax : 0 < max) :
    ∀ (fuel i : Nat), i ≤ arch.length → arch.length - i < fuel →
      walkIds arch max fuel (cursor arch i) = arch.drop i
  | 0, _, _, h => absurd h (by omega)
  | fuel + 1, i, hi, hf => by
    simp only [walkIds, pageAfter_cursor hnd max hi]
    split
    · next hlt =>
      rw [List.length_take] at hlt
      exact List.take_of_length_le (by
        rcases Nat.lt_or_ge (arch.drop i).length max with h | h
        · omega
        · rw [Nat.min_eq_left h] at hlt; omega)
    · next hge =>
      rw [List.length_take] at hge
      have hlen : max ≤ (arch.drop i).length := by
        rcases Nat.lt_or_ge (arch.drop i).length max with h | h
        · rw [Nat.min_eq_right h.le] at hge; omega
        · exact h
      rw [List.length_drop] at hlen
      have hlast : ((arch.drop i).take max).getLast?.map (·.id) = cursor arch (i + max) := by
        rw [List.getLast?_eq_getElem?]
        simp only [cursor, show i + max ≠ 0 by omega, if_false, List.length_take, List.length_drop,
          List.getElem?_take, List.getElem?_drop]
        rw [Nat.min_eq_left (by omega), if_pos (by omega)]
        congr 2
        omega
      have hd : List.drop (i + max) arch = List.drop max (List.drop i arch) := by
        rw [List.drop_drop]
      rw [hlast, walkIds_from hnd hmax fuel (i + max) (by omega) (by omega), hd, List.take_append_drop]

/-- **Paging by id is complete**: the walk returns the archive, in order and
exactly once, with no assumption on how many items share a timestamp. -/
theorem walkIds_complete {arch : List Item} (hnd : (arch.map Item.id).Nodup) {max : Nat}
    (hmax : 0 < max) : walkIds arch max (arch.length + 1) none = arch :=
  walkIds_from hnd hmax (arch.length + 1) 0 (Nat.zero_le _) (by omega)

/-- Five items in one second, pages of two: the hypotheses meet and the walk
returns all five. -/
example : (((List.range 5).map fun i => (⟨i, 9⟩ : Item)).map Item.id).Nodup ∧
    walkIds ((List.range 5).map fun i => ⟨i, 9⟩) 2 6 none = (List.range 5).map fun i => ⟨i, 9⟩ :=
  ⟨by decide, by decide⟩

/-- Paging after the last item's timestamp, exclusively. -/
def pageAfterTime (arch : List Item) (max : Nat) : Option Nat → List Item
  | none => arch.take max
  | some t => (arch.filter fun x => t < x.stamp).take max

/-- The walk with a timestamp cursor. -/
def walkTimes (arch : List Item) (max : Nat) : Nat → Option Nat → List Item
  | 0, _ => []
  | fuel + 1, after =>
    if (pageAfterTime arch max after).length < max then pageAfterTime arch max after
    else pageAfterTime arch max after ++
      walkTimes arch max fuel ((pageAfterTime arch max after).getLast?.map (·.stamp))

/-- Three items in one second, pages of two: the timestamp cursor skips the
third. -/
theorem after_time_misses : (⟨3, 5⟩ : Item) ∉ walkTimes [⟨1, 5⟩, ⟨2, 5⟩, ⟨3, 5⟩] 2 4 none ∧
    walkIds [⟨1, 5⟩, ⟨2, 5⟩, ⟨3, 5⟩] 2 4 none = [⟨1, 5⟩, ⟨2, 5⟩, ⟨3, 5⟩] := by decide

/-- The until-walk of `Nostr.Paging`, which pages back by time, misses an event
when one second holds more events than a page; `walk_complete` assumes it does
not. -/
theorem until_walk_misses : (5, 3) ∉ Nostr.Paging.walk 2 [(5, 1), (5, 2), (5, 3)] 10 none [] ∧
    ¬ ∀ t, (Nostr.Paging.atSecond [(5, 1), (5, 2), (5, 3)] t).length ≤ 2 := by
  refine ⟨by decide, fun h => absurd (h 5) (by decide)⟩

end Mettapedia.Protocols.Mail.Sync
