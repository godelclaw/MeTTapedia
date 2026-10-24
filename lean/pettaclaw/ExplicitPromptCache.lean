import Std

/-!
# Explicit prompt-cache entries

`PromptCacheLayout` establishes shared text prefixes. An explicit-breakpoint
provider additionally needs a previously written, unexpired entry and a
matching endpoint in its lookback window. Block identities here stand for
the encoded content and cache-relevant settings; hash collisions, provider
implementation and tokenization are outside this model.

The runtime records block/prefix hashes and marker lifetimes in request
receipts. The changing-tail and lookback fixtures are also exercised by
`tests/test_provider_protocol.py`. This model does not certify that a remote
service wrote an entry: reported usage is the evidence of that event.
-/

namespace PettaClaw.ExplicitPromptCache

structure Entry (α : Type) where
  blocks : List α
  expires : Nat
  deriving DecidableEq, Repr

/-- The breakpoint itself is one of the twenty inspected positions. -/
def Usable (prompt : List α) (point now : Nat) (entry : Entry α) : Prop :=
  now < entry.expires ∧ entry.blocks <+: prompt ∧
  entry.blocks.length ≤ point ∧ point < entry.blocks.length + 20 ∧
  point ≤ prompt.length

def Hit (entries : List (Entry α)) (prompt : List α)
    (points : List Nat) (now : Nat) : Prop :=
  ∃ entry ∈ entries, ∃ point ∈ points, Usable prompt point now entry

instance [DecidableEq α] (prompt : List α) (point now : Nat) (entry : Entry α) :
    Decidable (Usable prompt point now entry) := by
  unfold Usable
  infer_instance

instance [DecidableEq α] (entries : List (Entry α)) (prompt : List α)
    (points : List Nat) (now : Nat) : Decidable (Hit entries prompt points now) := by
  unfold Hit
  infer_instance

/-- More probe points preserve existing hits. The runtime separately enforces
the provider's four-marker limit. -/
theorem adding_checkpoint_preserves_hits
    (entries : List (Entry α)) (prompt : List α) (points : List Nat) (now extra : Nat)
    (hit : Hit entries prompt points now) :
    Hit entries prompt (extra :: points) now := by
  obtain ⟨entry, member, point, marked, usable⟩ := hit
  exact ⟨entry, member, point, List.mem_cons_of_mem extra marked, usable⟩

/-- A live entry for the shared prefix is found at its own checkpoint. -/
theorem written_shared_prefix_is_reusable
    (entries : List (Entry α)) (prompt : List α) (points : List Nat) (now : Nat)
    (entry : Entry α) (written : entry ∈ entries)
    (alive : now < entry.expires) (shared : entry.blocks <+: prompt)
    (marked : entry.blocks.length ∈ points) : Hit entries prompt points now := by
  exact ⟨entry, written, entry.blocks.length, marked,
    alive, shared, Nat.le_refl _, by omega, shared.length_le⟩

/-- Shared text that was never written as an entry cannot produce a hit. -/
theorem no_matching_written_entry_means_miss
    (entries : List (Entry α)) (prompt : List α) (points : List Nat) (now : Nat)
    (missing : ∀ entry ∈ entries, ¬ entry.blocks <+: prompt) :
    ¬ Hit entries prompt points now := by
  rintro ⟨entry, member, point, _, usable⟩
  exact missing entry member usable.2.1

/-- If the only write included a changing tail, its earlier shared content
was not implicitly cached. This holds for any choice of probe points. -/
theorem only_full_write_misses_changed_prompt
    (before after : List α) (sameLength : before.length = after.length)
    (changed : before ≠ after) (expires now : Nat) (points : List Nat) :
    ¬ Hit [⟨before, expires⟩] after points now := by
  apply no_matching_written_entry_means_miss
  intro entry member shared
  have same : entry = ⟨before, expires⟩ := List.mem_singleton.mp member
  subst entry
  have sameBlocks := List.prefix_iff_eq_take.mp shared
  rw [sameLength, List.take_length] at sameBlocks
  exact changed sameBlocks

theorem expired_entries_cannot_hit
    (entries : List (Entry α)) (prompt : List α) (points : List Nat) (now : Nat)
    (expired : ∀ entry ∈ entries, entry.expires ≤ now) :
    ¬ Hit entries prompt points now := by
  rintro ⟨entry, member, point, _, usable⟩
  have := expired entry member
  have := usable.1
  omega

/-- Twenty newly appended blocks put an old endpoint just outside lookback. -/
theorem distant_checkpoint_cannot_find_entry
    (entry : Entry α) (prompt : List α) (points : List Nat) (now : Nat)
    (distant : ∀ point ∈ points, entry.blocks.length + 20 ≤ point) :
    ¬ Hit [entry] prompt points now := by
  rintro ⟨found, member, point, marked, usable⟩
  have same : found = entry := List.mem_singleton.mp member
  subst found
  have := distant point marked
  have := usable.2.2.2.1
  omega

example : ¬ Hit [⟨[7, 8, 9], 300⟩] [7, 8, 10] [3] 1 := by decide

example : Hit [⟨[7, 8], 300⟩, ⟨[7, 8, 9], 300⟩] [7, 8, 10] [2, 3] 1 := by decide

example : ¬ Hit [⟨[7, 8], 300⟩] [7, 8] [2] 1800 := by decide

example : Hit [⟨[7, 8], 3600⟩] [7, 8] [2] 1800 := by decide

end PettaClaw.ExplicitPromptCache

#print axioms PettaClaw.ExplicitPromptCache.only_full_write_misses_changed_prompt
#print axioms PettaClaw.ExplicitPromptCache.written_shared_prefix_is_reusable
