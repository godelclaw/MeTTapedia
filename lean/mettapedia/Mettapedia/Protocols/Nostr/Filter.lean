import Mettapedia.Protocols.Nostr.Event
import Mathlib.Data.List.Sort

/-!
# Nostr filters (NIP-01)

A subscription asks for events by a list of filters. Within one filter every
condition must hold, and a list condition holds when the event's field is one of
the values listed. An event matches a subscription when it matches any of its
filters. `since` and `until` bound the creation time inclusively, and a tag
condition `#x` holds when one of the event's `x` tag values is listed.

`limit` applies to stored events only: a relay returns the newest that many,
newest first, with equal times ordered by identifier, and a relay may impose its
own cap. `select_complete` shows that every admitted match is returned while
the matches fit under the limit. `select_truncates` shows that past it, older
matches are not returned at all, so a reader that never narrows its filter by
time stops seeing older mail once newer mail fills the cap.
-/

namespace Mettapedia.Protocols.Nostr

/-- A NIP-01 filter. An absent condition holds of every event. -/
structure Filter where
  ids : Option (List EventId) := none
  authors : Option (List PubKey) := none
  kinds : Option (List Nat) := none
  /-- `#x` conditions: a tag name and the values accepted. -/
  tags : List (String × List String) := []
  since : Option Int := none
  «until» : Option Int := none
  limit : Option Nat := none
deriving DecidableEq, Repr

namespace Filter

/-- Every condition of the filter holds of the event. -/
def accepts (f : Filter) (e : Event) : Bool :=
  f.ids.all (·.contains e.id) && f.authors.all (·.contains e.pubkey) &&
    f.kinds.all (·.contains e.kind) && f.since.all (· ≤ e.createdAt) &&
    f.«until».all (e.createdAt ≤ ·) &&
    f.tags.all fun c => (tagValues e.tags c.1).any (c.2.contains ·)

/-- `a` comes before `b`: newer first, equal times by identifier. -/
def NewerFirst (a b : Event) : Prop :=
  b.createdAt < a.createdAt ∨ (a.createdAt = b.createdAt ∧ a.id ≤ b.id)

instance : DecidableRel NewerFirst := fun a b => by unfold NewerFirst; infer_instance

/-- The stored events a filter returns among those `admit` lets the reader see:
the newest `limit` of them, never more than `cap`, newest first. -/
def select (f : Filter) (cap : Nat) (admit : Event → Bool) (store : List Event) : List Event :=
  ((store.filter fun e => admit e && f.accepts e).insertionSort NewerFirst).take (min (f.limit.getD cap) cap)

theorem mem_select {f : Filter} {cap : Nat} {admit : Event → Bool} {store : List Event} {e : Event}
    (h : e ∈ f.select cap admit store) : e ∈ store ∧ admit e = true ∧ f.accepts e = true := by
  unfold select at h
  have h' := (List.perm_insertionSort NewerFirst _).mem_iff.mp (List.mem_of_mem_take h)
  simp only [List.mem_filter, Bool.and_eq_true] at h'
  exact ⟨h'.1, h'.2.1, h'.2.2⟩

/-- While the admitted matches fit under the limit, every one is returned. -/
theorem select_complete {f : Filter} {cap : Nat} {admit : Event → Bool} {store : List Event}
    {e : Event} (hs : e ∈ store) (ha : admit e = true) (hm : f.accepts e = true)
    (fits : (store.filter fun e => admit e && f.accepts e).length ≤ min (f.limit.getD cap) cap) :
    e ∈ f.select cap admit store := by
  unfold select
  rw [List.take_of_length_le (by rw [(List.perm_insertionSort NewerFirst _).length_eq]; exact fits)]
  exact (List.perm_insertionSort NewerFirst _).mem_iff.mpr (List.mem_filter.mpr ⟨hs, by simp [ha, hm]⟩)

end Filter

/-- An event matches a subscription when it matches one of its filters. -/
def acceptsAny (fs : List Filter) (e : Event) : Bool := fs.any (·.accepts e)

/-- Past the cap, an older match is not returned: with a cap of one, the older
of two matching events is invisible to a filter without a time bound. -/
theorem select_truncates : ∃ (store : List Event) (e : Event),
    e ∈ store ∧ ({} : Filter).accepts e = true ∧ e ∉ ({} : Filter).select 1 (fun _ => true) store := by
  let old : Event := ⟨⟨"a", 1, 3838, [], ""⟩, "x", ""⟩
  let new : Event := ⟨⟨"a", 2, 3838, [], ""⟩, "y", ""⟩
  refine ⟨[old, new], old, by simp, rfl, ?_⟩
  decide

end Mettapedia.Protocols.Nostr
