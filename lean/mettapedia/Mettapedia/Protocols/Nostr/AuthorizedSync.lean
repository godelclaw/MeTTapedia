import Mettapedia.Protocols.Nostr.Relay
import Mettapedia.Protocols.Sync.Rbsr

/-!
# Reconciling only what the reader may read

A gated relay serves a signed-in key only the events it may read
(`readableBy`: the key wrote the event, or a `p` tag names it). A NIP-77 session
must reconcile over those same events, and over all of them, because a session
has no cap.

- `mem_negView`: the session's view for key `me` and filter `f` is exactly the
  stored events `me` may read that `f` accepts.
- `answer_sub_negView`: every event a REQ returns is in that view. Past the cap
  the REQ returns less (`cap_hides`), and the session still covers the rest.
- `reconcile_readable`: every event the server's run reports is stored, readable
  by `me` and accepted by `f`.
- `reconcile_congr` and `splits_congr`: the run depends on the view alone. Two
  relays with the same view give the same report and the same number of splits,
  for every client set and range.
- `negView_store_unreadable`: storing an event that `me` may not read leaves the
  view, and so everything the run tells `me`, unchanged.

Mutant: reconciling over the whole store reports an event the reader may not
read (`wholeStore_leaks`), where the view reports nothing (`view_hides_secret`).

The model is `Relay.lean`'s store and read rule. Not modelled: the NEG-OPEN,
NEG-MSG and NEG-CLOSE messages, and the relay's handling of them.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Nostr.AuthorizedSync

open Mettapedia.Protocols.Nostr
open Mettapedia.Protocols.Sync.Rbsr

/-- The events a NIP-77 session reconciles for the signed-in key `me` and the
filter `f`: the stored events `me` may read that `f` accepts, with no cap. -/
def negView (r : Relay) (me : PubKey) (f : Filter) : List Event :=
  r.store.filter fun e => readableBy e me && f.accepts e

/-- **D1.** The view is exactly the readable, accepted stored events. -/
theorem mem_negView {r : Relay} {me : PubKey} {f : Filter} {e : Event} :
    e ∈ negView r me f ↔ e ∈ r.store ∧ readableBy e me = true ∧ f.accepts e = true := by
  simp [negView, Bool.and_eq_true]

/-- **D1.** Every event a REQ with the one filter `f` returns is in the view. -/
theorem answer_sub_negView (cfg : Config) (r : Relay) (me : PubKey) (f : Filter) {e : Event}
    (h : e ∈ Relay.answer cfg r me [f]) : e ∈ negView r me f := by
  unfold Relay.answer at h
  have h' := mem_of_mem_dedupById h
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at h'
  obtain ⟨hs, ha, hm⟩ := Filter.mem_select h'
  exact mem_negView.mpr ⟨hs, ha, hm⟩

section Run

variable {H : Type} [DecidableEq H]

/-- The server's run for the session: reconciliation over the view. -/
def reconcile (key : Event → Nat) (fp : Finset Event → H) (r : Relay) (me : PubKey) (f : Filter)
    (C : Finset Event) (lo hi : Nat) : Finset Event :=
  rbsrDiff key fp (negView r me f).toFinset C lo hi

/-- Every event the run reports is stored, readable by `me` and accepted by `f`. -/
theorem reconcile_readable (key : Event → Nat) (fp : Finset Event → H) (r : Relay) (me : PubKey)
    (f : Filter) (C : Finset Event) (lo hi : Nat) {e : Event}
    (h : e ∈ reconcile key fp r me f C lo hi) :
    e ∈ r.store ∧ readableBy e me = true ∧ f.accepts e = true := by
  have hs := Finset.mem_sdiff.mp (rbsrDiff_sound key fp _ C lo hi h)
  exact mem_negView.mp (List.mem_toFinset.mp (mem_sliceRange.mp hs.1).1)

/-- **D2.** The run depends on the view alone. -/
theorem reconcile_congr (key : Event → Nat) (fp : Finset Event → H) {r r' : Relay} {me : PubKey}
    {f : Filter} (hv : ∀ e, e ∈ negView r me f ↔ e ∈ negView r' me f) (C : Finset Event)
    (lo hi : Nat) : reconcile key fp r me f C lo hi = reconcile key fp r' me f C lo hi := by
  have : (negView r me f).toFinset = (negView r' me f).toFinset := by
    ext e
    simp only [List.mem_toFinset]
    exact hv e
  simp only [reconcile, this]

/-- **D2.** So does the number of ranges it splits. -/
theorem splits_congr (key : Event → Nat) (fp : Finset Event → H) {r r' : Relay} {me : PubKey}
    {f : Filter} (hv : ∀ e, e ∈ negView r me f ↔ e ∈ negView r' me f) (C : Finset Event)
    (lo hi : Nat) :
    rbsrSplits key fp (negView r me f).toFinset C lo hi =
      rbsrSplits key fp (negView r' me f).toFinset C lo hi := by
  have : (negView r me f).toFinset = (negView r' me f).toFinset := by
    ext e
    simp only [List.mem_toFinset]
    exact hv e
  rw [this]

end Run

/-- Storing an event that `me` may not read leaves `me`'s view unchanged. -/
theorem negView_store_unreadable (r : Relay) (me : PubKey) (f : Filter) {e : Event}
    (h : readableBy e me = false) :
    negView ⟨r.allow, e :: r.store, r.conns⟩ me f = negView r me f := by
  simp [negView, h]

/-! ## Examples and the mutant -/

section Examples

/-- An event from `a` with no `p` tag: `b` may not read it. -/
private def secret : Event := ⟨⟨"a", 1, 3838, [], ""⟩, "x", ""⟩

/-- Two events addressed to `b`. -/
private def toB₁ : Event := ⟨⟨"a", 1, 3838, [["p", "b"]], ""⟩, "y", ""⟩
private def toB₂ : Event := ⟨⟨"a", 2, 3838, [["p", "b"]], ""⟩, "z", ""⟩

/-- With a cap of one, a REQ returns one of `b`'s two events; the session's
view has both. -/
theorem cap_hides :
    (Relay.answer { relayUrls := [], maxLimit := 1 } ⟨["a", "b"], [toB₁, toB₂], []⟩ "b" [{}]).length = 1 ∧
      (negView ⟨["a", "b"], [toB₁, toB₂], []⟩ "b" {}).length = 2 := by
  decide

/-- The mutant of `reconcile_readable`: a run over the whole store reports an
event that `b` may not read. -/
theorem wholeStore_leaks :
    readableBy secret "b" = false ∧
      secret ∈ rbsrDiff (fun _ => 0) Finset.card ([secret].toFinset) (∅ : Finset Event) 0 1 := by
  decide

/-- The run over the view reports nothing to `b` on that store. -/
theorem view_hides_secret :
    reconcile (fun _ => 0) Finset.card ⟨["a", "b"], [secret], []⟩ "b" {} ∅ 0 1 = ∅ := by
  decide

/-- `reconcile_congr` with its hypothesis met by different stores: storing the
secret changes nothing `b` reconciles. -/
example : reconcile (fun _ => 0) Finset.card ⟨["a", "b"], [secret, toB₁], []⟩ "b" {} ∅ 0 1 =
    reconcile (fun _ => 0) Finset.card ⟨["a", "b"], [toB₁], []⟩ "b" {} ∅ 0 1 :=
  reconcile_congr _ _ (fun e => by
    rw [negView_store_unreadable ⟨["a", "b"], [toB₁], []⟩ "b" {} (by decide)]) ∅ 0 1

end Examples

end Mettapedia.Protocols.Nostr.AuthorizedSync
