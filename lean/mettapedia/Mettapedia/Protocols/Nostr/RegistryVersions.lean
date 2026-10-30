import Mettapedia.Protocols.Nostr.Event

/-!
# Registry versions: principals, keys, rotation and revocation

A registry says which keys speak for which principals. A principal has a stable identifier, while
its keys can change: a key is rotated when its owner moves to a new one, and revoked when it is
lost or stolen. Threads, receipts and grants name the principal, so they outlive a rotation.

The registry comes in versions. A version is a number and, for each principal, its keys. The
registry authority issues each version as an event of its own key. A reader starts from a pinned
version, and takes a new one only when the authority signed it and its number is higher than the
number of the version it holds.

Theorems:
- `follow_issued`: every version the reader holds is the pinned one, or one that the authority's
  owner issued with a higher number. Hence `speaksFor_sound`: a key that the reader takes as
  speaking for a principal is listed for it by the pinned version or by an issued one. A thief
  holding an old key, or any other key that is not the authority's, gains no standing by signing.
- `update_old`: a replayed version numbered no higher than the reader's changes nothing.
  `revoked_until_reissued`: a key that the reader's version does not list regains standing only
  through a version the authority issued with a higher number that lists it. Without the number
  check, a replay of an older version restores a revoked key (`rollback_restores`). The number
  protects only while the reader keeps it: a reader that restarts from the pinned version takes
  the replay again (`restart_rollback`), so the version held must survive restarts.
- `selfRotation_takeover`: where a listed key alone signs its successor, a thief with that key
  moves the principal to its own key, and a rotation the owner then signs with the old key changes
  nothing.
- `grant_follows_rotation`: a grant to a principal holds for the keys that the current version
  lists, so it passes to a rotated key and ends for a revoked one. A grant to a key outlives the
  key's revocation (`grantByKey_outlives`).

Not modelled: how versions reach readers. A reader acts on the newest version it holds, so a
revocation takes effect at each reader when it arrives there. Also not modelled: compromise of
the authority's key, and equivocation, where the authority signs two versions with one number.
Signatures by several authorities, and rotation committed to in advance (pre-rotation), are
separate designs.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Nostr.RegistryVersions

open Mettapedia.Protocols.Nostr

/-- A principal's stable identifier. -/
abbrev Principal := String

/-- A registry version: its number and each principal's keys. -/
structure Version where
  num : ℕ
  keys : Principal → List PubKey

/-- A key speaks for a principal in a version when the version lists it. -/
def speaksFor (v : Version) (k : PubKey) (p : Principal) : Prop := k ∈ v.keys p

/-- The reader's settings: the authority's key, and how a version reads from an event's content. -/
structure Reader where
  authority : PubKey
  decode : String → Option Version

namespace Reader

/-- The version an event carries: a valid event of the authority's key whose content reads as a
version. -/
def carried (R : Reader) (P : Primitives) (e : Event) : Option Version :=
  if e.check P && e.pubkey == R.authority then R.decode e.content else none

/-- The reader takes a carried version only when its number is higher. -/
def update (R : Reader) (P : Primitives) (cur : Version) (e : Event) : Version :=
  match R.carried P e with
  | some v => if cur.num < v.num then v else cur
  | none => cur

/-- The reader's version after a stream of events. -/
def follow (R : Reader) (P : Primitives) (v₀ : Version) (es : List Event) : Version :=
  es.foldl (R.update P) v₀

/-- The reader without the number check: it takes every version the authority signed. -/
def updateAny (R : Reader) (P : Primitives) (cur : Version) (e : Event) : Version :=
  (R.carried P e).getD cur

end Reader

/-- A version the authority's owner issued: an event of the authority's key, composed by its owner,
carries it. -/
def Issued (R : Reader) {P : Primitives} (A : Authorship P) (v : Version) : Prop :=
  ∃ u : Unsigned, A.authored u ∧ u.pubkey = R.authority ∧ R.decode u.content = some v

theorem carried_issued {R : Reader} {P : Primitives} (A : Authorship P) (cf : P.CollisionFree)
    (hk : ¬ A.compromised R.authority) {e : Event} {v : Version} (h : R.carried P e = some v) :
    Issued R A v := by
  unfold Reader.carried at h
  split at h
  · next hc =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact ⟨e.toUnsigned, authentic A cf ((Event.check_iff P e).mp hc.1) (hc.2 ▸ hk), hc.2, h⟩
  · cases h

/-- **Every version the reader holds is the pinned one, or one the authority's owner issued, with
a higher number.** -/
theorem follow_issued {R : Reader} {P : Primitives} (A : Authorship P) (cf : P.CollisionFree)
    (hk : ¬ A.compromised R.authority) (v₀ : Version) (es : List Event) :
    R.follow P v₀ es = v₀ ∨
      (Issued R A (R.follow P v₀ es) ∧ v₀.num < (R.follow P v₀ es).num) := by
  unfold Reader.follow
  induction es generalizing v₀ with
  | nil => exact Or.inl rfl
  | cons e es ih =>
    rw [List.foldl_cons]
    have hstep : R.update P v₀ e = v₀ ∨
        (Issued R A (R.update P v₀ e) ∧ v₀.num < (R.update P v₀ e).num) := by
      unfold Reader.update
      split
      · next v hv =>
        split
        · next hlt => exact Or.inr ⟨carried_issued A cf hk hv, hlt⟩
        · exact Or.inl rfl
      · exact Or.inl rfl
    rcases ih (R.update P v₀ e) with h | ⟨hi, hlt⟩
    · rw [h]
      exact hstep
    · refine Or.inr ⟨hi, ?_⟩
      rcases hstep with h' | ⟨-, h'⟩
      · simpa [h'] using hlt
      · exact h'.trans hlt

/-- **Standing comes from the authority.** A key that the reader takes as speaking for a principal
is listed for it by the pinned version, or by a version the authority's owner issued. -/
theorem speaksFor_sound {R : Reader} {P : Primitives} (A : Authorship P) (cf : P.CollisionFree)
    (hk : ¬ A.compromised R.authority) (v₀ : Version) (es : List Event) {k : PubKey}
    {p : Principal} (hs : speaksFor (R.follow P v₀ es) k p) :
    speaksFor v₀ k p ∨ ∃ v, Issued R A v ∧ speaksFor v k p := by
  rcases follow_issued A cf hk v₀ es with h | ⟨hi, -⟩
  · exact Or.inl (h ▸ hs)
  · exact Or.inr ⟨_, hi, hs⟩

/-- **No rollback.** A carried version numbered no higher than the reader's changes nothing. -/
theorem update_old {R : Reader} {P : Primitives} {cur v : Version} {e : Event}
    (h : R.carried P e = some v) (hle : v.num ≤ cur.num) : R.update P cur e = cur := by
  simp [Reader.update, h, Nat.not_lt.mpr hle]

/-- **A revocation holds until the authority says otherwise.** A key that the pinned version does
not list for a principal regains standing only through a version that the authority's owner
issued, numbered higher than the pinned one, that lists it. -/
theorem revoked_until_reissued {R : Reader} {P : Primitives} (A : Authorship P)
    (cf : P.CollisionFree) (hk : ¬ A.compromised R.authority) {v₀ : Version} {k : PubKey}
    {p : Principal} (hrev : ¬ speaksFor v₀ k p) (es : List Event)
    (hs : speaksFor (R.follow P v₀ es) k p) :
    ∃ v, Issued R A v ∧ v₀.num < v.num ∧ speaksFor v k p := by
  rcases follow_issued A cf hk v₀ es with h | ⟨hi, hlt⟩
  · exact absurd (h ▸ hs) hrev
  · exact ⟨_, hi, hlt, hs⟩

section Examples

/-- Version 1 lists the key `old` for `alice`, and version 2 rotates her to `new`. -/
private def v₀ : Version := ⟨0, fun _ => []⟩
private def v₁ : Version := ⟨1, fun p => if p = "alice" then ["old"] else []⟩
private def v₂ : Version := ⟨2, fun p => if p = "alice" then ["new"] else []⟩

private def decodeV : String → Option Version := fun s =>
  if s = "v1" then some v₁ else if s = "v2" then some v₂ else none

private def u₁ : Unsigned := ⟨"auth", 0, 30078, [], "v1"⟩
private def u₂ : Unsigned := ⟨"auth", 1, 30078, [], "v2"⟩

/-- **Necessity of the number check.** The authority issued version 1 and then version 2, which
rotates `alice` from `old` to `new`. A replay of version 1 restores `old` without the number
check. The reader with it keeps `old` revoked. The hash is collision free and the signature
assumption holds. -/
theorem rollback_restores :
    ∃ (P : Primitives) (A : Authorship P) (R : Reader) (es : List Event),
      P.CollisionFree ∧ ¬ A.compromised R.authority ∧
      speaksFor (es.foldl (R.updateAny P) v₀) "old" "alice" ∧
      ¬ speaksFor (R.follow P v₀ es) "old" "alice" := by
  obtain ⟨h, hinj⟩ := exists_injective_hash
  let P : Primitives := ⟨h, fun k d _ => k == "auth" && (d == h u₁ || d == h u₂)⟩
  let A : Authorship P :=
    { authored := fun u => u = u₁ ∨ u = u₂
      compromised := fun k => k ≠ "auth"
      sound := fun k d s hv hc => by
        simp only [P, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hv
        simp only [ne_eq, Decidable.not_not] at hc
        obtain ⟨-, hd | hd⟩ := hv
        · exact ⟨u₁, Or.inl rfl, by simp [u₁, hc], hd.symm⟩
        · exact ⟨u₂, Or.inr rfl, by simp [u₂, hc], hd.symm⟩ }
  let R : Reader := ⟨"auth", decodeV⟩
  let e₁ : Event := { u₁ with id := h u₁, sig := "s1" }
  let e₂ : Event := { u₂ with id := h u₂, sig := "s2" }
  refine ⟨P, A, R, [e₁, e₂, e₁], hinj, by simp [A, R], ?_, ?_⟩
  · simp [Reader.updateAny, Reader.carried, Event.check, P, R, e₁, e₂, u₁, u₂, decodeV, v₁, v₂,
      speaksFor]
  · simp [Reader.follow, Reader.update, Reader.carried, Event.check, P, R, e₁, e₂, u₁, u₂, decodeV,
      v₀, v₁, v₂, speaksFor]

/-- **The version must survive restarts.** The reader came to hold version 2, which rotates
`alice` from `old` to `new`. Restarted from the pinned version, it takes a replay of version 1, and
`old` speaks for `alice` again. Had it kept version 2, it would refuse the replay. The hash is
collision free and the signature assumption holds. -/
theorem restart_rollback :
    ∃ (P : Primitives) (A : Authorship P) (R : Reader) (e₁ e₂ : Event),
      P.CollisionFree ∧ ¬ A.compromised R.authority ∧ R.follow P v₀ [e₁, e₂] = v₂ ∧
      speaksFor (R.follow P v₀ [e₁]) "old" "alice" ∧
      ¬ speaksFor (R.follow P v₂ [e₁]) "old" "alice" := by
  obtain ⟨h, hinj⟩ := exists_injective_hash
  let P : Primitives := ⟨h, fun k d _ => k == "auth" && (d == h u₁ || d == h u₂)⟩
  let A : Authorship P :=
    { authored := fun u => u = u₁ ∨ u = u₂
      compromised := fun k => k ≠ "auth"
      sound := fun k d s hv hc => by
        simp only [P, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hv
        simp only [ne_eq, Decidable.not_not] at hc
        obtain ⟨-, hd | hd⟩ := hv
        · exact ⟨u₁, Or.inl rfl, by simp [u₁, hc], hd.symm⟩
        · exact ⟨u₂, Or.inr rfl, by simp [u₂, hc], hd.symm⟩ }
  let R : Reader := ⟨"auth", decodeV⟩
  let e₁ : Event := { u₁ with id := h u₁, sig := "s1" }
  let e₂ : Event := { u₂ with id := h u₂, sig := "s2" }
  refine ⟨P, A, R, e₁, e₂, hinj, by simp [A, R], ?_, ?_, ?_⟩
  · simp [Reader.follow, Reader.update, Reader.carried, Event.check, P, R, e₁, e₂, u₁, u₂, decodeV,
      v₀, v₁, v₂]
  · simp [Reader.follow, Reader.update, Reader.carried, Event.check, P, R, e₁, u₁, decodeV, v₀,
      v₁, speaksFor]
  · simp [Reader.follow, Reader.update, Reader.carried, Event.check, P, R, e₁, u₁, decodeV, v₁,
      v₂, speaksFor]

/-- Key-signed rotation for the principal `p`: a valid event from a key the version lists for `p`
names that key's successor in its content, and the successor replaces it. -/
def selfRotate (P : Primitives) (p : Principal) (cur : Version) (e : Event) : Version :=
  if e.check P && (cur.keys p).contains e.pubkey then
    { cur with
      keys := fun q =>
        if q = p then (cur.keys p).map fun k => if k = e.pubkey then e.content else k
        else cur.keys q }
  else cur

/-- **Necessity of rotation by the authority.** Under key-signed rotation, a thief who stole
`alice`'s key `a` rotates her to its own key `t`. Afterwards `a` no longer speaks for her, so a
rotation signed by her owner with `a` changes nothing. The hash is collision free and the
signature assumption holds. -/
theorem selfRotation_takeover :
    ∃ (P : Primitives) (A : Authorship P) (thief owner : Event),
      P.CollisionFree ∧ A.compromised "a" ∧ thief.pubkey = "a" ∧ owner.pubkey = "a" ∧
      A.authored owner.toUnsigned ∧
      speaksFor (selfRotate P "alice" ⟨1, fun _ => ["a"]⟩ thief) "t" "alice" ∧
      ¬ speaksFor (selfRotate P "alice" ⟨1, fun _ => ["a"]⟩ thief) "a" "alice" ∧
      selfRotate P "alice" (selfRotate P "alice" ⟨1, fun _ => ["a"]⟩ thief) owner =
        selfRotate P "alice" ⟨1, fun _ => ["a"]⟩ thief := by
  obtain ⟨h, hinj⟩ := exists_injective_hash
  let tu : Unsigned := ⟨"a", 0, 1, [], "t"⟩
  let ou : Unsigned := ⟨"a", 1, 1, [], "b"⟩
  let P : Primitives := ⟨h, fun k _ _ => k == "a"⟩
  let A : Authorship P :=
    { authored := fun u => u = ou
      compromised := fun k => k = "a"
      sound := fun k d s hv hc => by
        simp only [P, beq_iff_eq] at hv
        exact absurd hv hc }
  let thief : Event := { tu with id := h tu, sig := "x" }
  let owner : Event := { ou with id := h ou, sig := "y" }
  refine ⟨P, A, thief, owner, hinj, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [selfRotate, Event.check, P, thief, tu, speaksFor]
  · simp [selfRotate, Event.check, P, thief, tu, speaksFor]
  · simp [selfRotate, Event.check, P, thief, owner, tu, ou]

/-- A grant to principals holds for a key when the version lists the key for one of them. -/
def grantedTo (v : Version) (G : List Principal) (k : PubKey) : Prop := ∃ p ∈ G, k ∈ v.keys p

/-- **A grant to a principal follows its keys.** Granted to `alice`, it holds for `old` under
version 1, and under version 2 it holds for `new` and no longer for `old`. -/
theorem grant_follows_rotation :
    grantedTo v₁ ["alice"] "old" ∧ grantedTo v₂ ["alice"] "new" ∧
      ¬ grantedTo v₂ ["alice"] "old" := by
  simp [grantedTo, v₁, v₂]

/-- A grant to keys holds for exactly the keys it names, whatever the registry says. -/
def grantedToKeys (G : List PubKey) (k : PubKey) : Prop := k ∈ G

/-- **A grant to a key outlives its revocation.** Version 2 revokes `old`, yet a grant made to the
key `old` still holds for it, until every such grant is changed as well. -/
theorem grantByKey_outlives : ¬ speaksFor v₂ "old" "alice" ∧ grantedToKeys ["old"] "old" := by
  simp [speaksFor, grantedToKeys, v₂]

end Examples

end Mettapedia.Protocols.Nostr.RegistryVersions
