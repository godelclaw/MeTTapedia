import Mettapedia.Languages.MeTTa.MetavariableFrameStore

/-!
# Escape law for captured frame images

A closure that escapes its activation retains one owner count on the frame token
it captured (`Image.capture?`). This file states what that retention buys. Along
any allocator history in which the holder never spends its own count, the token
stays live, and observing the captured image with authority (`Image.lookupOwned`)
returns exactly the values present at capture. Other frames may be allocated,
shared, and released freely in between, and the same frame may be shared and
released by other holders.

Complete-directory capture (`ImageOf.captureAll?`) retains every actual present
frame. Its escape law protects both a contextual payload and distinct lexical
frames referenced inside that directory. The negative controls in the parent
file separate loss of a projected frame from loss of its owner count.

The negative facts that complete the picture are in the parent file:
`stale_owned_lookup` (a superseded incarnation never observes) and
`final_release_never_revives` (the last release ends authority for good).
-/

set_option autoImplicit false

universe u

namespace Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrame (Frame FrameEnv)
open private put put_other changeOwners? changeOwners_success live_witness
  from Mettapedia.Languages.MeTTa.MetavariableFrameStore

/-! ## Steps on other handles leave a live token untouched -/

private theorem changeOwners_other {allocator next : Allocator} {other : Token}
    {change : Cell → Cell} (success : changeOwners? allocator other change = some next)
    (handle : Nat) (distinct : other.handle ≠ handle) :
    next.cells[handle]? = allocator.cells[handle]? := by
  obtain ⟨cell, _, _, _, rfl⟩ := changeOwners_success success
  exact put_other allocator other.handle handle distinct (change cell)

/-- A successful owner change on a token sharing a live token's handle is a change on
that very token: the incarnation is pinned by the live generation. -/
private theorem changeOwners_same_handle {allocator next : Allocator} {token other : Token}
    {change : Cell → Cell} (live : Live allocator token)
    (success : changeOwners? allocator other change = some next)
    (same : other.handle = token.handle) : other = token := by
  obtain ⟨cell, present, generation, _, _⟩ := changeOwners_success success
  obtain ⟨cell', present', generation', _⟩ := live_witness live
  rw [same, present'] at present
  cases Option.some.inj present
  cases other
  cases token
  simp only [Token.mk.injEq]
  exact ⟨same, generation.symm.trans generation'⟩

theorem release_other_preserves_live {allocator next : Allocator} {token other : Token}
    (live : Live allocator token) (distinct : other ≠ token)
    (released : release? allocator other = some next) : Live next token := by
  by_cases same : other.handle = token.handle
  · exact absurd (changeOwners_same_handle live released same) distinct
  · have eq := changeOwners_other released token.handle same
    unfold Live at live ⊢
    rw [eq]
    exact live

/-! ## Histories in which a holder keeps its own count -/

/-- One allocator step that never spends `token`'s retention held by the escaped
closure: any allocation, any retention, a release of a different token, or a release of
`token` by another holder while it is shared. -/
inductive HeldStep (token : Token) : Allocator → Allocator → Prop where
  | allocate {before after : Allocator} {handle : Nat} {fresh : Token}
      (success : allocate? before handle = some (after, fresh)) : HeldStep token before after
  | retain {before after : Allocator} {other : Token}
      (success : retain? before other = some after) : HeldStep token before after
  | releaseOther {before after : Allocator} {other : Token} (distinct : other ≠ token)
      (success : release? before other = some after) : HeldStep token before after
  | releaseShared {before after : Allocator} {cell : Cell}
      (present : before.cells[token.handle]? = some cell) (shared : 1 < cell.owners)
      (success : release? before token = some after) : HeldStep token before after

inductive HeldTrace (token : Token) : Allocator → Allocator → Prop where
  | refl (allocator : Allocator) : HeldTrace token allocator allocator
  | next {before middle after : Allocator} (history : HeldTrace token before middle)
      (step : HeldStep token middle after) : HeldTrace token before after

theorem HeldTrace.trans {token : Token} {first middle last : Allocator}
    (before : HeldTrace token first middle) (after : HeldTrace token middle last) :
    HeldTrace token first last := by
  induction after with
  | refl => exact before
  | next _ step ih => exact .next ih step

theorem HeldStep.toStep {token : Token} {before after : Allocator}
    (step : HeldStep token before after) : Step before after := by
  cases step with
  | allocate success => exact .allocate success
  | retain success => exact .retain success
  | releaseOther _ success => exact .release success
  | releaseShared _ _ success => exact .release success

theorem HeldTrace.toTrace {token : Token} {before after : Allocator}
    (trace : HeldTrace token before after) : Trace before after := by
  induction trace with
  | refl => exact .refl _
  | next _ step ih => exact .next ih step.toStep

theorem HeldStep.live {token : Token} {before after : Allocator}
    (live : Live before token) (step : HeldStep token before after) : Live after token := by
  cases step with
  | allocate success => exact (allocation_separates_live success live).2.1
  | retain success => exact retain_preserves_live live success
  | releaseOther distinct success => exact release_other_preserves_live live distinct success
  | releaseShared present shared success => exact release_shared_stays_live present shared success

/-- A token whose holder never spends its own count stays live through any held history. -/
theorem HeldTrace.live {token : Token} {before after : Allocator}
    (live : Live before token) (trace : HeldTrace token before after) : Live after token := by
  induction trace with
  | refl => exact live
  | next _ step ih => exact step.live ih

/-! ## The escape law -/

/-- What an escaped closure is promised. After `capture?`, for as long as the closure holds
its owner count, authoritative observation of the captured image returns exactly the
values the source image held at capture, whatever else the allocator has done since. -/
theorem Image.escape_observes_capture {Payload : Type u} {allocator next after : Allocator}
    {image captured : ImageOf Payload} {token : Token}
    (success : image.capture? allocator token = some (next, captured))
    (held : HeldTrace token next after) (slot : Nat) :
    captured.lookupOwned after (token.ref slot) = image.lookup (token.ref slot) := by
  have live : Live after token := held.live (Image.capture_live success)
  change (if Live after token then captured.lookup (token.ref slot) else none) = _
  rw [if_pos live]
  exact Image.capture_preserves_lookup success slot

/-- Every captured frame remains authoritatively observable while the holder
keeps all its retained tokens. This includes unbound slots, invalid references,
and frames whose inventories contain no slots. -/
theorem ImageOf.escape_observes_captureAll {Payload : Type u}
    {allocator next after : Allocator} {image captured : ImageOf Payload}
    (success : image.captureAll? allocator = some (next, captured))
    (held : ∀ token ∈ image.inventory, HeldTrace token next after) (ref : MetavariableFrameStore.Ref) :
    captured.lookupOwned after ref = image.lookup ref := by
  rw [ImageOf.captureAll_preserves_image success]
  apply ImageOf.lookupOwned_eq_lookup
  intro token member
  exact (held token member).live (ImageOf.captureAll_live success token member)

/-- Escaping a selected frame preserves raw unbound markers, slot versions,
the frame's activation boundary and the captured directory clock together. -/
theorem ImageOf.escape_readSlot_capture {Payload : Type u} {allocator next after : Allocator}
    {image captured : ImageOf Payload} {token : Token}
    (success : image.capture? allocator token = some (next, captured))
    (held : HeldTrace token next after) (slot : Nat) :
    captured.readSlotOwned? after (token.ref slot) = image.readSlot? (token.ref slot) := by
  have live : Live after token := held.live (Image.capture_live success)
  change (if Live after token then captured.readSlot? (token.ref slot) else none) = _
  rw [if_pos live]
  exact ImageOf.capture_preserves_readSlot success slot

/-- Whole-image ownership retention licenses complete metadata readback after
the original holder releases its owners, including every valid unbound slot. -/
theorem ImageOf.escape_readSlot_captureAll {Payload : Type u}
    {allocator next after : Allocator} {image captured : ImageOf Payload}
    (success : image.captureAll? allocator = some (next, captured))
    (held : ∀ token ∈ image.inventory, HeldTrace token next after)
    (ref : MetavariableFrameStore.Ref) :
    captured.readSlotOwned? after ref = image.readSlot? ref := by
  rw [ImageOf.captureAll_preserves_image success]
  apply ImageOf.readSlotOwned?_eq_readSlot
  intro token member
  exact (held token member).live (ImageOf.captureAll_live success token member)

/-- The same token set can be retained for every frame through one checked batch:
retains never spend any existing holder's count. -/
theorem retainAll?_held {allocator next : Allocator} {tokens : List Token}
    (success : retainAll? allocator tokens = some next) (heldToken : Token) :
    HeldTrace heldToken allocator next := by
  induction tokens generalizing allocator with
  | nil =>
    simp only [retainAll?_nil, Option.some.injEq] at success
    subst next
    exact .refl _
  | cons token tokens ih =>
    rw [retainAll?_cons] at success
    cases retained : retain? allocator token with
    | none => simp [retained] at success
    | some middle =>
      have rest : retainAll? middle tokens = some next := by simpa [retained] using success
      exact HeldTrace.trans (.next (.refl _) (.retain retained)) (ih rest)

/-! The complete capture's two-frame control follows actual source-owner releases. -/

open private twoFrameImage twoWholeCapture twoWholeReleasedFirst twoWholeReleasedSecond
  twoFirstAllocation twoSecondAllocation twoContextualPayload twoLexicalPayload
  from Mettapedia.Languages.MeTTa.MetavariableFrameStore

theorem canary_whole_capture_source_releases_hold_every_token :
    ∀ token ∈ twoFrameImage.inventory,
      HeldTrace token twoWholeCapture.1 twoWholeReleasedSecond := by
  intro token member
  rw [canary_whole_inventory_is_actual_frames] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · have first : HeldStep twoFirstAllocation.2 twoWholeCapture.1 twoWholeReleasedFirst :=
      .releaseShared (cell := ⟨0, 2⟩) (by decide) (by decide) (by decide)
    have second : HeldStep twoFirstAllocation.2 twoWholeReleasedFirst twoWholeReleasedSecond :=
      .releaseOther (other := twoSecondAllocation.2) (by decide) (by decide)
    exact .next (.next (.refl _) first) second
  · have first : HeldStep twoSecondAllocation.2 twoWholeCapture.1 twoWholeReleasedFirst :=
      .releaseOther (other := twoFirstAllocation.2) (by decide) (by decide)
    have second : HeldStep twoSecondAllocation.2 twoWholeReleasedFirst twoWholeReleasedSecond :=
      .releaseShared (cell := ⟨0, 2⟩) (by decide) (by decide) (by decide)
    exact .next (.next (.refl _) first) second

/-- Both the retained raw payload and its different lexical frame remain observable. -/
theorem canary_whole_capture_escape_observes_payload_and_context :
    twoWholeCapture.2.lookupOwned twoWholeReleasedSecond (twoFirstAllocation.2.ref 0) =
      some (some twoContextualPayload) ∧
      twoWholeCapture.2.lookupOwned twoWholeReleasedSecond (twoSecondAllocation.2.ref 0) =
        some (some twoLexicalPayload) := by
  have captured : twoFrameImage.captureAll? twoSecondAllocation.1 = some twoWholeCapture :=
    (Option.some_get (by decide)).symm
  constructor
  · exact (ImageOf.escape_observes_captureAll (captured := twoWholeCapture.2) captured
      canary_whole_capture_source_releases_hold_every_token (twoFirstAllocation.2.ref 0)).trans
        (by decide)
  · exact (ImageOf.escape_observes_captureAll (captured := twoWholeCapture.2) captured
      canary_whole_capture_source_releases_hold_every_token (twoSecondAllocation.2.ref 0)).trans
        (by decide)

/-! ## Canaries -/

section Canary

/-- Two handles, generations bounded by 4. -/
private def canaryAllocator : Allocator := Allocator.empty 2 4

private def canaryFirst : Allocator × Token :=
  (allocate? canaryAllocator 1).getD (canaryAllocator, ⟨0, 0⟩)

private def canaryToken : Token := canaryFirst.2

private def canaryFrame : Frame := ["x"]

private def canaryEnv : FrameEnv canaryFrame := fun _ => some (Atom.symbol "captured")

private def canaryPublished : Image :=
  ((Image.empty 2).publish? canaryFirst.1 canaryToken canaryFrame canaryEnv).getD (Image.empty 2)

private def canaryCaptured : Allocator × Image :=
  (canaryPublished.capture? canaryFirst.1 canaryToken).getD (canaryFirst.1, canaryPublished)

/-- Another frame is allocated, retained, and released after the capture. -/
private def canaryOtherAllocated : Allocator × Token :=
  (allocate? canaryCaptured.1 0).getD (canaryCaptured.1, ⟨0, 0⟩)

private def canaryOtherRetained : Allocator :=
  (retain? canaryOtherAllocated.1 canaryOtherAllocated.2).getD canaryOtherAllocated.1

private def canaryOtherReleasedOnce : Allocator :=
  (release? canaryOtherRetained canaryOtherAllocated.2).getD canaryOtherRetained

private def canaryOtherReleasedTwice : Allocator :=
  (release? canaryOtherReleasedOnce canaryOtherAllocated.2).getD canaryOtherReleasedOnce

/-- The source image is written after the capture. -/
private def canaryWrittenSource : Image :=
  (canaryPublished.write? (canaryToken.ref 0) (some (Atom.symbol "later"))).getD canaryPublished

/-- The holder (capture) and the publisher each hold one count; two releases end authority. -/
private def canaryOwnReleasedOnce : Allocator :=
  (release? canaryOtherReleasedTwice canaryToken).getD canaryOtherReleasedTwice

private def canaryOwnReleasedTwice : Allocator :=
  (release? canaryOwnReleasedOnce canaryToken).getD canaryOwnReleasedOnce

theorem canary_capture_succeeded :
    (canaryPublished.capture? canaryFirst.1 canaryToken).isSome = true := by decide

theorem canary_other_history_is_held :
    HeldTrace canaryToken canaryCaptured.1 canaryOtherReleasedTwice := by
  have s1 : HeldStep canaryToken canaryCaptured.1 canaryOtherAllocated.1 :=
    .allocate (handle := 0) (fresh := canaryOtherAllocated.2) (by decide)
  have s2 : HeldStep canaryToken canaryOtherAllocated.1 canaryOtherRetained :=
    .retain (other := canaryOtherAllocated.2) (by decide)
  have s3 : HeldStep canaryToken canaryOtherRetained canaryOtherReleasedOnce :=
    .releaseOther (other := canaryOtherAllocated.2) (by decide) (by decide)
  have s4 : HeldStep canaryToken canaryOtherReleasedOnce canaryOtherReleasedTwice :=
    .releaseOther (other := canaryOtherAllocated.2) (by decide) (by decide)
  exact .next (.next (.next (.next (.refl _) s1) s2) s3) s4

theorem canary_escaped_observation_survives_other_frames :
    canaryCaptured.2.lookupOwned canaryOtherReleasedTwice (canaryToken.ref 0) =
      some (some (Atom.symbol "captured")) := by decide

/-- A write to the source after capture is visible in the source and invisible to the
captured image. -/
theorem canary_escaped_observation_ignores_later_source_writes :
    canaryWrittenSource.lookup (canaryToken.ref 0) = some (some (Atom.symbol "later")) ∧
      canaryCaptured.2.lookupOwned canaryOtherReleasedTwice (canaryToken.ref 0) =
        some (some (Atom.symbol "captured")) := by decide

/-- One release by the holder leaves the publisher's count, so authority remains. -/
theorem canary_shared_release_keeps_authority :
    canaryCaptured.2.lookupOwned canaryOwnReleasedOnce (canaryToken.ref 0) =
      some (some (Atom.symbol "captured")) := by decide

/-- The final release ends authority: the negative control. -/
theorem canary_own_release_ends_authority :
    canaryCaptured.2.lookupOwned canaryOwnReleasedTwice (canaryToken.ref 0) = none := by decide

end Canary

open private lineageProjected lineageCapture firstAllocation oneReleased allReleased
  from Mettapedia.Languages.MeTTa.MetavariableFrameStore

theorem canary_unbound_lineage_source_release_is_held :
    HeldTrace firstAllocation.2 lineageCapture.1 oneReleased := by
  exact .next (.refl _) (.releaseShared (cell := ⟨0, 2⟩)
    (by decide) (by decide) (by decide))

/-- Releasing the source owner does not invalidate an escaped unbound slot's
clock, boundary or version. The capture and held trace are constructed. -/
theorem canary_escaped_unbound_lineage_survives_source_release :
    lineageCapture.2.readSlotOwned? oneReleased (firstAllocation.2.ref 1) =
      some ⟨none, 0, 1, some 1⟩ := by
  have captured : lineageProjected.capture? firstAllocation.1 firstAllocation.2 =
      some lineageCapture := (Option.some_get (by decide)).symm
  exact (ImageOf.escape_readSlot_capture captured canary_unbound_lineage_source_release_is_held 1).trans
    (by decide)

theorem canary_final_release_revokes_lineage_readback :
    lineageCapture.2.readSlot? (firstAllocation.2.ref 1) = some ⟨none, 0, 1, some 1⟩ ∧
      lineageCapture.2.readSlotOwned? allReleased (firstAllocation.2.ref 1) = none := by decide

end Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
