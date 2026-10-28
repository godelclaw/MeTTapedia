import Mettapedia.Machines.OrderedDependencyOverlay

/-!
# Complete source-view epochs at preparation and publication

The existing ordered-dependency machine supplies the source and nested-overlay
transitions. Its local overlay revision alone is not a source-view key: a live
import may change without moving that revision. The complete epoch retains the
owner lifetime, the dependency read stamp and the local publication revision.

Validation is reduced to that machine's proved full-stamp check. It is neither
an execution permission nor a read interval. Finite-width clock allocation,
native lifetime management and the C read guard are separate implementation
obligations; no native-verification claim is made here.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.SourceViewEpoch

open Mettapedia.Machines
open OrderedDependencyOverlay OrderedDependencyStore

structure Epoch (size : Nat) where
  owner : Nat × Nat
  dependency : ReadStamp size
  localRevision : Nat
  deriving DecidableEq

variable {Entry : Type} {size : Nat}

def capture (source : State Entry size) : Epoch size :=
  ⟨(source.identity, source.generation), readStamp source.store source.reader, source.revision⟩

def validate (source : State Entry size) (expected : Epoch size) : Bool :=
  decide (expected = capture source)

theorem capture_eq_iff_stamp_eq (first second : State Entry size) :
    capture first = capture second ↔ stamp first = stamp second := by
  simp only [capture, Epoch.mk.injEq, Prod.mk.injEq, stamp, Stamp.mk.injEq]
  constructor
  · rintro ⟨⟨identity, generation⟩, root, sameLocal⟩
    refine ⟨identity, generation, root, ?_⟩
    have revision := congrArg ReadStamp.revision root
    simp only [readStamp] at revision
    simp only [clock]
    omega
  · rintro ⟨identity, generation, root, sameClock⟩
    refine ⟨⟨identity, generation⟩, root, ?_⟩
    have revision := congrArg ReadStamp.revision root
    simp only [readStamp] at revision
    simp only [clock] at sameClock
    omega

theorem validate_iff_checkStamp (source original : State Entry size) :
    validate source (capture original) = checkStamp source (stamp original) := by
  simp only [validate, checkStamp, capture_eq_iff_stamp_eq]

theorem unchanged_epoch_preserves_query (source : State Entry size)
    (holds : ObserverInvariant source.store) (actions : List (OrderedDependencyOverlay.Action Entry size))
    (current : validate (execute source actions) (capture source) = true) :
    query (execute source actions) = query source := by
  rw [validate_iff_checkStamp] at current
  exact validated_query source holds actions current

def publish (source : State Entry size) (actions : List (OrderedDependencyOverlay.Action Entry size)) :
    Option (List Entry) :=
  let after := execute source actions
  if validate after (capture source) then some (query after) else none

theorem published_observation (source : State Entry size) (holds : ObserverInvariant source.store)
    (actions : List (OrderedDependencyOverlay.Action Entry size)) (result : List Entry)
    (accepted : publish source actions = some result) : result = query source := by
  simp only [publish] at accepted
  split at accepted
  next current =>
    have same := unchanged_epoch_preserves_query source holds actions current
    exact (Option.some.inj accepted).symm.trans same
  next => contradiction

theorem changed_epoch_prevents_publication (source : State Entry size)
    (actions : List (OrderedDependencyOverlay.Action Entry size))
    (changed : validate (execute source actions) (capture source) = false) :
    publish source actions = none := by simp [publish, changed]

namespace Controls

open OrderedDependencyOverlay.Controls

def importedChange : State Nat 3 := step nested (.storeUpdate (.append 2 [8]))

theorem local_revision_misses_imported_change :
    importedChange.revision = nested.revision ∧ query importedChange ≠ query nested := by decide

theorem complete_epoch_rejects_imported_change :
    validate importedChange (capture nested) = false := by decide

theorem rejected_import_does_not_publish :
    publish nested [.storeUpdate (.append 2 [8])] = none := by decide

theorem unchanged_view_retains_duplicate_occurrences :
    publish nested [] = some [99, 99, 77, 7, 7] := by decide

theorem retired_lifetime_never_revives :
    let restored := step (step nested .retire) (.publish nested.layers)
    query restored = query nested ∧ validate restored (capture nested) = false := by decide

theorem changed_local_overlay_is_rejected :
    validate (step nested (.publish [])) (capture nested) = false := by decide

end Controls

#print axioms capture_eq_iff_stamp_eq
#print axioms validate_iff_checkStamp
#print axioms unchanged_epoch_preserves_query
#print axioms published_observation
#print axioms changed_epoch_prevents_publication
#print axioms Controls.local_revision_misses_imported_change
#print axioms Controls.complete_epoch_rejects_imported_change
#print axioms Controls.rejected_import_does_not_publish
#print axioms Controls.unchanged_view_retains_duplicate_occurrences
#print axioms Controls.retired_lifetime_never_revives
#print axioms Controls.changed_local_overlay_is_rejected

end Mettapedia.Algorithms.Compression.SourceViewEpoch
