import Mettapedia.Algorithms.Compression.LibraryTransfer

/-! Noncommuting recovery/replay controls on a declaration-prefix source.
The receiving source differs from the donor; copied definitions remain fixed.
Malformed late entries and the wrong replay order are negative controls. -/

set_option autoImplicit false

namespace Mettapedia.Examples.Compression.LibraryTransferControls

open Algorithms.Compression Algorithms.Compression.LayeredSource
open Algorithms.Compression.LibraryTransfer

private def oldCodec := octets [76, 67, 49]
private def outputCodec := octets [76, 67, 50]
private def nameA := octets [97]
private def nameB := octets [98]
private def layerA : Layer := ⟨oldCodec, nameA⟩
private def layerB : Layer := ⟨outputCodec, nameB⟩

private def expected (layer : Layer) : Option Nat :=
  if layer.name = nameA then some 7 else if layer.name = nameB then some 11 else none

private def extract (layer : Layer) : List Nat → Option Nat
  | [] => none
  | definition :: _ => if expected layer = some definition then some definition else none

private def undo (layer : Layer) : List Nat → Option (List Nat)
  | [] => none
  | definition :: source => if expected layer = some definition then some source else none

private def install (stage : Stage Nat) (source : List Nat) : Option (List Nat) :=
  if expected stage.layer = some stage.definition then some (stage.definition :: source) else none

private def recovered : List (Stage Nat) := [⟨layerA, 7⟩, ⟨layerB, 11⟩]

theorem fixed_stages_recovered :
    recover extract undo [layerA, layerB] [7, 11, 5] = some recovered := by decide

theorem donor_reconstruction : expand undo [layerA, layerB] [7, 11, 5] = some [5] := by decide

theorem checked_installation_is_a_local_inverse
    (stage : Stage Nat) (before after : List Nat) (checked : install stage before = some after) :
    undo (installedLayer outputCodec stage) after = some before := by
  unfold install at checked
  split at checked
  · rename_i admitted
    cases Option.some.inj checked
    have same : expected (installedLayer outputCodec stage) = some stage.definition := by
      exact admitted
    simp only [undo, same, if_true]
  · contradiction

theorem receiving_source_has_distinct_data :
    replay install recovered.reverse [99, 100] = some [7, 11, 99, 100] := by decide

theorem complete_receiving_reconstruction :
    expand undo (recovered.map (installedLayer outputCodec)) [7, 11, 99, 100] = some [99, 100] :=
  recovered_replay_reconstructs install undo outputCodec checked_installation_is_a_local_inverse
    recovered [99, 100] [7, 11, 99, 100] receiving_source_has_distinct_data

theorem replay_order_cannot_be_ignored :
    replay install recovered [99, 100] = some [11, 7, 99, 100] ∧
      expand undo [layerA, layerB] [11, 7, 99, 100] = none := by decide

theorem late_recovery_failure_is_not_skipped :
    recover extract undo [layerA, layerB] [7, 12, 5] = none := by decide

theorem late_install_failure_does_not_publish_a_prefix :
    replay install [⟨layerB, 11⟩, ⟨layerA, 8⟩] [99, 100] = none := by decide

theorem definition_is_not_refitted_to_the_receiver :
    install ⟨layerA, 8⟩ [8, 99, 100] = none := by decide

theorem unknown_helper_is_rejected :
    recover extract undo [⟨oldCodec, octets [120]⟩] [7, 99] = none ∧
      install ⟨⟨oldCodec, octets [120]⟩, 7⟩ [99] = none := by decide

theorem codec_conversion_preserves_every_name :
    (recovered.map (installedLayer outputCodec)).map Layer.name = [layerA, layerB].map Layer.name :=
  installed_names_preserved extract undo outputCodec [layerA, layerB] [7, 11, 5] recovered fixed_stages_recovered

#print axioms recover_cons_iff
#print axioms recovered_layers
#print axioms recovered_length
#print axioms recovery_checks_all_decoders
#print axioms replay_append
#print axioms failed_stage_rejects_publication
#print axioms replay_reconstructs
#print axioms installed_names_preserved
#print axioms recovered_replay_reconstructs
#print axioms accepted_complete_bits_decrease
#print axioms fixed_stages_recovered
#print axioms donor_reconstruction
#print axioms checked_installation_is_a_local_inverse
#print axioms receiving_source_has_distinct_data
#print axioms complete_receiving_reconstruction
#print axioms replay_order_cannot_be_ignored
#print axioms late_recovery_failure_is_not_skipped
#print axioms late_install_failure_does_not_publish_a_prefix
#print axioms definition_is_not_refitted_to_the_receiver
#print axioms unknown_helper_is_rejected
#print axioms codec_conversion_preserves_every_name

end Mettapedia.Examples.Compression.LibraryTransferControls
