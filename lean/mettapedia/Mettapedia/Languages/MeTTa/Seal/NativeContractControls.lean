import Mettapedia.Languages.MeTTa.Seal.NativeContract

/-!
# Adversarial controls for the native seal contract

These controls execute the reference primitive operations. They distinguish
fresh capsule identity from shared payload, exercise held-reference patterns,
and separate issuer-held authority from the caller's offered key. Ordinary
datum serialization has an explicit policy that rejects retained frame, state
and foreign descriptors. No native implementation is qualified by these tests.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Seal.NativeContract.Controls

inductive Datum where
  | number (value : Int)
  | symbol (name : String)
  | schematic (name : Nat)
  | frameRef (owner : Nat)
  | stateRef (owner : Nat)
  | foreignRef (owner : Nat)
  deriving DecidableEq, Repr

def admitDatum : Datum → Bool
  | .number _ | .symbol _ | .schematic _ => true
  | .frameRef _ | .stateRef _ | .foreignRef _ => false

def printDatum : Datum → String
  | .number value => toString value
  | .symbol name => name
  | .schematic name => "$" ++ toString name
  | .frameRef _ => "Frame"
  | .stateRef _ => "State"
  | .foreignRef _ => "Foreign"

def nickname (_ : Brand) : String := "math"

def root : Config Datum := (execute Config.empty 0 .newSeal).state
def term : Config Datum := (execute root 0 (.make (.schematic 0))).state
def frame : Config Datum := (execute term 0 (.make (.frameRef 11))).state
def prepared : Config Datum := (execute frame 0 (.pair 1 2)).state
def captured : Value Datum := .pair (.data (.schematic 0)) (.data (.frameRef 11))
def first : Call Datum := sealCall prepared 0 0 3
def second : Call Datum := sealCall first.state 0 0 3
def boxZero : Value Datum := .box 0 0 captured
def boxOne : Value Datum := .box 1 0 captured

theorem actual_prefix_reaches_second :
    Reach (fun _ _ _ => True) (Config.empty : Config Datum) second.state := by
  apply program_original (principal := 0)
    (actions := [.newSeal, .make (.schematic 0), .make (.frameRef 11),
      .pair 1 2, .sealBox 0 3, .sealBox 0 3])
  rfl

theorem reached_nested_identity_is_coherent : second.state.Coherent :=
  actual_prefix_reaches_second.empty_coherent

theorem actual_seals_of_one_payload_allocate_two_identities :
    first.reply = .value boxZero ∧ second.reply = .value boxOne := by
  exact ⟨rfl, rfl⟩

theorem fresh_boxes_with_shared_payload_are_distinct : ¬ boxZero.Same boxOne := by decide

theorem authority_erasure_does_not_preserve_identity :
    boxZero.erase = boxOne.erase ∧ ¬ boxZero.Same boxOne := by
  exact ⟨rfl, fresh_boxes_with_shared_payload_are_distinct⟩

theorem copied_reference_keeps_identity_and_original :
    ((execute second.state 0 (.send 4 1)).state.held 1 0).map Value.key = some boxZero.key ∧
    ((execute second.state 0 (.send 4 1)).state.held 0 4).map Value.key = some boxZero.key := by
  exact ⟨rfl, rfl⟩

theorem repeated_inspection_keeps_captured_variables_and_frame :
    (inspect second.state 0 0 4).reply = .value captured ∧
    (inspect (inspect second.state 0 0 4).state 0 0 4).reply = .value captured := by
  exact ⟨rfl, rfl⟩

def shiftSchematic : Datum → Datum
  | .schematic name => .schematic (name + 1)
  | other => other

theorem quotation_and_substitution_do_not_open_capsules :
    unquote (quote boxZero) = boxZero ∧
    boxZero.mapData shiftSchematic = boxZero ∧
    captured.mapData shiftSchematic = .pair (.data (.schematic 1)) (.data (.frameRef 11)) := by
  exact ⟨rfl, rfl, rfl⟩

theorem redacted_capsules_print_alike_but_data_is_not_redacted :
    display printDatum nickname boxZero = display printDatum nickname boxOne ∧
    display printDatum nickname (.data (.number 7)) = "7" ∧
    display printDatum nickname (.data (.number 9)) = "9" := by
  exact ⟨rfl, rfl, rfl⟩

theorem reference_pattern_and_equality_use_same_box :
    (matchPattern second.state 0 (.reference 4) boxZero []).isSome = true ∧
    (matchPattern second.state 0 (.reference 4) boxOne []).isSome = false := by decide

theorem guessed_other_principals_reference_is_absent :
    (matchPattern second.state 1 (.reference 4) boxZero []).isSome = false := by decide

theorem repeated_pattern_variable_preserves_aliasing :
    (matchPattern second.state 0 (.pair (.bind 0) (.bind 0)) (.pair boxZero boxZero) []).isSome = true ∧
    (matchPattern second.state 0 (.pair (.bind 0) (.bind 0)) (.pair boxZero boxOne) []).isSome = false := by decide

theorem capsule_is_not_a_destructurable_pair :
    (matchPattern second.state 0 (.pair (.bind 0) (.bind 1)) boxZero []).isSome = false := by decide

theorem removal_keeps_duplicate_occurrences :
    (removeFirst boxZero [boxZero, boxZero]).map Value.key = [boxZero.key] ∧
    (removeFirst boxOne [boxZero, boxOne, boxZero]).map Value.key = [boxZero.key, boxZero.key] := by
  exact ⟨rfl, rfl⟩

theorem no_capsule_or_facet_wire_encoding :
    serialize admitDatum boxZero = none ∧
    serialize admitDatum (.cap 0 Rights.sealOnly) = none ∧
    serialize admitDatum (.nonce 0) = none := by
  exact ⟨rfl, rfl, rfl⟩

theorem embedded_frame_state_and_foreign_descriptors_are_refused :
    serialize admitDatum (.data (.frameRef 11)) = none ∧
    serialize admitDatum (.pair (.data (.number 7)) (.data (.stateRef 0))) = none ∧
    decode admitDatum (.data (.foreignRef 0)) = none ∧
    decode admitDatum (.data (.stateRef 0)) = none := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem public_data_round_trip :
    decode admitDatum (.pair (.data (.symbol "claim")) (.data (.number 7))) =
      some (.pair (.data (.symbol "claim")) (.data (.number 7))) := rfl

theorem written_nickname_is_not_a_box :
    decode admitDatum (.data (.symbol "(Sealed math)")) = some (.data (.symbol "(Sealed math)")) ∧
    (matchPattern second.state 0 (.reference 4) (.data (.symbol "(Sealed math)")) []).isSome = false := by
  exact ⟨rfl, by decide⟩

def attenuated : Config Datum := (execute second.state 0 (.attenuate 0 Rights.sealOnly)).state
def anotherBrand : Config Datum := (execute second.state 0 .newSeal).state

theorem wrong_right_is_fault_but_wrong_brand_is_empty :
    (inspect attenuated 0 6 4).reply = .fault .missingRight ∧
    (inspect anotherBrand 0 6 4).reply = .empty ∧
    (inspect second.state 0 0 1).reply = .empty := by
  exact ⟨rfl, rfl, rfl⟩

theorem attenuation_does_not_recover_the_other_facet :
    (sealCall (execute second.state 0 (.attenuate 0 Rights.unsealOnly)).state 0 6 3).reply =
      .fault .missingRight := rfl

theorem fresh_surface_pair_has_separate_facets_and_no_public_root :
    (newSealFor (Config.empty : Config Datum) 0 1).map
      (fun (state, sealer, unsealer) =>
        ((state.held 1 sealer).map Value.key, (state.held 1 unsealer).map Value.key,
          (state.holds 1).map Value.key)) =
      some (some (.cap 0 Rights.sealOnly), some (.cap 0 Rights.unsealOnly),
        [.cap 0 Rights.sealOnly, .cap 0 Rights.unsealOnly]) := rfl

theorem surface_creation_does_not_use_a_public_issuer :
    newSealFor (Config.empty : Config Datum) 1 1 = none := rfl

def keyRoot : Config Datum := (execute (Config.empty : Config Datum) 0 .newSeal).state
def keyIssued : Config Datum := (execute keyRoot 0 .newNonce).state
def keyPayload : Config Datum := (execute keyIssued 0 (.make (.number 7))).state
def locked : Call Datum := sealKeyed keyPayload 0 0 2 1
def granted : Config Datum := (execute locked.state 0 (.send 1 1)).state

theorem possession_of_the_actual_offered_key_opens :
    (inspectKeyed granted 0 0 4 1 0).reply = .value (.data (.number 7)) := rfl

def callerPolicy (enabled : Bool) (caller issuer : Nat) (_ : Seal.Action Datum)
    (_ : Seal.Config Datum) : Bool := enabled && decide (caller = 1 ∧ issuer = 0)

theorem actual_key_and_current_policy_are_both_required :
    (invokeKeyed (callerPolicy true) granted 0 0 4 1 0).reply = .value (.data (.number 7)) ∧
    (invokeKeyed (callerPolicy false) granted 0 0 4 1 0).reply = .fault .denied ∧
    (invokeKeyed (callerPolicy false) granted 0 0 4 1 0).state.holds 0 = granted.holds 0 := by
  exact ⟨rfl, rfl, rfl⟩

theorem guessing_the_issuers_key_slot_does_not_open :
    (inspectKeyed locked.state 0 0 4 1 1).reply = .empty ∧
    (inspectKeyed locked.state 0 0 4 1 1).state.holds 0 = locked.state.holds 0 := by
  exact ⟨rfl, rfl⟩

def writtenKey : Config Datum := (execute locked.state 1 (.make (.number 0))).state

theorem literal_key_number_confers_no_authority :
    (inspectKeyed writtenKey 0 0 4 1 0).reply = .empty := rfl

def wrongKey : Config Datum := (execute locked.state 1 .newNonce).state

theorem wrong_key_retains_private_unseal_state :
    (inspectKeyed wrongKey 0 0 4 1 0).reply = .empty ∧
    ((inspectKeyed wrongKey 0 0 4 1 0).state.held 0 5).map Value.key =
      some (.pair (.nonce 0) (.data (.number 7))) := by
  exact ⟨rfl, rfl⟩

def leakedUnsealer : Config Datum := (execute locked.state 0 (.send 0 1)).state
def leakedBox : Config Datum := (execute leakedUnsealer 0 (.send 4 1)).state

theorem leaked_unsealer_bypasses_key_service :
    (inspect leakedBox 1 0 1).reply = .value (.pair (.nonce 0) (.data (.number 7))) ∧
    (execute (inspect leakedBox 1 0 1).state 1 (.snd 2)).reply = .value (.data (.number 7)) := by
  exact ⟨rfl, rfl⟩

def allowOperation (enabled : Bool) (_ : Nat) (_ : Seal.Action Datum) (_ : Seal.Config Datum) : Bool := enabled

theorem operation_revocation_does_not_change_retained_value :
    (invoke (allowOperation false) second.state 0 (.unsealBox 0 4)).reply = .fault .denied ∧
    ((invoke (allowOperation false) second.state 0 (.unsealBox 0 4)).state.held 0 4).map Value.key =
      some boxZero.key ∧
    (invoke (allowOperation true) second.state 0 (.unsealBox 0 4)).reply = .value captured := by
  exact ⟨rfl, rfl, rfl⟩

/-- Two references may be boxed without freezing the store they refer to. -/
def readState (heap : Nat → Int) : Value Datum → Option Int
  | .data (.stateRef owner) => some (heap owner)
  | _ => none

def mutablePayload : Value Datum := .data (.stateRef 0)

def mutableData : Config Datum := (execute root 0 (.make (.stateRef 0))).state
def mutableBox : Call Datum := sealCall mutableData 0 0 1
def mutableInspection : Call Datum := inspect mutableBox.state 0 0 2

def observeState (heap : Nat → Int) (call : Call Datum) : Option Int :=
  match call.reply with
  | .value value => readState heap value
  | _ => none

theorem opaque_box_does_not_freeze_a_mutable_referent :
    observeState (fun _ => 7) mutableInspection = some 7 ∧
    observeState (fun _ => 9) mutableInspection = some 9 ∧
    mutableBox.reply = .value (.box 0 0 mutablePayload) := by
  exact ⟨rfl, rfl, rfl⟩

def malformed : Config Datum :=
  ⟨fun principal => if principal = 0 then
    [.box 0 0 (.data (.number 7)), .box 0 1 (.data (.number 9))] else [], 2, 0, 1⟩

theorem bounds_alone_allow_inconsistent_identity : malformed.Bounded := by
  intro principal value member
  by_cases same : principal = 0
  · subst principal
    simp [malformed] at member
    rcases member with rfl | rfl <;> exact ⟨by decide, trivial⟩
  · simp [malformed, same] at member

theorem inconsistent_origin_is_rejected_by_coherence : ¬ malformed.Coherent := by
  intro coherent
  have firstBox : malformed.Issued 0 0 (.data (.number 7)) :=
    Config.issued_of_held (show malformed.held 0 0 = some (.box 0 0 (.data (.number 7))) by rfl) .here
  have secondBox : malformed.Issued 0 1 (.data (.number 9)) :=
    Config.issued_of_held (show malformed.held 0 1 = some (.box 0 1 (.data (.number 9))) by rfl) .here
  have impossible := (coherent _ _ _ _ _ firstBox secondBox).1
  cases impossible

end Mettapedia.Languages.MeTTa.Seal.NativeContract.Controls
