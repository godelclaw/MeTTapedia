import Mettapedia.Languages.MeTTa.HE.ArgumentResultCorrectness

/-!
# Tagged argument protocol controls

Successful argument data stays distinct from failed evaluation. The controls
include raw symbols, error-shaped expressions, nested success packets,
duplicate occurrences, malformed packets and an actual grounded failure.
-/

namespace Mettapedia.Languages.MeTTa.HE.ArgumentResult.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def rawData : List Atom := [.symbol "x", .symbol "Error", .symbol "y"]

theorem raw_error_symbol_retained :
    interpretArgs Space.empty GroundedDispatch.none rawData
      [Atom.atomType, Atom.atomType, Atom.atomType] Bindings.empty 16 =
      [(argumentPacket rawData, Bindings.empty)] := by
  exact interpretArgs_raw _ _ rawData _ 16 (by decide)

theorem arbitrary_error_payload_retained (payload : List Atom) :
    interpretArgs Space.empty GroundedDispatch.none
      [.symbol "x", .expression (.symbol "Error" :: payload), .symbol "y"]
      [Atom.atomType, Atom.atomType, Atom.atomType] Bindings.empty 16 =
      [(argumentPacket
        [.symbol "x", .expression (.symbol "Error" :: payload), .symbol "y"],
        Bindings.empty)] := by
  exact interpretArgs_raw _ _ _ _ 16 (by simp)

theorem success_packet_as_raw_data (payload : List Atom) :
    interpretArgs Space.empty GroundedDispatch.none [argumentPacket payload]
      [Atom.atomType] Bindings.empty 4 =
      [(argumentPacket [argumentPacket payload], Bindings.empty)] := by
  exact interpretArgs_raw _ _ _ _ 4 (by simp)

theorem duplicates_retained :
    interpretArgs Space.empty GroundedDispatch.none
      [.symbol "a", .symbol "a", .symbol "b"]
      [Atom.atomType, Atom.atomType, Atom.atomType] Bindings.empty 16 =
      [(argumentPacket [.symbol "a", .symbol "a", .symbol "b"], Bindings.empty)] := by
  exact interpretArgs_raw _ _ _ _ 16 (by decide)

theorem bare_error_list_is_not_success :
    argumentsSucceeded (.expression [.symbol "Error", .symbol "y"]) = false := by decide

theorem retained_data_is_not_error :
    isEmptyOrError (argumentPacket rawData) = false := by simp

theorem nested_tag_is_not_flattened (payload : List Atom) :
    argumentValues (argumentPacket [argumentPacket payload]) = [argumentPacket payload] := by
  simp

theorem missing_tag_rejected :
    unpackArguments (.expression [.symbol "x", .symbol "y"]) = none := by decide

theorem non_list_payload_rejected :
    unpackArguments (.expression [.symbol "Ok", .symbol "x"]) = none := by decide

theorem extra_packet_field_rejected :
    unpackArguments (.expression [.symbol "Ok", .expression [], .symbol "extra"]) = none := by
  decide

def failureSpace : Space := Space.ofList
  [.expression [.symbol ":", .symbol "fail", .expression [.symbol "->", .symbol "Value"]]]

def failureDispatch : GroundedDispatch where
  isExecutable := fun operator => operator == .symbol "fail"
  execute := fun _ _ => .runtimeError "failure"

def failingArgument : Atom := .expression [.symbol "fail"]
def failedResult : Atom := Atom.error failingArgument (.symbol "failure")

theorem changed_grounded_error_propagates :
    interpretArgs failureSpace failureDispatch
      [failingArgument, .symbol "later"] [.symbol "Value", Atom.atomType]
      Bindings.empty 32 = [(failedResult, Bindings.empty)] := by decide

theorem unchanged_error_is_data :
    interpretArgs Space.empty GroundedDispatch.none [failedResult]
      [Atom.atomType] Bindings.empty 4 =
      [(argumentPacket [failedResult], Bindings.empty)] := by
  exact interpretArgs_raw _ _ _ _ 4 (by decide)

theorem changed_error_is_not_success :
    argumentsSucceeded failedResult = false := by decide

end Mettapedia.Languages.MeTTa.HE.ArgumentResult.Controls
