import Mettapedia.OSLF.MeTTaIL.AuthoredPremiseServices
import Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel

/-!
# Executable original authored firing receipts

The profile fixes the complete finite source Plan, bound context, result type
and scope. Its registry coordinate selects one installed implementation.
The dynamic implementation is not supplied by the request. Files use the
common five-symbol finite alphabet without whitespace. Accepted replies
retain the entire submitted call and the checked result.
-/

set_option autoImplicit false
namespace Mettapedia.OSLF.MeTTaIL.CheckAuthoredPremises

open Mettapedia.OSLF.MeTTaIL.GeneralPremise
open Mettapedia.OSLF.Binding.WireCodec
open AuthoredPremiseServices

/-- Literal bindings to installed implementations. The bytes do not prove
that an arbitrary function implements one of these services. -/
def authorizedDynamic? (name : Lean.Name) : Option DynamicProvider :=
  if name = .str .anonymous "GeneralPremise.empty.v1" then some .empty
  else if name = .str .anonymous "MeTTa.AtomServices.v1" then
    some Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomServices.provider
  else none

/-- An unknown installed coordinate differs from a known checker's refusal. -/
def runAuthorized (header : Header) (request : List Binary.Alphabet) :
    Except String (Option (List Binary.Alphabet)) :=
  match authorizedDynamic? header.2.1 with
  | none => .error "unknown authorized handler"
  | some dynamic => .ok (External.run header.1 header.2.1 dynamic header.2.2.1
      header.2.2.2.1 header.2.2.2.2 request)

/-- The discovery route receives only an authored goal and slot budgets.
The actual implementation remains fixed by the same installed registry. -/
def runAuthorizedDiscovery (header : Header) (request : List Binary.Alphabet) :
    Except String (Option (List Binary.Alphabet × Bool)) :=
  match authorizedDynamic? header.2.1 with
  | none => .error "unknown authorized handler"
  | some dynamic => .ok (Discovery.External.run header.1 header.2.1 dynamic header.2.2.1
      header.2.2.2.1 header.2.2.2.2 request)

private def readFiles (profileFile requestFile : System.FilePath) :
    IO (Except String (Header × List Binary.Alphabet)) := do
  match Binary.Text.parse (← IO.FS.readFile profileFile) with
  | none => return .error "invalid profile alphabet"
  | some profileWord =>
    match Binary.canonicalDecodeWith External.profileCodec profileWord with
    | none => return .error "invalid profile"
    | some profile =>
      match Binary.Text.parse (← IO.FS.readFile requestFile) with
      | none => return .error "invalid request alphabet"
      | some requestWord => return .ok (profile, requestWord)

private def checkFile (profileFile requestFile : System.FilePath)
    (replyFile : Option System.FilePath) : IO UInt32 := do
  match ← readFiles profileFile requestFile with
  | .error message => IO.eprintln message; return 2
  | .ok (profile, requestWord) =>
    match runAuthorized profile requestWord with
    | .error message => IO.eprintln message; return 2
    | .ok none => IO.println "refused"; return 1
    | .ok (some reply) =>
      if let some destination := replyFile then
        IO.FS.writeFile destination (Binary.Text.render reply)
      IO.println "accepted"
      return 0

/-- A valid empty discovery writes an unknown reply and has its own exit
status. It is neither evidence refusal nor a negative source judgment. -/
private def discoverFile (profileFile requestFile replyFile : System.FilePath) : IO UInt32 := do
  match ← readFiles profileFile requestFile with
  | .error message => IO.eprintln message; return 2
  | .ok (profile, requestWord) =>
    match runAuthorizedDiscovery profile requestWord with
    | .error message => IO.eprintln message; return 2
    | .ok none => IO.println "refused"; return 1
    | .ok (some (reply, found)) =>
      IO.FS.writeFile replyFile (Binary.Text.render reply)
      if found then
        IO.println "found"
        return 0
      else
        IO.println "unknown"
        return 3

def run (arguments : List String) : IO UInt32 := do
  match arguments with
  | ["check", profile, request] => checkFile profile request none
  | ["run", profile, request, reply] => checkFile profile request (some reply)
  | ["discover", profile, request, reply] => discoverFile profile request reply
  | _ =>
    IO.println "authoredPremises check <profile> <request> | run <profile> <request> <reply> | discover <profile> <request> <reply>"
    return 2

end Mettapedia.OSLF.MeTTaIL.CheckAuthoredPremises

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.OSLF.MeTTaIL.CheckAuthoredPremises.run arguments
