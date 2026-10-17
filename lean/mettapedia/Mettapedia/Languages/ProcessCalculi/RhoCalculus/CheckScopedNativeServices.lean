import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedNativeServiceWire

/-!
# Executable intrinsic scoped rho source services

Requests and replies use the shared five-symbol alphabet without whitespace.
The request fixes its complete intrinsic source context, sort and terms. The
source-only protocol is distinct from the optional declared-calculus comparison.
Successful execution binds the original request to its actual checked result.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CheckScopedNativeServices
open Mettapedia.OSLF.Binding.WireCodec
open ScopedNativeServiceWire

private def checkFile (requestFile : System.FilePath) (replyFile : Option System.FilePath) : IO UInt32 := do
  match Binary.Text.parse (← IO.FS.readFile requestFile) with
  | none => IO.eprintln "invalid request alphabet"; return 2
  | some request =>
    match ScopedNativeServiceWire.run request with
    | none => IO.println "refused"; return 1
    | some reply =>
      if let some destination := replyFile then IO.FS.writeFile destination (Binary.Text.render reply)
      IO.println "accepted"
      return 0

def run (arguments : List String) : IO UInt32 := do
  match arguments with
  | ["check", request] => checkFile request none
  | ["run", request, reply] => checkFile request (some reply)
  | _ =>
    IO.println "rhoNativeServices check <request> | run <request> <reply>"
    return 2

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CheckScopedNativeServices

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.ProcessCalculi.RhoCalculus.CheckScopedNativeServices.run arguments
