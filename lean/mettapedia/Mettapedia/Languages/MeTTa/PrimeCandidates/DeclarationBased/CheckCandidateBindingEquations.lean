import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingEquationServices

/-!
# Executable source-faithful authored binding-equation requests

A profile file fixes a namespace and the complete language name, type and
constructor inventory. The profile authorizes the binding signature and its
derived collection laws; arbitrary source equations and rewrites are outside
this file format. Requests carry their own exact metadata and native fields,
which must match that fixed profile. Both files use the shared `0`, `1`, `e`,
`a`, `p` alphabet with no whitespace. Successful responses retain the complete
request and checked service result.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CheckCandidateBindingEquations

open Mettapedia.OSLF.Binding.WireCodec
open AuthoredBindingEquationServices

private def checkFile (profileFile requestFile : System.FilePath)
    (replyFile : Option System.FilePath) : IO UInt32 := do
  match Binary.Text.parse (← IO.FS.readFile profileFile) with
  | none => IO.eprintln "invalid profile alphabet"; return 2
  | some profileWord =>
    match Binary.canonicalDecodeWith External.profileCodec profileWord with
    | none => IO.eprintln "invalid profile"; return 2
    | some (scope, header) =>
      match Binary.Text.parse (← IO.FS.readFile requestFile) with
      | none => IO.eprintln "invalid request alphabet"; return 2
      | some requestWord =>
        match External.run scope (External.profileLanguage header) requestWord with
        | none => IO.println "refused"; return 1
        | some reply =>
          if let some destination := replyFile then
            IO.FS.writeFile destination (Binary.Text.render reply)
          IO.println "accepted"
          return 0

def run (arguments : List String) : IO UInt32 := do
  match arguments with
  | ["check", profile, request] => checkFile profile request none
  | ["run", profile, request, reply] => checkFile profile request (some reply)
  | _ =>
    IO.println "candidateBindingEquations check <profile> <request> | run <profile> <request> <reply>"
    return 2

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CheckCandidateBindingEquations

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CheckCandidateBindingEquations.run arguments
