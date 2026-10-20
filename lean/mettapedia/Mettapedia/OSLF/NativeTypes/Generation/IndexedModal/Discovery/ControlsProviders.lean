import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.Controls

/-! # Automatic contextual discovery retains finite provider origins -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.ControlsProviders

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open ControlsParameters ControlsPreparation Controls

def language : LanguageDef :=
  {Consumers.sharedLanguage with
    name := "ProviderContextualDiscovery"
    rewrites := [{Consumers.sharedRule with
      premises := [.relationQuery "permit" [.fvar "x"]]}]}

def install (rows : List ProviderRow) : IO Joined.Installed :=
  match Joined.generate
      ⟨language, [],
        {signatures := [⟨"permit", [.base "Focus"], [.input]⟩], rows := rows,
          dynamicRelations := []}⟩
      BindingPipeline.Controls.fragment BindingPipeline.Controls.fullLogic
      (fun _ => .star, fun _ => .star) [] with
  | .ok installed => pure installed
  | .error reason => throw (IO.userError ("Finite provider language refused: " ++ reprStr reason))

@[noinline] def run : IO Unit := do
  let installed ← install [⟨"permit", [.apply "F0" []]⟩, ⟨"permit", [.apply "F0" []]⟩]
  let question ← expect (sharedQuestion installed 0)
  let found ← positive question 500
  let origins := found.certificate.map fun witness =>
    witness.payload.history.filterMap fun event =>
      match event with
      | .query _ _ row _ => some row
      | _ => none
  if origins != [[0], [1]] then
    throw (IO.userError "Equal provider rows lost their distinct ordered source origins")
  let missing ← install []
  let denied ← expect (sharedQuestion missing 0)
  let rejected ← negative denied 500
  if !rejected.certificate.isEmpty then
    throw (IO.userError "Failed provider query invented an authorized response")
  IO.println "Automatic finite providers: duplicate rows retain origins 0/1; absent permit refutes the same contextual request"

#eval run

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.ControlsProviders
