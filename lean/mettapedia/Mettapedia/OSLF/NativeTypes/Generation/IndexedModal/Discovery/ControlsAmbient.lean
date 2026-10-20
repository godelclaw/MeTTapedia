import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.Controls

/-! # Automatic native questions preserve ambient variables under binders -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.ControlsAmbient

open Mettapedia.OSLF.MeTTaIL Syntax
open ControlsParameters ControlsPreparation Controls

@[noinline] def run : IO Unit := do
  let installed ← install BindingPipeline.Controls.originalLambda
  let openQuestion ← expect (prepareAt installed ["Term"] 0 [0] []
    [("A", [.bvar 0, identity])] (fun _ => lambdaTarget) identity)
  if sources openQuestion != [application (.bvar 0), application identity] then
    throw (IO.userError "Ambient contextual request was closed or shifted during reconstruction")
  let _ ← positive openQuestion 2000
  let outerTarget := Pattern.apply "Lam" [.lambda none (.bvar 1)]
  let binderQuestion ← expect (prepareAt installed ["Term"] 1 [0, 0] [] []
    (fun _ _ _ target => target == outerTarget) (.apply "App" [identity, .bvar 1]))
  let expected := Pattern.apply "Lam" [.lambda none (.apply "App" [identity, .bvar 1])]
  if sources binderQuestion != [expected] then
    throw (IO.userError "Source reconstruction captured or shifted the ambient variable under a binder")
  let found ← positive binderQuestion 2000
  if !found.certificate.all (fun witness => witness.payload.target == outerTarget) then
    throw (IO.userError "Scoped recursive execution captured the preexisting ambient variable")
  let _ ← negative (falseTarget binderQuestion) 2000
  IO.println "Automatic ambient contexts: free ambient argument and outer variable under LamCong retain their exact de Bruijn indices"

#eval run

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.ControlsAmbient
