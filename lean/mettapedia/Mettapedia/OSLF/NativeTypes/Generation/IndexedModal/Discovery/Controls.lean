import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.QueryLaws
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.ControlsPreparation

/-!
# Automatic finite native-membership discovery controls

Every question is prepared from authored typed parameter bodies before its
first execution session is started. Discovery computes source programs from
the generated one-hole context. All produced certificates are replayed through
the existing membership checker and expose executable response families.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.Controls

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.NativeTypes.Modal
open FocusMeaning FiniteFocusChecking ControlsParameters ControlsPreparation

variable {installed : Joined.Installed} {ambient : List String}

@[noinline] def positive (question : FocusQuery.Question installed ambient) (budget : Nat) :
    IO (Session question) := do
  let initial := begin question
  if !(requests question.parameters).isEmpty && initial.verdict != .unknown then
    throw (IO.userError "An unexecuted contextual request gave a semantic verdict")
  let finished := initial.resume budget
  if accepted : finished.verdict = .proved then
    let _meaning : question.Meaning := finished.proved accepted
    pure ()
  else
    throw (IO.userError ("Automatic contextual discovery did not prove membership: " ++ reprStr finished.verdict))
  if !check question.parameters question.focus finished.certificate then
    throw (IO.userError "Automatic certificate failed the original native checker")
  let split := (initial.resume (budget / 2)).resume (budget - budget / 2)
  if split.certificate != finished.certificate || split.verdict != finished.verdict then
    throw (IO.userError "Pause/resume changed automatic certificate discovery")
  let some membership := finished.membership?
    | throw (IO.userError "Proved discovery did not retain an executable response family")
  for values in (requests question.parameters).attach do
    let response := membership.family.respond values.val
      ((requests_exact question.parameters values.val).mp values.property)
    if !question.parameters.target values.val response.receipt.firing.answer.completed
        response.receipt.firing.answer.target then
      throw (IO.userError "Discovered family failed its dependent target at an admitted request")
  if finished.settled then
    if (finished.resume 10).certificate != finished.certificate then
      throw (IO.userError "Settled discovery changed its complete occurrence certificate")
  pure finished

@[noinline] def negative (question : FocusQuery.Question installed ambient) (budget : Nat) :
    IO (Session question) := do
  let initial := begin question
  if initial.verdict != .unknown then
    throw (IO.userError "A not-yet-executed negative request was decided")
  if initial.counterexample?.isSome then
    throw (IO.userError "Unfinished execution exposed an unsupported semantic counterexample")
  let finished := initial.resume budget
  if rejected : finished.verdict = .refuted then
    let _notMember : ¬ question.Meaning := finished.refuted rejected
    pure ()
  else
    throw (IO.userError ("Complete negative contextual question was not refuted: " ++ reprStr finished.verdict))
  if !finished.settled || finished.membership?.isSome then
    throw (IO.userError "Negative readout was not backed by complete failed coverage")
  let some counterexample := finished.counterexample?
    | throw (IO.userError "Refutation did not retain a concrete unanswered admitted input")
  let _notMember : ¬ question.Meaning := counterexample.not_member
  if finished.execution.hasResponse question.parameters question.focus counterexample.values then
    throw (IO.userError "Extracted semantic counterexample has an accepted response")
  pure finished

@[noinline] def lambda : IO Unit := do
  let installed ← install BindingPipeline.Controls.originalLambda
  let question ← expect (lambdaQuestion installed)
  if sources question != [application identity, application constant] then
    throw (IO.userError "Generated beta context did not reconstruct both independently supplied requests")
  let found ← positive question 2000
  if found.certificate.length != 2 then
    throw (IO.userError "Lambda automatic discovery lost a supplied argument or invented a receipt")
  if check question.parameters question.focus (found.certificate.take 1) then
    throw (IO.userError "A single discovered input certified the complete two-input family")
  let wrong ← negative (constantIdentityTarget question) 2000
  if !wrong.certificate.any (fun witness => witness.payload.target == constant) then
    throw (IO.userError "Wrong constant target was refuted without retaining the separating response")
  let root ← expect (rootQuestion installed)
  if (requests root.parameters).length != 1 then
    throw (IO.userError "Zero rely slots dropped their mandatory target obligation")
  let _ ← positive root 2000
  let emptyTarget ← negative (falseTarget root) 2000
  if emptyTarget.certificate.isEmpty then
    throw (IO.userError "False zero-rely target was not separated from absence of source execution")
  let illFormed := {question with focus := Pattern.apply "Unit" []}
  if (begin illFormed).verdict != .illFormedFocus then
    throw (IO.userError "Ill-formed focus was conflated with semantic nonmembership")
  IO.println "Automatic lambda: two independent arguments, complete response family, wrong constant target refuted, zero-rely target mandatory"

@[noinline] def binderLocal : IO Unit := do
  let installed ← install BindingPipeline.Controls.originalLambda
  let question ← expect (binderQuestion installed)
  if sources question != [Consumers.underBinderSource] then
    throw (IO.userError "Binder-local source reconstruction did not preserve the selected local scope")
  let found ← positive question 2000
  if !found.certificate.any (fun witness => !witness.payload.history.isEmpty) then
    throw (IO.userError "Binder-local discovery dropped its ordered scoped-premise evidence")
  let _ ← negative (falseTarget question) 2000
  IO.println "Automatic binder-local family: original LamCong source, local Term scope and scoped premise retained"

@[noinline] def pairCase : IO Unit := do
  let installed ← install BindingPipeline.Controls.originalLetCase
  let question ← expect (caseQuestion installed)
  if (requests question.parameters).length != 4 || (sources question).length != 4 then
    throw (IO.userError "Two independent rely domains did not reconstruct all four pair-case requests")
  let found ← positive question 2000
  if found.certificate.length != 4 then
    throw (IO.userError "Pair-case automatic discovery failed Cartesian response coverage")
  if check question.parameters question.focus (found.certificate.take 3) then
    throw (IO.userError "Three case instances certified four independent input pairs")
  let _ ← negative (falseTarget question) 2000
  IO.println "Automatic pair-case: four Cartesian requests, two local binders, dependent left-component result"

@[noinline] def sharedIndices : IO Unit := do
  let installed ← install indexedLanguage
  let first ← expect (sharedQuestion installed 0)
  let second ← expect (sharedQuestion installed 1)
  let left ← positive first 500
  let right ← positive second 500
  if left.certificate.map (fun witness => witness.payload.index) != [0, 1] ||
      right.certificate.map (fun witness => witness.payload.index) != [0, 1] then
    throw (IO.userError "Equal-target discovery merged distinct declaration origins")
  let some firstMembership := left.membership?
    | throw (IO.userError "First shared-index family was not executable")
  for values in (requests first.parameters).attach do
    let response := firstMembership.family.respond values.val
      ((requests_exact first.parameters values.val).mp values.property)
    if response.receipt.firing.answer.index != 0 then
      throw (IO.userError "First family responded using another declaration's origin")
  let some secondMembership := right.membership?
    | throw (IO.userError "Second shared-index family was not executable")
  for values in (requests second.parameters).attach do
    let response := secondMembership.family.respond values.val
      ((requests_exact second.parameters values.val).mp values.property)
    if response.receipt.firing.answer.index != 1 then
      throw (IO.userError "Second family responded using another declaration's origin")
  let changed ← expect (prepareAt installed [] 0 [0] [("x", .apply "F1" [])]
    [("x", [.apply "F1" []])] (fun _ _ _ target => target == Consumers.sharedTarget) (.apply "F0" []))
  let _ ← negative changed 500
  IO.println "Automatic shared indices: equal targets retain declarations 0/1; changing only the shared index refutes membership"

@[noinline] def vocabularyRefusal : IO Unit := do
  let .ok installed := Joined.generate (BindingPipeline.Controls.snapshot Consumers.sharedLanguage)
      BindingPipeline.Controls.fragment
      {BindingPipeline.Controls.fullLogic with native := ⟨[]⟩}
      (fun _ => .star, fun _ => .star) []
    | throw (IO.userError "Language installation failed before vocabulary selection")
  let some index := findSite? installed 0 [0]
    | throw (IO.userError "Forbidden vocabulary control lost its generated site")
  let some parameters := parameters? installed index [] [("x", .apply "F0" [])]
      [("x", [.apply "F0" []])] (fun _ _ target => target == Consumers.sharedTarget)
    | throw (IO.userError "Forbidden vocabulary control had invalid independent inputs")
  match FocusQuery.prepare installed index parameters (.apply "F0" []) with
  | .error .vocabularyRefused => pure ()
  | _ => throw (IO.userError "Forbidden formation was not refused independently of semantic truth")
  IO.println "Automatic query preparation: forbidden vocabulary is refused before discovery"

@[noinline] def run : IO Unit := do
  lambda
  binderLocal
  pairCase
  sharedIndices
  vocabularyRefusal

#eval run

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.Controls
