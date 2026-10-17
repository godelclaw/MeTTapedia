import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FiniteFocusReification
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FocusMeaningLaws
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FocusQuery
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.JoinedRuntime

/-! # Generated focus membership on authored binding languages -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FiniteFocusControls

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.NativeTypes.Modal
open NativeReceiptRechecking NativeBindingEventAction
open FocusMeaning FiniteFocusChecking

theorem forbidden_request_refutes {installed : Joined.Installed} {index : installed.Index}
    {ambient : List String} (parameters : Parameters installed index ambient)
    (first second : RelyValues installed index ambient) (focus : Pattern)
    (requested : Requested parameters.meaning second) (different : second ≠ first) :
    let restricted := {parameters with target := fun values _ _ => decide (values = first)}
    ¬ Inhabits restricted.meaning focus := by
  intro restricted
  apply empty_target_no_membership restricted.meaning focus second requested
  intro assignment target
  change ¬ decide (second = first) = true
  simpa only [decide_eq_true_eq] using different

def witnesses (installed : Joined.Installed) (ambient : List String) (sort : String)
    (sources : List Pattern) (budget : Nat) : List Witness :=
  sources.flatMap fun source =>
    (JoinedRuntime.payloads installed ambient sort source budget).map (fun payload => ⟨source, payload⟩)

def frames (installed : Joined.Installed) (index : installed.Index) (ambient : List String)
    (certificate : List Witness) :
    List (SemanticReceipts.Frame installed.indexed installed.semantic index ambient) :=
  certificate.filterMap fun witness =>
    (installed.checkReceipt index ambient witness.source witness.payload).map (·.frame)

@[noinline] def checkSession {installed : Joined.Installed} {index : installed.Index} {ambient : List String}
    (parameters : Parameters installed index ambient) (focus : Pattern) (certificate : List Witness) : IO Unit := do
  if !check parameters focus certificate then throw (IO.userError "Full finite-rely certificate rejected")
  let .ok question := FocusQuery.prepare installed index parameters focus
    | throw (IO.userError "Selected vocabulary refused generated family formation")
  let initial := FocusQuery.verify question certificate 0
  if !(requests parameters).isEmpty && initial.verdict != .unknown then
    throw (IO.userError "Unverified rely requests gave a conclusion")
  let fuel := (requests parameters).length
  let finished := initial.resume fuel
  if finished.verdict != .proved then throw (IO.userError "Covered rely family did not verify")
  let split := (initial.resume (fuel / 2)).resume (fuel - fuel / 2)
  if split.session.state.accepted != finished.session.state.accepted then
    throw (IO.userError "Split verification changed acceptance")
  if finished.certificate != certificate then throw (IO.userError "Verification changed receipt origins")
  let some membership := verify? parameters focus certificate
    | throw (IO.userError "Checked membership was not retained")
  for values in (requests parameters).attach do
    let response := membership.family.respond values.val ((requests_exact parameters values.val).mp values.property)
    if !parameters.target values.val response.receipt.firing.answer.completed response.receipt.firing.answer.target then
      throw (IO.userError "Executable family returned an invalid dependent target")
  let forbidden := {parameters with target := fun _ _ _ => false}
  if !(requests parameters).isEmpty && check forbidden focus certificate then
    throw (IO.userError "Mandatory target condition was ignored")

@[noinline] def singleConsumer (language : LanguageDef) (sort : String) (source : Pattern)
    (binderLocal : Bool := false) : IO Unit := do
  let installed ← match Consumers.generate language with
    | .ok installed => pure installed
    | .error reason => throw (IO.userError ("Authored language refused: " ++ reprStr reason))
  let certificate := witnesses installed [] sort [source] 2000
  if certificate.isEmpty then throw (IO.userError "Consumer produced no operational receipt")
  let mut checked := 0
  for index in List.finRange installed.indexed.headers.length do
    if !binderLocal || !(installed.indexed.schema index).focusBound.isEmpty then
      let decoded := frames installed index [] certificate
      match decoded.head? with
      | none => pure ()
      | some frame =>
          match parametersFromFrames [frame] (fun _ _ target => target == frame.point.val.receipt.target) with
          | none => throw (IO.userError "Generated typed parameter slot was unreadable")
          | some parameters =>
              checkSession parameters frame.focus certificate
              let damaged := certificate.map fun witness =>
                {witness with payload := {witness.payload with completed := []}}
              if !frame.point.val.receipt.completed.isEmpty && check parameters frame.focus damaged then
                throw (IO.userError "Missing scoped assignment accepted")
              checked := checked + 1
  if checked = 0 then throw (IO.userError "No generated focus family exercised")
  IO.println (language.name ++ ": semantic focus families=" ++ toString checked ++
    (if binderLocal then " (binder-local)" else ""))

def identity : Pattern := .apply "Lam" [.lambda none (.bvar 0)]
def constant : Pattern := .apply "Lam" [.lambda none (.apply "Lam" [.lambda none (.bvar 1)])]
def application (argument : Pattern) : Pattern := .apply "App" [identity, argument]

@[noinline] def twoRequests : IO Unit := do
  let installed ← match Consumers.generate BindingPipeline.Controls.originalLambda with
    | .ok installed => pure installed
    | .error reason => throw (IO.userError ("Lambda refused: " ++ reprStr reason))
  let certificate := witnesses installed [] "Term" [application identity, application constant] 2000
  let mut exercised := false
  for index in List.finRange installed.indexed.headers.length do
    if (installed.indexed.schema index).position == [0] then
      let decoded := frames installed index [] certificate
      if decoded.length == 2 then
        let some first := decoded.head? | throw (IO.userError "Missing first response")
        if !decoded.all (fun frame => frame.focus == first.focus) then
          throw (IO.userError "The two requests changed the focus")
        let some parameters := parametersFromFrames decoded (fun values _ target =>
            (List.finRange _).any (fun position => (values position).val.body == target))
          | throw (IO.userError "Rely decoding failed")
        checkSession parameters first.focus certificate
        if (requests parameters).length != 2 then throw (IO.userError "Rely product lost an input")
        if check parameters first.focus (certificate.take 1) then
          throw (IO.userError "One successful request certified the entire rely family")
        let some initial := (requests parameters).head? | throw (IO.userError "No first request")
        let restricted := {parameters with target := fun values _ _ => decide (values = initial)}
        if check restricted first.focus certificate then throw (IO.userError "Dependent target ignored the second request")
        let mut counterexample := false
        for request in (requests parameters).attach do
          if different : request.val ≠ initial then
            let _refuted : ¬ Inhabits restricted.meaning first.focus :=
              forbidden_request_refutes parameters initial request.val first.focus
                ((requests_exact parameters request.val).mp request.property) different
            counterexample := true
        if !counterexample then throw (IO.userError "Missing independent dependent-target counterexample")
        exercised := true
  if !exercised then throw (IO.userError "Authored beta function site was not generated")
  IO.println "Lambda: identity returns each supplied argument; two rely inputs verified, one instance insufficient"

def indexedLanguage : LanguageDef :=
  {Consumers.sharedLanguage with
    name := "IndexedFocusMembership"
    terms := Consumers.sharedLanguage.terms ++
      [{label := "F1", category := "Focus", params := [], syntaxPattern := []}]}

def pair (label : String) : Pattern := .apply "Pair" [.apply label [], .apply label []]

@[noinline] def indicesAndOrigins : IO Unit := do
  let .ok installed := Consumers.generate indexedLanguage | throw (IO.userError "Indexed language refused")
  let first := witnesses installed [] "Program" [pair "F0"] 500
  let second := witnesses installed [] "Program" [pair "F1"] 500
  if first.map (fun witness => witness.payload.index) != [0, 1] then
    throw (IO.userError "Equal targets lost authored origins")
  let mut exercised := 0
  for index in List.finRange installed.indexed.headers.length do
    if !installed.indexed.headers[index].indices.isEmpty then
      let left := frames installed index [] first
      let right := frames installed index [] second
      if let some a := left.head? then
        if let some b := right.head? then
          let some parameters := parametersFromFrames [a] (fun _ _ target => target == Consumers.sharedTarget)
            | throw (IO.userError "Index decoder failed")
          checkSession parameters a.focus first
          let some changed := parametersFromFrames [b] (fun _ _ target => target == Consumers.sharedTarget)
            | throw (IO.userError "Changed index decoder failed")
          if check changed a.focus first then throw (IO.userError "Changed shared index accepted old receipt")
          exercised := exercised + 1
  if exercised = 0 then throw (IO.userError "No shared index was generated")
  IO.println ("Shared indices: " ++ toString exercised ++ " families preserve fixed values and equal-target origins")

@[noinline] def vocabularyRefusal : IO Unit := do
  let .ok installed := Joined.generate (BindingPipeline.Controls.snapshot Consumers.sharedLanguage)
      BindingPipeline.Controls.fragment
      {BindingPipeline.Controls.fullLogic with native := ⟨[]⟩}
      (fun _ => .star, fun _ => .star) []
    | throw (IO.userError "Semantic installation refused before vocabulary checking")
  if enough : 0 < installed.indexed.headers.length then
    let index : installed.Index := ⟨0, enough⟩
    let certificate := witnesses installed [] "Program" [Consumers.sharedSource] 500
    let some frame := (frames installed index [] certificate).head?
      | throw (IO.userError "Missing source frame for vocabulary control")
    let some parameters := parametersFromFrames [frame] (fun _ _ target => target == Consumers.sharedTarget)
      | throw (IO.userError "Missing semantic parameters for vocabulary control")
    match FocusQuery.prepare installed index parameters frame.focus with
    | .error .vocabularyRefused => IO.println "Native vocabulary: forbidden formation is refused, not refuted"
    | _ => throw (IO.userError "Native vocabulary policy was bypassed")
  else throw (IO.userError "Source modal catalogue unexpectedly empty")

#eval do
  twoRequests
  singleConsumer BindingPipeline.Controls.originalLambda "Term" Consumers.underBinderSource true
  singleConsumer BindingPipeline.Controls.originalLetCase "Computation" BindingPipeline.Controls.letCaseSource.term
  singleConsumer BindingPipeline.Controls.originalMachine "Cfg" BindingPipeline.Controls.machineSource.term
  indicesAndOrigins
  vocabularyRefusal

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FiniteFocusControls
