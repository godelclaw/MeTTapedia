import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Resumption
import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.OSLF.MeTTaIL.CoreLanguageDef

/-!
# Controls: GödelClaw's protocol tables

Two of GödelClaw's protocol modules, as its runtime's module reader elaborates them: the request/call
reconciliation table (`retryWake`) and the display lifecycle of a streamed reply (`streamEvents`). Each rule
rewrites one application of a table (`reconcile(request, call)`, `display-step(state, event)`) to its
value, and neither language has an equation, so closed regions decide their formulas.

- **Reconciliation** (`retryWake`):
  - a failed request with a submitted call reconciles to an uncertain call (`failed_submitted_uncertain`),
    and not to a failed one (`failed_submitted_not_failed`);
  - every reconciliation has exactly one result, which has no step (`reconcile_total`);
  - a completed request never leaves a call claimed or submitted (`completed_settles`);
  - a pending request is not terminal, and the other request states are (`pending_not_terminal`,
    `others_terminal`).
- **Display lifecycle** (`streamEvents`):
  - every display step has exactly one result, which has no step (`display_total`);
  - a finished display stays finished whatever the event (`finished_absorbs`);
  - an interrupt finishes every state (`interrupt_finishes`);
  - no event brings a display that has left the forming state back to it (`never_back_to_forming`).
- **Tables are not composed** (`nested_stuck`): the modules author no congruence, so an application of a
  table to an unevaluated application does not step. Runs of a protocol, events applied one after another,
  need a congruence rule for the state argument.
- **The Lean reader** reads the modules' rule rows (`Label . Category ::= items;`), with positional
  parameters named as the runtime names them (`rule_rows`). A theory's exports are the sorts of the language
  it exports, so an exported sort no `Types` block declares is declared by its export, as the runtime's reader
  declares it. The Lean reader therefore reads both modules to the languages above, field for field.
-/

set_option autoImplicit false

open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.ProtocolControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)

/-- A loaded module's language, elaborated to its core. -/
def core (loaded : Except Mettapedia.GSLT.LanguageDef.ModuleSource.Error LanguageDef) : LanguageDef :=
  ((loaded.toOption.getD (LanguageDef.empty "")).toCore.toOption.map (·.language)).getD (LanguageDef.empty "")

def constant (label : String) : Pattern := .apply label []

/-! ## Deciding with closed regions -/

section Deciding

variable (language : LanguageDef)

/-- The front door proves the formula. -/
def proves (formula : Formula 0) (term : Pattern) : Bool :=
  match ask RelationEnv.empty [] language 2 formula term none 4 with
  | .proved _ => true
  | _ => false

/-- The front door refutes the formula. -/
def refutes (formula : Formula 0) (term : Pattern) : Bool :=
  match ask RelationEnv.empty [] language 2 formula term none 4 with
  | .refuted _ => true
  | _ => false

variable {language}

theorem proves_sound {formula : Formula 0} {term : Pattern} (proved : proves language formula term = true) :
    (referenceStructure RelationEnv.empty language).sat Env.closed formula term := by
  unfold proves at proved
  split at proved
  · exact ask_proved ‹_›
  · cases proved

theorem refutes_sound {formula : Formula 0} {term : Pattern} (refuted : refutes language formula term = true) :
    ¬ (referenceStructure RelationEnv.empty language).sat Env.closed formula term := by
  unfold refutes at refuted
  split at refuted
  · exact ask_refuted ‹_›
  · cases refuted

theorem proves_all {formula : Formula 0} {terms : List Pattern}
    (proved : terms.all (proves language formula) = true) :
    ∀ term ∈ terms, (referenceStructure RelationEnv.empty language).sat Env.closed formula term :=
  fun term member => proves_sound (List.all_eq_true.mp proved term member)

end Deciding

def steps : Formula 0 := .possibly .any .top

/-- Exactly one result, and it has no step. -/
def oneFinalResult : Formula 0 := .and (Formula.exactlyOne .forward .any) (.necessarily .any (.necessarily .any .bot))

/-! ## Reconciliation -/

/-- The reconciliation table, as the runtime's module reader elaborates it. -/
def retryWake : LanguageDef :=
  { «name» := "RetryWake",
    «types» := [⟨"RequestState", .ast⟩, ⟨"CallState", .ast⟩, ⟨"Flag", .ast⟩],
    «terms» := [
      { label := "RequestPending", category := "RequestState", params := [],
        syntaxPattern := [.terminal "request-pending"] },
      { label := "RequestCompleted", category := "RequestState", params := [],
        syntaxPattern := [.terminal "request-completed"] },
      { label := "RequestFailed", category := "RequestState", params := [],
        syntaxPattern := [.terminal "request-failed"] },
      { label := "RequestUnknown", category := "RequestState", params := [],
        syntaxPattern := [.terminal "request-unknown"] },
      { label := "CallAbsent", category := "CallState", params := [],
        syntaxPattern := [.terminal "call-absent"] },
      { label := "CallClaimed", category := "CallState", params := [],
        syntaxPattern := [.terminal "call-claimed"] },
      { label := "CallSubmitted", category := "CallState", params := [],
        syntaxPattern := [.terminal "call-submitted"] },
      { label := "CallCompleted", category := "CallState", params := [],
        syntaxPattern := [.terminal "call-completed"] },
      { label := "CallFailed", category := "CallState", params := [],
        syntaxPattern := [.terminal "call-failed"] },
      { label := "CallUncertain", category := "CallState", params := [],
        syntaxPattern := [.terminal "call-uncertain"] },
      { label := "FlagFalse", category := "Flag", params := [],
        syntaxPattern := [.terminal "flag-false"] },
      { label := "FlagTrue", category := "Flag", params := [],
        syntaxPattern := [.terminal "flag-true"] },
      { label := "IsActive", category := "Flag", params := [.simple "argument:0" (.base "CallState")],
        syntaxPattern := [.terminal "is-active", .terminal "(", .nonTerminal "argument:0", .terminal ")"] },
      { label := "IsTerminal", category := "Flag", params := [.simple "argument:0" (.base "RequestState")],
        syntaxPattern := [.terminal "is-terminal", .terminal "(", .nonTerminal "argument:0", .terminal ")"] },
      { label := "Reconcile", category := "CallState", params := [.simple "argument:0" (.base "RequestState"), .simple "argument:1" (.base "CallState")],
        syntaxPattern := [.terminal "reconcile", .terminal "(", .nonTerminal "argument:0", .terminal ",", .nonTerminal "argument:1", .terminal ")"] }],
    «equations» := [],
    «rewrites» := [
      { «name» := "PendingAbsent", typeContext := [], premises := [], left := .apply "Reconcile" [.apply "RequestPending" [], .apply "CallAbsent" []], right := .apply "CallAbsent" [] },
      { «name» := "PendingClaimed", typeContext := [], premises := [], left := .apply "Reconcile" [.apply "RequestPending" [], .apply "CallClaimed" []], right := .apply "CallClaimed" [] },
      { «name» := "PendingSubmitted", typeContext := [], premises := [], left := .apply "Reconcile" [.apply "RequestPending" [], .apply "CallSubmitted" []], right := .apply "CallSubmitted" [] },
      { «name» := "PendingCompleted", typeContext := [], premises := [], left := .apply "Reconcile" [.apply "RequestPending" [], .apply "CallCompleted" []], right := .apply "CallCompleted" [] },
      { «name» := "PendingFailed", typeContext := [], premises := [], left := .apply "Reconcile" [.apply "RequestPending" [], .apply "CallFailed" []], right := .apply "CallFailed" [] },
      { «name» := "PendingUncertain", typeContext := [], premises := [], left := .apply "Reconcile" [.apply "RequestPending" [], .apply "CallUncertain" []], right := .apply "CallUncertain" [] },
      { «name» := "CompletedAbsent", typeContext := [], premises := [], left := .apply "Reconcile" [.apply "RequestCompleted" [], .apply "CallAbsent" []], right := .apply "CallAbsent" [] },
      { «name» := "CompletedClaimed", typeContext := [], premises := [], left := .apply "Reconcile" [.apply "RequestCompleted" [], .apply "CallClaimed" []], right := .apply "CallCompleted" [] },
      { «name» := "CompletedSubmitted", typeContext := [], premises := [], left := .apply "Reconcile" [.apply "RequestCompleted" [], .apply "CallSubmitted" []], right := .apply "CallCompleted" [] },
      { «name» := "CompletedCompleted", typeContext := [], premises := [], left := .apply "Reconcile" [.apply "RequestCompleted" [], .apply "CallCompleted" []], right := .apply "CallCompleted" [] },
      { «name» := "CompletedFailed", typeContext := [], premises := [], left := .apply "Reconcile" [.apply "RequestCompleted" [], .apply "CallFailed" []], right := .apply "CallFailed" [] },
      { «name» := "CompletedUncertain", typeContext := [], premises := [], left := .apply "Reconcile" [.apply "RequestCompleted" [], .apply "CallUncertain" []], right := .apply "CallUncertain" [] },
      { «name» := "FailedAbsent", typeContext := [], premises := [], left := .apply "Reconcile" [.apply "RequestFailed" [], .apply "CallAbsent" []], right := .apply "CallAbsent" [] },
      { «name» := "FailedClaimed", typeContext := [], premises := [], left := .apply "Reconcile" [.apply "RequestFailed" [], .apply "CallClaimed" []], right := .apply "CallFailed" [] },
      { «name» := "FailedSubmitted", typeContext := [], premises := [], left := .apply "Reconcile" [.apply "RequestFailed" [], .apply "CallSubmitted" []], right := .apply "CallUncertain" [] },
      { «name» := "FailedCompleted", typeContext := [], premises := [], left := .apply "Reconcile" [.apply "RequestFailed" [], .apply "CallCompleted" []], right := .apply "CallCompleted" [] },
      { «name» := "FailedFailed", typeContext := [], premises := [], left := .apply "Reconcile" [.apply "RequestFailed" [], .apply "CallFailed" []], right := .apply "CallFailed" [] },
      { «name» := "FailedUncertain", typeContext := [], premises := [], left := .apply "Reconcile" [.apply "RequestFailed" [], .apply "CallUncertain" []], right := .apply "CallUncertain" [] },
      { «name» := "UnknownAbsent", typeContext := [], premises := [], left := .apply "Reconcile" [.apply "RequestUnknown" [], .apply "CallAbsent" []], right := .apply "CallAbsent" [] },
      { «name» := "UnknownClaimed", typeContext := [], premises := [], left := .apply "Reconcile" [.apply "RequestUnknown" [], .apply "CallClaimed" []], right := .apply "CallUncertain" [] },
      { «name» := "UnknownSubmitted", typeContext := [], premises := [], left := .apply "Reconcile" [.apply "RequestUnknown" [], .apply "CallSubmitted" []], right := .apply "CallUncertain" [] },
      { «name» := "UnknownCompleted", typeContext := [], premises := [], left := .apply "Reconcile" [.apply "RequestUnknown" [], .apply "CallCompleted" []], right := .apply "CallCompleted" [] },
      { «name» := "UnknownFailed", typeContext := [], premises := [], left := .apply "Reconcile" [.apply "RequestUnknown" [], .apply "CallFailed" []], right := .apply "CallFailed" [] },
      { «name» := "UnknownUncertain", typeContext := [], premises := [], left := .apply "Reconcile" [.apply "RequestUnknown" [], .apply "CallUncertain" []], right := .apply "CallUncertain" [] },
      { «name» := "ActiveAbsent", typeContext := [], premises := [], left := .apply "IsActive" [.apply "CallAbsent" []], right := .apply "FlagFalse" [] },
      { «name» := "ActiveClaimed", typeContext := [], premises := [], left := .apply "IsActive" [.apply "CallClaimed" []], right := .apply "FlagTrue" [] },
      { «name» := "ActiveSubmitted", typeContext := [], premises := [], left := .apply "IsActive" [.apply "CallSubmitted" []], right := .apply "FlagTrue" [] },
      { «name» := "ActiveCompleted", typeContext := [], premises := [], left := .apply "IsActive" [.apply "CallCompleted" []], right := .apply "FlagFalse" [] },
      { «name» := "ActiveFailed", typeContext := [], premises := [], left := .apply "IsActive" [.apply "CallFailed" []], right := .apply "FlagFalse" [] },
      { «name» := "ActiveUncertain", typeContext := [], premises := [], left := .apply "IsActive" [.apply "CallUncertain" []], right := .apply "FlagFalse" [] },
      { «name» := "TerminalPending", typeContext := [], premises := [], left := .apply "IsTerminal" [.apply "RequestPending" []], right := .apply "FlagFalse" [] },
      { «name» := "TerminalCompleted", typeContext := [], premises := [], left := .apply "IsTerminal" [.apply "RequestCompleted" []], right := .apply "FlagTrue" [] },
      { «name» := "TerminalFailed", typeContext := [], premises := [], left := .apply "IsTerminal" [.apply "RequestFailed" []], right := .apply "FlagTrue" [] },
      { «name» := "TerminalUnknown", typeContext := [], premises := [], left := .apply "IsTerminal" [.apply "RequestUnknown" []], right := .apply "FlagTrue" [] }] }

abbrev RetryWake := referenceStructure RelationEnv.empty retryWake

def requestStates : List String := ["RequestPending", "RequestCompleted", "RequestFailed", "RequestUnknown"]
def callStates : List String :=
  ["CallAbsent", "CallClaimed", "CallSubmitted", "CallCompleted", "CallFailed", "CallUncertain"]

def reconcile (request call : String) : Pattern := .apply "Reconcile" [constant request, constant call]

def reconciliations : List Pattern := requestStates.flatMap fun request => callStates.map (reconcile request)

/-- **A failed request with a submitted call reconciles to an uncertain call.** -/
theorem failed_submitted_uncertain :
    RetryWake.sat Env.closed (.necessarily .any (.is (constant "CallUncertain"))) (reconcile "RequestFailed" "CallSubmitted") ∧
      RetryWake.sat Env.closed steps (reconcile "RequestFailed" "CallSubmitted") :=
  ⟨proves_sound (by decide +kernel), proves_sound (by decide +kernel)⟩

/-- **And not to a failed call.** -/
theorem failed_submitted_not_failed :
    ¬ RetryWake.sat Env.closed (.possibly .any (.is (constant "CallFailed"))) (reconcile "RequestFailed" "CallSubmitted") :=
  refutes_sound (by decide +kernel)

/-- **Every reconciliation has exactly one result, which has no step.** -/
theorem reconcile_total : ∀ term ∈ reconciliations, RetryWake.sat Env.closed oneFinalResult term :=
  proves_all (by decide +kernel)

/-- **A completed request never leaves a call claimed or submitted.** -/
theorem completed_settles : ∀ term ∈ callStates.map (reconcile "RequestCompleted"),
    RetryWake.sat Env.closed
      (.necessarily .any (.and (.isNot (constant "CallClaimed")) (.isNot (constant "CallSubmitted")))) term :=
  proves_all (by decide +kernel)

def terminal (request : String) : Pattern := .apply "IsTerminal" [constant request]

/-- **A pending request is not terminal.** -/
theorem pending_not_terminal :
    RetryWake.sat Env.closed (.necessarily .any (.is (constant "FlagFalse"))) (terminal "RequestPending") ∧
      RetryWake.sat Env.closed steps (terminal "RequestPending") :=
  ⟨proves_sound (by decide +kernel), proves_sound (by decide +kernel)⟩

/-- **The other request states are.** -/
theorem others_terminal : ∀ term ∈ (requestStates.drop 1).map terminal,
    RetryWake.sat Env.closed (.and steps (.necessarily .any (.is (constant "FlagTrue")))) term :=
  proves_all (by decide +kernel)

/-- **Tables are not composed**: whether the reconciled call is active does not step. -/
theorem nested_stuck :
    ¬ RetryWake.sat Env.closed steps (.apply "IsActive" [reconcile "RequestFailed" "CallSubmitted"]) :=
  refutes_sound (by decide +kernel)

/-! ## Display lifecycle -/

/-- The display lifecycle, as the runtime's module reader elaborates it. -/
def streamEvents : LanguageDef :=
  { «name» := "Canonical",
    «types» := [⟨"DisplayState", .ast⟩, ⟨"DisplayEvent", .ast⟩],
    «terms» := [
      { label := "Forming", category := "DisplayState", params := [],
        syntaxPattern := [.terminal "forming"] },
      { label := "Streaming", category := "DisplayState", params := [],
        syntaxPattern := [.terminal "streaming"] },
      { label := "Running", category := "DisplayState", params := [],
        syntaxPattern := [.terminal "running"] },
      { label := "Finished", category := "DisplayState", params := [],
        syntaxPattern := [.terminal "finished"] },
      { label := "ProviderText", category := "DisplayEvent", params := [],
        syntaxPattern := [.terminal "ProviderText"] },
      { label := "ProviderTool", category := "DisplayEvent", params := [],
        syntaxPattern := [.terminal "ProviderTool"] },
      { label := "ExecutorStart", category := "DisplayEvent", params := [],
        syntaxPattern := [.terminal "ExecutorStart"] },
      { label := "ExecutorFinish", category := "DisplayEvent", params := [],
        syntaxPattern := [.terminal "ExecutorFinish"] },
      { label := "TerminalFinish", category := "DisplayEvent", params := [],
        syntaxPattern := [.terminal "TerminalFinish"] },
      { label := "Interrupt", category := "DisplayEvent", params := [],
        syntaxPattern := [.terminal "Interrupt"] },
      { label := "Step", category := "DisplayState", params := [.simple "argument:0" (.base "DisplayState"), .simple "argument:1" (.base "DisplayEvent")],
        syntaxPattern := [.terminal "display-step", .terminal "(", .nonTerminal "argument:0", .terminal ",", .nonTerminal "argument:1", .terminal ")"] }],
    «equations» := [],
    «rewrites» := [
      { «name» := "FormingProviderText", typeContext := [], premises := [], left := .apply "Step" [.apply "Forming" [], .apply "ProviderText" []], right := .apply "Streaming" [] },
      { «name» := "FormingProviderTool", typeContext := [], premises := [], left := .apply "Step" [.apply "Forming" [], .apply "ProviderTool" []], right := .apply "Forming" [] },
      { «name» := "FormingExecutorStart", typeContext := [], premises := [], left := .apply "Step" [.apply "Forming" [], .apply "ExecutorStart" []], right := .apply "Running" [] },
      { «name» := "FormingExecutorFinish", typeContext := [], premises := [], left := .apply "Step" [.apply "Forming" [], .apply "ExecutorFinish" []], right := .apply "Finished" [] },
      { «name» := "FormingTerminalFinish", typeContext := [], premises := [], left := .apply "Step" [.apply "Forming" [], .apply "TerminalFinish" []], right := .apply "Finished" [] },
      { «name» := "FormingInterrupt", typeContext := [], premises := [], left := .apply "Step" [.apply "Forming" [], .apply "Interrupt" []], right := .apply "Finished" [] },
      { «name» := "StreamingProviderText", typeContext := [], premises := [], left := .apply "Step" [.apply "Streaming" [], .apply "ProviderText" []], right := .apply "Streaming" [] },
      { «name» := "StreamingProviderTool", typeContext := [], premises := [], left := .apply "Step" [.apply "Streaming" [], .apply "ProviderTool" []], right := .apply "Streaming" [] },
      { «name» := "StreamingExecutorStart", typeContext := [], premises := [], left := .apply "Step" [.apply "Streaming" [], .apply "ExecutorStart" []], right := .apply "Running" [] },
      { «name» := "StreamingExecutorFinish", typeContext := [], premises := [], left := .apply "Step" [.apply "Streaming" [], .apply "ExecutorFinish" []], right := .apply "Finished" [] },
      { «name» := "StreamingTerminalFinish", typeContext := [], premises := [], left := .apply "Step" [.apply "Streaming" [], .apply "TerminalFinish" []], right := .apply "Finished" [] },
      { «name» := "StreamingInterrupt", typeContext := [], premises := [], left := .apply "Step" [.apply "Streaming" [], .apply "Interrupt" []], right := .apply "Finished" [] },
      { «name» := "RunningProviderText", typeContext := [], premises := [], left := .apply "Step" [.apply "Running" [], .apply "ProviderText" []], right := .apply "Running" [] },
      { «name» := "RunningProviderTool", typeContext := [], premises := [], left := .apply "Step" [.apply "Running" [], .apply "ProviderTool" []], right := .apply "Running" [] },
      { «name» := "RunningExecutorStart", typeContext := [], premises := [], left := .apply "Step" [.apply "Running" [], .apply "ExecutorStart" []], right := .apply "Running" [] },
      { «name» := "RunningExecutorFinish", typeContext := [], premises := [], left := .apply "Step" [.apply "Running" [], .apply "ExecutorFinish" []], right := .apply "Finished" [] },
      { «name» := "RunningTerminalFinish", typeContext := [], premises := [], left := .apply "Step" [.apply "Running" [], .apply "TerminalFinish" []], right := .apply "Finished" [] },
      { «name» := "RunningInterrupt", typeContext := [], premises := [], left := .apply "Step" [.apply "Running" [], .apply "Interrupt" []], right := .apply "Finished" [] },
      { «name» := "FinishedProviderText", typeContext := [], premises := [], left := .apply "Step" [.apply "Finished" [], .apply "ProviderText" []], right := .apply "Finished" [] },
      { «name» := "FinishedProviderTool", typeContext := [], premises := [], left := .apply "Step" [.apply "Finished" [], .apply "ProviderTool" []], right := .apply "Finished" [] },
      { «name» := "FinishedExecutorStart", typeContext := [], premises := [], left := .apply "Step" [.apply "Finished" [], .apply "ExecutorStart" []], right := .apply "Finished" [] },
      { «name» := "FinishedExecutorFinish", typeContext := [], premises := [], left := .apply "Step" [.apply "Finished" [], .apply "ExecutorFinish" []], right := .apply "Finished" [] },
      { «name» := "FinishedTerminalFinish", typeContext := [], premises := [], left := .apply "Step" [.apply "Finished" [], .apply "TerminalFinish" []], right := .apply "Finished" [] },
      { «name» := "FinishedInterrupt", typeContext := [], premises := [], left := .apply "Step" [.apply "Finished" [], .apply "Interrupt" []], right := .apply "Finished" [] }] }

abbrev StreamEvents := referenceStructure RelationEnv.empty streamEvents

def displayStates : List String := ["Forming", "Streaming", "Running", "Finished"]
def displayEvents : List String :=
  ["ProviderText", "ProviderTool", "ExecutorStart", "ExecutorFinish", "TerminalFinish", "Interrupt"]

def displayStep (state event : String) : Pattern := .apply "Step" [constant state, constant event]

def displaySteps : List Pattern := displayStates.flatMap fun state => displayEvents.map (displayStep state)

/-- **Every display step has exactly one result, which has no step.** -/
theorem display_total : ∀ term ∈ displaySteps, StreamEvents.sat Env.closed oneFinalResult term :=
  proves_all (by decide +kernel)

/-- **A finished display stays finished, whatever the event.** -/
theorem finished_absorbs : ∀ term ∈ displayEvents.map (displayStep "Finished"),
    StreamEvents.sat Env.closed (.and steps (.necessarily .any (.is (constant "Finished")))) term :=
  proves_all (by decide +kernel)

/-- **An interrupt finishes every state.** -/
theorem interrupt_finishes : ∀ term ∈ displayStates.map (displayStep · "Interrupt"),
    StreamEvents.sat Env.closed (.and steps (.necessarily .any (.is (constant "Finished")))) term :=
  proves_all (by decide +kernel)

/-- **No event brings a display that has left the forming state back to it.** -/
theorem never_back_to_forming : ∀ term ∈ (displayStates.drop 1).flatMap fun state => displayEvents.map (displayStep state),
    StreamEvents.sat Env.closed (.necessarily .any (.isNot (constant "Forming"))) term :=
  proves_all (by decide +kernel)

/-! ## The Lean reader

Reading a module makes its syntax available in the rest of the file, so the modules are read last. -/

/-- A tree is a leaf or a node of two trees, as rule rows read it. -/
def ruleRows : List GrammarRule :=
  [{ label := "Leaf", category := "Tree", params := [], syntaxPattern := [.terminal "leaf"] },
    { label := "Node", category := "Tree",
      params := [.simple "argument:0" (.base "Tree"), .simple "argument:1" (.base "Tree")],
      syntaxPattern := [.terminal "node", .terminal "(", .nonTerminal "argument:0", .terminal ",",
        .nonTerminal "argument:1", .terminal ")"] }]

open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL in
#module Module RuleRows {
  Theory Trees() {
    Types { Tree; }
    Terms {
      Leaf . Tree ::= "leaf";
      Node . Tree ::= "node" "(" Tree "," Tree ")";
    }
  }
  theory Trees()
}

/-- **Rule rows**: each category becomes the next positional parameter, `argument:0`, `argument:1`, …. -/
theorem rule_rows : (core RuleRows.language).terms = ruleRows := by cbv

#module_file "../../../../../../metta/gslt/module/godelclaw/RetryWake.module"
#module_file "../../../../../../metta/gslt/module/godelclaw/StreamEvents.module"

/-- The read language has the runtime reader's sorts, constructors, equations and rewrites. -/
def readsAs (loaded : Except Mettapedia.GSLT.LanguageDef.ModuleSource.Error LanguageDef) (expected : LanguageDef) :
    Bool :=
  match loaded with
  | .ok language =>
    decide (language.types = expected.types) && decide (language.terms = expected.terms) &&
      decide (language.equations = expected.equations) && decide (language.rewrites = expected.rewrites)
  | .error _ => false

/- **The Lean reader reads both modules as the runtime's reader does**: their exports declare the sorts. -/
#guard readsAs GodelClawRetryWake.language retryWake
#guard readsAs StreamEvents.language streamEvents

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.ProtocolControls
