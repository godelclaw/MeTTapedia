import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.SourceObservation
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.QueryLaws

/-!
# Native finite queries read from target source observations

Packets are checked against each question's actual source goal and finite
operational environment. Their ordered complete payloads become the existing
native certificate, without replacing source identity by target equality.
Malformed or wrong-context packets have no verdict. Semantic rejection is
proved only for packets equal to observations of replay-certified sessions;
an arbitrary decoded completion bit is not execution provenance.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.QueryTransport

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise StructuralDescent
open Mettapedia.OSLF.NativeTypes.Modal NativeReceiptRechecking
open Mettapedia.OSLF.NativeTypes.Generation
open IndexedModal FiniteFocusChecking FocusMeaning
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open MeTTaIL CompleteExecution

/-- Environment and goal equality are structural checks of the complete
encoded values, not comparisons of printed names. -/
def decodeSource? (environment : Environment) (source : SourceExecution.Source)
    (atom : Atom) : Option SourceExecution.Observation := do
  let observation ← SourceExecution.decodeAtom? atom
  if observation.environment = SourceExecution.environmentTerm environment source ∧
      observation.goal = DescentCodec.goalTerm (SourceExecution.sourceGoal environment source) then
    some observation
  else none

@[simp] theorem decodeSource?_observe (environment : Environment) (source : SourceExecution.Source)
    (snapshot : SourceExecution.Snapshot environment source) :
    decodeSource? environment source
      (CettaWireAtom.encode (SourceExecution.observe environment source snapshot).term) =
        some (SourceExecution.observe environment source snapshot) := by
  simp [decodeSource?, SourceExecution.observe]

theorem decodeSource?_context {environment : Environment} {source : SourceExecution.Source}
    {atom : Atom} {observation : SourceExecution.Observation}
    (decoded : decodeSource? environment source atom = some observation) :
    SourceExecution.decodeAtom? atom = some observation ∧
      observation.environment = SourceExecution.environmentTerm environment source ∧
      observation.goal = DescentCodec.goalTerm (SourceExecution.sourceGoal environment source) := by
  unfold decodeSource? at decoded
  cases parsed : SourceExecution.decodeAtom? atom with
  | none => simp [parsed] at decoded
  | some value =>
      by_cases compatible : value.environment = SourceExecution.environmentTerm environment source ∧
          value.goal = DescentCodec.goalTerm (SourceExecution.sourceGoal environment source)
      · simp [parsed, compatible] at decoded
        cases decoded
        exact ⟨rfl, compatible⟩
      · simp [parsed, compatible] at decoded

theorem decodeSource?_wrong_environment (environment : Environment) (source : SourceExecution.Source)
    (observation : SourceExecution.Observation)
    (different : observation.environment ≠ SourceExecution.environmentTerm environment source) :
    decodeSource? environment source (CettaWireAtom.encode observation.term) = none := by
  simp [decodeSource?, different]

theorem decodeSource?_wrong_goal (environment : Environment) (source : SourceExecution.Source)
    (observation : SourceExecution.Observation)
    (different : observation.goal ≠ DescentCodec.goalTerm (SourceExecution.sourceGoal environment source)) :
    decodeSource? environment source (CettaWireAtom.encode observation.term) = none := by
  simp [decodeSource?, different]

example (environment : Environment) (source : SourceExecution.Source) :
    decodeSource? environment source (.symbol "True") = none := rfl

private def decodeGoalSource? : Term → Option SourceExecution.Source
  | .application "DescentStepsGoal" [.natural _, bound, type, source, .natural _] => do
      pure ⟨← decodeList InferenceCettaWire.AuthoredRule.decodeType? bound,
        ← InferenceCettaWire.AuthoredRule.decodeType? type, ← InferenceCettaWire.decodePattern source⟩
  | _ => none

private theorem decodeGoalSource?_goalTerm (environment : Environment)
    (source : SourceExecution.Source) :
    decodeGoalSource? (DescentCodec.goalTerm (SourceExecution.sourceGoal environment source)) =
      some source := by
  cases source
  simp [decodeGoalSource?, DescentCodec.goalTerm, SourceExecution.sourceGoal, Scheduled.sourceGoal,
    DescentCodec.typesTerm, DescentCodec.typeTerm, DescentCodec.patternTerm, decodeList_encodeList]

theorem sourceGoal_fields {firstEnvironment secondEnvironment : Environment}
    {first second : SourceExecution.Source}
    (same : DescentCodec.goalTerm (SourceExecution.sourceGoal firstEnvironment first) =
      DescentCodec.goalTerm (SourceExecution.sourceGoal secondEnvironment second)) : first = second := by
  have decoded := congrArg decodeGoalSource? same
  simpa only [decodeGoalSource?_goalTerm, Option.some.injEq] using decoded

theorem decodeSource?_wrong_source (environment : Environment)
    (expected actual : SourceExecution.Source) (different : expected ≠ actual)
    (snapshot : SourceExecution.Snapshot environment actual) :
    decodeSource? environment expected
      (CettaWireAtom.encode (SourceExecution.observe environment actual snapshot).term) = none := by
  have goalDifferent : DescentCodec.goalTerm (SourceExecution.sourceGoal environment actual) ≠
      DescentCodec.goalTerm (SourceExecution.sourceGoal environment expected) :=
    fun same => different (sourceGoal_fields same).symm
  simp [decodeSource?, SourceExecution.observe, goalDifferent]

variable {installed : Joined.Installed} {ambient : List String}
  {question : FocusQuery.Question installed ambient}

abbrev Packets (question : FocusQuery.Question installed ambient) :=
  Fin (Discovery.sources question).length → Atom

structure Readout where
  certificate : List Witness
  settled : Bool
  deriving DecidableEq, Repr

abbrev sourceAt (question : FocusQuery.Question installed ambient)
    (position : Fin (Discovery.sources question).length) : SourceExecution.Source :=
  Discovery.Execution.source installed question.index ambient (Discovery.sources question)[position]

def decodeBlock? (question : FocusQuery.Question installed ambient)
    (position : Fin (Discovery.sources question).length) (atom : Atom) :
    Option (List Witness × Bool) := do
  let observation ← decodeSource? installed.indexed.operational.Environment (sourceAt question position) atom
  pure (observation.payloads.map (fun payload => ⟨(Discovery.sources question)[position], payload⟩),
    observation.settled)

def decodeBatch? (question : FocusQuery.Question installed ambient) (packets : Packets question) :
    Option Readout := do
  let blocks ← (List.finRange (Discovery.sources question).length).mapM
    (fun position => decodeBlock? question position (packets position))
  pure ⟨blocks.flatMap Prod.fst, blocks.all Prod.snd⟩

def observeSession (session : Discovery.Session question) : Packets question :=
  fun position => CettaWireAtom.encode
    (SourceExecution.observe installed.indexed.operational.Environment (sourceAt question position)
      (session.execution.runs position).state).term

@[simp] theorem decodeBlock?_observeSession (session : Discovery.Session question)
    (position : Fin (Discovery.sources question).length) :
    decodeBlock? question position (observeSession session position) =
      some (session.execution.sourceWitnesses position,
        (session.execution.runs position).state.agenda.isEmpty) := by
  unfold decodeBlock? observeSession
  rw [decodeSource?_observe]
  simp [SourceExecution.observe,
    Discovery.Execution.Batch.sourceWitnesses,
    BindingPipeline.Installed.CertifiedExecution.Session.receipts, BindingPipeline.Installed.receipts,
    List.map_map, Function.comp_def]

private theorem mapM_exact {α β : Type} (values : List α) (f : α → Option β) (g : α → β)
    (pointwise : ∀ value, f value = some (g value)) : values.mapM f = some (values.map g) := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp [pointwise, ih]

@[simp] theorem decodeBatch?_observeSession (session : Discovery.Session question) :
    decodeBatch? question (observeSession session) =
      some ⟨session.certificate, session.settled⟩ := by
  unfold decodeBatch?
  rw [mapM_exact _ _ _ (decodeBlock?_observeSession session)]
  simp [Discovery.Session.certificate, Discovery.Session.settled,
    Discovery.Execution.Batch.certificate, Discovery.Execution.Batch.settled,
    List.flatMap_map, Function.comp_def]

/-- Transport failure is separate from all semantic answers. The settled
field is used only as a readout; semantic force requires replay below. -/
def receive (question : FocusQuery.Question installed ambient) (packets : Packets question) :
    Option Discovery.Verdict := do
  let readout ← decodeBatch? question packets
  pure (if !checkFocus installed question.index ambient question.focus then .illFormedFocus
    else if FiniteFocusChecking.check question.parameters question.focus readout.certificate then .proved
    else if readout.settled then .refuted else .unknown)

@[simp] theorem receive_observeSession (session : Discovery.Session question) :
    receive question (observeSession session) = some session.verdict := by
  simp [receive, Discovery.Session.verdict]

def membership? (question : FocusQuery.Question installed ambient) (packets : Packets question) :
    Option (CertifiedMembership question.parameters question.focus) := do
  let readout ← decodeBatch? question packets
  verify? question.parameters question.focus readout.certificate

@[simp] theorem membership?_observeSession (session : Discovery.Session question) :
    membership? question (observeSession session) = session.membership? := by
  simp [membership?, Discovery.Session.membership?]

/-- Independently rechecking positive evidence needs no trusted completion
bit. Rejection, in contrast, uses actual replay below. -/
theorem receive_proved_checked (question : FocusQuery.Question installed ambient)
    (packets : Packets question) (accepted : receive question packets = some .proved) :
    ∃ readout, decodeBatch? question packets = some readout ∧
      FiniteFocusChecking.check question.parameters question.focus readout.certificate = true := by
  unfold receive at accepted
  cases decoded : decodeBatch? question packets with
  | none => simp [decoded] at accepted
  | some readout =>
      refine ⟨readout, rfl, ?_⟩
      cases admitted : checkFocus installed question.index ambient question.focus <;>
        cases checked : FiniteFocusChecking.check question.parameters question.focus readout.certificate <;>
        cases complete : readout.settled <;> simp_all

theorem receive_proved_sound (question : FocusQuery.Question installed ambient)
    (packets : Packets question) (accepted : receive question packets = some .proved) : question.Meaning := by
  obtain ⟨readout, _, checked⟩ := receive_proved_checked question packets accepted
  exact FiniteFocusChecking.check_sound question.parameters question.focus readout.certificate checked

/-- An unanswered request is initially only a search gap. Provenance and
settlement are required before turning it into a semantic counterexample. -/
def missingRequest? (question : FocusQuery.Question installed ambient) (packets : Packets question) :
    Option (Option (RelyValues installed question.index ambient)) := do
  let readout ← decodeBatch? question packets
  pure ((requests question.parameters).find? fun values =>
    !readout.certificate.any (accepts question.parameters question.focus values))

@[simp] theorem missingRequest?_observeSession (session : Discovery.Session question) :
    missingRequest? question (observeSession session) = some session.missingRequest? := by
  simp [missingRequest?, Discovery.Session.missingRequest?, Discovery.Execution.Batch.hasResponse,
    Discovery.Session.certificate]

theorem receive_proved (session : Discovery.Session question) (packets : Packets question)
    (replay : packets = observeSession session)
    (accepted : receive question packets = some .proved) : question.Meaning := by
  rw [replay, receive_observeSession] at accepted
  exact session.proved (Option.some.inj accepted)

theorem receive_refuted (session : Discovery.Session question) (packets : Packets question)
    (replay : packets = observeSession session)
    (rejected : receive question packets = some .refuted) : ¬ question.Meaning := by
  rw [replay, receive_observeSession] at rejected
  exact session.refuted (Option.some.inj rejected)

theorem receive_proved_iff (session : Discovery.Session question) (packets : Packets question)
    (replay : packets = observeSession session) (settled : session.settled = true) :
    receive question packets = some .proved ↔ question.Meaning := by
  rw [replay, receive_observeSession, Option.some.injEq]
  exact session.proved_iff settled

theorem receive_refuted_counterexample (session : Discovery.Session question) (packets : Packets question)
    (replay : packets = observeSession session)
    (rejected : receive question packets = some .refuted) :
    session.counterexample?.isSome = true := by
  rw [replay, receive_observeSession] at rejected
  exact session.refuted_counterexample (Option.some.inj rejected)

theorem received_missingRequest_sound (session : Discovery.Session question) (packets : Packets question)
    (replay : packets = observeSession session)
    (rejected : receive question packets = some .refuted)
    (values : RelyValues installed question.index ambient)
    (found : missingRequest? question packets = some (some values)) :
    FocusMeaning.Requested question.parameters.meaning values ∧
      ∀ source payload,
        ¬ FocusMeaning.SourceResponse question.parameters.meaning question.focus values source payload := by
  rw [replay, receive_observeSession] at rejected
  rw [replay, missingRequest?_observeSession, Option.some.injEq] at found
  have facts := session.missingRequest?_sound values found
  exact ⟨facts.1, session.no_response
    (session.refuted_checks.mp (Option.some.inj rejected)).2.2 values facts.1 facts.2⟩

/-- The returned tuple is computed from the received certificate. The
execution replay is used only to certify absence of all source responses. -/
def counterexample? (session : Discovery.Session question) (packets : Packets question)
    (replay : packets = observeSession session) : Option (Discovery.Counterexample question) :=
  if rejected : receive question packets = some .refuted then
    match found : missingRequest? question packets with
    | some (some values) =>
        let facts := received_missingRequest_sound session packets replay rejected values found
        some ⟨values, facts.1, facts.2⟩
    | _ => none
  else none

theorem counterexample?_returned (session : Discovery.Session question) (packets : Packets question)
    (replay : packets = observeSession session)
    (rejected : receive question packets = some .refuted) :
    (counterexample? session packets replay).isSome = true := by
  have original : session.verdict = .refuted := by
    simpa only [replay, receive_observeSession, Option.some.injEq] using rejected
  have missing := session.refuted_missingRequest original
  obtain ⟨values, found⟩ := Option.isSome_iff_exists.mp missing
  have received : missingRequest? question packets = some (some values) := by
    rw [replay, missingRequest?_observeSession, found]
  unfold counterexample?
  rw [dif_pos rejected]
  split <;> simp_all

theorem receive_unfinished_unknown (session : Discovery.Session question) (packets : Packets question)
    (replay : packets = observeSession session)
    (admitted : checkFocus installed question.index ambient question.focus = true)
    (unanswered : FiniteFocusChecking.check question.parameters question.focus session.certificate = false)
    (unfinished : session.settled = false) : receive question packets = some .unknown := by
  rw [replay, receive_observeSession]
  simp [Discovery.Session.verdict, admitted, unanswered, unfinished]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.QueryTransport
