import Mettapedia.GSLT.LanguageDef.ExecutableProtocolSafety

/-!
# Explicit protocol continuations

Finite target substitution composes ordinary C-shaped trees. The corresponding
caller executes the second protocol from the exact intermediate world and
reply suffix, retaining every call of the first stage even when the second
stage fails or suspends. Event charges are observations of these retained
occurrences, not a claim that a host's physical cost has been measured.

Token handoff is an explicit interface over the intermediate host world.
Concrete token identity may include owner and generation information; equal
resource-role spellings are not a handoff proof. Host conformance to the two
boundary contracts remains explicit. Symbolic continuation admission carries
the first stage's irreversible bit instead of restarting it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ExecutableProtocol

def CStmt.bind (body : CStmt) (next : Outcome → CStmt) : CStmt :=
  match body with
  | .ret outcome => next outcome
  | .ifCall name yes no => .ifCall name (yes.bind next) (no.bind next)
  | .voidCall name rest => .voidCall name (rest.bind next)

/-- The second result supplies the ordinary result, world and reply suffix;
the already executed first-stage trace is retained as a prefix. -/
def appendExecution {World : Type} (first second : Execution World) : Execution World :=
  { second with calls := first.calls ++ second.calls }

theorem appendExecution_stop {World : Type} (first : Execution World) (outcome : Outcome)
    (returned : first.status = .returned outcome) :
    appendExecution first (stop (.returned outcome) first.world first.remaining) = first := by
  cases first with
  | mk status world remaining calls =>
      simp only at returned
      subst status
      simp [appendExecution, stop]

def continueExecution {World : Type}
    (next : Outcome → World → List Bool → Execution World)
    (first : Execution World) : Execution World :=
  match first.status with
  | .returned outcome => appendExecution first (next outcome first.world first.remaining)
  | _ => first

theorem continueExecution_record {World : Type}
    (next : Outcome → World → List Bool → Execution World)
    (event : Event) (first : Execution World) :
    continueExecution next (record event first) =
      record event (continueExecution next first) := by
  cases first with
  | mk status world remaining calls =>
      cases status <;> rfl

theorem evalC_bind {World : Type} (host : Host World) (body : CStmt)
    (next : Outcome → CStmt) (world : World) (replies : List Bool) :
    evalC host (body.bind next) world replies =
      continueExecution (fun outcome => evalC host (next outcome))
        (evalC host body world replies) := by
  induction body generalizing world replies with
  | ret outcome => simp [CStmt.bind, evalC, continueExecution, appendExecution, stop]
  | ifCall name yes no ihYes ihNo =>
      cases replies with
      | nil => rfl
      | cons reply rest =>
          cases reply with
          | false =>
              simpa only [CStmt.bind, evalC, continueExecution_record] using
                congrArg (record (.boolean name false))
                  (ihNo (host.boolean name world false) rest)
          | true =>
              simpa only [CStmt.bind, evalC, continueExecution_record] using
                congrArg (record (.boolean name true))
                  (ihYes (host.boolean name world true) rest)
  | voidCall name rest ih =>
      simpa only [CStmt.bind, evalC, continueExecution_record] using
        congrArg (record (.void name)) (ih (host.void name world) replies)

def sequenceTarget (first second : CStmt) (on : Outcome → Bool) : CStmt :=
  first.bind fun outcome => if on outcome then second else .ret outcome

/-- An independent caller, using the two source interpreters directly. -/
def sequenceSource {World : Type} (first second : Protocol) (host : Host World)
    (on : Outcome → Bool) (world : World) (replies : List Bool) : Execution World :=
  let firstRun := evalSource first host first.body world replies
  match firstRun.status with
  | .returned outcome =>
      if on outcome then appendExecution firstRun
        (evalSource second host second.body firstRun.world firstRun.remaining)
      else firstRun
  | _ => firstRun

theorem plans_sequence_exact {World : Type} {first second : Plan}
    (firstValid : PlanValid first) (secondValid : PlanValid second)
    (host : Host World) (on : Outcome → Bool) (world : World) (replies : List Bool) :
    evalC host (sequenceTarget first.target second.target on) world replies =
      sequenceSource first.protocol second.protocol host on world replies := by
  rw [sequenceTarget, evalC_bind, firstValid.eval_exact]
  unfold sequenceSource continueExecution
  cases result : (evalSource first.protocol host first.protocol.body world replies).status with
  | returned outcome =>
      simp only [result]
      cases selected : on outcome with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, evalC]
          exact appendExecution_stop _ _ result
      | true => simp [secondValid.eval_exact]
  | noReply name => simp [result]
  | unknownHook id => simp [result]
  | unknownResource id => simp [result]

/-- The concatenation law has no success restriction on the second result. -/
theorem sequenceTarget_continues {World : Type} (host : Host World)
    (first second : CStmt) (on : Outcome → Bool) (world : World) (replies : List Bool)
    (outcome : Outcome) (returned : (evalC host first world replies).status = .returned outcome)
    (selected : on outcome = true) :
    evalC host (sequenceTarget first second on) world replies =
      appendExecution (evalC host first world replies)
        (evalC host second (evalC host first world replies).world
          (evalC host first world replies).remaining) := by
  simp only [sequenceTarget, evalC_bind, continueExecution, returned, selected,
    ↓reduceIte]

theorem sequenceTarget_skips {World : Type} (host : Host World)
    (first second : CStmt) (on : Outcome → Bool) (world : World) (replies : List Bool)
    (outcome : Outcome) (returned : (evalC host first world replies).status = .returned outcome)
    (selected : on outcome = false) :
    evalC host (sequenceTarget first second on) world replies =
      evalC host first world replies := by
  simp only [sequenceTarget, evalC_bind, continueExecution, returned, selected,
    Bool.false_eq_true, ↓reduceIte, evalC]
  exact appendExecution_stop _ _ returned

def invoice (charge : Event → Nat) (calls : List Event) : Nat :=
  (calls.map charge).sum

theorem invoice_append (charge : Event → Nat) (first second : List Event) :
    invoice charge (first ++ second) = invoice charge first + invoice charge second := by
  simp [invoice]

theorem sequenceTarget_invoice {World : Type} (host : Host World)
    (first second : CStmt) (on : Outcome → Bool) (world : World) (replies : List Bool)
    (outcome : Outcome) (returned : (evalC host first world replies).status = .returned outcome)
    (selected : on outcome = true) (charge : Event → Nat) :
    invoice charge (evalC host (sequenceTarget first second on) world replies).calls =
      invoice charge (evalC host first world replies).calls +
        invoice charge (evalC host second (evalC host first world replies).world
          (evalC host first world replies).remaining).calls := by
  rw [sequenceTarget_continues host first second on world replies outcome returned selected]
  exact invoice_append charge _ _

/-- Concrete boundary token identity is supplied by the caller. `owns` may
instantiate an existing owner/root/generation predicate; it is not inferred
from a source resource's name. Lists make duplicate-token obligations visible. -/
structure TokenBoundary (World Token : Type) where
  input : List Token
  output : Outcome → List Token
  owns : World → Token → Prop

def TokenBoundary.Ready {World Token : Type} (boundary : TokenBoundary World Token)
    (world : World) : Prop :=
  boundary.input.Nodup ∧ ∀ token ∈ boundary.input, boundary.owns world token

def TokenBoundary.Delivered {World Token : Type} (boundary : TokenBoundary World Token)
    (outcome : Outcome) (world : World) : Prop :=
  (boundary.output outcome).Nodup ∧
    ∀ token ∈ boundary.output outcome, boundary.owns world token

/-- Every continuation token is a distinct token actually delivered by the
first stage, and the second ownership predicate accepts that same token in
the unchanged intermediate world. The order is an explicit interface policy. -/
def TokenBoundary.Compatible {World Token : Type}
    (first second : TokenBoundary World Token) (on : Outcome → Bool) : Prop :=
  ∀ outcome, on outcome = true →
    second.input.Sublist (first.output outcome) ∧
      ∀ world token, token ∈ second.input → first.owns world token → second.owns world token

theorem TokenBoundary.ready_of_delivered {World Token : Type}
    {first second : TokenBoundary World Token} {on : Outcome → Bool}
    (compatible : first.Compatible second on) (outcome : Outcome) (selected : on outcome = true)
    (world : World) (delivered : first.Delivered outcome world) : second.Ready world := by
  obtain ⟨included, transport⟩ := compatible outcome selected
  exact ⟨included.nodup delivered.1,
    fun token member => transport world token member
      (delivered.2 token (included.subset member))⟩

/-- A finite boundary input is explicitly bound to the protocol's entry
resource roles. No role spelling is silently treated as a physical token. -/
def TokenBoundary.BindsEntry {World Token : Type} (boundary : TokenBoundary World Token)
    (p : Protocol) (binding : String → Option Token) : Prop :=
  List.Forall₂ (fun id token => binding id = some token) p.entryOwned boundary.input

theorem binding_member {Token : Type} {binding : String → Option Token}
    {ids : List String} {tokens : List Token}
    (bound : List.Forall₂ (fun id token => binding id = some token) ids tokens) :
    ∀ id ∈ ids, ∃ token ∈ tokens, binding id = some token := by
  induction bound with
  | nil => simp
  | @cons id token ids tokens head tail ih =>
      intro wanted member
      rcases List.mem_cons.mp member with same | rest
      · subst wanted
        exact ⟨token, by simp, head⟩
      · obtain ⟨found, present, foundBinding⟩ := ih wanted rest
        exact ⟨found, List.mem_cons_of_mem token present, foundBinding⟩

theorem TokenBoundary.entry_tokens_live {World Token : Type}
    {boundary : TokenBoundary World Token} {p : Protocol} {binding : String → Option Token}
    (bound : boundary.BindsEntry p binding) {world : World} (ready : boundary.Ready world) :
    ∀ id ∈ p.entryOwned, ∃ token, binding id = some token ∧ boundary.owns world token := by
  intro id member
  obtain ⟨token, present, foundBinding⟩ := binding_member bound id member
  exact ⟨token, foundBinding, ready.2 token present⟩

/-- This is a genuine host conformance obligation. Source admission does not
prove that an arbitrary C hook acquires, transfers or retains a real owner. -/
def TokenBoundary.Conforms {World Token : Type} (boundary : TokenBoundary World Token)
    (host : Host World) (target : CStmt) : Prop :=
  ∀ world replies, boundary.Ready world → ∀ outcome,
    (evalC host target world replies).status = .returned outcome →
      boundary.Delivered outcome (evalC host target world replies).world

/-- Component token contracts compose along the actual intermediate state.
The same theorem retains the exact first trace and every second-stage call. -/
theorem sequence_token_handoff {World Token : Type} (host : Host World)
    (first second : CStmt) (on : Outcome → Bool)
    (firstBoundary secondBoundary : TokenBoundary World Token)
    (firstConforms : firstBoundary.Conforms host first)
    (secondConforms : secondBoundary.Conforms host second)
    (compatible : firstBoundary.Compatible secondBoundary on)
    (world : World) (replies : List Bool) (ready : firstBoundary.Ready world)
    (outcome : Outcome) (returned : (evalC host first world replies).status = .returned outcome)
    (selected : on outcome = true) :
    secondBoundary.Ready (evalC host first world replies).world ∧
      (evalC host (sequenceTarget first second on) world replies).calls =
        (evalC host first world replies).calls ++
          (evalC host second (evalC host first world replies).world
            (evalC host first world replies).remaining).calls ∧
      ∀ finalOutcome,
        (evalC host (sequenceTarget first second on) world replies).status =
          .returned finalOutcome →
        secondBoundary.Delivered finalOutcome
          (evalC host (sequenceTarget first second on) world replies).world := by
  have intermediate := TokenBoundary.ready_of_delivered compatible outcome selected _
    (firstConforms world replies ready outcome returned)
  have exactRun := sequenceTarget_continues host first second on world replies
    outcome returned selected
  refine ⟨intermediate, ?_, ?_⟩
  · rw [exactRun]
    rfl
  · intro finalOutcome finalReturn
    rw [exactRun] at finalReturn ⊢
    exact secondConforms _ _ intermediate finalOutcome finalReturn

def continuationEntry (second : Protocol) (previous : Context) : Context :=
  { initial second with irreversible := previous.irreversible }

/-- Carrying irreversibility is necessary even when physical token handoff
has been justified independently. A continuation may not reopen fallback. -/
theorem continued_no_decline {World : Type} {second : Protocol} (previous : Context)
    (effect : previous.irreversible = true)
    (admitted : WellFormed second (continuationEntry second previous) second.body)
    (target : CStmt) (compiled : lower second second.body = some target)
    (host : Host World) (world : World) (replies : List Bool) :
    (evalC host target world replies).status ≠ .returned .declined := by
  exact lower_no_decline_after_effect admitted effect target compiled host world replies

end Mettapedia.GSLT.LanguageDef.ExecutableProtocol
