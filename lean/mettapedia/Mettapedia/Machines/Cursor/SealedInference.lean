import Mettapedia.Languages.MeTTa.Seal.Capability
import Mathlib.Data.List.Forall2

/-!
# Witness-checked inference through the seal operations

The public request supplies premise positions, a rule witness, a conclusion and
a recipient. The kernel fixes its actor, rule interface, brand and private
capability position. It obtains each premise by executing `unsealBox`, in the
supplied order, and tests the actual rule interface before sealing anything.
The successful execution below constructs a run of the original kernel policy;
it does not assume that an unspecified implementation respects that policy.
The mathematical executor's interface, actor, brand and capability slot are
trusted service parameters, never caller fields. The private-constructor
`Session` fixes these parameters and the original configuration across requests.
Reusing a live brand with a caller-chosen rule interface is not this protocol.

This is an authority and inference bridge for the capability calculus. Its
boxes have no fresh capsule identity. There is no representation-independence,
HE/PeTTa execution, native memory-safety or foreign-function security claim.
The intermediate configurations retain the explicit unseal effects.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.SealedInference

open Mettapedia.Logic
open Mettapedia.Languages.MeTTa.Seal

section General

variable {J : Type} {rules : List J → J → Prop}

/-- Caller-supplied data for one inference. The mint capability is not a field
of the request. Premise positions are occurrences, rather than a set. -/
structure Request (interface : RuleWitness rules) where
  premises : List Nat
  witness : interface.W
  conclusion : J
  recipient : Nat

/-- A successful primitive execution and the position delivered to its recipient.
The soundness theorems require an actual successful request; constructing this
ordinary reference record conveys no authority. -/
structure Delivery (J : Type) where
  state : Config J
  position : Nat

/-- Check the capability that this kernel actually holds. This bounded service
uses one private capability with both rights. -/
private def ready (c : Config J) (kernel brand capability : Nat) : Bool :=
  match c.held kernel capability with
  | some (.cap actual rights) => decide (actual = brand ∧ rights = Rights.both)
  | _ => false

private theorem ready_iff (c : Config J) (kernel brand capability : Nat) :
    ready c kernel brand capability = true ↔
      c.held kernel capability = some (.cap brand Rights.both) := by
  unfold ready
  cases found : c.held kernel capability with
  | none => simp
  | some value => cases value <;> simp

/-- Read only the data produced by an actual unseal operation. A box containing
another capsule or a capability is not a judgment premise. -/
private def openPremise (kernel capability index : Nat) (c : Config J) :
    Option (J × Config J) := do
  let next ← (Action.unsealBox capability index).run c kernel
  match next.held kernel (c.holds kernel).length with
  | some (.data judgment) => some (judgment, next)
  | _ => none

private theorem openPremise_output {kernel capability index : Nat}
    {c next : Config J} {judgment : J}
    (opened : openPremise kernel capability index c = some (judgment, next)) :
    (Action.unsealBox capability index).output c kernel =
      some (kernel, .data judgment) ∧
    next = c.give kernel (.data judgment) := by
  cases out : (Action.unsealBox capability index : Action J).output c kernel with
  | none => simp [openPremise, Action.run, out] at opened
  | some result =>
      rcases result with ⟨receiver, value⟩
      obtain ⟨same, _⟩ := Action.output_unseal out
      subst receiver
      cases value <;>
        simp [openPremise, Action.run, out, Action.advance,
          Config.held_give_last] at opened
      obtain ⟨rfl, rfl⟩ := opened
      exact ⟨rfl, rfl⟩

private def openPremises (kernel capability : Nat) :
    List Nat → Config J → Option (List J × Config J)
  | [], c => some ([], c)
  | index :: rest, c => do
      let (judgment, next) ← openPremise kernel capability index c
      let (judgments, final) ← openPremises kernel capability rest next
      some (judgment :: judgments, final)

/-- The positional relation records order and repetition. In particular, two
uses of the same held box remain two inputs to the rule-instance test. -/
private theorem openPremises_sound (kernel brand capability : Nat) :
    ∀ (indices : List Nat) (c final : Config J) (judgments : List J),
      c.held kernel capability = some (.cap brand Rights.both) →
      openPremises kernel capability indices c = some (judgments, final) →
      Reach (kernelPolicy rules kernel brand) c final ∧
      List.Forall₂ (fun index judgment =>
        final.held kernel index = some (.box brand (.data judgment))) indices judgments := by
  intro indices
  induction indices with
  | nil =>
      intro c final judgments _ opened
      simp only [openPremises, Option.some.injEq, Prod.mk.injEq] at opened
      obtain ⟨rfl, rfl⟩ := opened
      exact ⟨Relation.ReflTransGen.refl, .nil⟩
  | cons index rest ih =>
      intro c final judgments capabilityHeld opened
      cases first : openPremise kernel capability index c with
      | none => simp [openPremises, first] at opened
      | some result =>
          rcases result with ⟨judgment, next⟩
          cases later : openPremises kernel capability rest next with
          | none => simp [openPremises, first, later] at opened
          | some result =>
              rcases result with ⟨tail, finish⟩
              simp only [openPremises, first, bind, Option.bind, later,
                Option.some.injEq, Prod.mk.injEq] at opened
              obtain ⟨rfl, rfl⟩ := opened
              obtain ⟨out, rfl⟩ := openPremise_output first
              have step : Step (kernelPolicy rules kernel brand) c
                  (c.give kernel (.data judgment)) :=
                ⟨kernel, .unsealBox capability index, Or.inr trivial,
                  Action.run_of_output out⟩
              have one : Reach (kernelPolicy rules kernel brand) c
                  (c.give kernel (.data judgment)) := .single step
              obtain ⟨run, tailHeld⟩ := ih _ _ _ (one.held_stable capabilityHeld) later
              obtain ⟨_, actualBrand, rights, actualCap, _, box⟩ :=
                Action.output_unseal out
              rw [capabilityHeld] at actualCap
              cases actualCap
              exact ⟨one.trans run, .cons (Reach.held_stable (one.trans run) box) tailHeld⟩

private theorem related_premises_held {kernel brand : Nat} {c : Config J}
    {indices : List Nat} {judgments : List J}
    (related : List.Forall₂ (fun index judgment =>
      c.held kernel index = some (.box brand (.data judgment))) indices judgments) :
    ∀ judgment ∈ judgments, Val.box brand (.data judgment) ∈ c.holds kernel := by
  induction related with
  | nil => simp
  | cons first _ ih =>
      intro judgment member
      rcases List.mem_cons.mp member with rfl | later
      · exact Config.mem_of_held first
      · exact ih judgment later

/-- Only the checked request below calls this private sequence. -/
private def finish (kernel capability recipient : Nat) (c : Config J) (conclusion : J) :
    Option (Delivery J) := do
  let made ← (Action.make conclusion).run c kernel
  let boxed ← (Action.sealBox capability (c.holds kernel).length).run made kernel
  let sent ← (Action.send (made.holds kernel).length recipient).run boxed kernel
  some ⟨sent, (boxed.holds recipient).length⟩

private theorem finish_sound (kernel brand capability recipient : Nat)
    (c : Config J) (premises : List J) (conclusion : J)
    (capabilityHeld : c.held kernel capability = some (.cap brand Rights.both))
    (rule : rules premises conclusion)
    (premisesHeld : ∀ premise ∈ premises,
      Val.box brand (.data premise) ∈ c.holds kernel) :
    ∃ delivery, finish kernel capability recipient c conclusion = some delivery ∧
      Reach (kernelPolicy rules kernel brand) c delivery.state ∧
      delivery.state.held recipient delivery.position = some (.box brand (.data conclusion)) := by
  let made := c.give kernel (.data conclusion)
  have makeOut : (Action.make conclusion : Action J).output c kernel =
      some (kernel, .data conclusion) := rfl
  have makeStep : Step (kernelPolicy rules kernel brand) c made :=
    ⟨kernel, .make conclusion, Or.inr trivial, Action.run_of_output makeOut⟩
  have madeRun : Reach (kernelPolicy rules kernel brand) c made := .single makeStep
  have dataAt : made.held kernel (c.holds kernel).length = some (.data conclusion) :=
    Config.held_give_last c kernel _
  have capabilityAt := madeRun.held_stable capabilityHeld
  have sealOut : (Action.sealBox capability (c.holds kernel).length : Action J).output
      made kernel = some (kernel, .box brand (.data conclusion)) := by
    simp [Action.output, capabilityAt, dataAt, Rights.both]
  let boxed := made.give kernel (.box brand (.data conclusion))
  have sealStep : Step (kernelPolicy rules kernel brand) made boxed := by
    refine ⟨kernel, .sealBox capability (c.holds kernel).length,
      Or.inr ⟨conclusion, premises, dataAt, rule, ?_⟩, Action.run_of_output sealOut⟩
    intro premise member
    exact madeRun.mem_stable (premisesHeld premise member)
  have boxAt : boxed.held kernel (made.holds kernel).length =
      some (.box brand (.data conclusion)) := Config.held_give_last made kernel _
  have sendOut : (Action.send (made.holds kernel).length recipient : Action J).output
      boxed kernel = some (recipient, .box brand (.data conclusion)) := by
    simp [Action.output, boxAt]
  let sent := boxed.give recipient (.box brand (.data conclusion))
  have sendStep : Step (kernelPolicy rules kernel brand) boxed sent := by
    refine ⟨kernel, .send (made.holds kernel).length recipient, Or.inr ?_,
      Action.run_of_output sendOut⟩
    intro value found
    rw [boxAt] at found
    cases found
    simp [Val.hasCap]
  refine ⟨⟨sent, (boxed.holds recipient).length⟩, ?_,
    (madeRun.tail sealStep).tail sendStep, Config.held_give_last boxed recipient _⟩
  simp only [finish, Action.run_of_output makeOut, Action.advance, bind, Option.bind]
  change (do
    let boxed ← (Action.sealBox capability (c.holds kernel).length).run made kernel
    let sent ← (Action.send (made.holds kernel).length recipient).run boxed kernel
    some (⟨sent, (boxed.holds recipient).length⟩ : Delivery J)) = _
  simp only [Action.run_of_output sealOut, Action.advance, bind, Option.bind]
  change (do
    let sent ← (Action.send (made.holds kernel).length recipient).run boxed kernel
    some (⟨sent, (boxed.holds recipient).length⟩ : Delivery J)) = _
  simp only [Action.run_of_output sendOut, Action.advance, bind, Option.bind]
  rfl

/-- The checked-inference executor with trusted service parameters. Every premise is read through an actual
unseal operation. No conclusion is made or sealed before the witness succeeds.
The supported retained request path is `Session.advance`; callers supply only
`Request`, and cannot replace its session's interface or capability position.
Refusal here is absence of a successful execution; no rollback or physical-cost
claim about partially performed unseals is made. -/
def infer (interface : RuleWitness rules) (kernel brand capability : Nat)
    (c : Config J) (request : Request interface) : Option (List J × Delivery J) :=
  if ready c kernel brand capability = true then do
    let (premises, opened) ← openPremises kernel capability request.premises c
    if interface.isInstance request.witness premises request.conclusion = true then do
      let delivery ← finish kernel capability request.recipient opened request.conclusion
      some (premises, delivery)
    else none
  else none

/-- Success derives the original policy execution from the checks performed by
`infer`, and identifies its actual ordered inputs and delivered sealed value. -/
theorem infer_sound (interface : RuleWitness rules) (kernel brand capability : Nat)
    (c : Config J) (request : Request interface) (premises : List J) (delivery : Delivery J)
    (accepted : infer interface kernel brand capability c request = some (premises, delivery)) :
    c.held kernel capability = some (.cap brand Rights.both) ∧
    interface.isInstance request.witness premises request.conclusion = true ∧
    List.Forall₂ (fun index judgment =>
      delivery.state.held kernel index = some (.box brand (.data judgment)))
      request.premises premises ∧
    Reach (kernelPolicy rules kernel brand) c delivery.state ∧
    delivery.state.held request.recipient delivery.position =
      some (.box brand (.data request.conclusion)) := by
  unfold infer at accepted
  split at accepted
  · rename_i checkedCap
    have capabilityHeld := (ready_iff c kernel brand capability).mp checkedCap
    cases opened : openPremises kernel capability request.premises c with
    | none => simp [opened] at accepted
    | some result =>
        rcases result with ⟨actualPremises, middle⟩
        simp only [opened, bind, Option.bind] at accepted
        split at accepted
        · rename_i checkedRule
          obtain ⟨openingRun, originalHeld⟩ :=
            openPremises_sound kernel brand capability request.premises c middle actualPremises
              capabilityHeld opened
          have premisesHeld : ∀ premise ∈ actualPremises,
              Val.box brand (.data premise) ∈ middle.holds kernel :=
            related_premises_held originalHeld
          obtain ⟨actualDelivery, finished, finishingRun, delivered⟩ :=
            finish_sound kernel brand capability request.recipient middle actualPremises
              request.conclusion (openingRun.held_stable capabilityHeld)
              (interface.sound _ _ _ checkedRule) premisesHeld
          simp only [finished, Option.some.injEq, Prod.mk.injEq] at accepted
          obtain ⟨rfl, rfl⟩ := accepted
          refine ⟨capabilityHeld, checkedRule, ?_, openingRun.trans finishingRun, delivered⟩
          exact originalHeld.imp fun _ _ found => finishingRun.held_stable found
        · cases accepted
  · cases accepted

/-- A prior valid policy run can precede a request. The rule/theory predicate,
kernel and brand are exactly those of the original `KernelStart`. -/
theorem infer_derives (interface : RuleWitness rules) {kernel brand capability : Nat}
    {start current : Config J} (initial : KernelStart rules kernel brand start)
    (prior : Reach (kernelPolicy rules kernel brand) start current)
    (request : Request interface) {premises : List J} {delivery : Delivery J}
    (accepted : infer interface kernel brand capability current request = some (premises, delivery)) :
    Derives rules request.conclusion := by
  obtain ⟨_, _, _, run, held⟩ :=
    infer_sound interface kernel brand capability current request premises delivery accepted
  obtain ⟨judgment, equal, derived⟩ :=
    lcf_sound rules initial (prior.trans run) (Config.mem_of_held held)
  cases equal
  exact derived

/-- Previously held premises and capabilities retain their positions through
the successful request, including when the recipient is the kernel itself. -/
theorem infer_preserves_held (interface : RuleWitness rules) {kernel brand capability : Nat}
    {c : Config J} {request : Request interface} {premises : List J} {delivery : Delivery J}
    (accepted : infer interface kernel brand capability c request = some (premises, delivery))
    {principal index : Nat} {value : Val J} (held : c.held principal index = some value) :
    delivery.state.held principal index = some value :=
  (infer_sound interface kernel brand capability c request premises delivery accepted).2.2.2.1.held_stable held

/-- No primitive is started when the kernel lacks the actual matching rights. -/
theorem infer_refuses_without_cap (interface : RuleWitness rules) (kernel brand capability : Nat)
    (c : Config J) (request : Request interface)
    (missing : c.held kernel capability ≠ some (.cap brand Rights.both)) :
    infer interface kernel brand capability c request = none := by
  have notReady : ready c kernel brand capability ≠ true :=
    fun h => missing ((ready_iff c kernel brand capability).mp h)
  simp [infer, notReady]

/-- A rejected rule test cannot produce a successful delivery. This uses the
ordered judgments actually unsealed, rather than caller-supplied payloads. -/
theorem infer_rule_accepted (interface : RuleWitness rules) {kernel brand capability : Nat}
    {c : Config J} {request : Request interface} {premises : List J} {delivery : Delivery J}
    (accepted : infer interface kernel brand capability c request = some (premises, delivery)) :
    rules premises request.conclusion :=
  interface.sound _ _ _
    (infer_sound interface kernel brand capability c request premises delivery accepted).2.1

/-- The original configuration and actual rule interface index this reference
session. Only initialization and a successful checked request construct it.
The invariant proofs are erased; this is not a native unforgeability theorem. -/
structure Session (interface : RuleWitness rules) (kernel brand capability : Nat)
    (original : Config J) where
  private mk ::
  state : Config J
  private initialized : KernelStart rules kernel brand original
  private reached : Reach (kernelPolicy rules kernel brand) original state

namespace Session

/-- Initialize the fixed-profile service from its private start and actual
held capability. `KernelStart` alone does not assert that this slot exists. -/
def begin (interface : RuleWitness rules) (kernel brand capability : Nat)
    (original : Config J) (initial : KernelStart rules kernel brand original) :
    Option (Session interface kernel brand capability original) :=
  if ready original kernel brand capability = true then
    some ⟨original, initial, Relation.ReflTransGen.refl⟩
  else none

/-- Advance only the session's original checker. The returned tuple contains
the ordered checked premises, recipient position and retained session. -/
def advance {interface : RuleWitness rules} {kernel brand capability : Nat}
    {original : Config J} (session : Session interface kernel brand capability original)
    (request : Request interface) :
    Option (List J × Nat × Session interface kernel brand capability original) :=
  match accepted : infer interface kernel brand capability session.state request with
  | none => none
  | some (premises, delivery) =>
      some (premises, delivery.position,
        ⟨delivery.state, session.initialized,
          session.reached.trans
            (infer_sound interface kernel brand capability session.state request
              premises delivery accepted).2.2.2.1⟩)

/-- Every genuine box held in a retained session is sound under the original
rules, without requiring a new theory label or a new validity assumption. -/
theorem original_derives {interface : RuleWitness rules} {kernel brand capability : Nat}
    {original : Config J} (session : Session interface kernel brand capability original)
    {principal : Nat} {judgment : J}
    (held : Val.box brand (.data judgment) ∈ session.state.holds principal) :
    Derives rules judgment := by
  obtain ⟨actual, equal, derived⟩ :=
    lcf_sound rules session.initialized session.reached held
  cases equal
  exact derived

/-- The retained path both performs the actual inference executor and preserves
its delivery, ordered premises and original derivability claim. -/
theorem advance_sound {interface : RuleWitness rules} {kernel brand capability : Nat}
    {original : Config J} (session : Session interface kernel brand capability original)
    (request : Request interface) {premises : List J} {position : Nat}
    {next : Session interface kernel brand capability original}
    (accepted : session.advance request = some (premises, position, next)) :
    next.state.held request.recipient position = some (.box brand (.data request.conclusion)) ∧
    List.Forall₂ (fun index judgment =>
      next.state.held kernel index = some (.box brand (.data judgment))) request.premises premises ∧
    Reach (kernelPolicy rules kernel brand) session.state next.state ∧
    Derives rules request.conclusion := by
  unfold advance at accepted
  split at accepted
  · cases accepted
  · rename_i actualPremises delivery ran
    simp only [Option.some.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl, rfl⟩ := accepted
    obtain ⟨_, _, related, run, delivered⟩ :=
      infer_sound interface kernel brand capability session.state request actualPremises delivery ran
    exact ⟨delivered, related, run,
      infer_derives interface session.initialized session.reached request ran⟩

end Session

end General

namespace Controls

inductive Witness where
  | base
  | repeated
  | ordered
  deriving DecidableEq, Repr

def rules (premises : List Nat) (conclusion : Nat) : Prop :=
  (premises = [] ∧ conclusion = 1) ∨
  (premises = [1, 1] ∧ conclusion = 2) ∨
  (premises = [1, 2] ∧ conclusion = 3)

def interface : RuleWitness rules where
  W := Witness
  isInstance witness premises conclusion := match witness with
    | .base => decide (premises = [] ∧ conclusion = 1)
    | .repeated => decide (premises = [1, 1] ∧ conclusion = 2)
    | .ordered => decide (premises = [1, 2] ∧ conclusion = 3)
  sound := by
    intro witness premises conclusion accepted
    cases witness with
    | base => exact Or.inl (of_decide_eq_true accepted)
    | repeated => exact Or.inr (Or.inl (of_decide_eq_true accepted))
    | ordered => exact Or.inr (Or.inr (of_decide_eq_true accepted))
  complete := by
    intro premises conclusion instanceOf
    rcases instanceOf with first | second | third
    · exact ⟨.base, decide_eq_true first⟩
    · exact ⟨.repeated, decide_eq_true second⟩
    · exact ⟨.ordered, decide_eq_true third⟩

def initial : Config Nat := ⟨fun principal => if principal = 0 then [.cap 0 Rights.both] else [], 1, 0⟩

theorem initial_valid : KernelStart rules 0 0 initial where
  fresh := by decide
  boxes := by
    intro principal value member
    by_cases same : principal = 0
    · subst same
      simp only [initial, ↓reduceIte, List.mem_singleton] at member
      subst value
      trivial
    · simp [initial, same] at member
  othersCannotSeal := by
    intro principal value other member
    simp [initial, other] at member

def baseRequest : Request interface := ⟨[], .base, 1, 0⟩
def repeatedRequest : Request interface := ⟨[2, 2], .repeated, 2, 0⟩
def orderedRequest : Request interface := ⟨[2, 7], .ordered, 3, 1⟩

def first : Option (List Nat × Delivery Nat) := infer interface 0 0 0 initial baseRequest
def second : Option (List Nat × Delivery Nat) := do
  let (_, delivery) ← first
  infer interface 0 0 0 delivery.state repeatedRequest
def third : Option (List Nat × Delivery Nat) := do
  let (_, delivery) ← second
  infer interface 0 0 0 delivery.state orderedRequest

def retainedFirst : Option (List Nat × Nat × Session interface 0 0 0 initial) := do
  let session ← Session.begin interface 0 0 0 initial initial_valid
  session.advance baseRequest

def retainedSecond : Option (List Nat × Nat × Session interface 0 0 0 initial) := do
  let (_, _, session) ← retainedFirst
  session.advance repeatedRequest

def retainedThird : Option (List Nat × Nat × Session interface 0 0 0 initial) := do
  let (_, _, session) ← retainedSecond
  session.advance orderedRequest

def observed (request : Request interface) (result : Option (List Nat × Delivery Nat)) :
    Option (List Nat × Option (Val Nat)) :=
  result.map fun (premises, delivery) =>
    (premises, delivery.state.held request.recipient delivery.position)

theorem nullary_rule_mints : observed baseRequest first = some ([], some (.box 0 (.data 1))) := by decide

theorem repeated_held_premise_survives :
    observed repeatedRequest second = some ([1, 1], some (.box 0 (.data 2))) := by decide

theorem ordered_rule_uses_actual_judgments :
    observed orderedRequest third = some ([1, 2], some (.box 0 (.data 3))) := by decide

theorem retained_original_profile_checks_three_requests :
    retainedThird.map (fun (premises, position, session) =>
      (premises, session.state.held 1 position)) =
      some ([1, 2], some (.box 0 (.data 3))) := by decide

theorem retained_wrong_rule_refused :
    (do let (_, _, session) ← retainedFirst
        session.advance { baseRequest with conclusion := 99 }).isSome = false := by decide

theorem reversed_premises_refused :
    (do let (_, delivery) ← second
        infer interface 0 0 0 delivery.state { orderedRequest with premises := [7, 2] }).isSome = false := by decide

theorem one_premise_is_not_two :
    (do let (_, delivery) ← first
        infer interface 0 0 0 delivery.state { repeatedRequest with premises := [2] }).isSome = false := by decide

theorem forged_same_claim_data_refused :
    (do let (_, delivery) ← first
        infer interface 0 0 0 delivery.state { repeatedRequest with premises := [1, 1] }).isSome = false := by decide

theorem wrong_brand_premise_refused :
    (infer interface 0 0 0 (initial.give 0 (.box 1 (.data 1)))
      { repeatedRequest with premises := [1, 1] }).isSome = false := by decide

theorem absent_premise_refused :
    (infer interface 0 0 0 initial repeatedRequest).isSome = false := by decide

theorem wrong_rule_refused :
    (infer interface 0 0 0 initial { baseRequest with conclusion := 99 }).isSome = false := by decide

theorem wrong_brand_cap_refused :
    (infer interface 0 0 1 (initial.give 0 (.cap 1 Rights.both)) baseRequest).isSome = false := by decide

theorem absent_unseal_right_refused :
    (infer interface 0 0 1 (initial.give 0 (.cap 0 Rights.sealOnly)) baseRequest).isSome = false := by decide

theorem absent_seal_right_refused :
    (infer interface 0 0 1 (initial.give 0 (.cap 0 Rights.unsealOnly)) baseRequest).isSome = false := by decide

theorem absent_capability_refused :
    (infer interface 0 0 7 initial baseRequest).isSome = false := by decide

/-- An intentionally compromised state: the client holds the kernel's sealer.
It is not a `KernelStart` for actor 0. -/
def leaked : Config Nat := initial.give 1 (.cap 0 Rights.both)

theorem forged_claim_not_derivable : ¬ Derives rules 99 := by
  intro derived
  cases derived with
  | node premises _ rule _ => simp [rules] at rule

theorem leaked_cap_does_not_bypass_service_check :
    (infer interface 1 0 0 leaked { baseRequest with conclusion := 99 }).isSome = false := by decide

theorem leaked_cap_enables_raw_forgery :
    (do let made ← (Action.make 99).run leaked 1
        (Action.sealBox 0 1).run made 1).map
        (fun (state : Config Nat) => state.held 1 2) = some (some (.box 0 (.data 99))) := by decide

theorem leaked_is_not_private_start : ¬ KernelStart rules 0 0 leaked := by
  intro start
  have impossible := start.othersCannotSeal 1 (.cap 0 Rights.both) (by decide)
    (Config.mem_of_held (show leaked.held 1 0 = some (.cap 0 Rights.both) by decide))
  exact impossible (by simp [Val.hasCap, Rights.both])

end Controls

end Mettapedia.Machines.Cursor.SealedInference
