import Mettapedia.GSLT.Causality.EventConcurrency
import Mettapedia.GSLT.Dynamics.InteractionEventValuation
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Tactic.Abel

/-!
# Interaction on a bag of resources: linear consumption and persistent reads

A rule instance consumes a bag of resources, reads a second bag without
consuming it, and adds a third. Rho's communication consumes an output and an
input. An equation in a MeTTa space is read by every call it answers, and the
call is consumed. The calculi differ in which resources are linear.

Two firings are concurrent when their consumptions fit together, each beside
the other's reads. Concurrent firings commute. A resource present once and
consumed by both firings puts them in conflict: after either, the other is
disabled. A read resource is shared, so firings that read it in common are
concurrent.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Causality.OccurrenceHistory
open Mettapedia.GSLT.Causality.EventConcurrency

universe uRes uRule uEvent

/-- Rule instances over resources `R`: each consumes, reads and produces a bag. -/
structure System (R : Type uRes) where
  Site : Type uRule
  Instance : Site → Type uRule
  consume : ∀ {site : Site}, Instance site → Multiset R
  read : ∀ {site : Site}, Instance site → Multiset R
  produce : ∀ {site : Site}, Instance site → Multiset R

namespace System

variable {R : Type uRes} (S : System.{uRes, uRule} R)

/-- An instance is enabled when its consumption and its reads are both present. -/
def Enables (M : Multiset R) {site : S.Site} (i : S.Instance site) : Prop :=
  S.consume i + S.read i ≤ M

/-- Both consumptions fit together in the bag, each beside either read. -/
def Concurrent (M : Multiset R) {site₁ site₂ : S.Site} (i : S.Instance site₁)
    (j : S.Instance site₂) : Prop :=
  S.consume i + S.consume j + S.read i ≤ M ∧ S.consume i + S.consume j + S.read j ≤ M

theorem concurrent_symm {M : Multiset R} {site₁ site₂ : S.Site} {i : S.Instance site₁}
    {j : S.Instance site₂} (h : S.Concurrent M i j) : S.Concurrent M j i := by
  obtain ⟨hi, hj⟩ := h
  refine ⟨?_, ?_⟩
  · rw [add_comm (S.consume j)]
    exact hj
  · rw [add_comm (S.consume j)]
    exact hi

/-- **A read resource is shared.** Instances whose consumptions fit together
beside one bag of reads are concurrent, however much of it they both read. -/
theorem concurrent_of_shared_read (M : Multiset R) {site₁ site₂ : S.Site}
    (i : S.Instance site₁) (j : S.Instance site₂) (reads : Multiset R)
    (readI : S.read i ≤ reads) (readJ : S.read j ≤ reads)
    (fits : S.consume i + S.consume j + reads ≤ M) : S.Concurrent M i j :=
  ⟨le_trans (add_le_add le_rfl readI) fits, le_trans (add_le_add le_rfl readJ) fits⟩

variable [DecidableEq R]

/-- Firing removes the consumption and adds the production; reads remain. -/
def fire (M : Multiset R) {site : S.Site} (i : S.Instance site) : Multiset R :=
  M - S.consume i + S.produce i

/-- The rewrite theory of a resource system: configurations are bags. -/
def theory : GSLT where
  Term := Multiset R
  equations := ⟨Eq, eq_equivalence⟩
  rewrites := fun M N => ∃ site, ∃ i : S.Instance site, S.Enables M i ∧ N = S.fire M i
  rewrites_resp_left := by
    intro M M' N equal step
    exact ⟨N, equal ▸ step, rfl⟩
  rewrites_resp_right := by
    intro M N N' step equal
    exact equal ▸ step

/-- Events are enabled instances, one site per rule. -/
def presentation : InteractionPresentation S.theory where
  Site := S.Site
  Event := fun site M N => {i : S.Instance site // S.Enables M i ∧ N = S.fire M i}
  sound := fun {site} _ _ event => ⟨site, event.val, event.property.1, event.property.2⟩

/-- The instance an enabled event fires. -/
def inst {M : Multiset R} (e : S.presentation.Enabled M) : S.Instance e.site :=
  e.evidence.val

theorem enables_inst {M : Multiset R} (e : S.presentation.Enabled M) :
    S.Enables M (S.inst e) :=
  e.evidence.property.1

theorem target_inst {M : Multiset R} (e : S.presentation.Enabled M) :
    e.target = S.fire M (S.inst e) :=
  e.evidence.property.2

/-- The event firing an enabled instance. -/
def event (M : Multiset R) {site : S.Site} (i : S.Instance site) (enabled : S.Enables M i) :
    S.presentation.Enabled M where
  site := site
  target := S.fire M i
  evidence := ⟨i, enabled, rfl⟩

/-! ## Concurrency -/

/-- After one of two concurrent instances fires, the other is still enabled. -/
theorem enables_fire {M : Multiset R} {site₁ site₂ : S.Site} {i : S.Instance site₁}
    {j : S.Instance site₂} (h : S.Concurrent M i j) : S.Enables (S.fire M i) j := by
  have fits : S.consume j + S.read j ≤ M - S.consume i := by
    apply le_tsub_of_add_le_left
    rw [← add_assoc]
    exact h.2
  exact le_trans fits (Multiset.le_add_right _ _)

/-- Firing two concurrent instances in either order reaches one bag. -/
theorem fire_comm {M : Multiset R} {site₁ site₂ : S.Site} {i : S.Instance site₁}
    {j : S.Instance site₂} (h : S.Concurrent M i j) :
    S.fire (S.fire M i) j = S.fire (S.fire M j) i := by
  have both : S.consume i + S.consume j ≤ M :=
    le_trans (Multiset.le_add_right _ _) h.1
  have ji : S.consume j ≤ M - S.consume i := le_tsub_of_add_le_left both
  have ij : S.consume i ≤ M - S.consume j := by
    apply le_tsub_of_add_le_left
    rw [add_comm]
    exact both
  unfold fire
  rw [← tsub_add_eq_add_tsub ji, ← tsub_add_eq_add_tsub ij, tsub_tsub, tsub_tsub,
    add_comm (S.consume j) (S.consume i)]
  exact add_right_comm _ _ _

/-- **Concurrent firings are independent events.** The residual of either is the
same instance, and the two orders meet. -/
def concurrency : Concurrency S.presentation where
  Independent := fun {M} a b => S.Concurrent M (S.inst a) (S.inst b)
  symm := fun h => S.concurrent_symm h
  residual := fun {_} {a} {b} h =>
    S.event a.target (S.inst b) (by rw [S.target_inst a]; exact S.enables_fire h)
  residual_site := fun _ => rfl
  close := by
    intro M a b h
    change S.fire a.target (S.inst b) = S.fire b.target (S.inst a)
    rw [S.target_inst a, S.target_inst b]
    exact S.fire_comm h

/-! ## Conflict and sharing -/

/-- **A linear resource present once is a conflict.** Two instances that both
consume it are not concurrent. -/
theorem not_concurrent_of_shared_consumption (M : Multiset R) {site₁ site₂ : S.Site}
    (i : S.Instance site₁) (j : S.Instance site₂) (r : R) (inI : r ∈ S.consume i)
    (inJ : r ∈ S.consume j) (once : M.count r ≤ 1) : ¬ S.Concurrent M i j := by
  intro h
  have fits := Multiset.count_le_of_le r (le_trans (Multiset.le_add_right _ _) h.1)
  rw [Multiset.count_add] at fits
  have countI := Multiset.count_pos.mpr inI
  have countJ := Multiset.count_pos.mpr inJ
  omega

/-- **After either conflicting firing, the other is disabled**, unless the first
puts the resource back. -/
theorem disabled_after (M : Multiset R) {site₁ site₂ : S.Site} (i : S.Instance site₁)
    (j : S.Instance site₂) (r : R) (inI : r ∈ S.consume i) (inJ : r ∈ S.consume j)
    (once : M.count r ≤ 1) (notBack : r ∉ S.produce i) :
    ¬ S.Enables (S.fire M i) j := by
  intro h
  have fits := Multiset.count_le_of_le r (le_trans (Multiset.le_add_right _ _) h)
  rw [fire, Multiset.count_add, Multiset.count_sub, Multiset.count_eq_zero.mpr notBack]
    at fits
  have countI := Multiset.count_pos.mpr inI
  have countJ := Multiset.count_pos.mpr inJ
  omega

end System

/-! ## Controls: a rho receiver and a MeTTa space

A rho input is consumed by the message it takes. Two messages on one channel,
with one input, are in conflict: a run takes one of them. A replicated input
is read instead, and both messages are taken.

An equation of a MeTTa space is read by the call it answers, and the call is
consumed. Two equations for one call are conflicting alternatives: each run
takes one, and an all-answer search collects both. Two calls answered by one
equation are concurrent: they are two firings of one rule instance. -/

/-! ## Algebra-first linear effects -/

/-- Exact linear effect of one occurrence.  `site` classifies the interaction;
the resource multisets govern concurrent ownership. -/
structure LinearEffect (Site : Type uRule) (Resource : Type uRes) where
  site : Site
  consumed : Multiset Resource
  produced : Multiset Resource

/-- Proof-relevant common-source decomposition of two linear effects. -/
structure PairSeparation {Site : Type uRule} {Resource : Type uRes}
    (source : Multiset Resource)
    (left right : LinearEffect Site Resource) : Type uRes where
  frame : Multiset Resource
  source_eq : source = left.consumed + right.consumed + frame

namespace PairSeparation

variable {Site : Type uRule} {Resource : Type uRes} [DecidableEq Resource]
variable {source : Multiset Resource}
variable {left right : LinearEffect Site Resource}

/-- The exact demand placed on the common source. -/
def demand (_source : Multiset Resource)
    (left right : LinearEffect Site Resource) : Multiset Resource :=
  left.consumed + right.consumed

/-- Construct the canonical remainder from a successful linear-resource
check. -/
def of_le (funded : demand source left right ≤ source) :
    PairSeparation source left right where
  frame := source - demand source left right
  source_eq := by
    rw [add_comm]
    exact (Multiset.sub_add_cancel funded).symm

/-- Executable pair analysis.  There is no fallback meaning for a failed
resource check. -/
def analyze? (source : Multiset Resource)
    (left right : LinearEffect Site Resource) :
    Option (PairSeparation source left right) :=
  if funded : demand source left right ≤ source then
    some (of_le funded)
  else
    none

/-- Analysis succeeds exactly when the combined linear demand fits the
source. -/
theorem analyze?_isSome_iff :
    (analyze? source left right).isSome = true ↔
      demand source left right ≤ source := by
  by_cases funded : demand source left right ≤ source
  · simp [analyze?, funded]
  · simp [analyze?, funded]

/-- A supplied separation certificate is never rejected by the executable
analysis. -/
theorem analyze?_complete
    (separation : PairSeparation source left right) :
    (analyze? source left right).isSome = true := by
  rw [analyze?_isSome_iff]
  apply Multiset.le_iff_exists_add.mpr
  exact ⟨separation.frame, separation.source_eq⟩

/-- A successful result exposes its exact common-source equation. -/
theorem source_eq_of_analyze?_eq_some
    {separation : PairSeparation source left right}
    (_result : analyze? source left right = some separation) :
    source = left.consumed + right.consumed + separation.frame :=
  separation.source_eq

end PairSeparation

/-! ## Exact occurrence analyses -/

/-- An occurrence-effect analysis assigns exact linear effects to the
proof-relevant occurrences of one interaction presentation. -/
structure OccurrenceEffectAnalysis {theory : GSLT}
    (presentation : InteractionPresentation.{uRule, uEvent} theory)
    (Resource : Type uRes) where
  effect : Mettapedia.GSLT.Dynamics.InteractionEventValuation.Occurrence presentation → LinearEffect presentation.Site Resource

namespace OccurrenceEffectAnalysis

variable {theory : GSLT}
variable {presentation : InteractionPresentation.{uRule, uEvent} theory}
variable {Resource : Type uRes} [DecidableEq Resource]

/-- Analyze two exact occurrences against one resource inventory. -/
def separate? (analysis : OccurrenceEffectAnalysis presentation Resource)
    (source : Multiset Resource)
    (left right : Mettapedia.GSLT.Dynamics.InteractionEventValuation.Occurrence presentation) :
    Option (PairSeparation source (analysis.effect left)
      (analysis.effect right)) :=
  PairSeparation.analyze? source (analysis.effect left)
    (analysis.effect right)

end OccurrenceEffectAnalysis


/-- Forget persistent reads explicitly when projecting a resource firing to
its consumed and produced linear effects. -/
def System.linearEffect {R : Type uRes} (system : System.{uRes, uRule} R)
    {site : system.Site} (firing : system.Instance site) :
    LinearEffect system.Site R where
  site := site
  consumed := system.consume firing
  produced := system.produce firing

/-- Exact linear pair decomposition is precisely the submultiset condition;
the proof-relevant certificate also retains the untouched frame. -/
theorem PairSeparation.nonempty_iff {Site : Type uRule} {R : Type uRes}
    {source : Multiset R} {left right : LinearEffect Site R} :
    Nonempty (PairSeparation source left right) ↔
      left.consumed + right.consumed ≤ source := by
  constructor
  · rintro ⟨separation⟩
    exact Multiset.le_iff_exists_add.mpr ⟨separation.frame, separation.source_eq⟩
  · intro fits
    obtain ⟨frame, equal⟩ := Multiset.le_iff_exists_add.mp fits
    exact ⟨⟨frame, equal⟩⟩

/-- The linear separation check agrees exactly with the existing concurrency
judgment for firings with no persistent reads. -/
theorem System.pairSeparation_iff_concurrent {R : Type uRes}
    (system : System.{uRes, uRule} R) (source : Multiset R)
    {leftSite rightSite : system.Site}
    (left : system.Instance leftSite) (right : system.Instance rightSite)
    (leftRead : system.read left = 0) (rightRead : system.read right = 0) :
    Nonempty (PairSeparation source (system.linearEffect left)
      (system.linearEffect right)) ↔ system.Concurrent source left right := by
  rw [PairSeparation.nonempty_iff]
  simp only [System.linearEffect, System.Concurrent, leftRead, rightRead,
    add_zero, and_self]


namespace Controls

/-- Messages on one channel, a receiver, and received values. -/
inductive Res where
  | message (value : ℕ)
  | receiver
  | received (value : ℕ)
  deriving DecidableEq

/-- An input consumed by the message it takes. -/
def linearReceiver : System Res where
  Site := Unit
  Instance := fun _ => ℕ
  consume := fun value => {Res.message value, Res.receiver}
  read := fun _ => 0
  produce := fun value => {Res.received value}

/-- A replicated input: read by every message it takes. -/
def persistentReceiver : System Res where
  Site := Unit
  Instance := fun _ => ℕ
  consume := fun value => {Res.message value}
  read := fun _ => {Res.receiver}
  produce := fun value => {Res.received value}

/-- Two messages and one receiver. -/
def twoMessages : Multiset Res := {Res.message 1, Res.message 2, Res.receiver}

/-- Taking message `value`. -/
def take (value : ℕ) : linearReceiver.Instance () := value

/-- Taking message `value` with the replicated input. -/
def takeAgain (value : ℕ) : persistentReceiver.Instance () := value

/-- **One input, two messages: a conflict.** -/
theorem linear_receiver_conflict : ¬ linearReceiver.Concurrent twoMessages (take 1) (take 2) :=
  linearReceiver.not_concurrent_of_shared_consumption twoMessages (take 1) (take 2) Res.receiver
    (by decide) (by decide) (by decide)

/-- **After one message is taken, the other cannot be.** -/
theorem linear_receiver_takes_one :
    linearReceiver.Enables twoMessages (take 1) ∧
      ¬ linearReceiver.Enables (linearReceiver.fire twoMessages (take 1)) (take 2) :=
  ⟨by unfold System.Enables; decide,
    linearReceiver.disabled_after twoMessages (take 1) (take 2) Res.receiver
      (by decide) (by decide) (by decide) (by decide)⟩

/-- **A replicated input takes both messages, in either order.** -/
theorem persistent_receiver_concurrent :
    persistentReceiver.Concurrent twoMessages (takeAgain 1) (takeAgain 2) :=
  persistentReceiver.concurrent_of_shared_read twoMessages (takeAgain 1) (takeAgain 2)
    {Res.receiver} le_rfl le_rfl (by decide)

/-- Calls, equations and answers of a space. -/
inductive SpaceRes where
  | call
  | equation (index : ℕ)
  | answer (index : ℕ)
  deriving DecidableEq

/-- Equation `index` answers the call. The equation is read; the call is
consumed. -/
def space : System SpaceRes where
  Site := Unit
  Instance := fun _ => ℕ
  consume := fun _ => {SpaceRes.call}
  read := fun index => {SpaceRes.equation index}
  produce := fun index => {SpaceRes.answer index}

/-- Answer the call by equation `index`. -/
def answerBy (index : ℕ) : space.Instance () := index

/-- One call and two equations for it. -/
def oneCallTwoEquations : Multiset SpaceRes :=
  {SpaceRes.call, SpaceRes.equation 1, SpaceRes.equation 2}

/-- Two calls and one equation. -/
def twoCallsOneEquation : Multiset SpaceRes :=
  {SpaceRes.call, SpaceRes.call, SpaceRes.equation 1}

/-- **Two equations for one call are alternatives.** Each run answers by one;
the other is then disabled. -/
theorem equations_are_alternatives :
    ¬ space.Concurrent oneCallTwoEquations (answerBy 1) (answerBy 2) ∧
      ¬ space.Enables (space.fire oneCallTwoEquations (answerBy 1)) (answerBy 2) :=
  ⟨space.not_concurrent_of_shared_consumption oneCallTwoEquations (answerBy 1) (answerBy 2)
      SpaceRes.call (by decide) (by decide) (by decide),
    space.disabled_after oneCallTwoEquations (answerBy 1) (answerBy 2) SpaceRes.call
      (by decide) (by decide) (by decide) (by decide)⟩

/-- **Two calls share one equation.** The same rule instance fires twice,
concurrently. -/
theorem calls_share_equation :
    space.Concurrent twoCallsOneEquation (answerBy 1) (answerBy 1) :=
  space.concurrent_of_shared_read twoCallsOneEquation (answerBy 1) (answerBy 1)
    {SpaceRes.equation 1} le_rfl le_rfl (by decide)

/-- The two answers of the shared equation are one trace. -/
def sharedPair : space.concurrency.Pair twoCallsOneEquation where
  first := space.event twoCallsOneEquation (answerBy 1) (by unfold System.Enables; decide)
  second := space.event twoCallsOneEquation (answerBy 1) (by unfold System.Enables; decide)
  independent := calls_share_equation

theorem shared_answers_commute :
    Trace.mk (T := space.concurrency.tiles) (sharedPair.route space.concurrency) =
      Trace.mk (sharedPair.swapped space.concurrency) :=
  Trace.mk_sound (.tile (T := space.concurrency.tiles) sharedPair)

/-- With two actual linear receivers the shared separation theorem licenses
both firings; neither receiver occurrence is contracted. -/
theorem two_linear_receivers_are_separated :
    linearReceiver.Concurrent (twoMessages + {Res.receiver}) (take 1) (take 2) := by
  apply (linearReceiver.pairSeparation_iff_concurrent
    (twoMessages + {Res.receiver}) (take 1) (take 2) rfl rfl).mp
  exact PairSeparation.nonempty_iff.mpr (by decide)

/-- Consumption-only separation cannot replace a shared-read requirement:
the messages fit, but their persistent receiver is absent. -/
theorem consumption_separation_does_not_supply_reads :
    Nonempty (PairSeparation ({Res.message 1, Res.message 2} : Multiset Res)
      (persistentReceiver.linearEffect (takeAgain 1))
      (persistentReceiver.linearEffect (takeAgain 2))) ∧
      ¬ persistentReceiver.Concurrent {Res.message 1, Res.message 2}
        (takeAgain 1) (takeAgain 2) := by
  constructor
  · exact PairSeparation.nonempty_iff.mpr (by decide)
  · unfold System.Concurrent persistentReceiver takeAgain
    decide


end Controls

#print axioms System.fire_comm
#print axioms System.not_concurrent_of_shared_consumption
#print axioms System.disabled_after
#print axioms Controls.linear_receiver_takes_one
#print axioms Controls.persistent_receiver_concurrent
#print axioms Controls.equations_are_alternatives
#print axioms Controls.shared_answers_commute

end Mettapedia.GSLT.Causality.ResourceInteraction
