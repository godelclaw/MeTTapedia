import Mettapedia.GSLT.Logic.TaskRelativeMemory
import Mettapedia.GSLT.Contracts.AppendAuthority
import Mathlib.Data.Finset.Lattice.Basic

/-!
# Persistent traces of temporary collectives

Reports accumulate idempotently by source identity. Equivocation is retained,
not overwritten: growing knowledge can invalidate an unambiguous-report
readout. Observation reports, model results and scenario-scoped hypotheses
are distinct constructors. Their labels do not certify their truth.

The network carries immutable snapshots. A received snapshot is joined into
local knowledge; it never becomes a permission or a commitment discharge.
The propagation theorem requires fair transport along the declared edges.
It does not assert convergence under partition, starvation or endless input.

The lifecycle motivation is Hakim Bey's temporary and periodic collectives:
https://theanarchistlibrary.org/library/hakim-bey-the-periodic-autonomous-zone
https://theanarchistlibrary.org/library/hakim-bey-t-a-z-the-temporary-autonomous-zone-ontological-anarchy-poetic-terrorism
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.CollectiveAgency.Memory

inductive Content (Fact Model Scenario : Type*) where
  | observation (fact : Fact)
  | modelResult (model : Model) (fact : Fact)
  | hypothesis (scenario : Scenario) (fact : Fact)
  deriving DecidableEq

def Content.value {Fact Model Scenario : Type*} : Content Fact Model Scenario → Fact
  | .observation p | .modelResult _ p | .hypothesis _ p => p

/-- A checked result retains its interpreting model and the semantic proof.
An arbitrary `Content.modelResult` report does not carry this certificate. -/
structure CheckedModelResult {Model Fact : Type*} (holds : Model → Fact → Prop) where
  model : Model
  fact : Fact
  correct : holds model fact

def checkModelResult {Model Fact : Type*} (holds : Model → Fact → Prop) [DecidableRel holds]
    (model : Model) (fact : Fact) : Option (CheckedModelResult holds) :=
  if h : holds model fact then some ⟨model, fact, h⟩ else none

theorem checkModelResult_success {Model Fact : Type*} (holds : Model → Fact → Prop)
    [DecidableRel holds] (model : Model) (fact : Fact) :
    (checkModelResult holds model fact).isSome = true ↔ holds model fact := by
  unfold checkModelResult
  split_ifs <;> simp_all

abbrev Store (Key Payload : Type*) := Finset (Key × Payload)

section Reports
variable {Key Payload : Type*} [DecidableEq Key] [DecidableEq Payload]

def report (s : Store Key Payload) (key : Key) (payload : Payload) : Store Key Payload :=
  insert (key, payload) s

theorem report_idempotent (s : Store Key Payload) (key : Key) (payload : Payload) :
    report (report s key payload) key payload = report s key payload := by
  simp [report]

theorem report_monotone (s : Store Key Payload) (key : Key) (payload : Payload) :
    s ⊆ report s key payload := Finset.subset_insert _ _

theorem reports_commute (s : Store Key Payload) (k l : Key) (p q : Payload) :
    report (report s k p) l q = report (report s l q) k p := by
  simp [report, Finset.insert_comm]

def Unambiguous (s : Store Key Payload) (key : Key) (payload : Payload) : Prop :=
  (key, payload) ∈ s ∧ ∀ other, (key, other) ∈ s → other = payload

theorem conflict_retained (s : Store Key Payload) (key : Key) (p q : Payload) :
    (key, p) ∈ report (report s key p) key q ∧
      (key, q) ∈ report (report s key p) key q := by
  simp [report]

theorem conflicting_not_unambiguous (s : Store Key Payload) (key : Key) (p q : Payload)
    (different : p ≠ q) : ¬ Unambiguous (report (report s key p) key q) key p := by
  intro h
  exact different ((h.2 q (by simp [report])).symm)

theorem report_within_append (s : Store Key Payload) (key : Key) (payload : Payload) :
    (Mettapedia.GSLT.Contracts.AppendAuthority.toClaim
      Mettapedia.GSLT.Contracts.AppendAuthority.Rights.appender).guarantee s (report s key payload) :=
  report_monotone s key payload

end Reports

section Network
variable {Node Data : Type*} [DecidableEq Node] [SemilatticeSup Data]

structure Message (Node Data : Type*) where
  source : Node
  target : Node
  snapshot : Data

structure Network (Node Data : Type*) where
  cache : Node → Data
  sent : List (Message Node Data)

def send (s : Network Node Data) (origin destination : Node) : Network Node Data :=
  { s with sent := s.sent ++ [⟨origin, destination, s.cache origin⟩] }

/-- The receiver joins the supplied payload. Authenticity is the network
delivery contract, not a remote-state oracle inside this handler. -/
def receive (s : Network Node Data) (m : Message Node Data) : Network Node Data :=
  { s with cache := Function.update s.cache m.target (s.cache m.target ⊔ m.snapshot) }

theorem receive_grows (s : Network Node Data) (m : Message Node Data) :
    s.cache ≤ (receive s m).cache := by
  intro node
  by_cases h : node = m.target
  · subst node
    simpa only [receive, Function.update_self] using (le_sup_left : s.cache m.target ≤ s.cache m.target ⊔ m.snapshot)
  · simp only [receive, Function.update_of_ne h]
    exact le_rfl

theorem received_snapshot (s : Network Node Data) (m : Message Node Data) :
    m.snapshot ≤ (receive s m).cache m.target := by
  simpa only [receive, Function.update_self] using (le_sup_right : m.snapshot ≤ s.cache m.target ⊔ m.snapshot)

theorem duplicate_receive (s : Network Node Data) (m : Message Node Data) :
    receive (receive s m) m = receive s m := by
  unfold receive
  congr 1
  funext node
  by_cases h : node = m.target <;> simp [h]

def AuthenticHistory (s : Network Node Data) : Prop :=
  ∀ m ∈ s.sent, m.snapshot ≤ s.cache m.source

omit [DecidableEq Node] in
theorem send_authentic (s : Network Node Data) (origin destination : Node) (before : AuthenticHistory s) :
    AuthenticHistory (send s origin destination) := by
  intro m member
  rcases List.mem_append.mp member with old | fresh
  · exact before m old
  · simp only [List.mem_singleton] at fresh
    subst m
    exact le_rfl

theorem receive_authentic (s : Network Node Data) (m : Message Node Data)
    (before : AuthenticHistory s) : AuthenticHistory (receive s m) :=
  fun old member => (before old member).trans (receive_grows s m old.source)

inductive Step : Network Node Data → Network Node Data → Prop where
  | send (s : Network Node Data) (origin destination : Node) : Step s (send s origin destination)
  | receive (s : Network Node Data) (m : Message Node Data) :
      m ∈ s.sent → Step s (receive s m)

theorem step_grows {s t : Network Node Data} (move : Step s t) : s.cache ≤ t.cache := by
  cases move with
  | send => exact le_rfl
  | receive => exact receive_grows _ _

theorem reached_grows {s t : Network Node Data} (trace : Relation.ReflTransGen Step s t) :
    s.cache ≤ t.cache := by
  induction trace with
  | refl => exact le_rfl
  | tail _ move ih => exact ih.trans (step_grows move)

theorem reached_authentic {s t : Network Node Data} (before : AuthenticHistory s)
    (trace : Relation.ReflTransGen Step s t) : AuthenticHistory t := by
  induction trace with
  | refl => exact before
  | tail _ move ih =>
    cases move with
    | send => exact send_authentic _ _ _ ih
    | receive => exact receive_authentic _ _ ih

end Network

section Fairness
variable {Node Data : Type*} [Preorder Data]

/-- Every declared edge eventually transports each available knowledge
snapshot. Scheduling must supply this premise; mere graph connectivity cannot. -/
def FairTransport (states : Nat → Node → Data) (edge : Node → Node → Prop) : Prop :=
  ∀ a b, edge a b → ∀ t, ∃ u, t ≤ u ∧ states t a ≤ states u b

theorem eventually_along_path (states : Nat → Node → Data) (edge : Node → Node → Prop)
    (fair : FairTransport states edge) {a b : Node}
    (path : Relation.ReflTransGen edge a b) (t : Nat) :
    ∃ u, t ≤ u ∧ states t a ≤ states u b := by
  induction path with
  | refl => exact ⟨t, le_rfl, le_rfl⟩
  | tail _ link ih =>
    obtain ⟨u, tu, transported⟩ := ih
    obtain ⟨v, uv, next⟩ := fair _ _ link u
    exact ⟨v, tu.trans uv, transported.trans next⟩

end Fairness

section TaskMemory
open Mettapedia.GSLT.TaskRelativeMemory
variable {State Input Query Readout : Type*} {Result : Query → Type*}
  (step : State → Input → State) (observe : (q : Query) → State → Result q)
  {memory : State → Readout}

/-- Persistent recipes support renewed execution only for the promised tests. -/
theorem renewed_execution (realization : Realization step observe memory)
    (s : State) (word : List Input) (q : Query) :
    realization.read q (word.foldl realization.update (memory s)) =
      observe q (word.foldl step s) := by
  rw [realization.foldl_agrees, realization.read_agrees]

end TaskMemory

namespace Controls

theorem ambiguity_readout_not_monotone :
    Unambiguous ({(0, false)} : Store Nat Bool) 0 false ∧
    ({(0, false)} : Store Nat Bool) ⊆ {(0, false), (0, true)} ∧
    ¬ Unambiguous ({(0, false), (0, true)} : Store Nat Bool) 0 false := by
  constructor
  · simp [Unambiguous]
  constructor
  · decide
  · intro h
    have := h.2 true (by decide)
    cases this

theorem scope_erasure_loses_distinction :
    (Content.observation true : Content Bool Unit Nat).value =
      (Content.hypothesis 7 true : Content Bool Unit Nat).value ∧
    (Content.observation true : Content Bool Unit Nat) ≠ Content.hypothesis 7 true := by decide

theorem model_relative_is_not_actual :
    (checkModelResult (Eq : Bool → Bool → Prop) true true).isSome = true ∧
    ¬ (Eq : Bool → Bool → Prop) false true := by decide

def partitioned (_ : Nat) (node : Bool) : Finset Nat := if node then ∅ else {0}

theorem connected_but_starved :
    ¬ FairTransport partitioned (fun (a b : Bool) => a = false ∧ b = true) := by
  intro fair
  obtain ⟨_, _, h⟩ := fair false true ⟨rfl, rfl⟩ 0
  have := h (by decide : 0 ∈ partitioned 0 false)
  simp [partitioned] at this

theorem expanded_queries_need_refresh :
    (∃ read : Bool → Bool, ∀ s : Bool × Bool, read s.1 = s.1) ∧
    ¬ ∃ read : Bool → Bool, ∀ s : Bool × Bool, read s.1 = s.2 := by
  refine ⟨⟨id, fun _ => rfl⟩, ?_⟩
  rintro ⟨read, agrees⟩
  have a := agrees (false, false)
  have b := agrees (false, true)
  exact Bool.false_ne_true (a.symm.trans b)

end Controls

end Mettapedia.CognitiveArchitecture.CollectiveAgency.Memory
