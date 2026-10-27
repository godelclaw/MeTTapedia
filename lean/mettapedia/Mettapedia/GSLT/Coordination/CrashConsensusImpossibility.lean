import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

/-!
# No deterministic consensus in an asynchronous system with one crash

The theorem of Fischer, Lynch and Paterson, *Impossibility of distributed consensus with one
faulty process* (J. ACM 1985), in the form of the textbooks (Lynch, *Distributed Algorithms*;
Attiya and Welch, *Distributed Computing*).

## The model

`n` deterministic processes. In one step a process receives one message, or nothing, changes its
state and sends finitely many messages (`Protocol.step`). Messages wait in a buffer until they
are delivered, in any order and after any delay. The network tags each message with its sender
and the sender's step number (`Envelope`), so that equal messages sent twice are two envelopes;
the tags are invisible to the receiver. A process's output is written once (`output_stable`).

**Fault model.** Asynchrony: no bound on delays or relative speeds. At most one process crashes:
from some point on it takes no steps.

## What is ruled out

A protocol solves consensus (`TotallyCorrect`) when
* **agreement**: no reachable configuration has two processes with different outputs;
* **non-triviality**: each value is the output in some reachable configuration;
* **termination**: in every fair run, some process decides; and in every fair run in which one
  process crashes at a reachable configuration, some other process decides.

A run is fair when every process that does not crash takes infinitely many steps and every
envelope addressed to such a process is eventually delivered. Runs are given block by block
(`BlockRun`); concatenating the blocks gives the usual infinite sequence of events.

* **No protocol solves consensus** (`not_totallyCorrect`).

Termination after a crash asks that a process other than the crashed one decide, as in the
textbook statements. The original theorem also rules out the weaker requirement that some
process, possibly the crashed one, has decided; that strengthening is not proved here.

Without crashes the problem is easy: a protocol in which one process outputs its input at once
has agreement, non-triviality and termination in every fair run (`Controls.crashFree_consensus`),
and therefore fails termination after a crash (`Controls.leaderDecides_crash_fails`).

## The proof

* Events of different processes commute (`apply_comm`), and so do schedules of different processes
  (`run_comm`).
* Some initial configuration is **bivalent**: both outputs are still reachable
  (`exists_bivalent_initial`).
* From a bivalent configuration, any applicable event can be postponed so that applying it leads
  to a bivalent configuration (`bivalent_after_event`).
* Round by round, each process receives every envelope waiting for it and takes a step, through
  bivalent configurations only (`stage`). The run so built is fair, and no process ever decides in
  it (`fair_run_never_decides`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.CrashConsensusImpossibility

universe u v

variable {n : ℕ} {S : Type u} {M : Type v}

/-- A deterministic protocol: initial states by input, one step on a message or on nothing, and a
write-once output. -/
structure Protocol (n : ℕ) (S : Type u) (M : Type v) where
  init : Fin n → Bool → S
  step : Fin n → S → Option M → S × List (Fin n × M)
  output : S → Option Bool
  output_stable : ∀ p s m value, output s = some value → output (step p s m).1 = some value

/-- A message in transit, tagged by the network with its sender, the sender's step number and its
position among that step's messages. -/
structure Envelope (n : ℕ) (M : Type v) where
  dest : Fin n
  content : M
  sender : Fin n
  seq : ℕ
  index : ℕ
  deriving DecidableEq

/-- A configuration: states, step counts, and the envelopes in transit. -/
@[ext]
structure Config (n : ℕ) (S : Type u) (M : Type v) where
  state : Fin n → S
  count : Fin n → ℕ
  buffer : Finset (Envelope n M)

/-- An event: deliver an envelope to its destination, or let a process step on nothing. -/
inductive Event (n : ℕ) (M : Type v) where
  | deliver (env : Envelope n M)
  | null (p : Fin n)
  deriving DecidableEq

namespace Event

/-- The process that takes the step. -/
def proc : Event n M → Fin n
  | deliver env => env.dest
  | null p => p

/-- What the process receives. -/
def received : Event n M → Option M
  | deliver env => some env.content
  | null _ => none

end Event

variable [DecidableEq M]

/-- Tag the messages of one step. -/
def stamp (sender : Fin n) (seq : ℕ) : ℕ → List (Fin n × M) → List (Envelope n M)
  | _, [] => []
  | i, (dest, content) :: rest => ⟨dest, content, sender, seq, i⟩ :: stamp sender seq (i + 1) rest

omit [DecidableEq M] in
theorem mem_stamp {sender : Fin n} {seq i : ℕ} {sent : List (Fin n × M)} {env : Envelope n M}
    (member : env ∈ stamp sender seq i sent) : env.sender = sender ∧ env.seq = seq := by
  induction sent generalizing i with
  | nil => simp [stamp] at member
  | cons head rest ih =>
      obtain ⟨dest, content⟩ := head
      simp only [stamp, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨rfl, rfl⟩
      · exact ih member

/-- An event is applicable when its envelope is in transit; a step on nothing always is. -/
def Applicable (C : Config n S M) : Event n M → Prop
  | .deliver env => env ∈ C.buffer
  | .null _ => True

instance (C : Config n S M) (e : Event n M) : Decidable (Applicable C e) := by
  cases e <;> unfold Applicable <;> infer_instance

/-- Remove the delivered envelope. -/
def Event.drop (buffer : Finset (Envelope n M)) : Event n M → Finset (Envelope n M)
  | .deliver env => buffer.erase env
  | .null _ => buffer

variable (P : Protocol n S M)

/-- The step of the process that takes the event. -/
def result (C : Config n S M) (e : Event n M) : S × List (Fin n × M) :=
  P.step e.proc (C.state e.proc) e.received

/-- The envelopes an event sends. -/
def sent (C : Config n S M) (e : Event n M) : Finset (Envelope n M) :=
  (stamp e.proc (C.count e.proc) 0 (result P C e).2).toFinset

/-- Apply an event. -/
def apply (C : Config n S M) (e : Event n M) : Config n S M where
  state := Function.update C.state e.proc (result P C e).1
  count := Function.update C.count e.proc (C.count e.proc + 1)
  buffer := e.drop C.buffer ∪ sent P C e

/-- Run a schedule. -/
def run (C : Config n S M) : List (Event n M) → Config n S M
  | [] => C
  | e :: es => run (apply P C e) es

/-- A schedule is applicable when each event is applicable when it comes. -/
def Runs (C : Config n S M) : List (Event n M) → Prop
  | [] => True
  | e :: es => Applicable C e ∧ Runs (apply P C e) es

/-- Every envelope in transit carries a step number its sender has passed. -/
def WellFormed (C : Config n S M) : Prop := ∀ env ∈ C.buffer, env.seq < C.count env.sender

variable {P}

theorem mem_sent {C : Config n S M} {e : Event n M} {env : Envelope n M} (member : env ∈ sent P C e) :
    env.sender = e.proc ∧ env.seq = C.count e.proc :=
  mem_stamp (List.mem_toFinset.mp member)

/-- What an event sends is new. -/
theorem sent_fresh {C : Config n S M} (wf : WellFormed C) (e : Event n M) {env : Envelope n M}
    (member : env ∈ sent P C e) : env ∉ C.buffer := fun inBuffer => by
  have := wf env inBuffer
  obtain ⟨sender, seq⟩ := mem_sent member
  rw [sender, seq] at this
  omega

theorem wellFormed_apply {C : Config n S M} (wf : WellFormed C) (e : Event n M) :
    WellFormed (apply P C e) := by
  intro env member
  simp only [apply] at member ⊢
  rcases Finset.mem_union.mp member with old | new
  · have inBuffer : env ∈ C.buffer := by
      cases e with
      | deliver d => exact Finset.mem_of_mem_erase old
      | null _ => exact old
    have := wf env inBuffer
    by_cases same : env.sender = e.proc
    · rw [same, Function.update_self]; rw [same] at this; omega
    · rw [Function.update_of_ne same]; exact this
  · obtain ⟨sender, seq⟩ := mem_sent new
    rw [sender, Function.update_self, seq]
    omega

theorem wellFormed_run {C : Config n S M} (wf : WellFormed C) (σ : List (Event n M)) :
    WellFormed (run P C σ) := by
  induction σ generalizing C with
  | nil => exact wf
  | cons e rest ih => exact ih (wellFormed_apply wf e)

theorem run_append (C : Config n S M) (first second : List (Event n M)) :
    run P C (first ++ second) = run P (run P C first) second := by
  induction first generalizing C with
  | nil => rfl
  | cons e rest ih => exact ih _

theorem runs_append {C : Config n S M} {first second : List (Event n M)} :
    Runs P C (first ++ second) ↔ Runs P C first ∧ Runs P (run P C first) second := by
  induction first generalizing C with
  | nil => simp [Runs, run]
  | cons e rest ih => simp only [List.cons_append, Runs, ih, run, and_assoc]

/-! ## Events of different processes commute -/

theorem apply_state (C : Config n S M) (e : Event n M) :
    (apply P C e).state = Function.update C.state e.proc (result P C e).1 := rfl

theorem apply_count (C : Config n S M) (e : Event n M) :
    (apply P C e).count = Function.update C.count e.proc (C.count e.proc + 1) := rfl

theorem apply_buffer (C : Config n S M) (e : Event n M) :
    (apply P C e).buffer = e.drop C.buffer ∪ sent P C e := rfl

theorem result_apply_other {C : Config n S M} {e e' : Event n M} (apart : e.proc ≠ e'.proc) :
    result P (apply P C e) e' = result P C e' := by
  simp [result, apply, Function.update_of_ne (Ne.symm apart)]

theorem sent_apply_other {C : Config n S M} {e e' : Event n M} (apart : e.proc ≠ e'.proc) :
    sent P (apply P C e) e' = sent P C e' := by
  have countSame : (apply P C e).count e'.proc = C.count e'.proc :=
    Function.update_of_ne (Ne.symm apart) _ _
  unfold sent
  rw [result_apply_other apart, countSame]

/-- An event stays applicable after an event of another process. -/
theorem applicable_apply_other {C : Config n S M} {e e' : Event n M} (apart : e.proc ≠ e'.proc)
    (applicable : Applicable C e') : Applicable (apply P C e) e' := by
  cases e' with
  | null _ => trivial
  | deliver env =>
      simp only [Applicable, apply] at applicable ⊢
      refine Finset.mem_union_left _ ?_
      cases e with
      | null _ => exact applicable
      | deliver d =>
          refine Finset.mem_erase.mpr ⟨fun same => apart ?_, applicable⟩
          rw [same]

/-- **Events of different processes commute.** -/
theorem apply_comm {C : Config n S M} (wf : WellFormed C) {e e' : Event n M}
    (apart : e.proc ≠ e'.proc) (applicable : Applicable C e) (applicable' : Applicable C e') :
    apply P (apply P C e) e' = apply P (apply P C e') e := by
  have result₁ := result_apply_other (P := P) (C := C) apart
  have result₂ := result_apply_other (P := P) (C := C) (Ne.symm apart)
  have sent₁ := sent_apply_other (P := P) (C := C) apart
  have sent₂ := sent_apply_other (P := P) (C := C) (Ne.symm apart)
  ext1
  · simp only [apply_state, result₁, result₂]
    exact Function.update_comm apart _ _ _
  · simp only [apply_count]
    rw [Function.update_of_ne (Ne.symm apart), Function.update_of_ne apart]
    exact Function.update_comm apart _ _ _
  · -- the envelopes: each event removes its own envelope, which the other did not send
    simp only [apply_buffer, sent₁, sent₂]
    have notSent : ∀ {e₁ e₂ : Event n M}, e₁.proc ≠ e₂.proc → Applicable C e₂ →
        ∀ env, e₂ = .deliver env → env ∉ sent P C e₁ := by
      intro e₁ e₂ _ applicable₂ env isDeliver member
      subst isDeliver
      exact sent_fresh wf e₁ member applicable₂
    ext env
    cases e with
    | null p =>
        cases e' with
        | null q =>
            simp only [Event.drop, Finset.mem_union]
            tauto
        | deliver d =>
            simp only [Event.drop, Finset.mem_union, Finset.mem_erase]
            have := notSent apart applicable' d rfl
            constructor
            · rintro (⟨ne, inB | inS⟩ | inS')
              · exact Or.inl (Or.inl ⟨ne, inB⟩)
              · exact Or.inr inS
              · exact Or.inl (Or.inr inS')
            · rintro ((⟨ne, inB⟩ | inS') | inS)
              · exact Or.inl ⟨ne, Or.inl inB⟩
              · exact Or.inr inS'
              · exact Or.inl ⟨fun same => this (same ▸ inS), Or.inr inS⟩
    | deliver d =>
        cases e' with
        | null q =>
            simp only [Event.drop, Finset.mem_union, Finset.mem_erase]
            have := notSent (Ne.symm apart) applicable d rfl
            constructor
            · rintro ((⟨ne, inB⟩ | inS) | inS')
              · exact Or.inl ⟨ne, Or.inl inB⟩
              · exact Or.inr inS
              · exact Or.inl ⟨fun same => this (same ▸ inS'), Or.inr inS'⟩
            · rintro (⟨ne, inB | inS'⟩ | inS)
              · exact Or.inl (Or.inl ⟨ne, inB⟩)
              · exact Or.inr inS'
              · exact Or.inl (Or.inr inS)
        | deliver d' =>
            simp only [Event.drop, Finset.mem_union, Finset.mem_erase]
            have notSent₁ := notSent apart applicable' d' rfl
            have notSent₂ := notSent (Ne.symm apart) applicable d rfl
            constructor
            · rintro (⟨ne', ⟨ne, inB⟩ | inS⟩ | inS')
              · exact Or.inl ⟨ne, Or.inl ⟨ne', inB⟩⟩
              · exact Or.inr inS
              · exact Or.inl ⟨fun same => notSent₂ (same ▸ inS'), Or.inr inS'⟩
            · rintro (⟨ne, ⟨ne', inB⟩ | inS'⟩ | inS)
              · exact Or.inl ⟨ne', Or.inl ⟨ne, inB⟩⟩
              · exact Or.inr inS'
              · exact Or.inl ⟨fun same => notSent₁ (same ▸ inS), Or.inr inS⟩

/-! ## Schedules of different processes commute -/

/-- A schedule in which `p` takes no step. -/
def Avoids (p : Fin n) (σ : List (Event n M)) : Prop := ∀ e ∈ σ, e.proc ≠ p

/-- A schedule of `p` alone. -/
def Only (p : Fin n) (ρ : List (Event n M)) : Prop := ∀ e ∈ ρ, e.proc = p

/-- One event of `p` commutes with a schedule that avoids `p`. -/
theorem run_comm_event {p : Fin n} {e : Event n M} (isP : e.proc = p) :
    ∀ (σ : List (Event n M)) (C : Config n S M), WellFormed C → Applicable C e → Avoids p σ →
      Runs P C σ →
      Runs P (apply P C e) σ ∧ Applicable (run P C σ) e ∧ run P (apply P C e) σ = apply P (run P C σ) e := by
  intro σ
  induction σ with
  | nil => intro C _ applicable _ _; exact ⟨trivial, applicable, rfl⟩
  | cons f rest ih =>
      intro C wf applicable avoids runs
      have apart : e.proc ≠ f.proc := fun same => avoids f (List.mem_cons_self ..) (same ▸ isP)
      obtain ⟨applicableF, runsRest⟩ := runs
      have comm := apply_comm (P := P) wf apart applicable applicableF
      obtain ⟨runs', applicable', eq'⟩ := ih (apply P C f) (wellFormed_apply wf f)
        (applicable_apply_other (Ne.symm apart) applicable)
        (fun g member => avoids g (List.mem_cons_of_mem _ member)) runsRest
      refine ⟨⟨applicable_apply_other apart applicableF, ?_⟩, applicable', ?_⟩
      · rw [comm]; exact runs'
      · show run P (apply P (apply P C e) f) rest = apply P (run P (apply P C f) rest) e
        rw [comm]; exact eq'

/-- **A schedule of `p` commutes with a schedule that avoids `p`.** -/
theorem run_comm {p : Fin n} {ρ : List (Event n M)} (onlyP : Only p ρ) :
    ∀ (σ : List (Event n M)) (C : Config n S M), WellFormed C → Avoids p σ → Runs P C ρ → Runs P C σ →
      Runs P (run P C ρ) σ ∧ Runs P (run P C σ) ρ ∧ run P (run P C ρ) σ = run P (run P C σ) ρ := by
  induction ρ with
  | nil => intro σ C _ _ _ runsσ; exact ⟨runsσ, trivial, rfl⟩
  | cons e rest ih =>
      intro σ C wf avoids runsρ runsσ
      obtain ⟨applicable, runsRest⟩ := runsρ
      obtain ⟨runs₁, applicable₁, eq₁⟩ := run_comm_event (P := P) (onlyP e (List.mem_cons_self ..)) σ C wf
        applicable avoids runsσ
      obtain ⟨runs₂, runs₃, eq₂⟩ := ih (fun f member => onlyP f (List.mem_cons_of_mem _ member)) σ
        (apply P C e) (wellFormed_apply wf e) avoids runsRest runs₁
      refine ⟨runs₂, ⟨applicable₁, ?_⟩, ?_⟩
      · rw [← eq₁]; exact runs₃
      · show run P (run P (apply P C e) rest) σ = run P (apply P (run P C σ) e) rest
        rw [eq₂, eq₁]

/-! ## Persistence -/

/-- An event stays applicable until it is taken. -/
theorem applicable_apply_ne {C : Config n S M} {e f : Event n M} (applicable : Applicable C e)
    (apart : f ≠ e) : Applicable (apply P C f) e := by
  cases e with
  | null _ => trivial
  | deliver env =>
      simp only [Applicable, apply_buffer] at applicable ⊢
      refine Finset.mem_union_left _ ?_
      cases f with
      | null _ => exact applicable
      | deliver d =>
          exact Finset.mem_erase.mpr ⟨fun same => apart (by rw [same]), applicable⟩

theorem applicable_run_of_not_mem {e : Event n M} :
    ∀ (σ : List (Event n M)) (C : Config n S M), Applicable C e → e ∉ σ → Applicable (run P C σ) e := by
  intro σ
  induction σ with
  | nil => intro C applicable _; exact applicable
  | cons f rest ih =>
      intro C applicable notMem
      exact ih _ (applicable_apply_ne applicable fun same => notMem (same ▸ List.mem_cons_self ..))
        fun member => notMem (List.mem_cons_of_mem _ member)

theorem count_le_apply (C : Config n S M) (e : Event n M) (q : Fin n) :
    C.count q ≤ (apply P C e).count q := by
  rw [apply_count]
  by_cases same : q = e.proc
  · subst same; simp
  · rw [Function.update_of_ne same]

theorem count_le_run (C : Config n S M) (σ : List (Event n M)) (q : Fin n) :
    C.count q ≤ (run P C σ).count q := by
  induction σ generalizing C with
  | nil => exact le_rfl
  | cons e rest ih => exact (count_le_apply C e q).trans (ih _)

/-- **A delivered envelope never comes back.** -/
theorem gone_run {env : Envelope n M} :
    ∀ (σ : List (Event n M)) (C : Config n S M), env.seq < C.count env.sender → env ∉ C.buffer →
      env ∉ (run P C σ).buffer := by
  intro σ
  induction σ with
  | nil => intro C _ gone; exact gone
  | cons f rest ih =>
      intro C passed gone
      refine ih _ (lt_of_lt_of_le passed (count_le_apply C f _)) ?_
      rw [apply_buffer]
      intro member
      rcases Finset.mem_union.mp member with old | new
      · apply gone
        cases f with
        | null _ => exact old
        | deliver d => exact Finset.mem_of_mem_erase old
      · obtain ⟨sender, seq⟩ := mem_sent new
        rw [seq, ← sender] at passed
        omega

/-- Delivering an envelope removes it for good. -/
theorem gone_after_deliver {C : Config n S M} (wf : WellFormed C) {env : Envelope n M}
    (member : env ∈ C.buffer) (σ : List (Event n M)) :
    env ∉ (run P (apply P C (.deliver env)) σ).buffer := by
  refine gone_run σ _ (lt_of_lt_of_le (wf env member) (count_le_apply C _ _)) ?_
  rw [apply_buffer]
  intro inAfter
  rcases Finset.mem_union.mp inAfter with old | new
  · simp [Event.drop] at old
  · exact sent_fresh wf _ new member

/-- An envelope that was in transit and is gone was delivered. -/
theorem delivered_of_gone {C : Config n S M} {env : Envelope n M} (member : env ∈ C.buffer)
    {σ : List (Event n M)} (gone : env ∉ (run P C σ).buffer) : Event.deliver env ∈ σ := by
  by_contra notMem
  exact gone (applicable_run_of_not_mem (e := .deliver env) σ C member notMem)

/-! ## Configurations that differ in one process -/

/-- Two configurations agree except in the state of `p`. -/
structure AgreeExcept (p : Fin n) (C D : Config n S M) : Prop where
  count : C.count = D.count
  buffer : C.buffer = D.buffer
  state : ∀ q, q ≠ p → C.state q = D.state q

theorem agree_apply {p : Fin n} {C D : Config n S M} (agree : AgreeExcept p C D) {e : Event n M}
    (apart : e.proc ≠ p) : AgreeExcept p (apply P C e) (apply P D e) := by
  have sameResult : result P C e = result P D e := by simp [result, agree.state _ apart]
  have sameSent : sent P C e = sent P D e := by simp [sent, sameResult, agree.count]
  refine ⟨?_, ?_, fun q other => ?_⟩
  · simp [apply_count, agree.count]
  · simp [apply_buffer, agree.buffer, sameSent]
  · simp only [apply_state, sameResult]
    by_cases same : q = e.proc
    · subst same; simp
    · simp [Function.update_of_ne same, agree.state q other]

theorem agree_run {p : Fin n} :
    ∀ (σ : List (Event n M)) (C D : Config n S M), AgreeExcept p C D → Avoids p σ → Runs P C σ →
      Runs P D σ ∧ AgreeExcept p (run P C σ) (run P D σ) := by
  intro σ
  induction σ with
  | nil => intro C D agree _ _; exact ⟨trivial, agree⟩
  | cons e rest ih =>
      intro C D agree avoids runs
      have apart := avoids e (List.mem_cons_self ..)
      obtain ⟨applicable, runsRest⟩ := runs
      have applicableD : Applicable D e := by
        cases e with
        | null _ => trivial
        | deliver env => simp only [Applicable] at applicable ⊢; rw [← agree.buffer]; exact applicable
      obtain ⟨runsD, agreeAfter⟩ := ih _ _ (agree_apply agree apart)
        (fun f member => avoids f (List.mem_cons_of_mem _ member)) runsRest
      exact ⟨⟨applicableD, runsD⟩, agreeAfter⟩

/-! ## Decisions and valence -/

variable (P)

/-- Some process has output `value`. -/
def Decided (C : Config n S M) (value : Bool) : Prop := ∃ q, P.output (C.state q) = some value

/-- Some schedule from `C` leads to output `value`. -/
def ReachesValue (C : Config n S M) (value : Bool) : Prop :=
  ∃ σ, Runs P C σ ∧ Decided P (run P C σ) value

/-- **Bivalent**: both outputs are still reachable. -/
def Bivalent (C : Config n S M) : Prop := ReachesValue P C false ∧ ReachesValue P C true

/-- The initial configuration for the given inputs. -/
def initial (inputs : Fin n → Bool) : Config n S M := ⟨fun p => P.init p (inputs p), fun _ => 0, ∅⟩

/-- Reachable from some initial configuration. -/
def Reachable (C : Config n S M) : Prop :=
  ∃ inputs σ, Runs P (initial P inputs) σ ∧ run P (initial P inputs) σ = C

/-- **Agreement**: no reachable configuration has two different outputs. -/
def Agreement : Prop :=
  ∀ C, Reachable P C → ∀ p q first second, P.output (C.state p) = some first →
    P.output (C.state q) = some second → first = second

/-- **Non-triviality**: each value is the output in some reachable configuration. -/
def NonTrivial : Prop := ∀ value, ∃ C, Reachable P C ∧ Decided P C value

/-- **Termination despite one crash, finitely**: from every reachable configuration, without any
step of `p`, some other process can be brought to decide. -/
def OneCrashTermination : Prop :=
  ∀ C, Reachable P C → ∀ p, ∃ σ, Avoids p σ ∧ Runs P C σ ∧
    ∃ q, q ≠ p ∧ ∃ value, P.output ((run P C σ).state q) = some value

variable {P}

theorem output_apply {C : Config n S M} {q : Fin n} {value : Bool}
    (decided : P.output (C.state q) = some value) (e : Event n M) :
    P.output ((apply P C e).state q) = some value := by
  rw [apply_state]
  by_cases same : q = e.proc
  · subst same
    rw [Function.update_self]
    exact P.output_stable _ _ _ _ decided
  · rw [Function.update_of_ne same]; exact decided

theorem output_run {C : Config n S M} {q : Fin n} {value : Bool}
    (decided : P.output (C.state q) = some value) (σ : List (Event n M)) :
    P.output ((run P C σ).state q) = some value := by
  induction σ generalizing C with
  | nil => exact decided
  | cons e rest ih => exact ih (output_apply decided e)

theorem reachable_run {C : Config n S M} (reach : Reachable P C) {σ : List (Event n M)}
    (runs : Runs P C σ) : Reachable P (run P C σ) := by
  obtain ⟨inputs, τ, runsτ, rfl⟩ := reach
  exact ⟨inputs, τ ++ σ, runs_append.mpr ⟨runsτ, runs⟩, run_append _ _ _⟩

theorem reachable_apply {C : Config n S M} (reach : Reachable P C) {e : Event n M}
    (applicable : Applicable C e) : Reachable P (apply P C e) :=
  reachable_run (σ := [e]) reach ⟨applicable, trivial⟩

theorem wellFormed_of_reachable {C : Config n S M} (reach : Reachable P C) : WellFormed C := by
  obtain ⟨inputs, σ, _, rfl⟩ := reach
  exact wellFormed_run (fun env member => by simp [initial] at member) σ

theorem reachesValue_of_decided {C : Config n S M} {value : Bool} (decided : Decided P C value) :
    ReachesValue P C value := ⟨[], trivial, decided⟩

/-- What is reachable after a schedule is reachable before it. -/
theorem reachesValue_of_run {C : Config n S M} {σ : List (Event n M)} (runs : Runs P C σ)
    {value : Bool} (later : ReachesValue P (run P C σ) value) : ReachesValue P C value := by
  obtain ⟨τ, runsτ, decided⟩ := later
  exact ⟨σ ++ τ, runs_append.mpr ⟨runs, runsτ⟩, by rw [run_append]; exact decided⟩

/-- **A decided configuration is not bivalent.** -/
theorem not_reaches_other {C : Config n S M} (agree : Agreement P) (reach : Reachable P C)
    {value : Bool} (decided : Decided P C value) : ¬ ReachesValue P C (!value) := by
  rintro ⟨σ, runs, r, other⟩
  obtain ⟨q, decidedQ⟩ := decided
  have := agree _ (reachable_run reach runs) q r _ _ (output_run decidedQ σ) other
  cases value <;> simp at this

theorem not_decided_of_bivalent {C : Config n S M} (agree : Agreement P) (reach : Reachable P C)
    (bivalent : Bivalent P C) (value : Bool) : ¬ Decided P C value := fun decided => by
  have := not_reaches_other agree reach decided
  cases value
  · exact this bivalent.2
  · exact this bivalent.1

/-- Every reachable configuration still reaches some output. -/
theorem reaches_some (oneCrash : OneCrashTermination P) {C : Config n S M} (reach : Reachable P C)
    (p : Fin n) : ∃ value, ReachesValue P C value := by
  obtain ⟨σ, _, runs, q, _, value, decided⟩ := oneCrash C reach p
  exact ⟨value, σ, runs, q, decided⟩

/-! ## A bivalent initial configuration -/

theorem exists_step {g : ℕ → Prop} : ∀ m, ¬ g 0 → g m → ∃ j < m, ¬ g j ∧ g (j + 1)
  | 0, start, finish => absurd finish start
  | m + 1, start, finish => by
      by_cases middle : g m
      · obtain ⟨j, lt, h⟩ := exists_step m start middle
        exact ⟨j, by omega, h⟩
      · exact ⟨m, by omega, middle, finish⟩

/-- **Some initial configuration is bivalent.** -/
theorem exists_bivalent_initial (nontrivial : NonTrivial P)
    (oneCrash : OneCrashTermination P) : ∃ inputs, Bivalent P (initial P inputs) := by
  by_contra none
  push Not at none
  obtain ⟨C₀, ⟨a₀, σ₀, runs₀, rfl⟩, decided₀⟩ := nontrivial false
  obtain ⟨C₁, ⟨a₁, σ₁, runs₁, rfl⟩, decided₁⟩ := nontrivial true
  let chain : ℕ → Fin n → Bool := fun j i => if i.val < j then a₁ i else a₀ i
  let g : ℕ → Prop := fun j => ReachesValue P (initial P (chain j)) true
  have start : ¬ g 0 := by
    intro reachesTrue
    have reachesFalse : ReachesValue P (initial P a₀) false := ⟨σ₀, runs₀, decided₀⟩
    have : chain 0 = a₀ := by funext i; simp [chain]
    change ReachesValue P (initial P (chain 0)) true at reachesTrue
    rw [this] at reachesTrue
    exact none a₀ ⟨reachesFalse, reachesTrue⟩
  have finish : g n := by
    have : chain n = a₁ := by funext i; simp [chain, i.isLt]
    show ReachesValue P (initial P (chain n)) true
    rw [this]; exact ⟨σ₁, runs₁, decided₁⟩
  obtain ⟨j, lt, notTrue, nextTrue⟩ := exists_step n start finish
  let p : Fin n := ⟨j, lt⟩
  have reachX : Reachable P (initial P (chain j)) := ⟨chain j, [], trivial, rfl⟩
  obtain ⟨σ, avoids, runs, q, other, value, decided⟩ := oneCrash _ reachX p
  have valueFalse : value = false := by
    cases value
    · rfl
    · exact absurd ⟨σ, runs, q, decided⟩ notTrue
  have agree₀ : AgreeExcept p (initial P (chain j)) (initial P (chain (j + 1))) :=
    ⟨rfl, rfl, fun r apart => by
      have : r.val ≠ j := fun same => apart (Fin.ext same)
      simp only [initial, chain]
      congr 1
      by_cases below : r.val < j
      · simp [below, show r.val < j + 1 by omega]
      · simp [below, show ¬ r.val < j + 1 by omega]⟩
  obtain ⟨runsY, agreeY⟩ := agree_run σ _ _ agree₀ avoids runs
  have reachesFalseY : ReachesValue P (initial P (chain (j + 1))) false :=
    ⟨σ, runsY, q, by rw [← agreeY.state q other, ← valueFalse]; exact decided⟩
  exact none _ ⟨reachesFalseY, nextTrue⟩

/-! ## Postponing an event keeps bivalence -/

theorem split_first {e : Event n M} : ∀ {σ : List (Event n M)}, e ∈ σ →
    ∃ τ τ', σ = τ ++ e :: τ' ∧ e ∉ τ
  | f :: rest, member => by
      by_cases same : f = e
      · exact ⟨[], rest, by rw [same]; rfl, by simp⟩
      · obtain ⟨τ, τ', eq, notIn⟩ := split_first (List.mem_of_ne_of_mem (Ne.symm same) member)
        exact ⟨f :: τ, τ', by rw [eq]; rfl, by simp [Ne.symm same, notIn]⟩

theorem runs_take {C : Config n S M} {σ : List (Event n M)} (runs : Runs P C σ) (i : ℕ) :
    Runs P C (σ.take i) := by
  have := runs_append (P := P) (C := C) (first := σ.take i) (second := σ.drop i)
  rw [List.take_append_drop] at this
  exact (this.mp runs).1

/-- **From a bivalent configuration, an applicable event can be postponed so that it leads to a
bivalent configuration.** -/
theorem bivalent_after_event (oneCrash : OneCrashTermination P)
    {C : Config n S M} (reach : Reachable P C) (bivalent : Bivalent P C) {e : Event n M}
    (applicable : Applicable C e) :
    ∃ τ, e ∉ τ ∧ Runs P C τ ∧ Bivalent P (apply P (run P C τ) e) := by
  by_contra none
  push Not at none
  -- every postponed configuration reaches exactly one output
  have reachD : ∀ τ, Runs P C τ → e ∉ τ → Reachable P (apply P (run P C τ) e) := fun τ runs notIn =>
    reachable_apply (reachable_run reach runs) (applicable_run_of_not_mem τ C applicable notIn)
  have univalent : ∀ τ, Runs P C τ → e ∉ τ → ∀ value, ReachesValue P (apply P (run P C τ) e) value →
      ¬ ReachesValue P (apply P (run P C τ) e) (!value) := by
    intro τ runs notIn value reaches other
    apply none τ notIn runs
    cases value
    · exact ⟨reaches, other⟩
    · exact ⟨other, reaches⟩
  -- both outputs occur among the postponed configurations
  have both : ∀ value, ∃ τ, Runs P C τ ∧ e ∉ τ ∧ ReachesValue P (apply P (run P C τ) e) value := by
    intro value
    obtain ⟨σ, runs, decided⟩ := (by cases value; exacts [bivalent.1, bivalent.2] :
      ReachesValue P C value)
    by_cases inσ : e ∈ σ
    · obtain ⟨τ, τ', rfl, notIn⟩ := split_first inσ
      obtain ⟨runsτ, runsRest⟩ := runs_append.mp runs
      obtain ⟨_, runsτ'⟩ := runsRest
      refine ⟨τ, runsτ, notIn, τ', runsτ', ?_⟩
      rw [run_append] at decided
      exact decided
    · obtain ⟨q, decidedQ⟩ := decided
      exact ⟨σ, runs, inσ, reachesValue_of_decided ⟨q, output_apply decidedQ e⟩⟩
  -- walk from the immediate configuration to one of the other valence
  let val : List (Event n M) → Prop := fun τ => ReachesValue P (apply P (run P C τ) e) true
  obtain ⟨target, runsTarget, notInTarget, targetDiffers⟩ :
      ∃ τ, Runs P C τ ∧ e ∉ τ ∧ (val [] ↔ ¬ val τ) := by
    by_cases startTrue : val []
    · obtain ⟨τ, runs, notIn, reaches⟩ := both false
      exact ⟨τ, runs, notIn, ⟨fun _ => univalent τ runs notIn false reaches, fun _ => startTrue⟩⟩
    · obtain ⟨τ, runs, notIn, reaches⟩ := both true
      exact ⟨τ, runs, notIn, ⟨fun h => absurd h startTrue, fun h => absurd reaches h⟩⟩
  have prefixes : ∀ i, Runs P C (target.take i) ∧ e ∉ target.take i := fun i =>
    ⟨runs_take runsTarget i, fun member => notInTarget (List.mem_of_mem_take member)⟩
  have endpoints : val (target.take 0) ↔ ¬ val (target.take target.length) := by
    rw [List.take_zero, List.take_length]; exact targetDiffers
  obtain ⟨i, lt, flip⟩ : ∃ i < target.length, (val (target.take i) ↔ ¬ val (target.take (i + 1))) := by
    by_cases startTrue : val (target.take 0)
    · obtain ⟨j, lt, notJ, nextJ⟩ := exists_step (g := fun i => ¬ val (target.take i)) target.length
        (not_not.mpr startTrue) (endpoints.mp startTrue)
      exact ⟨j, lt, ⟨fun _ => nextJ, fun _ => not_not.mp notJ⟩⟩
    · obtain ⟨j, lt, notJ, nextJ⟩ := exists_step (g := fun i => val (target.take i)) target.length
        startTrue (by by_contra h; exact startTrue (endpoints.mpr h))
      exact ⟨j, lt, ⟨fun h => absurd h notJ, fun h => absurd nextJ h⟩⟩
  -- the neighbouring configurations
  let e' := target[i]
  have takeSucc : target.take (i + 1) = target.take i ++ [e'] := List.take_succ_eq_append_getElem lt
  set E₀ := run P C (target.take i) with E₀def
  have runs₀ := (prefixes i).1
  have runs₁ := (prefixes (i + 1)).1
  rw [takeSucc] at runs₁
  have applicable' : Applicable E₀ e' := (runs_append.mp runs₁).2.1
  have E₁eq : run P C (target.take (i + 1)) = apply P E₀ e' := by rw [takeSucc, run_append]; rfl
  have reach₀ : Reachable P E₀ := reachable_run reach runs₀
  have wf₀ : WellFormed E₀ := wellFormed_of_reachable reach₀
  have applicable₀ : Applicable E₀ e := applicable_run_of_not_mem _ C applicable (prefixes i).2
  have applicable₁ : Applicable (apply P E₀ e') e := by
    rw [← E₁eq]; exact applicable_run_of_not_mem _ C applicable (prefixes (i + 1)).2
  have uni₀ := univalent _ (prefixes i).1 (prefixes i).2
  have uni₁ := univalent _ (prefixes (i + 1)).1 (prefixes (i + 1)).2
  rw [E₁eq] at uni₁
  have flip' : ReachesValue P (apply P E₀ e) true ↔
      ¬ ReachesValue P (apply P (apply P E₀ e') e) true := by
    have h : ReachesValue P (apply P (run P C (target.take i)) e) true ↔
        ¬ ReachesValue P (apply P (run P C (target.take (i + 1))) e) true := flip
    rw [E₁eq] at h
    exact h
  -- the two neighbours reach different outputs
  have differ : ∀ value, ReachesValue P (apply P E₀ e) value →
      ReachesValue P (apply P (apply P E₀ e') e) value → False := by
    intro value r₀ r₁
    cases value
    · exact uni₀ false r₀ (flip'.mpr (uni₁ false r₁))
    · exact flip'.mp r₀ r₁
  by_cases sameProc : e'.proc = e.proc
  · -- the same process: run the others until one decides, without that process
    obtain ⟨σ, avoids, runsσ, q, _, value, decided⟩ := oneCrash E₀ reach₀ e.proc
    have only₁ : Only e.proc [e] := fun f member => by simp at member; rw [member]
    have only₂ : Only e.proc [e', e] := fun f member => by
      simp at member; rcases member with rfl | rfl
      · exact sameProc
      · rfl
    obtain ⟨runsAfter₁, _, comm₁⟩ := run_comm only₁ σ E₀ wf₀ avoids ⟨applicable₀, trivial⟩ runsσ
    obtain ⟨runsAfter₂, _, comm₂⟩ := run_comm only₂ σ E₀ wf₀ avoids
      ⟨applicable', applicable₁, trivial⟩ runsσ
    refine differ value ⟨σ, runsAfter₁, q, ?_⟩ ⟨σ, runsAfter₂, q, ?_⟩
    · have : run P (run P E₀ [e]) σ = run P (run P E₀ σ) [e] := comm₁
      simp only [run] at this
      rw [this]; exact output_apply decided e
    · have : run P (run P E₀ [e', e]) σ = run P (run P E₀ σ) [e', e] := comm₂
      simp only [run] at this
      rw [this]; exact output_apply (output_apply decided e') e
  · -- different processes: the second neighbour is reached from the first
    have comm := apply_comm (P := P) wf₀ sameProc applicable' applicable₀
    obtain ⟨value, reaches₁⟩ := reaches_some oneCrash (reachD _ (prefixes (i + 1)).1 (prefixes (i + 1)).2)
      e.proc
    rw [E₁eq] at reaches₁
    have reaches₀ : ReachesValue P (apply P E₀ e) value := by
      have moved : ReachesValue P (run P (apply P E₀ e) [e']) value := by
        show ReachesValue P (apply P (apply P E₀ e) e') value
        rw [← comm]; exact reaches₁
      exact reachesValue_of_run (σ := [e'])
        (show Runs P (apply P E₀ e) [e'] from ⟨applicable_apply_other (Ne.symm sameProc) applicable', trivial⟩)
        moved
    exact differ value reaches₀ reaches₁

/-! ## Runs, block by block -/

/-- An infinite run, given block by block from a start. -/
structure BlockRun (n : ℕ) (S : Type u) (M : Type v) where
  start : Config n S M
  blocks : ℕ → List (Event n M)

variable (P)

/-- The configuration after the first `k` blocks. -/
def configAt (r : BlockRun n S M) : ℕ → Config n S M
  | 0 => r.start
  | k + 1 => run P (configAt r k) (r.blocks k)

/-- Every block can be run where it comes. -/
def Valid (r : BlockRun n S M) : Prop := ∀ k, Runs P (configAt P r k) (r.blocks k)

/-- **Fair**: every process steps in infinitely many blocks, and every envelope in transit is
delivered later. -/
def Fair (r : BlockRun n S M) : Prop :=
  (∀ p k, ∃ j ≥ k, ∃ e ∈ r.blocks j, e.proc = p) ∧
    ∀ k env, env ∈ (configAt P r k).buffer → ∃ j ≥ k, Event.deliver env ∈ r.blocks j

/-- **Fair with `p` crashed**: `p` takes no step; every other process steps in infinitely many
blocks; every envelope in transit to another process is delivered later. -/
def FairExcept (p : Fin n) (r : BlockRun n S M) : Prop :=
  (∀ q, q ≠ p → ∀ k, ∃ j ≥ k, ∃ e ∈ r.blocks j, e.proc = q) ∧
    (∀ k env, env ∈ (configAt P r k).buffer → env.dest ≠ p →
      ∃ j ≥ k, Event.deliver env ∈ r.blocks j) ∧
    ∀ k, Avoids p (r.blocks k)

/-- **Termination in fair runs**: every fair run from an initial configuration decides. -/
def FairTermination : Prop :=
  ∀ r : BlockRun n S M, (∃ inputs, r.start = initial P inputs) → Valid P r → Fair P r →
    ∃ k value, Decided P (configAt P r k) value

/-- **Termination despite a crash**: every fair run in which one process has crashed at a reachable
configuration brings some other process to decide. -/
def CrashTermination : Prop :=
  ∀ r : BlockRun n S M, Reachable P r.start → ∀ p, Valid P r → FairExcept P p r →
    ∃ k q, q ≠ p ∧ ∃ value, P.output ((configAt P r k).state q) = some value

/-- **Consensus in spite of one crash.** -/
structure TotallyCorrect : Prop where
  agreement : Agreement P
  nontrivial : NonTrivial P
  fair : FairTermination P
  crash : CrashTermination P

variable {P}

/-- The concatenation of the first `k` blocks. -/
def prefixBlocks (r : BlockRun n S M) : ℕ → List (Event n M)
  | 0 => []
  | k + 1 => prefixBlocks r k ++ r.blocks k

theorem configAt_prefix (r : BlockRun n S M) (k : ℕ) :
    configAt P r k = run P r.start (prefixBlocks r k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [configAt, ih, prefixBlocks, run_append]

theorem runs_prefix {r : BlockRun n S M} (valid : Valid P r) (k : ℕ) :
    Runs P r.start (prefixBlocks r k) := by
  induction k with
  | zero => trivial
  | succ k ih =>
      refine runs_append.mpr ⟨ih, ?_⟩
      rw [← configAt_prefix]; exact valid k

omit [DecidableEq M] in
theorem avoids_prefix {r : BlockRun n S M} {p : Fin n} (avoids : ∀ k, Avoids p (r.blocks k)) :
    ∀ k, Avoids p (prefixBlocks r k)
  | 0 => fun _ member => by simp [prefixBlocks] at member
  | k + 1 => fun e member => by
      simp only [prefixBlocks, List.mem_append] at member
      rcases member with old | new
      · exact avoids_prefix avoids k e old
      · exact avoids k e new

/-- A process's turn comes after every block. -/
theorem next_turn (positive : 0 < n) (k : ℕ) (q : Fin n) : ∃ j ≥ k, j % n = q.val := by
  refine ⟨n * (k + 1) + q.val, ?_, ?_⟩
  · have : k + 1 ≤ n * (k + 1) := Nat.le_mul_of_pos_left _ positive
    omega
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt q.isLt]

/-- An envelope that is in transit after `k` blocks and gone after `j` was delivered in between. -/
theorem delivered_between {r : BlockRun n S M} {env : Envelope n M} {k : ℕ}
    (member : env ∈ (configAt P r k).buffer) :
    ∀ j, k ≤ j → env ∉ (configAt P r j).buffer → ∃ i, k ≤ i ∧ i < j ∧ Event.deliver env ∈ r.blocks i := by
  intro j le
  induction j, le using Nat.le_induction with
  | base => exact fun gone => absurd member gone
  | succ j le ih =>
      intro gone
      by_cases present : env ∈ (configAt P r j).buffer
      · exact ⟨j, le, by omega, delivered_of_gone present gone⟩
      · obtain ⟨i, low, high, delivered⟩ := ih present
        exact ⟨i, low, by omega, delivered⟩

/-- The events of a stage for `q`: deliver every envelope waiting for `q`, then a step on nothing. -/
noncomputable def stageEvents (C : Config n S M) (q : Fin n) : List (Event n M) :=
  ((C.buffer.filter fun env => env.dest = q).toList.map Event.deliver) ++ [Event.null q]

omit [DecidableEq M] in
theorem deliver_mem_stageEvents {C : Config n S M} {env : Envelope n M} (member : env ∈ C.buffer) :
    Event.deliver env ∈ stageEvents C env.dest := by
  simp [stageEvents, member]

omit [DecidableEq M] in
theorem stageEvents_proc {C : Config n S M} {q : Fin n} {e : Event n M} (member : e ∈ stageEvents C q) :
    e.proc = q := by
  simp only [stageEvents, List.mem_append, List.mem_map, Finset.mem_toList, Finset.mem_filter,
    List.mem_singleton] at member
  rcases member with ⟨env, ⟨_, isQ⟩, rfl⟩ | rfl
  · exact isQ
  · rfl

/-! ## The run with a crash: deliver everything, round by round -/

theorem runs_deliver_all {q : Fin n} :
    ∀ (envs : List (Envelope n M)) (C : Config n S M), envs.Nodup → (∀ env ∈ envs, env ∈ C.buffer) →
      Runs P C (envs.map Event.deliver ++ [Event.null q]) := by
  intro envs
  induction envs with
  | nil => intro _ _ _; exact ⟨trivial, trivial⟩
  | cons env rest ih =>
      intro C nodup present
      refine ⟨present env (List.mem_cons_self ..), ih _ (List.nodup_cons.mp nodup).2 fun env' member => ?_⟩
      have apart : env' ≠ env := fun same => (List.nodup_cons.mp nodup).1 (same ▸ member)
      exact applicable_apply_ne (e := .deliver env') (present env' (List.mem_cons_of_mem _ member))
        fun same => apart (by cases same; rfl)

theorem runs_stageEvents (C : Config n S M) (q : Fin n) : Runs P C (stageEvents C q) :=
  runs_deliver_all _ C (Finset.nodup_toList _) fun env member => by
    simp only [Finset.mem_toList, Finset.mem_filter] at member
    exact member.1

/-- The round-robin turn of block `k`. -/
def turn (positive : 0 < n) (k : ℕ) : Fin n := ⟨k % n, Nat.mod_lt _ positive⟩

/-- The configurations of the run in which `p` has crashed and the others take turns. -/
noncomputable def crashConfig (positive : 0 < n) (p : Fin n) (C : Config n S M) : ℕ → Config n S M
  | 0 => C
  | k + 1 =>
      run P (crashConfig positive p C k)
        (if turn positive k = p then [] else stageEvents (crashConfig positive p C k) (turn positive k))

/-- The run in which `p` has crashed. -/
noncomputable def crashRun (positive : 0 < n) (p : Fin n) (C : Config n S M) : BlockRun n S M where
  start := C
  blocks k := if turn positive k = p then [] else
    stageEvents (crashConfig (P := P) positive p C k) (turn positive k)

theorem crashRun_config (positive : 0 < n) (p : Fin n) (C : Config n S M) (k : ℕ) :
    configAt P (crashRun (P := P) positive p C) k = crashConfig (P := P) positive p C k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show run P (configAt P (crashRun (P := P) positive p C) k) ((crashRun (P := P) positive p C).blocks k) = _
      rw [ih]
      rfl

theorem crashRun_valid (positive : 0 < n) (p : Fin n) (C : Config n S M) :
    Valid P (crashRun (P := P) positive p C) := by
  intro k
  rw [crashRun_config]
  simp only [crashRun]
  split_ifs
  · trivial
  · exact runs_stageEvents _ _

theorem crashRun_fair (positive : 0 < n) (p : Fin n) (C : Config n S M) :
    FairExcept P p (crashRun (P := P) positive p C) := by
  refine ⟨fun q other k => ?_, fun k env member notP => ?_, fun k e member => ?_⟩
  · obtain ⟨j, le, isTurn⟩ := next_turn positive k q
    have turnIs : turn positive j = q := Fin.ext isTurn
    refine ⟨j, le, .null q, ?_, rfl⟩
    simp only [crashRun, turnIs, if_neg other]
    simp [stageEvents]
  · obtain ⟨j, le, isTurn⟩ := next_turn positive k env.dest
    have turnIs : turn positive j = env.dest := Fin.ext isTurn
    by_cases present : env ∈ (configAt P (crashRun (P := P) positive p C) j).buffer
    · refine ⟨j, le, ?_⟩
      simp only [crashRun, turnIs, if_neg notP]
      rw [crashRun_config] at present
      exact deliver_mem_stageEvents present
    · obtain ⟨i, low, _, delivered⟩ := delivered_between member j le present
      exact ⟨i, low, delivered⟩
  · simp only [crashRun] at member
    split_ifs at member with isP
    · simp at member
    · rw [stageEvents_proc member]; exact isP

/-- **Termination despite a crash gives a finite schedule**: from every reachable configuration,
without any step of `p`, some other process can be brought to decide. -/
theorem oneCrash_of_crashTermination (crash : CrashTermination P) (positive : 0 < n) :
    OneCrashTermination P := by
  intro C reach p
  obtain ⟨k, q, other, value, decided⟩ := crash (crashRun (P := P) positive p C) reach p
    (crashRun_valid positive p C) (crashRun_fair positive p C)
  refine ⟨prefixBlocks (crashRun (P := P) positive p C) k,
    avoids_prefix (crashRun_fair (P := P) positive p C).2.2 k,
    runs_prefix (crashRun_valid positive p C) k, q, other, value, ?_⟩
  rw [show run P C (prefixBlocks (crashRun (P := P) positive p C) k) =
    configAt P (crashRun (P := P) positive p C) k from
      (configAt_prefix (P := P) (crashRun (P := P) positive p C) k).symm]
  exact decided

/-! ## The run that never decides -/

variable (P) in
/-- Reachable and bivalent. -/
def Good (C : Config n S M) : Prop := Reachable P C ∧ Bivalent P C

theorem good_extend (oneCrash : OneCrashTermination P) {C : Config n S M} (good : Good P C)
    {e : Event n M} (applicable : Applicable C e) :
    ∃ τ, e ∉ τ ∧ Runs P C τ ∧ Good P (apply P (run P C τ) e) := by
  obtain ⟨τ, notIn, runs, bivalent⟩ := bivalent_after_event oneCrash good.1 good.2 applicable
  exact ⟨τ, notIn, runs, reachable_apply (reachable_run good.1 runs)
    (applicable_run_of_not_mem τ C applicable notIn), bivalent⟩

open Classical in
/-- Postpone `e` until applying it keeps bivalence, then apply it. -/
noncomputable def extend (oneCrash : OneCrashTermination P) (C : Config n S M) (e : Event n M) :
    List (Event n M) :=
  if h : Good P C ∧ Applicable C e then Classical.choose (good_extend oneCrash h.1 h.2) ++ [e] else []

theorem extend_spec (oneCrash : OneCrashTermination P) {C : Config n S M} (good : Good P C)
    (e : Event n M) :
    Runs P C (extend oneCrash C e) ∧ Good P (run P C (extend oneCrash C e)) := by
  unfold extend
  split_ifs with h
  · obtain ⟨notIn, runs, good'⟩ := Classical.choose_spec (good_extend oneCrash h.1 h.2)
    refine ⟨runs_append.mpr ⟨runs, applicable_run_of_not_mem _ C h.2 notIn, trivial⟩, ?_⟩
    rw [run_append]; exact good'
  · exact ⟨trivial, good⟩

theorem extend_removes (oneCrash : OneCrashTermination P) {C : Config n S M} (good : Good P C)
    {env : Envelope n M} (member : env ∈ C.buffer) :
    env ∉ (run P C (extend oneCrash C (.deliver env))).buffer := by
  unfold extend
  rw [dif_pos ⟨good, member⟩]
  obtain ⟨notIn, runs, _⟩ := Classical.choose_spec (good_extend oneCrash good (e := .deliver env) member)
  rw [run_append]
  exact gone_after_deliver (wellFormed_of_reachable (reachable_run good.1 runs))
    (applicable_run_of_not_mem (e := .deliver env) _ C member notIn) []

theorem extend_steps (oneCrash : OneCrashTermination P) {C : Config n S M} (good : Good P C)
    (q : Fin n) : Event.null q ∈ extend oneCrash C (.null q) := by
  unfold extend
  rw [dif_pos ⟨good, trivial⟩]
  exact List.mem_append_right _ (List.mem_singleton_self _)

/-- Process a list of events in order, each postponed until it keeps bivalence. -/
noncomputable def processAll (oneCrash : OneCrashTermination P) :
    Config n S M → List (Event n M) → List (Event n M)
  | _, [] => []
  | C, e :: es => extend oneCrash C e ++ processAll oneCrash (run P C (extend oneCrash C e)) es

theorem processAll_spec (oneCrash : OneCrashTermination P) :
    ∀ (L : List (Event n M)) (C : Config n S M), Good P C →
      Runs P C (processAll oneCrash C L) ∧ Good P (run P C (processAll oneCrash C L)) := by
  intro L
  induction L with
  | nil => intro C good; exact ⟨trivial, good⟩
  | cons e rest ih =>
      intro C good
      obtain ⟨runs₁, good₁⟩ := extend_spec oneCrash good e
      obtain ⟨runs₂, good₂⟩ := ih _ good₁
      refine ⟨runs_append.mpr ⟨runs₁, runs₂⟩, ?_⟩
      simp only [processAll]
      rw [run_append]; exact good₂

theorem processAll_delivers (oneCrash : OneCrashTermination P) {env : Envelope n M} :
    ∀ (L : List (Event n M)) (C : Config n S M), Good P C → env ∈ C.buffer → Event.deliver env ∈ L →
      env ∉ (run P C (processAll oneCrash C L)).buffer := by
  intro L
  induction L with
  | nil => intro _ _ _ member; simp at member
  | cons e rest ih =>
      intro C good member inL
      obtain ⟨_, good₁⟩ := extend_spec oneCrash good e
      simp only [processAll]
      rw [run_append]
      by_cases present : env ∈ (run P C (extend oneCrash C e)).buffer
      · rcases List.mem_cons.mp inL with same | later
        · subst same
          exact absurd present (extend_removes oneCrash good member)
        · exact ih _ good₁ present later
      · have passed : env.seq < (run P C (extend oneCrash C e)).count env.sender :=
          lt_of_lt_of_le (wellFormed_of_reachable good.1 env member) (count_le_run _ _ _)
        exact gone_run _ _ passed present

theorem processAll_steps (oneCrash : OneCrashTermination P) {q : Fin n} :
    ∀ (L : List (Event n M)) (C : Config n S M), Good P C → Event.null q ∈ L →
      ∃ f ∈ processAll oneCrash C L, f.proc = q := by
  intro L
  induction L with
  | nil => intro _ _ member; simp at member
  | cons e rest ih =>
      intro C good inL
      obtain ⟨_, good₁⟩ := extend_spec oneCrash good e
      simp only [processAll]
      rcases List.mem_cons.mp inL with same | later
      · subst same
        exact ⟨.null q, List.mem_append_left _ (extend_steps oneCrash good q), rfl⟩
      · obtain ⟨f, member, isQ⟩ := ih _ good₁ later
        exact ⟨f, List.mem_append_right _ member, isQ⟩

/-- The configurations of the run that stays bivalent: in block `k`, the process whose turn it is
receives every envelope waiting for it and steps on nothing, each event postponed so as to keep
bivalence. -/
noncomputable def bivalentConfig (oneCrash : OneCrashTermination P) (positive : 0 < n)
    (C₀ : Config n S M) : ℕ → Config n S M
  | 0 => C₀
  | k + 1 =>
      run P (bivalentConfig oneCrash positive C₀ k)
        (processAll oneCrash (bivalentConfig oneCrash positive C₀ k)
          (stageEvents (bivalentConfig oneCrash positive C₀ k) (turn positive k)))

/-- The run that stays bivalent. -/
noncomputable def bivalentRun (oneCrash : OneCrashTermination P) (positive : 0 < n)
    (C₀ : Config n S M) : BlockRun n S M where
  start := C₀
  blocks k := processAll oneCrash (bivalentConfig oneCrash positive C₀ k)
    (stageEvents (bivalentConfig oneCrash positive C₀ k) (turn positive k))

theorem bivalentRun_config (oneCrash : OneCrashTermination P) (positive : 0 < n) (C₀ : Config n S M)
    (k : ℕ) : configAt P (bivalentRun oneCrash positive C₀) k = bivalentConfig oneCrash positive C₀ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show run P (configAt P (bivalentRun oneCrash positive C₀) k)
        ((bivalentRun oneCrash positive C₀).blocks k) = _
      rw [ih]
      rfl

theorem bivalentConfig_good (oneCrash : OneCrashTermination P) (positive : 0 < n)
    {C₀ : Config n S M} (good : Good P C₀) : ∀ k, Good P (bivalentConfig oneCrash positive C₀ k)
  | 0 => good
  | k + 1 => (processAll_spec oneCrash _ _ (bivalentConfig_good oneCrash positive good k)).2

/-- **A fair run that never decides**: under agreement, non-triviality and one-crash termination,
some fair run from an initial configuration has no process deciding, ever. -/
theorem fair_run_never_decides (agree : Agreement P) (nontrivial : NonTrivial P)
    (oneCrash : OneCrashTermination P) :
    ∃ r : BlockRun n S M, (∃ inputs, r.start = initial P inputs) ∧ Valid P r ∧ Fair P r ∧
      ∀ k value, ¬ Decided P (configAt P r k) value := by
  obtain ⟨_, _, q, _⟩ := nontrivial true
  have positive : 0 < n := Fin.pos q
  obtain ⟨inputs, bivalent⟩ := exists_bivalent_initial nontrivial oneCrash
  have good₀ : Good P (initial P inputs) := ⟨⟨inputs, [], trivial, rfl⟩, bivalent⟩
  set r := bivalentRun oneCrash positive (initial P inputs)
  have goodAt : ∀ k, Good P (configAt P r k) := fun k => by
    rw [bivalentRun_config]; exact bivalentConfig_good oneCrash positive good₀ k
  refine ⟨r, ⟨inputs, rfl⟩, fun k => ?_, ⟨fun p k => ?_, fun k env member => ?_⟩, fun k value => ?_⟩
  · have := (processAll_spec oneCrash
      (stageEvents (bivalentConfig oneCrash positive (initial P inputs) k) (turn positive k)) _
      (bivalentConfig_good oneCrash positive good₀ k)).1
    rw [bivalentRun_config]; exact this
  · obtain ⟨j, le, isTurn⟩ := next_turn positive k p
    have turnIs : turn positive j = p := Fin.ext isTurn
    obtain ⟨f, member, isP⟩ := processAll_steps oneCrash (q := p)
      (stageEvents (bivalentConfig oneCrash positive (initial P inputs) j) (turn positive j)) _
      (bivalentConfig_good oneCrash positive good₀ j) (by
        rw [turnIs]; simp [stageEvents])
    refine ⟨j, le, f, ?_, isP⟩
    show f ∈ processAll oneCrash (bivalentConfig oneCrash positive (initial P inputs) j)
      (stageEvents (bivalentConfig oneCrash positive (initial P inputs) j) (turn positive j))
    exact member
  · obtain ⟨j, le, isTurn⟩ := next_turn positive k env.dest
    have turnIs : turn positive j = env.dest := Fin.ext isTurn
    by_cases present : env ∈ (configAt P r j).buffer
    · refine ⟨j, le, ?_⟩
      have presentJ := present
      rw [bivalentRun_config] at presentJ
      have gone := processAll_delivers oneCrash
        (stageEvents (bivalentConfig oneCrash positive (initial P inputs) j) (turn positive j)) _
        (bivalentConfig_good oneCrash positive good₀ j)
        presentJ (by rw [turnIs]; exact deliver_mem_stageEvents presentJ)
      exact delivered_of_gone present (σ := r.blocks j) (by
        show env ∉ (run P (configAt P r j) (r.blocks j)).buffer
        rw [bivalentRun_config]
        exact gone)
    · obtain ⟨i, low, _, delivered⟩ := delivered_between member j le present
      exact ⟨i, low, delivered⟩
  · exact not_decided_of_bivalent agree (goodAt k).1 (goodAt k).2 value

/-- **No deterministic protocol solves consensus in an asynchronous system in which one process may
crash.** -/
theorem not_totallyCorrect (P : Protocol n S M) : ¬ TotallyCorrect P := by
  intro correct
  obtain ⟨_, _, q, _⟩ := correct.nontrivial true
  have positive : 0 < n := Fin.pos q
  have oneCrash := oneCrash_of_crashTermination correct.crash positive
  obtain ⟨r, initialStart, valid, fair, never⟩ :=
    fair_run_never_decides correct.agreement correct.nontrivial oneCrash
  obtain ⟨k, value, decided⟩ := correct.fair r initialStart valid fair
  exact never k value decided

/-! ## Controls -/

namespace Controls

/-- Process `0` outputs its input at once; process `1` never outputs; nobody sends anything. -/
def leaderDecides : Protocol 2 (Option Bool) Unit where
  init p input := if p = 0 then some input else none
  step _ state _ := (state, [])
  output state := state
  output_stable _ _ _ _ h := h

theorem leaderDecides_state (C : Config 2 (Option Bool) Unit) (σ : List (Event 2 Unit)) :
    (run leaderDecides C σ).state = C.state := by
  induction σ generalizing C with
  | nil => rfl
  | cons e rest ih =>
      rw [run, ih]
      funext q
      simp [apply_state, result, leaderDecides]

/-- **Without crashes, consensus is easy**: the protocol has agreement, non-triviality and
termination in every fair run. -/
theorem crashFree_consensus :
    Agreement leaderDecides ∧ NonTrivial leaderDecides ∧ FairTermination leaderDecides := by
  refine ⟨?_, fun value => ⟨initial leaderDecides fun _ => value, ⟨_, [], trivial, rfl⟩, 0, ?_⟩, ?_⟩
  · rintro C ⟨inputs, σ, _, rfl⟩ p q first second hp hq
    rw [leaderDecides_state] at hp hq
    simp only [initial, leaderDecides] at hp hq
    split_ifs at hp hq with h₁ h₂
    simp_all
  · simp [initial, leaderDecides]
  · rintro r ⟨inputs, start⟩ _ _
    exact ⟨0, inputs 0, 0, by simp [configAt, start, initial, leaderDecides]⟩

/-- **So it fails termination despite a crash**, as the theorem says: when process `0` is the one
that crashes, process `1` never decides. -/
theorem leaderDecides_crash_fails : ¬ CrashTermination leaderDecides := fun crash =>
  not_totallyCorrect leaderDecides
    ⟨crashFree_consensus.1, crashFree_consensus.2.1, crashFree_consensus.2.2, crash⟩

/-! ### Positive and negative controls of each consensus predicate -/

/-- A two-process protocol whose states never change and which sends nothing, given by its
initial states. `leaderDecides` is the one where only process `0` starts decided. -/
def frozenProtocol (init : Fin 2 → Bool → Option Bool) : Protocol 2 (Option Bool) Unit where
  init := init
  step _ state _ := (state, [])
  output state := state
  output_stable _ _ _ _ h := h

theorem frozenProtocol_state (init : Fin 2 → Bool → Option Bool) (C : Config 2 (Option Bool) Unit)
    (σ : List (Event 2 Unit)) : (run (frozenProtocol init) C σ).state = C.state := by
  induction σ generalizing C with
  | nil => rfl
  | cons e rest ih =>
      rw [run, ih]
      funext q
      simp [apply_state, result, frozenProtocol]

/-- Each process outputs, at its first step on nothing, whether it is process `0`. -/
def firstStepDecides : Protocol 2 (Option Bool) Unit where
  init _ _ := none
  step p state _ := (if state = none then some (decide (p = 0)) else state, [])
  output state := state
  output_stable _ s _ _ h := by subst h; simp

/-- **Agreement, negative**: when every process outputs its own input at once, inputs `true` and
`false` give two different outputs in a reachable configuration. (`crashFree_consensus` is the
positive control.) -/
theorem ownInput_disagrees : ¬ Agreement (frozenProtocol fun _ input => some input) := fun agree =>
  absurd (agree _ ⟨fun p => decide (p = 0), [], trivial, rfl⟩ 0 1 true false rfl rfl) (by decide)

/-- **Decided, positive**: with input `true`, process `0` of `leaderDecides` has output `true`. -/
theorem leader_decided_true : Decided leaderDecides (initial leaderDecides fun _ => true) true :=
  ⟨0, rfl⟩

/-- **Decided, negative**: in the same configuration nobody has output `false`: process `0` has
output `true` and process `1` has no output. -/
theorem leader_not_decided_false :
    ¬ Decided leaderDecides (initial leaderDecides fun _ => true) false := by
  rintro ⟨q, h⟩
  fin_cases q <;> simp [initial, leaderDecides] at h

/-- **Bivalent, positive**: from the start of `firstStepDecides` both outputs are reachable: a step
of process `1` on nothing decides `false`, a step of process `0` decides `true`. -/
theorem firstStep_bivalent : Bivalent firstStepDecides (initial firstStepDecides fun _ => false) :=
  ⟨⟨[.null 1], ⟨trivial, trivial⟩, 1, rfl⟩, ⟨[.null 0], ⟨trivial, trivial⟩, 0, rfl⟩⟩

/-- **Bivalent, negative**: the start of `leaderDecides` with input `true` is univalent: no
schedule leads to output `false`. -/
theorem leader_not_bivalent : ¬ Bivalent leaderDecides (initial leaderDecides fun _ => true) := by
  rintro ⟨⟨σ, -, q, h⟩, -⟩
  rw [leaderDecides_state] at h
  fin_cases q <;> simp [initial, leaderDecides] at h

/-- **Non-triviality, negative**: a protocol in which everyone outputs `false` at once never
outputs `true`. (`crashFree_consensus` is the positive control.) -/
theorem alwaysFalse_trivial : ¬ NonTrivial (frozenProtocol fun _ _ => some false) := by
  intro nontrivial
  obtain ⟨C, ⟨inputs, σ, -, rfl⟩, q, h⟩ := nontrivial true
  rw [frozenProtocol_state] at h
  simp [initial, frozenProtocol] at h

/-- **Termination despite one crash, positive**: when every process outputs its own input at once,
whichever process crashes, the other has already decided. -/
theorem ownInput_oneCrashTermination :
    OneCrashTermination (frozenProtocol fun _ input => some input) := by
  rintro C ⟨inputs, σ, -, rfl⟩ p
  refine ⟨[], fun _ h => absurd h List.not_mem_nil, trivial, if p = 0 then 1 else 0,
    by fin_cases p <;> decide, inputs (if p = 0 then 1 else 0), ?_⟩
  rw [show ∀ C, run (frozenProtocol fun _ input => some input) C [] = C from fun _ => rfl,
    frozenProtocol_state]
  rfl

/-- **Termination despite one crash, negative**: when process `0` of `leaderDecides` crashes,
process `1` never decides. -/
theorem leader_not_oneCrashTermination : ¬ OneCrashTermination leaderDecides := by
  intro termination
  obtain ⟨σ, -, -, q, notZero, value, h⟩ := termination _ ⟨fun _ => true, [], trivial, rfl⟩ 0
  simp only [leaderDecides_state] at h
  fin_cases q
  · exact notZero rfl
  · simp [initial, leaderDecides] at h

/-- The block run in which both processes step on nothing in every block. -/
def bothStep (start : Config 2 (Option Bool) Unit) : BlockRun 2 (Option Bool) Unit :=
  ⟨start, fun _ => [.null 0, .null 1]⟩

/-- A frozen protocol sends nothing, so a schedule only removes envelopes from transit. -/
theorem frozenProtocol_buffer_subset (init : Fin 2 → Bool → Option Bool)
    (C : Config 2 (Option Bool) Unit) (σ : List (Event 2 Unit)) :
    (run (frozenProtocol init) C σ).buffer ⊆ C.buffer := by
  induction σ generalizing C with
  | nil => exact Finset.Subset.refl _
  | cons e rest ih =>
      refine (ih _).trans ?_
      intro env member
      rw [apply_buffer] at member
      rcases Finset.mem_union.mp member with dropped | sentNew
      · cases e with
        | deliver delivered => exact Finset.mem_of_mem_erase dropped
        | null _ => exact dropped
      · simp [sent, result, frozenProtocol, stamp] at sentNew

/-- Along any block run of a frozen protocol the states never change and nothing enters transit. -/
theorem frozenProtocol_configAt (init : Fin 2 → Bool → Option Bool)
    (r : BlockRun 2 (Option Bool) Unit) (k : ℕ) :
    (configAt (frozenProtocol init) r k).state = r.start.state ∧
      (configAt (frozenProtocol init) r k).buffer ⊆ r.start.buffer := by
  induction k with
  | zero => exact ⟨rfl, Finset.Subset.refl _⟩
  | succ k ih =>
      exact ⟨by rw [configAt, frozenProtocol_state, ih.1],
        (frozenProtocol_buffer_subset _ _ _).trans ih.2⟩

/-- **Termination in fair runs, negative**: a protocol in which nobody ever outputs does not
terminate in the fair run where both processes step on nothing forever. (`crashFree_consensus` is
the positive control.) -/
theorem neverDecides_unfair_termination : ¬ FairTermination (frozenProtocol fun _ _ => none) := by
  intro termination
  have valid : Valid (frozenProtocol fun _ _ => none)
      (bothStep (initial (frozenProtocol fun _ _ => none) fun _ => false)) :=
    fun _ => ⟨trivial, trivial, trivial⟩
  have fair : Fair (frozenProtocol fun _ _ => none)
      (bothStep (initial (frozenProtocol fun _ _ => none) fun _ => false)) := by
    refine ⟨fun p k => ⟨k, le_rfl, .null p, ?_, rfl⟩, fun k env member => ?_⟩
    · fin_cases p <;> simp [bothStep]
    · have := (frozenProtocol_configAt _ _ k).2 member
      simp [bothStep, initial] at this
  obtain ⟨k, value, q, h⟩ := termination _ ⟨_, rfl⟩ valid fair
  rw [(frozenProtocol_configAt _ _ k).1] at h
  simp [bothStep, initial, frozenProtocol] at h

/-- **Termination despite a crash, positive**: when every process outputs its own input at once,
every run that starts at a reachable configuration has a non-crashed process decided at once.
(`leaderDecides_crash_fails` is the negative control.) -/
theorem ownInput_crashTermination : CrashTermination (frozenProtocol fun _ input => some input) := by
  rintro r ⟨inputs, σ, -, start⟩ p - -
  refine ⟨0, if p = 0 then 1 else 0, by fin_cases p <;> decide,
    inputs (if p = 0 then 1 else 0), ?_⟩
  rw [configAt, ← start, frozenProtocol_state]
  rfl

/-- **Total correctness, negative**: `leaderDecides` has agreement, non-triviality and fair
termination, and fails only termination despite a crash. No protocol is a positive control:
`not_totallyCorrect` is the theorem that none exists. -/
theorem leader_not_totallyCorrect : ¬ TotallyCorrect leaderDecides := fun correct =>
  leaderDecides_crash_fails correct.crash

/-- **Reachable, positive**: a start configuration is reachable, by the empty schedule. -/
theorem leader_start_reachable : Reachable leaderDecides (initial leaderDecides fun _ => true) :=
  ⟨fun _ => true, [], trivial, rfl⟩

/-- **Reachable, negative**: no configuration of `leaderDecides` in which process `1` has an output
is reachable: process `1` never outputs. -/
theorem leader_second_output_unreachable :
    ¬ Reachable leaderDecides ⟨fun _ => some true, fun _ => 0, ∅⟩ := by
  rintro ⟨inputs, σ, -, h⟩
  have := congrArg (fun C : Config 2 (Option Bool) Unit => C.state 1) h
  simp only [leaderDecides_state] at this
  simp [initial, leaderDecides] at this

/-- **Valid, negative**: a block run whose first block delivers an envelope that was never sent
cannot be run. (Every fair run built above is a positive control.) -/
theorem phantom_delivery_invalid :
    ¬ Valid leaderDecides
      ⟨initial leaderDecides fun _ => true, fun _ => [.deliver ⟨0, (), 1, 0, 0⟩]⟩ := by
  intro valid
  have := (valid 0).1
  simp [configAt, Applicable, initial] at this

/-- **Applicable, positive and negative**: delivering the envelope in transit is applicable;
delivering it where nothing is in transit is not. -/
theorem inTransit_applicable :
    Applicable (⟨fun _ => none, fun _ => 0, {⟨0, (), 1, 0, 0⟩}⟩ : Config 2 (Option Bool) Unit)
        (.deliver ⟨0, (), 1, 0, 0⟩) ∧
      ¬ Applicable (initial leaderDecides fun _ => true) (.deliver ⟨0, (), 1, 0, 0⟩) := by
  decide

/-- **Reaches a value, positive**: from the start of `firstStepDecides`, a step of process `1`
reaches output `false`. -/
theorem firstStep_reaches_false :
    ReachesValue firstStepDecides (initial firstStepDecides fun _ => false) false :=
  firstStep_bivalent.1

/-- **Reaches a value, negative**: from the start of `leaderDecides` with input `true`, no schedule
reaches output `false`. -/
theorem leader_not_reaches_false :
    ¬ ReachesValue leaderDecides (initial leaderDecides fun _ => true) false := fun reaches =>
  leader_not_bivalent ⟨reaches, [], trivial, 0, rfl⟩

/-- **Avoids, positive and negative**: a schedule of process `1` alone avoids process `0`; one
with a step of `0` does not. -/
theorem avoids_controls :
    Avoids (0 : Fin 2) ([.null 1, .null 1] : List (Event 2 Unit)) ∧
      ¬ Avoids (0 : Fin 2) ([.null 1, .null 0] : List (Event 2 Unit)) := by
  unfold Avoids; decide

/-- **Only, positive and negative**: a schedule of process `1` alone is only `1`'s; one with a step
of `0` is not. -/
theorem only_controls :
    Only (1 : Fin 2) ([.null 1, .null 1] : List (Event 2 Unit)) ∧
      ¬ Only (1 : Fin 2) ([.null 1, .null 0] : List (Event 2 Unit)) := by
  unfold Only; decide

/-- **Fair with a crash, negative**: in the run where both processes step in every block, process
`0` has not crashed. -/
theorem bothStep_not_fairExcept :
    ¬ FairExcept leaderDecides 0 (bothStep (initial leaderDecides fun _ => true)) := fun fair =>
  absurd (fair.2.2 0) (by unfold Avoids bothStep; decide)

end Controls

end Mettapedia.GSLT.Coordination.CrashConsensusImpossibility
