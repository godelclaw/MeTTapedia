import Mettapedia.GSLT.Logic.KnowledgeBasedPrograms
import Mathlib.Logic.Relation

/-!
# Coordinated attack over lossy links

Two processes run a deterministic protocol in synchronous rounds. In every round each process
sends one message to the other, and **any message may be lost**: a run is fixed by the two inputs
and the set of delivered messages (`Delivery`). After a fixed number of rounds each process
decides.

**Fault model**: lossy links, no bound on the number of lost messages; no crashes, no corruption,
synchronous rounds, deterministic processes.

**Property ruled out** (`SolvesAttack`): agreement (the two processes always decide alike), no
attack unless ordered (if both inputs are `false` the decision is `false`, whatever is
delivered), and attack when ordered and nothing is lost (if both inputs are `true` and every
message arrives, the decision is `true`). Termination is built in: both decide after the last
round.

## The theorem

* **No protocol solves coordinated attack** (`not_solvesAttack`), for any number of rounds.
  This is the theorem of Akkoyunlu, Ekanadham and Huber, and of Gray, in the form of Lynch,
  *Distributed Algorithms*, Theorem 5.1.

The proof walks a chain of runs. Order the message slots by round, and in a round the message of
`true` first; `upTo n` delivers exactly the first `n` slots. Between `upTo n` and `upTo (n + 1)`
only the `n`-th slot differs, and every later slot is lost in both, so the sender of that slot
receives the same messages in both runs (`sender_view_upTo`). With nothing delivered, a process's
final state depends on its own input only (`view_of_silent`). Agreement carries the decision along
the chain, from the run with both inputs `true` and everything delivered to the run with both
inputs `false` and nothing delivered.

## Common knowledge

The same chain needs no assumption on the protocol. Two runs are **linked** when one process ends
both in the same state. Every run in which both inputs are `true` and all messages are delivered
is linked, through a chain of runs, to the run in which both inputs are `false` and nothing is
delivered (`chain_good_to_silent`). Knowledge is read through the processes' final states
(`KnowledgeBasedPrograms.knows`), and **common knowledge** is everyone-knows iterated without
bound (`common`).

* **What is common knowledge in one run holds at every linked run**
  (`common_of_reflTransGen`).
* **Attack is never common knowledge** (`attack_never_common`): for any protocol in which both
  processes stay home when both inputs are `false`, attack is not common knowledge even in the
  run where every message is delivered. This is the theorem of Halpern and Moses, *Knowledge and
  common knowledge in a distributed environment*, for this system.

## Controls

* **Reliable links make it easy** (`Controls.exchange_reliable`): exchanging inputs in one round
  and attacking when both are `true` gives agreement and both validity conditions when nothing is
  lost.
* **One lost message breaks it** (`Controls.exchange_loses_agreement`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.CoordinatedAttack

universe u v

/-- `delivered round sender`: the message `sender` sends in `round` arrives. -/
abbrev Delivery := ℕ → Bool → Bool

/-! ## Message slots -/

/-- The position of a message slot: in round `round`, the message of `true` comes first. -/
def slot (round : ℕ) (sender : Bool) : ℕ := 2 * round + if sender then 0 else 1

/-- Deliver exactly the first `n` slots. -/
def upTo (n : ℕ) : Delivery := fun round sender => decide (slot round sender < n)

theorem slot_injective {round round' : ℕ} {sender sender' : Bool}
    (same : slot round sender = slot round' sender') : round = round' ∧ sender = sender' := by
  cases sender <;> cases sender' <;> simp [slot] at same ⊢ <;> omega

/-- The sender of slot `n`. -/
def senderOf (n : ℕ) : Bool := decide (n % 2 = 0)

theorem slot_senderOf (n : ℕ) : slot (n / 2) (senderOf n) = n := by
  unfold slot senderOf
  by_cases even : n % 2 = 0
  · simp only [even, decide_true, if_true]; omega
  · simp only [even, decide_false, Bool.false_eq_true, if_false]; omega

/-- No message to `p` is delivered. -/
def Silent (delivered : Delivery) (p : Bool) : Prop := ∀ round, delivered round (!p) = false

/-- A deterministic two-process protocol: the processes are `true` and `false`. -/
structure Protocol (S : Type u) (M : Type v) where
  init : Bool → Bool → S
  send : Bool → S → M
  receive : Bool → S → Option M → S
  decide : Bool → S → Bool

namespace Protocol

variable {S : Type u} {M : Type v} (P : Protocol S M)

/-- The state of process `p` after `round` rounds. -/
def state (inputs : Bool → Bool) (delivered : Delivery) : ℕ → Bool → S
  | 0, p => P.init p (inputs p)
  | round + 1, p => P.receive p (state inputs delivered round p)
      (if delivered round (!p) then some (P.send (!p) (state inputs delivered round (!p)))
        else none)

/-- What process `p` decides after `rounds` rounds. -/
def decision (rounds : ℕ) (inputs : Bool → Bool) (delivered : Delivery) (p : Bool) : Bool :=
  P.decide p (P.state inputs delivered rounds p)

/-- **Coordinated attack**: agreement, no attack unless ordered, attack when ordered and nothing
is lost. -/
structure SolvesAttack (rounds : ℕ) : Prop where
  agreement : ∀ inputs delivered,
    P.decision rounds inputs delivered true = P.decision rounds inputs delivered false
  stayHome : ∀ delivered p, P.decision rounds (fun _ => false) delivered p = false
  attack : ∀ p, P.decision rounds (fun _ => true) (fun _ _ => true) p = true

/-! ## Views -/

variable {P}

/-- Runs whose deliveries agree before `round` reach the same states at `round`. -/
theorem state_eq_of_agree {inputs : Bool → Bool} {first second : Delivery} {round : ℕ}
    (agree : ∀ earlier < round, ∀ sender, first earlier sender = second earlier sender) :
    ∀ earlier ≤ round, ∀ p, P.state inputs first earlier p = P.state inputs second earlier p := by
  intro earlier
  induction earlier with
  | zero => intro _ p; rfl
  | succ earlier ih =>
      intro le p
      have before := ih (Nat.le_of_succ_le le)
      simp only [state, before p, before (!p), agree earlier (Nat.lt_of_succ_le le) (!p)]

/-- **The view of a process**: if, before `round`, process `p` has the same input and receives
the same messages in two runs, it is in the same state at `round`. -/
theorem view_eq {inputs inputs' : Bool → Bool} {first second : Delivery} {p : Bool}
    (sameInput : inputs p = inputs' p) {round : ℕ}
    (sameFlags : ∀ earlier < round, first earlier (!p) = second earlier (!p))
    (sameMessages : ∀ earlier < round, first earlier (!p) = true →
      P.state inputs first earlier (!p) = P.state inputs' second earlier (!p)) :
    P.state inputs first round p = P.state inputs' second round p := by
  induction round with
  | zero => simp [state, sameInput]
  | succ round ih =>
      have before := ih (fun earlier lt => sameFlags earlier (Nat.lt_succ_of_lt lt))
        (fun earlier lt => sameMessages earlier (Nat.lt_succ_of_lt lt))
      simp only [state, before, ← sameFlags round (Nat.lt_succ_self round)]
      split_ifs with delivered
      · rw [sameMessages round (Nat.lt_succ_self round) delivered]
      · rfl

/-- **A process that hears nothing** ends in a state that depends on its own input only. -/
theorem view_of_silent {inputs inputs' : Bool → Bool} {delivered : Delivery} {p : Bool}
    (silent : Silent delivered p) (sameInput : inputs p = inputs' p) (round : ℕ) :
    P.state inputs delivered round p = P.state inputs' delivered round p :=
  view_eq sameInput (fun _ _ => rfl) (fun earlier _ delivered' => by
    rw [silent earlier] at delivered'
    exact absurd delivered' (by decide))

/-! ## The chain of deliveries -/

/-- **Dropping the last delivered message does not change what its sender sees.** -/
theorem sender_view_upTo (inputs : Bool → Bool) (n round : ℕ) :
    P.state inputs (upTo n) round (senderOf n) = P.state inputs (upTo (n + 1)) round (senderOf n) := by
  have slotP : slot (n / 2) (senderOf n) = n := slot_senderOf n
  generalize senderOf n = p at slotP ⊢
  have otherSlot : ∀ earlier, slot earlier (!p) ≠ n := by
    intro earlier same
    have := (slot_injective (same.trans slotP.symm)).2
    cases p <;> simp at this
  refine view_eq rfl (fun earlier _ => ?_) (fun earlier _ delivered => ?_)
  · have := otherSlot earlier
    simp only [upTo, decide_eq_decide]
    omega
  · -- A message delivered to the sender before the last slot was sent while both runs agreed.
    simp only [upTo, decide_eq_true_eq] at delivered
    have early : earlier ≤ n / 2 := by
      have : 2 * earlier ≤ slot earlier (!p) := by unfold slot; omega
      omega
    refine state_eq_of_agree (round := earlier) (fun before lt sender => ?_) earlier le_rfl (!p)
    have : slot before sender < n := by
      have : slot before sender ≤ 2 * before + 1 := by unfold slot; split_ifs <;> omega
      have : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
      omega
    simp only [upTo, decide_eq_decide]
    omega

/-- Under agreement, both processes decide alike, so the decision of `true` is that of `p`. -/
theorem decision_true_eq {rounds : ℕ} (solves : P.SolvesAttack rounds) (inputs : Bool → Bool)
    (delivered : Delivery) (p : Bool) :
    P.decision rounds inputs delivered true = P.decision rounds inputs delivered p := by
  cases p
  · exact solves.agreement inputs delivered
  · rfl

theorem decision_upTo_succ {rounds : ℕ} (solves : P.SolvesAttack rounds) (inputs : Bool → Bool)
    (n : ℕ) : P.decision rounds inputs (upTo (n + 1)) true = P.decision rounds inputs (upTo n) true := by
  rw [decision_true_eq solves inputs (upTo (n + 1)) (senderOf n),
    decision_true_eq solves inputs (upTo n) (senderOf n)]
  unfold decision
  rw [sender_view_upTo]

theorem decision_upTo {rounds : ℕ} (solves : P.SolvesAttack rounds) (inputs : Bool → Bool) :
    ∀ n, P.decision rounds inputs (upTo n) true = P.decision rounds inputs (upTo 0) true
  | 0 => rfl
  | n + 1 => (decision_upTo_succ solves inputs n).trans (decision_upTo solves inputs n)

/-- Within `rounds` rounds, delivering the first `2 * rounds` slots delivers everything. -/
theorem state_upTo_all (inputs : Bool → Bool) (rounds : ℕ) (p : Bool) :
    P.state inputs (upTo (2 * rounds)) rounds p = P.state inputs (fun _ _ => true) rounds p := by
  refine state_eq_of_agree (fun earlier lt sender => ?_) rounds le_rfl p
  have : slot earlier sender < 2 * rounds := by unfold slot; split_ifs <;> omega
  simp [upTo, this]

theorem upTo_zero_silent (p : Bool) : Silent (upTo 0) p := fun _ => by simp [upTo]

/-- **No protocol solves coordinated attack over lossy links.** -/
theorem not_solvesAttack (rounds : ℕ) : ¬ P.SolvesAttack rounds := by
  intro solves
  have good := solves.attack true
  -- Everything delivered decides like delivering the first `2 * rounds` slots, then like nothing.
  have toSilent : P.decision rounds (fun _ => true) (fun _ _ => true) true =
      P.decision rounds (fun _ => true) (upTo 0) true := by
    rw [← decision_upTo solves _ (2 * rounds)]
    unfold decision
    rw [state_upTo_all]
  -- With nothing delivered, change the input of `false`, which `true` cannot see, then that of
  -- `true`, which `false` cannot see.
  let mixed : Bool → Bool := fun p => p
  have firstChange : P.decision rounds (fun _ => true) (upTo 0) true =
      P.decision rounds mixed (upTo 0) true := by
    unfold decision
    rw [view_of_silent (inputs := fun _ => true) (inputs' := mixed) (upTo_zero_silent true) rfl]
  have secondChange : P.decision rounds mixed (upTo 0) true =
      P.decision rounds (fun _ => false) (upTo 0) true := by
    rw [decision_true_eq solves mixed (upTo 0) false,
      decision_true_eq solves (fun _ => false) (upTo 0) false]
    unfold decision
    rw [view_of_silent (inputs := mixed) (inputs' := fun _ => false) (upTo_zero_silent false) rfl]
  have home := solves.stayHome (upTo 0) true
  rw [toSilent, firstChange, secondChange, home] at good
  exact absurd good (by decide)

/-! ## Common knowledge -/

/-- A run: the two inputs and the deliveries. -/
abbrev Run := (Bool → Bool) × Delivery

/-- Process `p` cannot tell two runs apart when it ends both in the same state. -/
def observer (rounds : ℕ) (p : Bool) : Setoid Run :=
  Setoid.ker fun run => P.state run.1 run.2 rounds p

/-- Everyone knows a proposition about runs. -/
def everyone (rounds : ℕ) (proposition : Set Run) : Set Run :=
  Mettapedia.GSLT.KnowledgeBasedPrograms.knows (P.observer rounds true) proposition ∩
    Mettapedia.GSLT.KnowledgeBasedPrograms.knows (P.observer rounds false) proposition

/-- Everyone knows, iterated `depth` times. -/
def everyoneIter (rounds : ℕ) (proposition : Set Run) : ℕ → Set Run
  | 0 => proposition
  | depth + 1 => P.everyone rounds (everyoneIter rounds proposition depth)

/-- **Common knowledge**: everyone knows, to every depth. -/
def common (rounds : ℕ) (proposition : Set Run) : Set Run :=
  {run | ∀ depth, run ∈ P.everyoneIter rounds proposition depth}

/-- Two runs are linked when some process ends both in the same state. -/
def Linked (rounds : ℕ) (first second : Run) : Prop :=
  ∃ p, P.state first.1 first.2 rounds p = P.state second.1 second.2 rounds p

theorem everyoneIter_linked {rounds : ℕ} {proposition : Set Run} {depth : ℕ} {first second : Run}
    (known : first ∈ P.everyoneIter rounds proposition (depth + 1)) (linked : P.Linked rounds first second) :
    second ∈ P.everyoneIter rounds proposition depth := by
  obtain ⟨p, same⟩ := linked
  cases p
  · exact known.2 second same
  · exact known.1 second same

/-- **What is common knowledge holds at every linked run.** -/
theorem common_of_reflTransGen {rounds : ℕ} {proposition : Set Run} {first second : Run}
    (known : first ∈ P.common rounds proposition)
    (chain : Relation.ReflTransGen (P.Linked rounds) first second) :
    second ∈ P.common rounds proposition := by
  induction chain with
  | refl => exact known
  | tail _ linked ih => exact fun depth => P.everyoneIter_linked (ih (depth + 1)) linked

theorem common_le {rounds : ℕ} {proposition : Set Run} : P.common rounds proposition ⊆ proposition :=
  fun _ known => known 0

theorem linked_upTo_succ (rounds : ℕ) (inputs : Bool → Bool) (n : ℕ) :
    P.Linked rounds (inputs, upTo (n + 1)) (inputs, upTo n) :=
  ⟨senderOf n, (sender_view_upTo inputs n rounds).symm⟩

theorem chain_upTo (rounds : ℕ) (inputs : Bool → Bool) :
    ∀ n, Relation.ReflTransGen (P.Linked rounds) (inputs, upTo n) (inputs, upTo 0)
  | 0 => Relation.ReflTransGen.refl
  | n + 1 => Relation.ReflTransGen.head (P.linked_upTo_succ rounds inputs n) (chain_upTo rounds inputs n)

/-- **Every good run is linked to the silent run with both inputs `false`.** -/
theorem chain_good_to_silent (rounds : ℕ) :
    Relation.ReflTransGen (P.Linked rounds) ((fun _ => true), fun _ _ => true)
      ((fun _ => false), upTo 0) := by
  have toUpTo : P.Linked rounds ((fun _ => true), fun _ _ => true) ((fun _ => true), upTo (2 * rounds)) :=
    ⟨true, (state_upTo_all _ rounds true).symm⟩
  have firstChange : P.Linked rounds ((fun _ => true), upTo 0) ((fun p => p), upTo 0) :=
    ⟨true, view_of_silent (P := P) (inputs := fun _ => true) (inputs' := fun p => p)
      (upTo_zero_silent true) rfl rounds⟩
  have secondChange : P.Linked rounds ((fun p => p), upTo 0) ((fun _ => false), upTo 0) :=
    ⟨false, view_of_silent (P := P) (inputs := fun p => p) (inputs' := fun _ => false)
      (upTo_zero_silent false) rfl rounds⟩
  exact Relation.ReflTransGen.head toUpTo
    ((P.chain_upTo rounds _ (2 * rounds)).tail firstChange |>.tail secondChange)

/-- The runs in which process `true` attacks. -/
def attacks (rounds : ℕ) : Set Run := {run | P.decision rounds run.1 run.2 true = true}

/-- **Attack is never common knowledge**, even when every message is delivered, for every
protocol that stays home when both inputs are `false`. -/
theorem attack_never_common (rounds : ℕ)
    (stayHome : ∀ delivered, P.decision rounds (fun _ => false) delivered true = false) :
    ((fun _ => true), fun _ _ => true) ∉ P.common rounds (P.attacks rounds) := by
  intro known
  have there : P.decision rounds (fun _ => false) (upTo 0) true = true :=
    P.common_le (P.common_of_reflTransGen known (P.chain_good_to_silent rounds))
  rw [stayHome (upTo 0)] at there
  exact absurd there (by decide)

end Protocol

/-! ## Controls -/

namespace Controls

/-- Exchange inputs in the first round; attack when both are `true`. The state is the own input
and what was heard. -/
def exchange : Protocol (Bool × Option Bool) Bool where
  init _ input := (input, none)
  send _ state := state.1
  receive _ state heard := (state.1, heard)
  decide _ state := state.1 && state.2 == some true

/-- **Reliable links make it easy**: with every message delivered, exchanging inputs gives
agreement and both validity conditions. -/
theorem exchange_reliable (inputs : Bool → Bool) :
    exchange.decision 1 inputs (fun _ _ => true) true =
        exchange.decision 1 inputs (fun _ _ => true) false ∧
      exchange.decision 1 (fun _ => false) (fun _ _ => true) true = false ∧
        exchange.decision 1 (fun _ => true) (fun _ _ => true) true = true := by
  refine ⟨?_, by decide, by decide⟩
  cases h : inputs true <;> cases h' : inputs false <;>
    simp [Protocol.decision, Protocol.state, exchange, h, h']

/-- Only the message of `false` in the first round is delivered. -/
def onlyFalseSends : Delivery := fun round sender => round == 0 && !sender

/-- **One lost message breaks agreement**: with both inputs `true`, `true` hears `false` and
attacks, while `false` hears nothing and stays home. -/
theorem exchange_loses_agreement :
    exchange.decision 1 (fun _ => true) onlyFalseSends true = true ∧
      exchange.decision 1 (fun _ => true) onlyFalseSends false = false := by
  decide

/-- So `exchange` does not solve coordinated attack, as the theorem says of every protocol. -/
theorem exchange_not_solves : ¬ exchange.SolvesAttack 1 := exchange.not_solvesAttack 1

end Controls

end Mettapedia.GSLT.Coordination.CoordinatedAttack
