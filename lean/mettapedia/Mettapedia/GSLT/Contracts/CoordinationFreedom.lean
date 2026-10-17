import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set

/-!
# Presence, absence and coordination

A store of facts is an element of a complete lattice (sets of atoms, or
annotations with an idempotent merge).  A *rule* maps a store to a store.
A rule is **presence-only** when it is monotone and inflationary: it reads
only what is present, so a larger store enables at least as much, and it only
adds.  A rule that fires on the *absence* of a fact is inflationary but not
monotone.

## Presence-only programs need no coordination

* **Schedule independence** (`quiescent_run_eq_closure`, `run_confluent`):
  every schedule of presence-only rules that reaches a quiescent store reaches
  the same one, the least store above the input closed under every rule.
* **Coordination freedom** (`net_agreement_eq_closure`): nodes fire rules on
  their own copies and merge copies they receive, in any order, with any
  delay or duplication.  Every node stays below the closure of all inputs
  (`net_le_closure`), and whenever the nodes agree on a quiescent store it is
  that closure.
* **CALM** (`coordinationFree_of_presenceOnly`, `monotone_of_coordinationFree`):
  presence-only programs compute their closure without coordination, and
  conversely, if every two-node execution of an inflationary program that
  agrees on a quiescent store yields one function of the input, that function
  is monotone.  These are the two halves of the CALM theorem (Hellerstein and
  Alvaro, *Keeping CALM: when distributed consistency is easy*; Ameloot, Neven
  and Van den Bussche, *Relational transducers for declarative networking*) in
  this setting.

## Absence breaks it, and a frontier repairs it

* **Counterexample** (`Controls.absence_not_confluent`,
  `Controls.absence_not_monotone`, `Controls.absence_net_disagrees`): the rule
  "add `q` when `p` is absent", beside a rule adding `p`, has two quiescent
  outcomes, is not monotone, and two nodes agree on a store that a single node
  never reaches.
* **Frontier-stratified absence restores determinacy**
  (`stratified_determinate`): split the store into a lower and an upper part.
  Lower rules are presence-only on the lower part; upper rules may read the
  lower part in any way, absence included, and are presence-only on the upper
  part.  Every schedule that fires upper rules only at a **frontier**, a state
  whose lower part is quiescent, and that reaches a quiescent state, ends in
  the closure of the lower input followed by the closure of the upper input
  under the upper rules at that lower closure.
* The frontier is necessary (`Controls.frontier_necessary`), and determinacy
  does not survive joining two stratified programs whose strata disagree: a
  cycle through absence has two quiescent outcomes
  (`Controls.cycle_through_absence`).

## Bubbles

A *bubble* is a class of programs, and its guarantees are the properties all
of its programs have.  Joining two programs runs the rules of both.

* **The presence bubble is closed under joins** (`presenceOnly_join`), so its
  guarantees compose: a join of presence-only programs is confluent and
  coordination free.
* **A stratified bubble is closed under joins over the same strata**
  (`stratified_join`); joins over opposite strata leave it
  (`Controls.cycle_through_absence`).  The guarantees of a join can therefore be
  strictly fewer than those common to the parts: composing absence needs a
  common frontier.
* **Consumption is not confluent** (`Controls.consumption_not_confluent`): two
  rules that consume one token reach two quiescent stores.  Consumption needs
  atomicity and a scheduler, and then the scheduler's order decides the
  outcome.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.Coordination

universe u v w

variable {α : Type u} {ι : Type v}

/-- Apply the rules a schedule names, first to last. -/
def run (rules : ι → α → α) : α → List ι → α
  | store, [] => store
  | store, rule :: schedule => run rules (rules rule store) schedule

@[simp] theorem run_nil (rules : ι → α → α) (store : α) : run rules store [] = store := rfl

@[simp] theorem run_cons (rules : ι → α → α) (store : α) (rule : ι) (schedule : List ι) :
    run rules store (rule :: schedule) = run rules (rules rule store) schedule := rfl

theorem run_append (rules : ι → α → α) (store : α) (first second : List ι) :
    run rules store (first ++ second) = run rules (run rules store first) second := by
  induction first generalizing store with
  | nil => rfl
  | cons rule first ih => exact ih (rules rule store)

/-- No rule changes the store. -/
def Quiescent (rules : ι → α → α) (store : α) : Prop := ∀ rule, rules rule store = store

variable [CompleteLattice α]

/-- The least store above `store` closed under every rule. -/
def closure (rules : ι → α → α) (store : α) : α :=
  sInf {closed | store ≤ closed ∧ ∀ rule, rules rule closed ≤ closed}

/-- **Presence-only rules**: monotone and inflationary. -/
structure PresenceOnly (rules : ι → α → α) : Prop where
  monotone : ∀ rule, Monotone (rules rule)
  inflationary : ∀ rule store, store ≤ rules rule store

theorem le_closure (rules : ι → α → α) (store : α) : store ≤ closure rules store :=
  le_sInf fun _ member => member.1

theorem closure_le {rules : ι → α → α} {store closed : α} (above : store ≤ closed)
    (isClosed : ∀ rule, rules rule closed ≤ closed) : closure rules store ≤ closed :=
  sInf_le ⟨above, isClosed⟩

theorem closure_le_of_quiescent {rules : ι → α → α} {store closed : α} (above : store ≤ closed)
    (quiescent : Quiescent rules closed) : closure rules store ≤ closed :=
  closure_le above fun rule => (quiescent rule).le

/-- The closure is closed under monotone rules. -/
theorem rule_closure_le {rules : ι → α → α} (monotone : ∀ rule, Monotone (rules rule))
    (store : α) (rule : ι) : rules rule (closure rules store) ≤ closure rules store :=
  le_sInf fun _ member =>
    ((monotone rule) (sInf_le member)).trans (member.2 rule)

theorem closure_mono {rules : ι → α → α} {first second : α} (le : first ≤ second) :
    closure rules first ≤ closure rules second :=
  le_sInf fun _ member => sInf_le ⟨le.trans member.1, member.2⟩

/-- Runs of inflationary rules only grow. -/
theorem le_run {rules : ι → α → α} (inflationary : ∀ rule store, store ≤ rules rule store)
    (store : α) (schedule : List ι) : store ≤ run rules store schedule := by
  induction schedule generalizing store with
  | nil => exact le_rfl
  | cons rule schedule ih => exact (inflationary rule store).trans (ih _)

/-- Runs of monotone rules stay below the closure of their start. -/
theorem run_le_closure {rules : ι → α → α} (monotone : ∀ rule, Monotone (rules rule))
    {store start : α} (below : store ≤ closure rules start) (schedule : List ι) :
    run rules store schedule ≤ closure rules start := by
  induction schedule generalizing store with
  | nil => exact below
  | cons rule schedule ih =>
      exact ih (((monotone rule) below).trans (rule_closure_le monotone start rule))

/-- **Schedule independence**: a quiescent store reached by any schedule of
presence-only rules is the closure of the start. -/
theorem quiescent_run_eq_closure {rules : ι → α → α} (presence : PresenceOnly rules)
    (store : α) (schedule : List ι) (quiescent : Quiescent rules (run rules store schedule)) :
    run rules store schedule = closure rules store :=
  le_antisymm (run_le_closure presence.monotone (le_closure rules store) schedule)
    (closure_le_of_quiescent (le_run presence.inflationary store schedule) quiescent)

/-- **Confluence**: two schedules reaching quiescent stores reach the same
store. -/
theorem run_confluent {rules : ι → α → α} (presence : PresenceOnly rules) (store : α)
    (first second : List ι) (quiescentFirst : Quiescent rules (run rules store first))
    (quiescentSecond : Quiescent rules (run rules store second)) :
    run rules store first = run rules store second :=
  (quiescent_run_eq_closure presence store first quiescentFirst).trans
    (quiescent_run_eq_closure presence store second quiescentSecond).symm

/-! ## Networks of replicas -/

/-- An event of a network: a node fires a rule on its copy, or a node merges
the current copy of another node. -/
inductive Event (ι : Type v) (ν : Type w)
  | fire (node : ν) (rule : ι)
  | deliver (source target : ν)

variable {ν : Type w} [DecidableEq ν]

/-- One event. -/
def Event.apply (rules : ι → α → α) (copies : ν → α) : Event ι ν → ν → α
  | .fire node rule => Function.update copies node (rules rule (copies node))
  | .deliver source target => Function.update copies target (copies target ⊔ copies source)

/-- A network execution. -/
def runNet (rules : ι → α → α) : (ν → α) → List (Event ι ν) → ν → α
  | copies, [] => copies
  | copies, event :: events => runNet rules (event.apply rules copies) events

@[simp] theorem runNet_nil (rules : ι → α → α) (copies : ν → α) :
    runNet rules copies [] = copies := rfl

@[simp] theorem runNet_cons (rules : ι → α → α) (copies : ν → α) (event : Event ι ν)
    (events : List (Event ι ν)) :
    runNet rules copies (event :: events) = runNet rules (event.apply rules copies) events := rfl

theorem runNet_append (rules : ι → α → α) (copies : ν → α) (first second : List (Event ι ν)) :
    runNet rules copies (first ++ second) = runNet rules (runNet rules copies first) second := by
  induction first generalizing copies with
  | nil => rfl
  | cons event first ih => exact ih _

/-- Copies only grow under inflationary rules. -/
theorem le_runNet {rules : ι → α → α} (inflationary : ∀ rule store, store ≤ rules rule store)
    (copies : ν → α) (events : List (Event ι ν)) (node : ν) :
    copies node ≤ runNet rules copies events node := by
  induction events generalizing copies with
  | nil => exact le_rfl
  | cons event events ih =>
      refine le_trans ?_ (ih _)
      cases event with
      | fire fired rule =>
          by_cases same : node = fired
          · subst same
            simp [Event.apply, inflationary]
          · simp [Event.apply, Function.update_of_ne same]
      | deliver source target =>
          by_cases same : node = target
          · subst same
            simp [Event.apply]
          · simp [Event.apply, Function.update_of_ne same]

/-- **Safety**: every copy stays below the closure of all inputs. -/
theorem net_le_closure {rules : ι → α → α} (monotone : ∀ rule, Monotone (rules rule))
    {start : α} (copies : ν → α) (below : ∀ node, copies node ≤ closure rules start)
    (events : List (Event ι ν)) (node : ν) :
    runNet rules copies events node ≤ closure rules start := by
  induction events generalizing copies with
  | nil => exact below node
  | cons event events ih =>
      apply ih
      intro other
      cases event with
      | fire fired rule =>
          by_cases same : other = fired
          · subst same
            simp only [Event.apply, Function.update_self]
            exact ((monotone rule) (below other)).trans (rule_closure_le monotone start rule)
          · simp only [Event.apply, Function.update_of_ne same]
            exact below other
      | deliver source target =>
          by_cases same : other = target
          · subst same
            simp only [Event.apply, Function.update_self]
            exact sup_le (below other) (below source)
          · simp only [Event.apply, Function.update_of_ne same]
            exact below other

/-- **Coordination freedom**: whenever the nodes agree on a quiescent store,
in any order of firing, delivery, delay or duplication, that store is the
closure of all inputs. -/
theorem net_agreement_eq_closure {rules : ι → α → α} (presence : PresenceOnly rules)
    (copies : ν → α) (events : List (Event ι ν)) (agreed : α)
    (agree : ∀ node, runNet rules copies events node = agreed) (node : ν)
    (quiescent : Quiescent rules agreed) :
    agreed = closure rules (⨆ other, copies other) := by
  apply le_antisymm
  · rw [← agree node]
    exact net_le_closure presence.monotone copies
      (fun other => (le_iSup copies other).trans (le_closure rules _)) events node
  · refine closure_le_of_quiescent (iSup_le fun other => ?_) quiescent
    rw [← agree other]
    exact le_runNet presence.inflationary copies events other

/-! ## The converse: coordination freedom forces monotonicity -/

/-- An inflationary program computes `outcome` without coordination when every
two-node execution that ends with both nodes agreeing on a quiescent store
ends in `outcome` of the merged inputs. -/
def CoordinationFree (rules : ι → α → α) (outcome : α → α) : Prop :=
  ∀ (copies : Bool → α) (events : List (Event ι Bool)) (agreed : α),
    (∀ node, runNet rules copies events node = agreed) → Quiescent rules agreed →
      agreed = outcome (copies true ⊔ copies false)

/-- **CALM, the direct half**: presence-only programs compute their closure
without coordination. -/
theorem coordinationFree_of_presenceOnly {rules : ι → α → α} (presence : PresenceOnly rules) :
    CoordinationFree rules (closure rules) := by
  intro copies events agreed agree quiescent
  rw [net_agreement_eq_closure presence copies events agreed agree true quiescent, iSup_bool_eq]

/-- A local run of one node as network events. -/
def fireAll (node : ν) : List ι → List (Event ι ν) :=
  List.map (Event.fire node)

theorem runNet_fireAll (rules : ι → α → α) (copies : ν → α) (node : ν) (schedule : List ι) :
    runNet rules copies (fireAll node schedule) =
      Function.update copies node (run rules (copies node) schedule) := by
  induction schedule generalizing copies with
  | nil => simp [fireAll]
  | cons rule schedule ih =>
      simp only [fireAll, List.map_cons, runNet_cons] at ih ⊢
      rw [ih]
      simp [Event.apply]

/-- **CALM, the converse**: if every store can be run to quiescence, an
inflationary program that computes `outcome` without coordination computes a
monotone function. -/
theorem monotone_of_coordinationFree {rules : ι → α → α}
    (inflationary : ∀ rule store, store ≤ rules rule store)
    (terminates : ∀ store, ∃ schedule, Quiescent rules (run rules store schedule))
    {outcome : α → α} (free : CoordinationFree rules outcome) : Monotone outcome := by
  intro small large le
  obtain ⟨localSchedule, localQuiet⟩ := terminates small
  set reached := run rules small localSchedule
  -- Both nodes start with `small`; the first runs to quiescence and the second copies it.
  have alone : reached = outcome (small ⊔ small) := by
    refine free (fun _ => small) (fireAll true localSchedule ++ [.deliver true false]) reached
      ?_ localQuiet
    intro node
    rw [runNet_append, runNet_fireAll]
    cases node <;> simp [Event.apply, reached, le_run inflationary small localSchedule]
  -- The first node starts with `small`, the second with `large`.
  obtain ⟨finalSchedule, finalQuiet⟩ := terminates (reached ⊔ large)
  set final := run rules (reached ⊔ large) finalSchedule
  have together : final = outcome (small ⊔ large) := by
    let copies : Bool → α := fun node => if node then small else large
    refine free copies (fireAll true localSchedule ++ [.deliver false true] ++
      fireAll true finalSchedule ++ [.deliver true false]) final ?_ finalQuiet
    have grows := le_run inflationary (reached ⊔ large) finalSchedule
    intro node
    simp only [runNet_append, runNet_fireAll]
    cases node
    · simp only [copies, runNet_cons, runNet_nil, Event.apply, Function.update_self,
        Function.update_of_ne (show (false : Bool) ≠ true by decide), if_false, if_true,
        Bool.false_eq_true]
      exact sup_eq_right.mpr ((le_sup_right.trans grows))
    · simp [copies, Event.apply, reached, final]
  rw [sup_idem] at alone
  rw [sup_eq_right.mpr le] at together
  rw [← alone, ← together]
  exact (le_sup_left.trans (le_run inflationary (reached ⊔ large) finalSchedule))

/-! ## Frontier-stratified absence -/

section Stratified

variable {L : Type u} [CompleteLattice L] {U : Type v} [CompleteLattice U]
variable {ι κ : Type w}

/-- Lower rules act on the lower part; upper rules read the lower part in any
way and act on the upper part. -/
structure Stratified (lower : ι → L → L) (upper : κ → L → U → U) : Prop where
  lowerPresence : PresenceOnly lower
  upperPresence : ∀ lowerStore, PresenceOnly fun rule => upper rule lowerStore

/-- One event of a two-stratum program. -/
def stratumStep (lower : ι → L → L) (upper : κ → L → U → U) : L × U → ι ⊕ κ → L × U
  | (low, high), .inl rule => (lower rule low, high)
  | (low, high), .inr rule => (low, upper rule low high)

/-- A two-stratum run. -/
def stratumRun (lower : ι → L → L) (upper : κ → L → U → U) : L × U → List (ι ⊕ κ) → L × U
  | state, [] => state
  | state, event :: events => stratumRun lower upper (stratumStep lower upper state event) events

/-- **A frontier-respecting schedule** fires an upper rule only in a state whose
lower part is quiescent. -/
inductive RespectsFrontier (lower : ι → L → L) (upper : κ → L → U → U) :
    L × U → List (ι ⊕ κ) → Prop
  | nil (state : L × U) : RespectsFrontier lower upper state []
  | lower (state : L × U) (rule : ι) (events : List (ι ⊕ κ)) :
      RespectsFrontier lower upper (stratumStep lower upper state (.inl rule)) events →
        RespectsFrontier lower upper state (.inl rule :: events)
  | upper (state : L × U) (rule : κ) (events : List (ι ⊕ κ)) :
      Quiescent lower state.1 →
        RespectsFrontier lower upper (stratumStep lower upper state (.inr rule)) events →
          RespectsFrontier lower upper state (.inr rule :: events)

/-- Two-stratum state: everything is decided by the lower closure once the
frontier is passed. -/
def StratumInvariant (lower : ι → L → L) (upper : κ → L → U → U) (start : L × U)
    (state : L × U) : Prop :=
  (∃ lowSchedule, state.1 = run lower start.1 lowSchedule) ∧
    ∃ highSchedule, state.2 = run (fun rule => upper rule (closure lower start.1)) start.2 highSchedule ∧
      (highSchedule = [] ∨ state.1 = closure lower start.1)

theorem stratumInvariant_run {lower : ι → L → L} {upper : κ → L → U → U}
    (stratified : Stratified lower upper) (start : L × U) :
    ∀ (state : L × U) (events : List (ι ⊕ κ)),
      StratumInvariant lower upper start state → RespectsFrontier lower upper state events →
        StratumInvariant lower upper start (stratumRun lower upper state events) := by
  intro state events invariant respects
  induction respects with
  | nil state => exact invariant
  | lower state rule events _ ih =>
      apply ih
      obtain ⟨⟨lowSchedule, low⟩, highSchedule, high, decided⟩ := invariant
      refine ⟨⟨lowSchedule ++ [rule], ?_⟩, highSchedule, high, ?_⟩
      · simp [stratumStep, run_append, ← low]
      · rcases decided with empty | settled
        · exact Or.inl empty
        · right
          simp only [stratumStep]
          rw [settled]
          refine le_antisymm (rule_closure_le stratified.lowerPresence.monotone _ rule)
            (stratified.lowerPresence.inflationary rule _)
  | upper state rule events quiet _ ih =>
      apply ih
      obtain ⟨⟨lowSchedule, low⟩, highSchedule, high, _⟩ := invariant
      have settled : state.1 = closure lower start.1 := by
        rw [low] at quiet ⊢
        exact quiescent_run_eq_closure stratified.lowerPresence start.1 lowSchedule quiet
      refine ⟨⟨lowSchedule, low⟩, highSchedule ++ [rule], ?_, Or.inr settled⟩
      simp only [stratumStep, run_append, run_cons, run_nil]
      rw [← high, settled]

/-- **Frontier-stratified absence is determinate.** -/
theorem stratified_determinate {lower : ι → L → L} {upper : κ → L → U → U}
    (stratified : Stratified lower upper) (start : L × U) (events : List (ι ⊕ κ))
    (respects : RespectsFrontier lower upper start events)
    (quietLow : Quiescent lower (stratumRun lower upper start events).1)
    (quietHigh : Quiescent (fun rule => upper rule (stratumRun lower upper start events).1)
      (stratumRun lower upper start events).2) :
    stratumRun lower upper start events =
      (closure lower start.1,
        closure (fun rule => upper rule (closure lower start.1)) start.2) := by
  obtain ⟨⟨lowSchedule, low⟩, highSchedule, high, _⟩ :=
    stratumInvariant_run stratified start start events
      ⟨⟨[], rfl⟩, [], rfl, Or.inl rfl⟩ respects
  have settled : (stratumRun lower upper start events).1 = closure lower start.1 := by
    rw [low] at quietLow ⊢
    exact quiescent_run_eq_closure stratified.lowerPresence start.1 lowSchedule quietLow
  rw [settled] at quietHigh
  rw [high] at quietHigh
  have highClosure := quiescent_run_eq_closure
    (stratified.upperPresence (closure lower start.1)) start.2 highSchedule quietHigh
  ext
  · exact settled
  · rw [high, highClosure]

/-- **Stratified programs over the same strata join.** -/
theorem stratified_join {ι' κ' : Type w} {lower : ι → L → L} {upper : κ → L → U → U}
    {lower' : ι' → L → L} {upper' : κ' → L → U → U} (first : Stratified lower upper)
    (second : Stratified lower' upper') :
    Stratified (Sum.elim lower lower') (Sum.elim upper upper') where
  lowerPresence :=
    { monotone := fun rule => by
        cases rule with
        | inl rule => exact first.lowerPresence.monotone rule
        | inr rule => exact second.lowerPresence.monotone rule
      inflationary := fun rule store => by
        cases rule with
        | inl rule => exact first.lowerPresence.inflationary rule store
        | inr rule => exact second.lowerPresence.inflationary rule store }
  upperPresence lowerStore :=
    { monotone := fun rule => by
        cases rule with
        | inl rule => exact (first.upperPresence lowerStore).monotone rule
        | inr rule => exact (second.upperPresence lowerStore).monotone rule
      inflationary := fun rule store => by
        cases rule with
        | inl rule => exact (first.upperPresence lowerStore).inflationary rule store
        | inr rule => exact (second.upperPresence lowerStore).inflationary rule store }

end Stratified

/-! ## Bubbles -/

/-- **The presence bubble is closed under joins.** -/
theorem presenceOnly_join {ι' : Type w} {rules : ι → α → α} {rules' : ι' → α → α}
    (first : PresenceOnly rules) (second : PresenceOnly rules') :
    PresenceOnly (Sum.elim rules rules') where
  monotone rule := by
    cases rule with
    | inl rule => exact first.monotone rule
    | inr rule => exact second.monotone rule
  inflationary rule store := by
    cases rule with
    | inl rule => exact first.inflationary rule store
    | inr rule => exact second.inflationary rule store

/-- Confluence: every two schedules that reach quiescent stores from the same
start reach the same store. -/
def Confluent (rules : ι → α → α) : Prop :=
  ∀ store first second, Quiescent rules (run rules store first) →
    Quiescent rules (run rules store second) → run rules store first = run rules store second

/-- Presence-only programs are confluent. -/
theorem presenceOnly_confluent {rules : ι → α → α} (presence : PresenceOnly rules) :
    Confluent rules :=
  fun store first second => run_confluent presence store first second

/-- **A join of presence-only programs is confluent.** -/
theorem join_confluent {ι' : Type w} {rules : ι → α → α} {rules' : ι' → α → α}
    (first : PresenceOnly rules) (second : PresenceOnly rules') :
    Confluent (Sum.elim rules rules') :=
  presenceOnly_confluent (presenceOnly_join first second)

/-! ## Controls -/

namespace Controls

/-- Two facts. -/
inductive Fact
  | p
  | q
  deriving DecidableEq

/-- Two rules over a store of facts. -/
inductive Rule
  | addP
  | absentPAddsQ
  deriving DecidableEq

/-- `addP` adds `p`; `absentPAddsQ` adds `q` when `p` is absent. -/
def rules : Rule → Set Fact → Set Fact
  | .addP, store => insert .p store
  | .absentPAddsQ, store => store ∪ {fact | fact = .q ∧ Fact.p ∉ store}

/-- A presence-only program: add `p`. -/
theorem addP_presenceOnly : PresenceOnly fun (_ : Unit) (store : Set Fact) => insert Fact.p store where
  monotone _ _ _ le := Set.insert_subset_insert le
  inflationary _ _ := Set.subset_insert _ _

/-- The hypotheses of the converse are satisfiable: adding `p` terminates in
one step, computes its closure without coordination, and so computes a
monotone function. -/
theorem addP_converse :
    Monotone (closure fun (_ : Unit) (store : Set Fact) => insert Fact.p store) :=
  monotone_of_coordinationFree addP_presenceOnly.inflationary
    (fun store => ⟨[()], fun _ => by simp [run]⟩)
    (coordinationFree_of_presenceOnly addP_presenceOnly)

theorem rules_inflationary (rule : Rule) (store : Set Fact) : store ≤ rules rule store := by
  cases rule
  · exact Set.subset_insert _ _
  · exact Set.subset_union_left

theorem run_p_first : run rules ∅ [.addP, .absentPAddsQ] = {Fact.p} := by
  ext fact
  cases fact <;> simp [run, rules]

theorem run_q_first : run rules ∅ [.absentPAddsQ, .addP] = {Fact.p, Fact.q} := by
  ext fact
  cases fact <;> simp [run, rules]

theorem quiescent_p : Quiescent rules {Fact.p} := by
  intro rule
  ext fact
  cases rule <;> cases fact <;> simp [rules]

theorem quiescent_pq : Quiescent rules {Fact.p, Fact.q} := by
  intro rule
  ext fact
  cases rule <;> cases fact <;> simp [rules]

/-- **Absence is not schedule independent**: two schedules reach distinct
quiescent stores. -/
theorem absence_not_confluent :
    Quiescent rules (run rules ∅ [.addP, .absentPAddsQ]) ∧
      Quiescent rules (run rules ∅ [.absentPAddsQ, .addP]) ∧
        run rules ∅ [.addP, .absentPAddsQ] ≠ run rules ∅ [.absentPAddsQ, .addP] := by
  rw [run_p_first, run_q_first]
  refine ⟨quiescent_p, quiescent_pq, fun same => ?_⟩
  have : Fact.q ∈ ({Fact.p} : Set Fact) := by rw [same]; simp
  simp at this

/-- **The absence rule is not monotone.** -/
theorem absence_not_monotone : ¬ Monotone (rules .absentPAddsQ) := by
  intro monotone
  have := monotone (Set.empty_subset {Fact.p})
  have member : Fact.q ∈ rules .absentPAddsQ ∅ := by simp [rules]
  have := this member
  simp [rules] at this

/-- **Two replicas disagree with a single node**: the first replica fires the
absence rule before it hears of `p`; the agreed quiescent store contains `q`,
which no single node that has `p` from the start ever derives. -/
theorem absence_net_disagrees :
    let copies : Bool → Set Fact := fun node => if node then {Fact.p} else ∅
    let events : List (Event Rule Bool) :=
      [.fire false .absentPAddsQ, .deliver true false, .deliver false true]
    (∀ node, runNet rules copies events node = {Fact.p, Fact.q}) ∧
      Quiescent rules {Fact.p, Fact.q} ∧
        ∀ schedule, Fact.q ∉ run rules {Fact.p} schedule := by
  refine ⟨?_, quiescent_pq, ?_⟩
  · intro node
    ext fact
    cases node <;> cases fact <;> simp [Event.apply, rules, Function.update]
  · intro schedule
    have stays : ∀ (store : Set Fact) (schedule : List Rule), store = {Fact.p} →
        run rules store schedule = {Fact.p} := by
      intro store schedule eq
      induction schedule generalizing store with
      | nil => exact eq
      | cons rule schedule ih =>
          apply ih
          rw [eq]
          exact quiescent_p rule
    rw [stays {Fact.p} schedule rfl]
    simp

/-! ### The frontier is necessary -/

/-- The lower stratum adds `p`; the upper stratum adds `q` when `p` is absent. -/
def lowerAddP : Unit → Prop → Prop := fun _ _ => True

/-- The upper rule reads the lower stratum's absence. -/
def upperAbsentP : Unit → Prop → Prop → Prop := fun _ low high => high ∨ ¬ low

theorem stratified_example : Stratified lowerAddP upperAbsentP where
  lowerPresence :=
    { monotone := fun _ _ _ _ => le_rfl
      inflationary := fun _ _ _ => trivial }
  upperPresence _ :=
    { monotone := fun _ _ _ le held => held.imp_left le
      inflationary := fun _ _ held => Or.inl held }

/-- **Firing the upper rule before the frontier gives a second quiescent
outcome.** -/
theorem frontier_necessary :
    RespectsFrontier lowerAddP upperAbsentP (False, False) [.inl (), .inr ()] ∧
      ¬ RespectsFrontier lowerAddP upperAbsentP (False, False) [.inr (), .inl ()] ∧
        (stratumRun lowerAddP upperAbsentP (False, False) [.inl (), .inr ()]).2 = (False ∨ ¬ True) ∧
          (stratumRun lowerAddP upperAbsentP (False, False) [.inr (), .inl ()]).2 = (False ∨ ¬ False) ∧
            ((False ∨ ¬ True) ↔ False) ∧ (False ∨ ¬ False) := by
  refine ⟨?_, ?_, rfl, rfl, by simp, Or.inr id⟩
  · refine .lower _ () _ (.upper _ () _ ?_ (.nil _))
    intro rule
    rfl
  · intro respects
    cases respects with
    | upper _ _ _ quiet _ =>
        have := quiet ()
        simp [lowerAddP] at this

/-! ### Joining two stratified programs -/

/-- `q` when `p` is absent, and `p` when `q` is absent. -/
def cycleRules : Bool → Set Fact → Set Fact
  | true, store => store ∪ {fact | fact = .q ∧ Fact.p ∉ store}
  | false, store => store ∪ {fact | fact = .p ∧ Fact.q ∉ store}

/-- **A cycle through absence has two quiescent outcomes**: each rule alone is
stratified, with opposite strata, and their join is not determinate. -/
theorem cycle_through_absence :
    run cycleRules ∅ [true, false] = {Fact.q} ∧ run cycleRules ∅ [false, true] = {Fact.p} ∧
      Quiescent cycleRules {Fact.q} ∧ Quiescent cycleRules {Fact.p} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext fact; cases fact <;> simp [run, cycleRules]
  · ext fact; cases fact <;> simp [run, cycleRules]
  · intro rule; ext fact; cases rule <;> cases fact <;> simp [cycleRules]
  · intro rule; ext fact; cases rule <;> cases fact <;> simp [cycleRules]

/-! ### Consumption -/

/-- Three facts: a token and two products. -/
inductive Token
  | token
  | left
  | right
  deriving DecidableEq

/-- Two rules each consume the token and make their own product. -/
def consumers : Bool → Set Token → Set Token
  | true, store => {fact | (fact ∈ store ∧ fact ≠ .token) ∨
      (fact = .left ∧ Token.token ∈ store)} ∪ {fact | fact ∈ store ∧ Token.token ∉ store}
  | false, store => {fact | (fact ∈ store ∧ fact ≠ .token) ∨
      (fact = .right ∧ Token.token ∈ store)} ∪ {fact | fact ∈ store ∧ Token.token ∉ store}

/-- **Consumption is not confluent**: whichever consumer fires first takes the
token. -/
theorem consumption_not_confluent : ¬ Confluent consumers := by
  intro confluent
  have quietLeft : Quiescent consumers (run consumers {.token} [true]) := by
    intro rule; ext fact; cases rule <;> cases fact <;> simp [run, consumers]
  have quietRight : Quiescent consumers (run consumers {.token} [false]) := by
    intro rule; ext fact; cases rule <;> cases fact <;> simp [run, consumers]
  have same := confluent {.token} [true] [false] quietLeft quietRight
  have : Token.left ∈ run consumers {.token} [true] := by simp [run, consumers]
  rw [same] at this
  simp [run, consumers] at this

end Controls

end Mettapedia.GSLT.Contracts.Coordination
