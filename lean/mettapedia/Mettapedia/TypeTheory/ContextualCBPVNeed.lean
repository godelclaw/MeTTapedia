import Mettapedia.TypeTheory.ContextualCBPVEquations
import Mettapedia.GSLT.Dynamics.ContextualStrategyQualification

/-!
# Call by need over the contextual effect signature

A consumer that may demand one suspended producer is a `Demand` tree: the
operations of `Program` plus `demand`, which continues with the producer's
value. Three handlers give it a producer:

* `cell`: the memo cell. A pending cell runs the producer at a demand and is
  then ready; a ready cell answers its value. Each alternative of a choice
  keeps its own copy of the cell, so sharing never crosses branches
  (call-time choice).
* `resample`: call by name. Every demand runs the producer again.
* `eager`: call by value. The producer runs once, before the consumer.

**Need is value at first demand** (`cell_none`): the pending memo cell is
exactly `share`, which runs the producer at the first demand on each path and
serves that value to every later demand there (`fill`).

**The qualified laws, with exact side conditions.**

* An immediate demand: need and value coincide for every producer
  (`share_demand_eq_eager`).
* At most one demand on every path: need and name coincide for every producer
  (`share_eq_resample_of_affine`).
* A pure producer: all three coincide for every consumer (`pure_producer_agree`).
* A read-only producer and a consumer that writes nothing: all three are
  observed alike, for any number of demands, choices and intents
  (`readOnly_writeFree_agree`).
* A read-only producer and a consumer that never demands: value and need are
  observed alike, whatever the consumer writes (`readOnly_unused_agree`).

**Controls**, each showing that a side condition is needed: a two-way choice
demanded twice gives two correlated pairs under need and value and four
under name (`coin_twice_*`); an unused choice gives one answer under need and
two under value (`coin_unused_*`); an unused intent is requested only under
value (`intent_unused_*`); a write before the demand is seen by need but not
by value (`write_before_demand`); a write between two demands is seen by name
but not by need (`write_between_demands`); a choice before the demand orders
the alternatives differently under need and value (`choice_before_demand`).

**ContextualCBPV.** The call-by-name and call-by-value forms of the curriculum
programs are observed exactly as `resample` and `eager` on the same consumer
(`Examples.reforced_is_resample`, `Examples.shared_is_eager`,
`Examples.thunked_is_need`, `Examples.eager_argument_is_eager`).

These are the contextual-model counterparts of the operational need theorems
already in the tree: the immediate-demand law
(`ScopedNeedImmediateDemand`, `PolarizedNeedImmediateDemand`), and agreement
of the three profiles exactly for deterministic producers or one use
(`CallTimeChoice.deterministic_agree`, `CallTimeChoice.profiles_agree_iff`).
A formal translation from those calculi into this model is not given here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCBPV

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.GSLT.Dynamics.ContextualStrategyQualification
open Mettapedia.TypeTheory.ContextualDependentSequencing

universe u

/-- A consumer of one suspended producer. -/
inductive Demand (State Value Answer Intent : Type u) : Type u where
  | pure (answer : Answer)
  | choose (left right : Demand State Value Answer Intent)
  | read (next : State → Demand State Value Answer Intent)
  | write (state : State) (next : Demand State Value Answer Intent)
  | intent (request : Intent) (next : Demand State Value Answer Intent)
  | demand (next : Value → Demand State Value Answer Intent)

namespace Demand

variable {State Value Answer Intent : Type u}

/-- Serve a known value to every demand. -/
def fill (value : Value) : Demand State Value Answer Intent → Program State Answer Intent
  | .pure answer => .pure answer
  | .choose left right => .choose (fill value left) (fill value right)
  | .read next => .read fun state => fill value (next state)
  | .write state next => .write state (fill value next)
  | .intent request next => .intent request (fill value next)
  | .demand next => fill value (next value)

variable (producer : Program State Value Intent)

/-- The memo cell: pending (`none`) or ready (`some value`). Each branch of a
choice continues from the parent's cell. -/
def cell : Option Value → Demand State Value Answer Intent → Program State Answer Intent
  | _, .pure answer => .pure answer
  | cache, .choose left right => .choose (cell cache left) (cell cache right)
  | cache, .read next => .read fun state => cell cache (next state)
  | cache, .write state next => .write state (cell cache next)
  | cache, .intent request next => .intent request (cell cache next)
  | some value, .demand next => cell (some value) (next value)
  | none, .demand next => producer.bind fun value => cell (some value) (next value)

/-- Value at first demand: on each path the first demand runs the producer;
every later demand on that path receives its value. -/
def share : Demand State Value Answer Intent → Program State Answer Intent
  | .pure answer => .pure answer
  | .choose left right => .choose (share left) (share right)
  | .read next => .read fun state => share (next state)
  | .write state next => .write state (share next)
  | .intent request next => .intent request (share next)
  | .demand next => producer.bind fun value => fill value (next value)

/-- Call by name: every demand runs the producer again. -/
def resample : Demand State Value Answer Intent → Program State Answer Intent
  | .pure answer => .pure answer
  | .choose left right => .choose (resample left) (resample right)
  | .read next => .read fun state => resample (next state)
  | .write state next => .write state (resample next)
  | .intent request next => .intent request (resample next)
  | .demand next => producer.bind fun value => resample (next value)

/-- Call by value: the producer runs once, before the consumer. -/
def eager (consumer : Demand State Value Answer Intent) : Program State Answer Intent :=
  producer.bind fun value => fill value consumer

/-! ## Need is value at first demand -/

/-- A ready cell serves its value everywhere. -/
theorem cell_some (value : Value) (consumer : Demand State Value Answer Intent) :
    cell producer (some value) consumer = fill value consumer := by
  induction consumer generalizing value with
  | pure answer => rfl
  | choose left right leftIH rightIH => simp only [cell, fill, leftIH, rightIH]
  | read next ih => simp only [cell, fill, ih]
  | write state next ih => simp only [cell, fill, ih]
  | intent request next ih => simp only [cell, fill, ih]
  | demand next ih => simp only [cell, fill, ih]

/-- **Need is value at first demand.** The pending memo cell is `share`. -/
theorem cell_none (consumer : Demand State Value Answer Intent) :
    cell producer none consumer = share producer consumer := by
  induction consumer with
  | pure answer => rfl
  | choose left right leftIH rightIH => simp only [cell, share, leftIH, rightIH]
  | read next ih => simp only [cell, share, ih]
  | write state next ih => simp only [cell, share, ih]
  | intent request next ih => simp only [cell, share, ih]
  | demand next _ => simp only [cell, share, cell_some]

/-! ## The qualified laws -/

/-- **An immediate demand: need is value**, for every producer. -/
theorem share_demand_eq_eager (next : Value → Demand State Value Answer Intent) :
    share producer (.demand next) = eager producer (.demand next) := rfl

/-- Consumers that never demand. -/
inductive DemandFree : Demand State Value Answer Intent → Prop where
  | pure (answer : Answer) : DemandFree (.pure answer)
  | choose {left right : Demand State Value Answer Intent} :
      DemandFree left → DemandFree right → DemandFree (.choose left right)
  | read {next : State → Demand State Value Answer Intent} :
      (∀ state, DemandFree (next state)) → DemandFree (.read next)
  | write (state : State) {next : Demand State Value Answer Intent} :
      DemandFree next → DemandFree (.write state next)
  | intent (request : Intent) {next : Demand State Value Answer Intent} :
      DemandFree next → DemandFree (.intent request next)

/-- Consumers that demand at most once on every path. -/
inductive Affine : Demand State Value Answer Intent → Prop where
  | pure (answer : Answer) : Affine (.pure answer)
  | choose {left right : Demand State Value Answer Intent} :
      Affine left → Affine right → Affine (.choose left right)
  | read {next : State → Demand State Value Answer Intent} :
      (∀ state, Affine (next state)) → Affine (.read next)
  | write (state : State) {next : Demand State Value Answer Intent} :
      Affine next → Affine (.write state next)
  | intent (request : Intent) {next : Demand State Value Answer Intent} :
      Affine next → Affine (.intent request next)
  | demand {next : Value → Demand State Value Answer Intent} :
      (∀ value, DemandFree (next value)) → Affine (.demand next)

theorem DemandFree.fill_eq_resample {consumer : Demand State Value Answer Intent}
    (free : DemandFree consumer) (value : Value) :
    fill value consumer = resample producer consumer := by
  induction free with
  | pure answer => rfl
  | choose _ _ leftIH rightIH => simp only [fill, resample, leftIH, rightIH]
  | read _ ih => simp only [fill, resample, ih]
  | write state _ ih => simp only [fill, resample, ih]
  | intent request _ ih => simp only [fill, resample, ih]

theorem DemandFree.share_eq_resample {consumer : Demand State Value Answer Intent}
    (free : DemandFree consumer) : share producer consumer = resample producer consumer := by
  induction free with
  | pure answer => rfl
  | choose _ _ leftIH rightIH => simp only [share, resample, leftIH, rightIH]
  | read _ ih => simp only [share, resample, ih]
  | write state _ ih => simp only [share, resample, ih]
  | intent request _ ih => simp only [share, resample, ih]

/-- **At most one demand on every path: need is name**, for every producer. -/
theorem share_eq_resample_of_affine {consumer : Demand State Value Answer Intent}
    (affine : Affine consumer) : share producer consumer = resample producer consumer := by
  induction affine with
  | pure answer => rfl
  | choose _ _ leftIH rightIH => simp only [share, resample, leftIH, rightIH]
  | read _ ih => simp only [share, resample, ih]
  | write state _ ih => simp only [share, resample, ih]
  | intent request _ ih => simp only [share, resample, ih]
  | demand free =>
      simp only [share, resample]
      congr 1
      funext value
      exact (free value).fill_eq_resample producer value

/-- **A pure producer: all three strategies coincide** for every consumer. -/
theorem pure_producer_agree (value : Value) (consumer : Demand State Value Answer Intent) :
    share (.pure value) consumer = fill value consumer ∧
      resample (.pure value) consumer = fill value consumer ∧
      eager (.pure value) consumer = fill value consumer := by
  refine ⟨?_, ?_, rfl⟩
  · induction consumer with
    | pure answer => rfl
    | choose left right leftIH rightIH => simp only [share, fill, leftIH, rightIH]
    | read next ih => simp only [share, fill, ih]
    | write state next ih => simp only [share, fill, ih]
    | intent request next ih => simp only [share, fill, ih]
    | demand next _ => rfl
  · induction consumer with
    | pure answer => rfl
    | choose left right leftIH rightIH => simp only [resample, fill, leftIH, rightIH]
    | read next ih => simp only [resample, fill, ih]
    | write state next ih => simp only [resample, fill, ih]
    | intent request next ih => simp only [resample, fill, ih]
    | demand next ih => exact ih value

/-- Consumers that write nothing. -/
inductive WriteFree : Demand State Value Answer Intent → Prop where
  | pure (answer : Answer) : WriteFree (.pure answer)
  | choose {left right : Demand State Value Answer Intent} :
      WriteFree left → WriteFree right → WriteFree (.choose left right)
  | read {next : State → Demand State Value Answer Intent} :
      (∀ state, WriteFree (next state)) → WriteFree (.read next)
  | intent (request : Intent) {next : Demand State Value Answer Intent} :
      WriteFree next → WriteFree (.intent request next)
  | demand {next : Value → Demand State Value Answer Intent} :
      (∀ value, WriteFree (next value)) → WriteFree (.demand next)

section ReadOnly

variable {producer}
variable {state : State} {answerAt : Value}
  (replay : ∀ {Result : Type u} (next : Value → Program State Result Intent)
    (branch : BranchTrace),
    runWorldsAt (producer.bind next) state branch = runWorldsAt (next answerAt) state branch)
include replay

theorem WriteFree.resample_observed {consumer : Demand State Value Answer Intent}
    (free : WriteFree consumer) (branch : BranchTrace) :
    runWorldsAt (resample producer consumer) state branch =
      runWorldsAt (fill answerAt consumer) state branch := by
  induction free generalizing branch with
  | pure answer => rfl
  | choose _ _ leftIH rightIH =>
      simp only [resample, fill, runWorldsAt, leftIH, rightIH]
  | read _ ih => exact ih state branch
  | intent request _ ih => simp only [resample, fill, runWorldsAt, ih]
  | @demand next _ ih =>
      simp only [resample, fill]
      rw [replay]
      exact ih answerAt branch

theorem WriteFree.share_observed {consumer : Demand State Value Answer Intent}
    (free : WriteFree consumer) (branch : BranchTrace) :
    runWorldsAt (share producer consumer) state branch =
      runWorldsAt (fill answerAt consumer) state branch := by
  induction free generalizing branch with
  | pure answer => rfl
  | choose _ _ leftIH rightIH =>
      simp only [share, fill, runWorldsAt, leftIH, rightIH]
  | read _ ih => exact ih state branch
  | intent request _ ih => simp only [share, fill, runWorldsAt, ih]
  | @demand next _ _ =>
      simp only [share, fill]
      rw [replay]

end ReadOnly

/-- **A read-only producer and a consumer that writes nothing: need, name and
value are observed alike**, for any number of demands, choices and intents. -/
theorem readOnly_writeFree_agree (qualified : ReadOnly producer)
    {consumer : Demand State Value Answer Intent} (free : WriteFree consumer)
    (state : State) (branch : BranchTrace) :
    runWorldsAt (share producer consumer) state branch =
        runWorldsAt (eager producer consumer) state branch ∧
      runWorldsAt (resample producer consumer) state branch =
        runWorldsAt (eager producer consumer) state branch := by
  obtain ⟨answerAt, replay⟩ := readOnly_bind producer qualified state
  have eagerObserved : runWorldsAt (eager producer consumer) state branch =
      runWorldsAt (fill answerAt consumer) state branch := replay _ branch
  rw [eagerObserved]
  exact ⟨free.share_observed replay branch, free.resample_observed replay branch⟩

/-- **A read-only producer that is never demanded: value and need are observed
alike**, whatever the consumer writes. -/
theorem readOnly_unused_agree (qualified : ReadOnly producer)
    {consumer : Demand State Value Answer Intent} (free : DemandFree consumer)
    (state : State) (branch : BranchTrace) :
    runWorldsAt (eager producer consumer) state branch =
      runWorldsAt (share producer consumer) state branch := by
  obtain ⟨answerAt, replay⟩ := readOnly_bind producer qualified state
  rw [eager, replay, free.fill_eq_resample producer answerAt, free.share_eq_resample producer]

end Demand

/-! ## Controls -/

namespace Demand.Controls

open Demand

/-- A two-way choice. -/
def coin : Program Unit Bool Unit := .choose (.pure false) (.pure true)

/-- Demand twice and pair the values. -/
def twice : Demand Unit Bool (Bool × Bool) Unit := .demand fun first => .demand fun second =>
  .pure (first, second)

theorem coin_twice_need :
    (runWorlds (share coin twice) ()).map WorldResult.answer = [(false, false), (true, true)] := rfl

theorem coin_twice_value :
    (runWorlds (eager coin twice) ()).map WorldResult.answer = [(false, false), (true, true)] := rfl

theorem coin_twice_name :
    (runWorlds (resample coin twice) ()).map WorldResult.answer =
      [(false, false), (false, true), (true, false), (true, true)] := rfl

/-- **Four occurrences against two**: name is not need for a choice used
twice. -/
theorem coin_twice_four_vs_two :
    (runWorlds (resample coin twice) ()).length = 4 ∧
      (runWorlds (share coin twice) ()).length = 2 := ⟨rfl, rfl⟩

/-- A consumer that never demands. -/
def unused : Demand Unit Bool Bool Unit := .pure true

theorem coin_unused_need : (runWorlds (share coin unused) ()).length = 1 := rfl

theorem coin_unused_value : (runWorlds (eager coin unused) ()).length = 2 := rfl

/-- An unused producer with an external request: only value requests it. -/
def requesting : Program Unit Bool Nat := .intent 7 (.pure false)

def unusedRequest : Demand Unit Bool Bool Nat := .pure true

theorem intent_unused_need :
    (runWorlds (share requesting unusedRequest) ()).map WorldResult.intents = [[]] := rfl

theorem intent_unused_value :
    (runWorlds (eager requesting unusedRequest) ()).map WorldResult.intents = [[7]] := rfl

/-- A read-only producer: the current state. -/
def readState : Program Nat Nat Unit := .read fun state => .pure state

theorem readState_readOnly : ReadOnly readState := .read _ fun _ => .pure _

/-- **A write before the demand is seen by need, not by value.** -/
def writeThenDemand : Demand Nat Nat Nat Unit := .write 1 (.demand fun value => .pure value)

theorem write_before_demand :
    (runWorlds (share readState writeThenDemand) 0).map WorldResult.answer = [1] ∧
      (runWorlds (eager readState writeThenDemand) 0).map WorldResult.answer = [0] :=
  ⟨rfl, rfl⟩

/-- **A write between two demands is seen by name, not by need.** -/
def demandWriteDemand : Demand Nat Nat (Nat × Nat) Unit :=
  .demand fun first => .write 1 (.demand fun second => .pure (first, second))

theorem write_between_demands :
    (runWorlds (share readState demandWriteDemand) 0).map WorldResult.answer = [(0, 0)] ∧
      (runWorlds (resample readState demandWriteDemand) 0).map WorldResult.answer = [(0, 1)] :=
  ⟨rfl, rfl⟩

/-- **A choice before the demand**: need runs the producer inside each
alternative, value runs it first. The answers agree as a multiset, not as a
list. -/
def chooseThenDemand : Demand Unit Bool (Bool × Bool) Unit :=
  .choose (.demand fun value => .pure (false, value)) (.demand fun value => .pure (true, value))

theorem choice_before_demand :
    (runWorlds (share coin chooseThenDemand) ()).map WorldResult.answer =
        [(false, false), (false, true), (true, false), (true, true)] ∧
      (runWorlds (eager coin chooseThenDemand) ()).map WorldResult.answer =
        [(false, false), (true, false), (false, true), (true, true)] := ⟨rfl, rfl⟩

theorem choice_before_demand_perm :
    ((runWorlds (share coin chooseThenDemand) ()).map WorldResult.answer).Perm
      ((runWorlds (eager coin chooseThenDemand) ()).map WorldResult.answer) := by
  rw [choice_before_demand.1, choice_before_demand.2]
  exact List.Perm.swap (true, false) (false, true) [(true, true)] |>.cons (false, false)

end Demand.Controls

/-! ## The exact side condition for choice

A producer choosing among `k ≥ 1` values, demanded `n` times. As multisets of
answers, value and need agree exactly when the producer is demanded at all or
has one value; need and name agree exactly when it is demanded at most once
or has one value (`value_need_agree_iff`, `need_name_agree_iff`). These are
the contextual counterparts of `CallTimeChoice.profiles_agree_iff`. -/

namespace Demand.Profiles

open Demand

variable {Value : Type}

/-- The answers of a program with no state or requests. -/
def answersOf {Answer : Type} (program : Program Unit Answer Unit) : List Answer :=
  (runWorlds program ()).map WorldResult.answer

theorem answers_branch {Answer : Type} (program : Program Unit Answer Unit)
    (branch other : BranchTrace) :
    (runWorldsAt program () branch).map WorldResult.answer =
      (runWorldsAt program () other).map WorldResult.answer := by
  induction program generalizing branch other with
  | pure answer => rfl
  | choose left right leftIH rightIH =>
      simp only [runWorldsAt, List.map_append]
      rw [leftIH (false :: branch) (false :: other), rightIH (true :: branch) (true :: other)]
  | read next ih => exact ih () branch other
  | write state next ih => exact ih branch other
  | intent request next ih =>
      simp only [runWorldsAt, List.map_map, Function.comp_def]
      exact ih branch other

theorem answersOf_bind {Answer Other : Type} (program : Program Unit Answer Unit)
    (next : Answer → Program Unit Other Unit) :
    answersOf (program.bind next) = (answersOf program).flatMap fun answer =>
      answersOf (next answer) := by
  unfold answersOf runWorlds
  rw [runWorldsAt_bind, List.map_flatMap, List.flatMap_map]
  congr 1
  funext prior
  simp only [List.map_map, Function.comp_def, WorldResult.prependIntents]
  exact answers_branch (next prior.answer) prior.branch []

/-- A choice among `first :: rest`. -/
def choice : Value → List Value → Program Unit Value Unit
  | first, [] => .pure first
  | first, next :: rest => .choose (.pure first) (choice next rest)

theorem answersOf_choice (first : Value) (rest : List Value) :
    answersOf (choice first rest) = first :: rest := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih =>
      unfold answersOf runWorlds at ih ⊢
      simp only [choice, runWorldsAt, List.map_cons, List.singleton_append]
      rw [answers_branch (choice next rest) (true :: []) [], ih next]

/-- Demand `count` more times, collecting the values. -/
def uses : Nat → List Value → Demand Unit Value (List Value) Unit
  | 0, collected => .pure collected.reverse
  | count + 1, collected => .demand fun value => uses count (value :: collected)

theorem replicate_append_cons (value : Value) (count : Nat) (rest : List Value) :
    List.replicate count value ++ value :: rest = value :: (List.replicate count value ++ rest) := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, ih]

theorem flatMap_singleton_eq_map {Other : Type} (values : List Value) (function : Value → Other) :
    values.flatMap (fun value => [function value]) = values.map function := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp [ih]

theorem fill_uses (value : Value) (count : Nat) (collected : List Value) :
    fill value (uses count collected) = .pure (List.replicate count value ++ collected).reverse := by
  induction count generalizing collected with
  | zero => rfl
  | succ count ih =>
      simp only [uses, fill, ih, List.replicate_succ, List.cons_append]
      rw [replicate_append_cons]

/-- All `count`-tuples over the values, in the order of the choices. -/
def tuples : Nat → List Value → List (List Value)
  | 0, _ => [[]]
  | count + 1, values => values.flatMap fun value => (tuples count values).map (value :: ·)

theorem tuples_length (count : Nat) (values : List Value) :
    (tuples count values).length = values.length ^ count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [tuples, List.length_flatMap, List.length_map, ih, List.map_const',
        List.sum_replicate, smul_eq_mul]
      ring

theorem answersOf_resample_uses (first : Value) (rest : List Value) (count : Nat)
    (collected : List Value) :
    answersOf (resample (choice first rest) (uses count collected)) =
      (tuples count (first :: rest)).map (collected.reverse ++ ·) := by
  induction count generalizing collected with
  | zero => simp [uses, resample, answersOf, runWorlds, runWorldsAt, tuples]
  | succ count ih =>
      simp only [uses, resample]
      rw [answersOf_bind, answersOf_choice]
      simp only [ih, tuples, List.map_flatMap, List.map_map, Function.comp_def,
        List.reverse_cons, List.append_assoc, List.singleton_append]

theorem answersOf_share_uses_zero (first : Value) (rest : List Value) :
    answersOf (share (choice first rest) (uses 0 [])) = [[]] := rfl

theorem answersOf_share_uses_succ (first : Value) (rest : List Value) (count : Nat) :
    answersOf (share (choice first rest) (uses (count + 1) [])) =
      (first :: rest).map (List.replicate (count + 1)) := by
  simp only [uses, share]
  rw [answersOf_bind, answersOf_choice]
  simp only [fill_uses]
  simp only [answersOf, runWorlds, runWorldsAt, List.map_cons, List.map_nil]
  rw [flatMap_singleton_eq_map]
  simp [List.reverse_append, List.reverse_replicate, List.replicate_succ]

theorem answersOf_eager_uses (first : Value) (rest : List Value) (count : Nat) :
    answersOf (eager (choice first rest) (uses count [])) =
      (first :: rest).map (List.replicate count) := by
  unfold eager
  rw [answersOf_bind, answersOf_choice]
  simp only [fill_uses]
  simp only [answersOf, runWorlds, runWorldsAt, List.map_cons, List.map_nil]
  rw [flatMap_singleton_eq_map]
  simp [List.reverse_replicate]

/-- **Value and need agree exactly when the producer is demanded or has one
value.** -/
theorem value_need_agree_iff (first : Value) (rest : List Value) (count : Nat) :
    ((answersOf (eager (choice first rest) (uses count [])) : Multiset (List Value)) =
        answersOf (share (choice first rest) (uses count []))) ↔
      (1 ≤ count ∨ rest = []) := by
  cases count with
  | zero =>
      rw [answersOf_eager_uses, answersOf_share_uses_zero]
      constructor
      · intro equal
        right
        have cards := congrArg Multiset.card equal
        simpa using cards
      · rintro (impossible | rfl)
        · omega
        · rfl
  | succ count =>
      rw [answersOf_eager_uses, answersOf_share_uses_succ]
      simp

/-- **Need and name agree exactly when the producer is demanded at most once
or has one value.** -/
theorem need_name_agree_iff (first : Value) (rest : List Value) (count : Nat) :
    ((answersOf (share (choice first rest) (uses count [])) : Multiset (List Value)) =
        answersOf (resample (choice first rest) (uses count []))) ↔
      (count ≤ 1 ∨ rest = []) := by
  rw [answersOf_resample_uses]
  rcases count with _ | _ | count
  · simp [answersOf_share_uses_zero, tuples]
  · rw [answersOf_share_uses_succ]
    simp only [tuples]
    have pointwise : (List.replicate 1 : Value → List Value) = ((fun x => x) ∘ fun value => [value]) := by
      funext value
      rfl
    simp [pointwise, flatMap_singleton_eq_map]
  · rw [answersOf_share_uses_succ]
    constructor
    · intro equal
      right
      have cards := congrArg Multiset.card equal
      simp only [Multiset.coe_card, List.length_map, tuples_length] at cards
      by_contra nonempty
      have two : 2 ≤ (first :: rest).length := by
        cases rest with
        | nil => exact absurd rfl nonempty
        | cons _ _ => simp
      have grow : (first :: rest).length < (first :: rest).length ^ (count + 1 + 1) := by
        calc (first :: rest).length = (first :: rest).length ^ 1 := (pow_one _).symm
          _ < (first :: rest).length ^ (count + 1 + 1) :=
            Nat.pow_lt_pow_right (by omega) (by omega)
      omega
    · rintro (impossible | rfl)
      · omega
      · congr 1
        simp only [List.map_cons, List.map_nil, List.reverse_nil, List.nil_append, List.map_id']
        have single : ∀ count, tuples count [first] = [List.replicate count first] := by
          intro count
          induction count with
          | zero => rfl
          | succ count ih => simp [tuples, ih, List.replicate_succ]
        rw [single]

end Demand.Profiles

/-! ## The ContextualCBPV curriculum, read through the handlers -/

namespace Examples

open Demand

/-- The CBPV coin's denotation, as a producer. -/
def coinProducer : Program (State demo) (VTy.den demo symT ⊕ Raised demo) (Request demo) :=
  CTy.asProgram demo ((coin : Comp demo [] (.ret symT)).den Env.empty)

/-- Pair two returned values; a raised no-value propagates. -/
def pairOutcomes (first second : VTy.den demo symT ⊕ Raised demo) :
    VTy.den demo (.prod symT symT) ⊕ Raised demo :=
  match first, second with
  | .inl left, .inl right => .inl (left, right)
  | .inr raised, _ => .inr raised
  | _, .inr raised => .inr raised

/-- The consumer of `(P $x $x)`: demand twice and pair. -/
def twiceConsumer :
    Demand (State demo) (VTy.den demo symT ⊕ Raised demo)
      (VTy.den demo (.prod symT symT) ⊕ Raised demo) (Request demo) :=
  .demand fun first => .demand fun second => .pure (pairOutcomes first second)

/-- The consumer of `(k one $x)`: never demand. -/
def keepConsumer :
    Demand (State demo) (VTy.den demo symT ⊕ Raised demo) (VTy.den demo symT ⊕ Raised demo)
      (Request demo) :=
  .pure (.inl ("one" : String))

set_option backward.isDefEq.respectTransparency false in
/-- The call-by-name CBPV term is name on the same consumer. -/
theorem reforced_is_resample :
    answers reforcedArgument =
      (runWorlds (resample coinProducer twiceConsumer) (0 : Nat)).map WorldResult.answer := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The shared CBPV term is value on the same consumer (and need: the consumer
demands at once). -/
theorem shared_is_eager :
    answers sharedArgument =
        (runWorlds (eager coinProducer twiceConsumer) (0 : Nat)).map WorldResult.answer ∧
      answers sharedArgument =
        (runWorlds (share coinProducer twiceConsumer) (0 : Nat)).map WorldResult.answer :=
  ⟨rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The thunked unused argument is need (and name) on the consumer that never
demands. -/
theorem thunked_is_need :
    answers thunkedArgument =
      (runWorlds (share coinProducer keepConsumer) (0 : Nat)).map WorldResult.answer := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The call-by-value translation of the same call is value. -/
theorem eager_argument_is_eager :
    answers eagerArgument =
      (runWorlds (eager coinProducer keepConsumer) (0 : Nat)).map WorldResult.answer := rfl

end Examples

#print axioms Demand.cell_none
#print axioms Demand.share_eq_resample_of_affine
#print axioms Demand.pure_producer_agree
#print axioms Demand.readOnly_writeFree_agree
#print axioms Demand.readOnly_unused_agree
#print axioms Demand.Controls.coin_twice_four_vs_two
#print axioms Demand.Controls.write_before_demand
#print axioms Demand.Controls.write_between_demands
#print axioms Demand.Controls.choice_before_demand_perm
#print axioms Demand.Profiles.value_need_agree_iff
#print axioms Demand.Profiles.need_name_agree_iff
#print axioms Examples.reforced_is_resample
#print axioms Examples.shared_is_eager
#print axioms Examples.thunked_is_need
#print axioms Examples.eager_argument_is_eager

end Mettapedia.TypeTheory.ContextualCBPV
