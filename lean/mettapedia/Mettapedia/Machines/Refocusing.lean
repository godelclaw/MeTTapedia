import Mathlib.Combinatorics.Quiver.Path
import Mettapedia.Machines.ProductiveCoreAdapters
import Mettapedia.Machines.ProductiveCoreOrdered
import Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-!
# Kinded refocusing machines

The eval/apply construction follows Definition 4 of Biernacka, Charatonik
and Zielinska, *Generalized Refocusing* (FSCD 2017). Frames are supplied by
the language's evaluation strategy. A structural syntax position alone does
not supply a frame. Stacks reuse `Quiver.Path`, with their existing identity
and composition laws; the authored MeTTaIL contexts supply a concrete adapter.

Local decomposition equations give readback soundness. Local search credits
give a productive common event machine, without requiring contractions to
terminate. A contraction with identical source and target is still a
computational occurrence. Reverse tracing is constructed for deterministic
source reduction when terminal machine states are source-normal. These are
separate language obligations, rather than assumed correspondence laws.
Ordered branching strategies require their own completeness and scheduling
laws.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Refocusing

open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- The kinds describe evaluation modes; they need not be term sorts. -/
structure Signature where
  Term : Type
  Kind : Type
  Frame : Kind → Kind → Type
  Value : Kind → Type
  Redex : Kind → Type
  plugFrame : {outer inner : Kind} → Frame outer inner → Term → Term
  valueTerm : {kind : Kind} → Value kind → Term
  redexTerm : {kind : Kind} → Redex kind → Term

instance Signature.frameQuiver (g : Signature) : Quiver g.Kind := ⟨g.Frame⟩

abbrev Context (g : Signature) (outer inner : g.Kind) :=
  @Quiver.Path g.Kind g.frameQuiver outer inner

namespace Context

def plug {g : Signature} {outer : g.Kind} :
    {inner : g.Kind} → Context g outer inner → g.Term → g.Term
  | _, .nil, term => term
  | _, .cons rest frame, term => plug rest (g.plugFrame frame term)

@[simp] theorem plug_nil {g : Signature} {kind : g.Kind} (term : g.Term) :
    plug (g := g) (.nil : Context g kind kind) term = term := rfl

@[simp] theorem plug_cons {g : Signature} {outer middle inner : g.Kind}
    (rest : Context g outer middle) (frame : g.Frame middle inner) (term : g.Term) :
    plug (rest.cons frame) term = plug rest (g.plugFrame frame term) := rfl

theorem plug_comp {g : Signature} {outer middle inner : g.Kind}
    (first : Context g outer middle) (second : Context g middle inner) (term : g.Term) :
    plug (first.comp second) term = plug first (plug second term) := by
  induction second generalizing term with
  | nil => rfl
  | cons rest frame ih => exact ih (g.plugFrame frame term)

end Context

/-- One local inspection either exposes a value/redex, descends through a
licensed frame, or identifies a stuck term. -/
inductive Decision (g : Signature) (kind : g.Kind) where
  | value (value : g.Value kind)
  | redex (redex : g.Redex kind)
  | descend {inner : g.Kind} (term : g.Term) (frame : g.Frame kind inner)
  | blocked (term : g.Term)

def Decision.reconstruct {g : Signature} {kind : g.Kind} : Decision g kind → g.Term
  | .value v => g.valueTerm v
  | .redex r => g.redexTerm r
  | .descend term frame => g.plugFrame frame term
  | .blocked term => term

/-- Executable local strategy data, with local readback equations. No
machine/source correspondence or termination theorem is assumed. -/
structure Strategy (g : Signature) where
  inspect : (kind : g.Kind) → g.Term → Decision g kind
  resume : {outer inner : g.Kind} → g.Frame outer inner → g.Value inner → Decision g outer
  contract : {kind : g.Kind} → g.Redex kind → Option g.Term
  inspect_correct : ∀ kind term, (inspect kind term).reconstruct = term
  resume_correct : ∀ {outer inner} (frame : g.Frame outer inner) value,
    (resume frame value).reconstruct = g.plugFrame frame (g.valueTerm value)

inductive State (g : Signature) (root : g.Kind) where
  | eval {kind : g.Kind} (term : g.Term) (context : Context g root kind)
  | ret {kind : g.Kind} (value : g.Value kind) (context : Context g root kind)

def State.readback {g : Signature} {root : g.Kind} : State g root → g.Term
  | .eval term context => context.plug term
  | .ret value context => context.plug (g.valueTerm value)

/-- The Boolean records a contraction, independently of term equality. -/
def advance {g : Signature} (strategy : Strategy g) {root kind : g.Kind}
    (context : Context g root kind) : Decision g kind → Option (Bool × State g root)
  | .value value => some (false, .ret value context)
  | .redex redex => (strategy.contract redex).map fun term => (true, .eval term context)
  | .descend term frame => some (false, .eval term (context.cons frame))
  | .blocked _ => none

def transition {g : Signature} (strategy : Strategy g) {root : g.Kind} :
    State g root → Option (Bool × State g root)
  | .eval (kind := kind) term context => advance strategy context (strategy.inspect kind term)
  | .ret _ .nil => none
  | .ret value (.cons context frame) => advance strategy context (strategy.resume frame value)

def answer {g : Signature} {root : g.Kind} : State g root → Option (g.Value root)
  | .ret value .nil => some value
  | _ => none

abbrev core {g : Signature} (strategy : Strategy g) (root : g.Kind) : MachineCore g.Term where
  State := State g root
  load := fun term => .eval term .nil
  step := fun state => (transition strategy state).map Prod.snd

theorem answer_final {g : Signature} (strategy : Strategy g) {root : g.Kind}
    (state : State g root) (value : g.Value root) (observed : answer state = some value) :
    (core strategy root).step state = none := by
  cases state with
  | eval => cases observed
  | ret value context => cases context <;> simp_all [answer, core, transition]

abbrev answerCore {g : Signature} (strategy : Strategy g) (root : g.Kind) :
    AnswerMachineCore g.Term (g.Value root) where
  toMachineCore := core strategy root
  answer := answer
  answer_final := answer_final strategy

/-- Contextual closure of the language's contraction relation, independent
of the machine's traversal and inspection functions. -/
inductive SourceStep {g : Signature} (strategy : Strategy g) : g.Kind → g.Term → g.Term → Prop where
  | contract {kind : g.Kind} (redex : g.Redex kind) (term : g.Term)
      (contracts : strategy.contract redex = some term) :
      SourceStep strategy kind (g.redexTerm redex) term
  | frame {outer inner : g.Kind} (frame : g.Frame outer inner) {first second : g.Term}
      (step : SourceStep strategy inner first second) :
      SourceStep strategy outer (g.plugFrame frame first) (g.plugFrame frame second)

theorem SourceStep.context {g : Signature} {strategy : Strategy g} {root kind : g.Kind}
    (context : Context g root kind) {first second : g.Term}
    (step : SourceStep strategy kind first second) :
    SourceStep strategy root (context.plug first) (context.plug second) := by
  induction context generalizing first second with
  | nil => exact step
  | cons rest frame ih => exact ih (.frame frame step)

theorem advance_sound {g : Signature} (strategy : Strategy g) {root kind : g.Kind}
    (context : Context g root kind) (decision : Decision g kind)
    {computational : Bool} {next : State g root}
    (stepped : advance strategy context decision = some (computational, next)) :
    if computational then
      SourceStep strategy root (context.plug decision.reconstruct) next.readback
    else context.plug decision.reconstruct = next.readback := by
  cases decision with
  | value value => cases stepped; rfl
  | descend term frame => cases stepped; rfl
  | blocked term => cases stepped
  | redex redex =>
      cases contracts : strategy.contract redex with
      | none => simp [advance, contracts] at stepped
      | some term =>
          simp only [advance, contracts, Option.map_some, Option.some.injEq, Prod.mk.injEq] at stepped
          rcases stepped with ⟨rfl, rfl⟩
          exact SourceStep.context context (.contract redex term contracts)

/-- Administrative steps preserve readback; computational steps are
actual contextual contractions, including contractions back to themselves. -/
theorem transition_sound {g : Signature} (strategy : Strategy g) {root : g.Kind}
    {state next : State g root} {computational : Bool}
    (stepped : transition strategy state = some (computational, next)) :
    if computational then SourceStep strategy root state.readback next.readback
    else state.readback = next.readback := by
  cases state with
  | eval term context =>
      have sound := advance_sound strategy context (strategy.inspect _ term) stepped
      simpa only [strategy.inspect_correct, State.readback] using sound
  | ret value context =>
      cases context with
      | nil => cases stepped
      | cons context frame =>
          have sound := advance_sound strategy context (strategy.resume frame value) stepped
          simpa only [strategy.resume_correct, State.readback, Context.plug_cons] using sound

theorem core_step_sound {g : Signature} (strategy : Strategy g) {root : g.Kind}
    {state next : State g root} (stepped : (core strategy root).StepRel state next) :
    Relation.ReflTransGen (SourceStep strategy root) state.readback next.readback := by
  change (transition strategy state).map Prod.snd = some next at stepped
  obtain ⟨⟨computational, target⟩, advanced, same⟩ := Option.map_eq_some_iff.mp stepped
  cases same
  have sound := transition_sound strategy advanced
  cases computational with
  | false => rw [show state.readback = target.readback from sound]
  | true => exact .single sound

/-- Every finite machine execution reads back to a finite source execution.
The reverse tracing direction is a separate strategy-completeness obligation. -/
theorem core_steps_sound {g : Signature} (strategy : Strategy g) {root : g.Kind}
    {state final : State g root} (ran : (core strategy root).Steps state final) :
    Relation.ReflTransGen (SourceStep strategy root) state.readback final.readback := by
  induction ran with
  | refl => exact .refl
  | tail _ last ih => exact ih.trans (core_step_sound strategy last)

/-- Choose a contraction observer before constructing its event. Navigation
and retained states are shared; a coarse observer need not materialize source
terms. Its own encoding cost is separate from the state-based instruction
prices used by the common machine interface. -/
abbrev machineWithObserver {g : Signature} {Event : Type}
    (strategy : Strategy g) (root : g.Kind)
    (observe : State g root → State g root → Event) :
    Machine (State g root) Event (g.Value root) Empty where
  step state :=
    match transition strategy state with
    | some (false, next) => some (.silent next)
    | some (true, next) => some (.publish [observe state next] next)
    | none => (answer state).map Transition.finish

def machine {g : Signature} (strategy : Strategy g) (root : g.Kind) :
    Machine (State g root) (g.Term × g.Term) (g.Value root) Empty :=
  machineWithObserver strategy root fun state next => (state.readback, next.readback)

/-- Observing a projection of a contraction event agrees with the existing
event-machine relabeling. The projected factory does not first build the richer
event, and neither construction changes the transition or retained state. -/
theorem machineWithObserver_relabel {g : Signature} {Event View : Type}
    (strategy : Strategy g) (root : g.Kind)
    (observe : State g root → State g root → Event) (project : Event → View) :
    machineWithObserver strategy root (fun state next => project (observe state next)) =
      (machineWithObserver strategy root observe).relabel project id id := by
  apply congrArg (fun step => (⟨step⟩ : Machine (State g root) View (g.Value root) Empty))
  funext state
  cases advanced : transition strategy state with
  | none =>
      cases observed : answer state <;>
        simp [advanced, observed, Transition.relabel]
  | some result =>
      rcases result with ⟨computational, next⟩
      cases computational <;> simp [advanced, Transition.relabel]

/-- The observer keeps contraction occurrences and erases administrative
occurrences. It reads the transition tag, not equality of reconstructed terms. -/
def observeOccurrence {g : Signature} (strategy : Strategy g) {root : g.Kind}
    (occurrence : State g root × State g root) : Option (g.Term × g.Term) :=
  match transition strategy occurrence.1 with
  | some (true, _) => some (occurrence.1.readback, occurrence.2.readback)
  | _ => none

/-- The source-step observer and the existing core adapter have exactly the
same bounded outcomes and residuals. Their traces differ by the constructed
occurrence observer alone. Order and repeated contractions are retained. -/
theorem run_core_observer {g : Signature} (strategy : Strategy g) (root : g.Kind)
    (fuel : Nat) (state : State g root) :
    (machine strategy root).run fuel state =
      let observed := (ProductiveCoreAdapters.answerMachine (answerCore strategy root)).run fuel state
      (observed.1.filterMap (observeOccurrence strategy), observed.2) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases advanced : transition strategy state with
      | some result =>
          rcases result with ⟨computational, next⟩
          have coreStep : (core strategy root).StepRel state next := by
            simp [MachineCore.StepRel, core, advanced]
          have adapterStep := ProductiveCoreAdapters.answer_step (answerCore strategy root) coreStep
          cases computational with
          | false =>
              have machineStep : (machine strategy root).step state = some (.silent next) := by
                simp [machine, advanced]
              simp only [Machine.run, machineStep, adapterStep, List.singleton_append]
              rw [ih]
              rw [List.filterMap_cons]
              simp only [observeOccurrence, advanced]
          | true =>
              have machineStep : (machine strategy root).step state =
                  some (.publish [(state.readback, next.readback)] next) := by
                simp [machine, advanced]
              simp only [Machine.run, machineStep, adapterStep, List.singleton_append]
              rw [ih]
              rw [List.filterMap_cons]
              simp only [observeOccurrence, advanced]
      | none =>
          have coreStopped : (core strategy root).step state = none := by simp [core, advanced]
          cases observed : answer state with
          | some value =>
              have adapterStep := ProductiveCoreAdapters.observed_finish
                (answerCore strategy root) observed
              simp only [Machine.run, machine, advanced, observed, Option.map_some, adapterStep]
              rfl
          | none =>
              have adapterStep := ProductiveCoreAdapters.unobserved_stuck
                (answerCore strategy root) observed coreStopped
              simp only [Machine.run, machine, advanced, observed, Option.map_none, adapterStep]
              rfl

/-- Any state-based instruction price agrees with the existing core adapter.
Erasing an administrative observation does not erase its execution cost. -/
theorem spent_core_agreement {g : Signature} (strategy : Strategy g) (root : g.Kind)
    (price : State g root → Nat) (fuel : Nat) (state : State g root) :
    (machine strategy root).spent price fuel state =
      (ProductiveCoreAdapters.answerMachine (answerCore strategy root)).spent price fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases advanced : transition strategy state with
      | some result =>
          rcases result with ⟨computational, next⟩
          have coreStep : (core strategy root).StepRel state next := by
            simp [MachineCore.StepRel, core, advanced]
          have adapterStep := ProductiveCoreAdapters.answer_step (answerCore strategy root) coreStep
          cases computational with
          | false =>
              have machineStep : (machine strategy root).step state = some (.silent next) := by
                simp [machine, advanced]
              simp only [Machine.spent, machineStep, adapterStep, ih]
          | true =>
              have machineStep : (machine strategy root).step state =
                  some (.publish [(state.readback, next.readback)] next) := by
                simp [machine, advanced]
              simp only [Machine.spent, machineStep, adapterStep, ih]
      | none =>
          have coreStopped : (core strategy root).step state = none := by simp [core, advanced]
          cases observed : answer state with
          | some value =>
              have adapterStep := ProductiveCoreAdapters.observed_finish
                (answerCore strategy root) observed
              simp [Machine.spent, machine, advanced, observed, adapterStep]
          | none =>
              have adapterStep := ProductiveCoreAdapters.unobserved_stuck
                (answerCore strategy root) observed coreStopped
              simp [Machine.spent, machine, advanced, observed, adapterStep]

theorem outcome_core_agreement {g : Signature} (strategy : Strategy g) (root : g.Kind)
    (fuel : Nat) (state : State g root) :
    ((machine strategy root).run fuel state).2 =
      ((ProductiveCoreAdapters.answerMachine (answerCore strategy root)).run fuel state).2 :=
  congrArg Prod.snd (run_core_observer strategy root fuel state)

theorem divergence_core_agreement {g : Signature} (strategy : Strategy g) (root : g.Kind)
    (state : State g root) :
    (machine strategy root).DivergesWithin state ↔
      (ProductiveCoreAdapters.answerMachine (answerCore strategy root)).DivergesWithin state := by
  constructor
  · intro diverges fuel
    obtain ⟨residual, pending⟩ := diverges fuel
    exact ⟨residual, (outcome_core_agreement strategy root fuel state).symm.trans pending⟩
  · intro diverges fuel
    obtain ⟨residual, pending⟩ := diverges fuel
    exact ⟨residual, (outcome_core_agreement strategy root fuel state).trans pending⟩

theorem produces_iff_finished {g : Signature} (strategy : Strategy g) (root : g.Kind)
    (term : g.Term) (value : g.Value root) :
    (answerCore strategy root).Produces term value ↔
      ∃ fuel events, (machine strategy root).run fuel (.eval term .nil) =
        (events, .finished value) := by
  constructor
  · intro produces
    obtain ⟨fuel, events, ran⟩ :=
      (ProductiveCoreAdapters.produces_iff_finished (answerCore strategy root) term value).mp produces
    refine ⟨fuel, events.filterMap (observeOccurrence strategy), ?_⟩
    rw [run_core_observer, ran]
  · rintro ⟨fuel, events, ran⟩
    apply (ProductiveCoreAdapters.produces_iff_finished (answerCore strategy root) term value).mpr
    refine ⟨fuel, ((ProductiveCoreAdapters.answerMachine (answerCore strategy root)).run fuel
      (.eval term .nil)).1, ?_⟩
    apply Prod.ext
    · rfl
    · exact (outcome_core_agreement strategy root fuel (.eval term .nil)).symm.trans
        (congrArg Prod.snd ran)

/-- Local remaining-work credits for inspection and continuation dispatch.
There is deliberately no decreasing condition on contraction. -/
structure SearchCredits {g : Signature} (strategy : Strategy g) where
  term : g.Kind → g.Term → Nat
  frame : {outer inner : g.Kind} → g.Frame outer inner → Nat
  inspect_value : ∀ kind input value, strategy.inspect kind input = .value value → 0 < term kind input
  inspect_descend : ∀ outer input inner child (context : g.Frame outer inner),
    strategy.inspect outer input = .descend child context →
    term inner child + frame context < term outer input
  resume_value : ∀ outer inner (context : g.Frame outer inner) value result,
    strategy.resume context value = .value result → 0 < frame context
  resume_descend : ∀ outer inner next (context : g.Frame outer inner) value child
      (following : g.Frame outer next),
    strategy.resume context value = .descend child following →
    term next child + frame following < frame context

def SearchCredits.context {g : Signature} {strategy : Strategy g} (credits : SearchCredits strategy)
    {root : g.Kind} : {kind : g.Kind} → Context g root kind → Nat
  | _, .nil => 0
  | _, .cons rest frame => credits.context rest + credits.frame frame

def SearchCredits.work {g : Signature} {strategy : Strategy g} (credits : SearchCredits strategy)
    {root : g.Kind} : State g root → Nat
  | .eval (kind := kind) term context => credits.term kind term + credits.context context
  | .ret _ context => credits.context context

theorem SearchCredits.administration_decreases {g : Signature} {strategy : Strategy g}
    (credits : SearchCredits strategy) {root : g.Kind} {state next : State g root}
    (stepped : transition strategy state = some (false, next)) : credits.work next < credits.work state := by
  cases state with
  | @eval kind term context =>
      cases inspected : strategy.inspect kind term with
      | value value =>
          simp only [transition, inspected, advance, Option.some.injEq, Prod.mk.injEq] at stepped
          rcases stepped with ⟨_, rfl⟩
          have progress := credits.inspect_value _ term value inspected
          simp only [SearchCredits.work]
          omega
      | descend child frame =>
          simp only [transition, inspected, advance, Option.some.injEq, Prod.mk.injEq] at stepped
          rcases stepped with ⟨_, rfl⟩
          have progress := credits.inspect_descend _ term _ child frame inspected
          simp only [SearchCredits.work, SearchCredits.context]
          omega
      | redex redex =>
          cases contracts : strategy.contract redex <;> simp [transition, inspected, advance, contracts] at stepped
      | blocked term => simp [transition, inspected, advance] at stepped
  | ret value context =>
      cases context with
      | nil => cases stepped
      | cons rest frame =>
          cases resumed : strategy.resume frame value with
          | value result =>
              simp only [transition, resumed, advance, Option.some.injEq, Prod.mk.injEq] at stepped
              rcases stepped with ⟨_, rfl⟩
              have progress := credits.resume_value _ _ frame value result resumed
              simp only [SearchCredits.work, SearchCredits.context]
              omega
          | descend child following =>
              simp only [transition, resumed, advance, Option.some.injEq, Prod.mk.injEq] at stepped
              rcases stepped with ⟨_, rfl⟩
              have progress := credits.resume_descend _ _ _ frame value child following resumed
              simp only [SearchCredits.work, SearchCredits.context]
              omega
          | redex redex =>
              cases contracts : strategy.contract redex <;> simp [transition, resumed, advance, contracts] at stepped
          | blocked term => simp [transition, resumed, advance] at stepped

/-- Local search credits and a separate no-stuckness proof construct the
existing common productivity certificate. Credits alone do not exclude
stuck states, and neither premise requires contractions to terminate. -/
def SearchCredits.productive {g : Signature} {strategy : Strategy g}
    (credits : SearchCredits strategy) (root : g.Kind)
    (moves : ∀ state, (machine strategy root).step state ≠ none) :
    (machine strategy root).Productive where
  rank := credits.work
  silent_decreases := by
    intro state next stepped
    cases advanced : transition strategy state with
    | none =>
        cases observed : answer state <;> simp [machine, advanced, observed] at stepped
    | some result =>
        rcases result with ⟨computational, target⟩
        cases computational with
        | true => simp [machine, advanced] at stepped
        | false =>
            simp only [machine, advanced, Option.some.injEq, Transition.silent.injEq] at stepped
            subst next
            exact credits.administration_decreases advanced
  moves := moves

theorem SearchCredits.no_infinite_administration {g : Signature} {strategy : Strategy g}
    (credits : SearchCredits strategy) {root : g.Kind} (states : Nat → State g root) :
    ¬ (∀ n, transition strategy (states n) = some (false, states (n + 1))) := by
  intro steps
  have bounded : ∀ n, credits.work (states n) + n ≤ credits.work (states 0) := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
        have progress := credits.administration_decreases (steps n)
        omega
  have impossible := bounded (credits.work (states 0) + 1)
  omega

/-- A diverging execution reaches its next genuine contraction within the
current search credits plus one transition. Its complete residual is retained,
and the published occurrence is an independently defined source step. -/
theorem SearchCredits.next_contraction {g : Signature} {strategy : Strategy g}
    (credits : SearchCredits strategy) {root : g.Kind} (state : State g root)
    (diverges : (machine strategy root).DivergesWithin state) :
    ∃ fuel final, fuel ≤ credits.work state + 1 ∧
      (machine strategy root).run fuel state =
        ([(state.readback, final.readback)], .exhausted final) ∧
      SourceStep strategy root state.readback final.readback := by
  have search : ∀ work, ∀ state : State g root, credits.work state = work →
      (machine strategy root).DivergesWithin state →
      ∃ fuel final, fuel ≤ credits.work state + 1 ∧
        (machine strategy root).run fuel state =
          ([(state.readback, final.readback)], .exhausted final) ∧
        SourceStep strategy root state.readback final.readback := by
    intro work
    induction work using Nat.strong_induction_on with
    | h work ih =>
        intro state same diverges
        cases advanced : transition strategy state with
        | none =>
            obtain ⟨residual, pending⟩ := diverges 1
            cases observed : answer state <;>
              simp [Machine.run, machine, advanced, observed] at pending
        | some result =>
            rcases result with ⟨computational, next⟩
            cases computational with
            | true =>
                refine ⟨1, next, by omega, ?_, transition_sound strategy advanced⟩
                simp [Machine.run, machine, advanced]
            | false =>
                have paused : (machine strategy root).run 1 state = ([], .exhausted next) := by
                  simp [Machine.run, machine, advanced]
                have nextDiverges := diverges.resume (machine strategy root) paused
                have decreases := credits.administration_decreases advanced
                obtain ⟨fuel, final, bound, ran, contracted⟩ :=
                  ih (credits.work next) (by omega) next rfl nextDiverges
                have readback : state.readback = next.readback := transition_sound strategy advanced
                refine ⟨fuel + 1, final, by omega, ?_, ?_⟩
                · simpa [Machine.run, machine, advanced, readback] using ran
                · exact readback ▸ contracted
  exact search (credits.work state) state rfl diverges

/-- Productive divergence cannot disappear when the observer erases navigation.
Every finite number of contraction occurrences has an exact retained prefix;
equal source/target terms and repeated occurrences are counted separately. -/
theorem SearchCredits.divergence_has_event_prefixes {g : Signature} {strategy : Strategy g}
    (credits : SearchCredits strategy) {root : g.Kind} (state : State g root)
    (diverges : (machine strategy root).DivergesWithin state) (count : Nat) :
    ∃ fuel events final, events.length = count ∧
      (machine strategy root).run fuel state = (events, .exhausted final) := by
  induction count generalizing state with
  | zero => exact ⟨0, [], state, rfl, rfl⟩
  | succ count ih =>
      obtain ⟨first, residual, _, published, _⟩ := credits.next_contraction state diverges
      obtain ⟨later, events, final, length, rest⟩ :=
        ih residual (diverges.resume (machine strategy root) published)
      refine ⟨first + later, (state.readback, residual.readback) :: events, final, ?_, ?_⟩
      · simp [length]
      · rw [(machine strategy root).run_add, published]
        simp [Machine.continueRun, rest]



theorem event_count_le_fuel {g : Signature} (strategy : Strategy g) (root : g.Kind)
    (fuel : Nat) (state : State g root) :
    ((machine strategy root).run fuel state).1.length ≤ fuel := by
  rw [run_core_observer]
  exact (List.length_filterMap_le _ _).trans
    (ProductiveCoreAdapters.answer_occurrences_le_budget (answerCore strategy root) fuel state)

/-- Exact prefixes with every finite event count imply that no finite run
has terminated or become stuck. This direction does not need search credits. -/
theorem diverges_of_event_prefixes {g : Signature} (strategy : Strategy g) (root : g.Kind)
    (state : State g root)
    (prefixes : ∀ count : Nat, ∃ fuel events final, events.length = count ∧
      (machine strategy root).run fuel state = (events, .exhausted final)) :
    (machine strategy root).DivergesWithin state := by
  intro budget
  obtain ⟨fuel, events, final, length, ran⟩ := prefixes budget
  have lower : budget ≤ fuel := by
    have bound := event_count_le_fuel strategy root fuel state
    simpa [ran, length] using bound
  have split : (machine strategy root).run fuel state =
      (machine strategy root).continueRun (fuel - budget)
        ((machine strategy root).run budget state) := by
    rw [← (machine strategy root).run_add]
    congr 1
    omega
  cases before : (machine strategy root).run budget state with
  | mk published outcome =>
      cases outcome with
      | exhausted residual => exact ⟨residual, rfl⟩
      | _ => simp [before, Machine.continueRun, ran] at split

theorem SearchCredits.divergence_iff_event_prefixes {g : Signature} {strategy : Strategy g}
    (credits : SearchCredits strategy) {root : g.Kind} (state : State g root) :
    (machine strategy root).DivergesWithin state ↔
      ∀ count : Nat, ∃ fuel events final, events.length = count ∧
        (machine strategy root).run fuel state = (events, .exhausted final) :=
  ⟨fun diverges count => credits.divergence_has_event_prefixes state diverges count,
    diverges_of_event_prefixes strategy root state⟩

/-- Search credits turn machine divergence into a genuine infinite source
reduction. The source relation is the independently defined contextual closure
of contraction, and consecutive terms need not be unequal. -/
theorem SearchCredits.divergence_has_source_reduction {g : Signature} {strategy : Strategy g}
    (credits : SearchCredits strategy) {root : g.Kind} (state : State g root)
    (diverges : (machine strategy root).DivergesWithin state) :
    ∃ terms : Nat → g.Term, terms 0 = state.readback ∧
      ∀ n, SourceStep strategy root (terms n) (terms (n + 1)) := by
  let Diverging := { state : State g root // (machine strategy root).DivergesWithin state }
  have successor : ∀ current : Diverging, ∃ next : Diverging,
      SourceStep strategy root current.val.readback next.val.readback := by
    intro current
    obtain ⟨fuel, next, _, ran, contracted⟩ :=
      credits.next_contraction current.val current.property
    exact ⟨⟨next, current.property.resume (machine strategy root) ran⟩, contracted⟩
  choose next advances using successor
  let states : Nat → Diverging := Nat.rec ⟨state, diverges⟩ (fun _ previous => next previous)
  exact ⟨fun n => (states n).val.readback, rfl, fun n => advances (states n)⟩


/-- Reverse tracing is constructed from source determinacy and terminal
normality. Neither hypothesis supplies machine paths or correspondence. Each
source contraction produces exactly one event, within the local search bound. -/
theorem SearchCredits.trace_source_step {g : Signature} {strategy : Strategy g}
    (credits : SearchCredits strategy) (root : g.Kind)
    (determinate : ∀ first second third, SourceStep strategy root first second →
      SourceStep strategy root first third → second = third)
    (normal : ∀ state : State g root, transition strategy state = none →
      ∀ target, ¬ SourceStep strategy root state.readback target)
    (state : State g root) (target : g.Term)
    (source : SourceStep strategy root state.readback target) :
    ∃ fuel final, 0 < fuel ∧ fuel ≤ credits.work state + 1 ∧
      (machine strategy root).run fuel state =
        ([(state.readback, target)], .exhausted final) ∧ final.readback = target := by
  have search : ∀ work, ∀ state : State g root, credits.work state = work →
      ∀ target, SourceStep strategy root state.readback target →
      ∃ fuel final, 0 < fuel ∧ fuel ≤ credits.work state + 1 ∧
        (machine strategy root).run fuel state =
          ([(state.readback, target)], .exhausted final) ∧ final.readback = target := by
    intro work
    induction work using Nat.strong_induction_on with
    | h work ih =>
        intro state same target source
        cases advanced : transition strategy state with
        | none => exact False.elim (normal state advanced target source)
        | some result =>
            rcases result with ⟨computational, next⟩
            cases computational with
            | true =>
                have readback := determinate _ _ _ (transition_sound strategy advanced) source
                refine ⟨1, next, by omega, by omega, ?_, readback⟩
                simp [Machine.run, machine, advanced, readback]
            | false =>
                have readback : state.readback = next.readback := transition_sound strategy advanced
                have nextSource : SourceStep strategy root next.readback target := by
                  simpa only [readback] using source
                have decreases := credits.administration_decreases advanced
                obtain ⟨fuel, final, positive, bound, ran, finalReadback⟩ :=
                  ih (credits.work next) (by omega) next rfl target nextSource
                refine ⟨fuel + 1, final, by omega, by omega, ?_, finalReadback⟩
                simpa [Machine.run, machine, advanced, readback] using ran
  exact search (credits.work state) state rfl target source

/-- Every finite source path has an exact machine trace with the same ordered
contraction occurrences and a complete retained residual. Repeated terms are
retained as distinct events; no source termination hypothesis is used. -/
theorem SearchCredits.trace_source_path {g : Signature} {strategy : Strategy g}
    (credits : SearchCredits strategy) (root : g.Kind)
    (determinate : ∀ first second third, SourceStep strategy root first second →
      SourceStep strategy root first third → second = third)
    (normal : ∀ state : State g root, transition strategy state = none →
      ∀ target, ¬ SourceStep strategy root state.readback target)
    (state : State g root) (targets : List g.Term)
    (source : List.IsChain (SourceStep strategy root) (state.readback :: targets)) :
    ∃ fuel final, (machine strategy root).run fuel state =
      ((state.readback :: targets).zip targets, .exhausted final) ∧
      final.readback = targets.getLastD state.readback := by
  induction targets generalizing state with
  | nil => exact ⟨0, state, rfl, rfl⟩
  | cons target rest ih =>
      rcases List.isChain_cons_cons.mp source with ⟨firstStep, restSteps⟩
      obtain ⟨first, middle, _, _, firstRun, readback⟩ :=
        credits.trace_source_step root determinate normal state target firstStep
      have remaining : List.IsChain (SourceStep strategy root) (middle.readback :: rest) := by
        simpa only [readback] using restSteps
      obtain ⟨later, final, restRun, finalReadback⟩ := ih middle remaining
      refine ⟨first + later, final, ?_, ?_⟩
      · rw [(machine strategy root).run_add, firstRun]
        simp [Machine.continueRun, restRun, readback]
      · simpa only [List.getLastD_cons, readback] using finalReadback

/-- The actual event-machine residual is the ordered core's bounded walk.
Answer polling is not confused with a transition or with budget exhaustion. -/
theorem walk_of_exhausted {g : Signature} (strategy : Strategy g) (root : g.Kind)
    {fuel : Nat} {state final : State g root} {events : List (g.Term × g.Term)}
    (paused : (machine strategy root).run fuel state = (events, .exhausted final)) :
    ProductiveCoreOrdered.walk (core strategy root) fuel state = final := by
  induction fuel generalizing state events with
  | zero =>
      simp only [Machine.run, Prod.mk.injEq, Outcome.exhausted.injEq] at paused
      exact paused.2
  | succ fuel ih =>
      cases advanced : transition strategy state with
      | none =>
          cases observed : answer state <;>
            simp [Machine.run, machine, advanced, observed] at paused
      | some result =>
          rcases result with ⟨computational, next⟩
          have nextPaused : (machine strategy root).run fuel next =
              (((machine strategy root).run fuel next).1, .exhausted final) := by
            apply Prod.ext
            · rfl
            have outcome := congrArg Prod.snd paused
            cases computational <;>
              simpa [Machine.run, machine, advanced] using outcome
          simpa only [ProductiveCoreOrdered.walk, core, advanced, Option.map_some] using ih nextPaused

/-- Sufficient service reaches the exact source-path boundary in each reserved
slot. Equal-looking initial states remain separate occurrences. No service
clock or machine path is assumed: both are constructed from the source paths. -/
theorem SearchCredits.scheduled_source_paths {g : Signature} {strategy : Strategy g}
    (credits : SearchCredits strategy) (root : g.Kind)
    (determinate : ∀ first second third, SourceStep strategy root first second →
      SourceStep strategy root first third → second = third)
    (normal : ∀ state : State g root, transition strategy state = none →
      ∀ target, ¬ SourceStep strategy root state.readback target)
    {n : Nat} (states : Fin n → State g root) (targets : Fin n → List g.Term)
    (paths : ∀ id, List.IsChain (SourceStep strategy root) ((states id).readback :: targets id)) :
    ∃ clocks : Fin n → Nat, ∀ schedule : List
        (Mettapedia.GSLT.Distinction.ScheduledFrontier.Command n),
      (∀ id, clocks id ≤ Mettapedia.Machines.Cursor.Scheduling.allocation id schedule) →
      (Mettapedia.GSLT.Distinction.ScheduledFrontier.view
        (Mettapedia.GSLT.Distinction.ScheduledFrontier.execute
          (ProductiveCoreOrdered.orderedCore (core strategy root)) schedule
          (Mettapedia.GSLT.Distinction.ScheduledFrontier.reserve clocks
            (fun id => [states id])))).map State.readback =
        List.ofFn (fun id => (targets id).getLastD (states id).readback) := by
  have traced := fun id => credits.trace_source_path root determinate normal
    (states id) (targets id) (paths id)
  choose clocks finals runs readbacks using traced
  refine ⟨clocks, ?_⟩
  intro schedule enough
  rw [Mettapedia.GSLT.Distinction.ScheduledFrontier.view_enough _ schedule clocks
    (fun id => [states id]) enough]
  have frontiers : (fun id => (ProductiveCoreOrdered.orderedCore (core strategy root)).runFrontier
      (clocks id) [states id]) = (fun id => [finals id]) := by
    funext id
    exact (ProductiveCoreOrdered.ordered_frontier_walk (core strategy root) (clocks id)
      [states id]).trans (by
        change [ProductiveCoreOrdered.walk (core strategy root) (clocks id) (states id)] = [finals id]
        exact congrArg (fun state => [state]) (walk_of_exhausted strategy root (runs id)))
  rw [frontiers]
  have singletonLists : List.ofFn (fun id => [finals id]) =
      (List.ofFn finals).map (fun state => [state]) := by rw [List.map_ofFn]; rfl
  rw [singletonLists, ← List.flatMap_def, List.flatMap_singleton', List.map_ofFn]
  apply congrArg List.ofFn
  funext id
  exact readbacks id

/-- A finite schedule realizes every finite family of independent source paths.
The clocks and the schedule are derived, including for paths inside a diverging
computation; an answer or source-termination assumption is unnecessary. -/
theorem SearchCredits.scheduled_source_realization {g : Signature} {strategy : Strategy g}
    (credits : SearchCredits strategy) (root : g.Kind)
    (determinate : ∀ first second third, SourceStep strategy root first second →
      SourceStep strategy root first third → second = third)
    (normal : ∀ state : State g root, transition strategy state = none →
      ∀ target, ¬ SourceStep strategy root state.readback target)
    {n : Nat} (states : Fin n → State g root) (targets : Fin n → List g.Term)
    (paths : ∀ id, List.IsChain (SourceStep strategy root) ((states id).readback :: targets id)) :
    ∃ clocks : Fin n → Nat, ∃ schedule : List
        (Mettapedia.GSLT.Distinction.ScheduledFrontier.Command n),
      (Mettapedia.GSLT.Distinction.ScheduledFrontier.view
        (Mettapedia.GSLT.Distinction.ScheduledFrontier.execute
          (ProductiveCoreOrdered.orderedCore (core strategy root)) schedule
          (Mettapedia.GSLT.Distinction.ScheduledFrontier.reserve clocks
            (fun id => [states id])))).map State.readback =
        List.ofFn (fun id => (targets id).getLastD (states id).readback) := by
  obtain ⟨clocks, realized⟩ := credits.scheduled_source_paths root determinate normal states targets paths
  obtain ⟨count, bound⟩ := Finite.exists_le clocks
  refine ⟨clocks, Mettapedia.GSLT.Distinction.ScheduledFrontier.rounds 1 count, realized _ ?_⟩
  intro id
  simpa only [Mettapedia.GSLT.Distinction.ScheduledFrontier.rounds_allocation, Nat.mul_one] using bound id

/-- An infinite independent source reduction keeps the machine running.
The construction uses finite prefixes and does not assume source termination. -/
theorem SearchCredits.diverges_of_source_reduction {g : Signature} {strategy : Strategy g}
    (credits : SearchCredits strategy) (root : g.Kind)
    (determinate : ∀ first second third, SourceStep strategy root first second →
      SourceStep strategy root first third → second = third)
    (normal : ∀ state : State g root, transition strategy state = none →
      ∀ target, ¬ SourceStep strategy root state.readback target)
    (state : State g root) (terms : Nat → g.Term) (initial : terms 0 = state.readback)
    (advances : ∀ n, SourceStep strategy root (terms n) (terms (n + 1))) :
    (machine strategy root).DivergesWithin state := by
  apply diverges_of_event_prefixes strategy root state
  have prefixes : ∀ count index, ∀ current : State g root, current.readback = terms index →
      ∃ fuel events final, events.length = count ∧
        (machine strategy root).run fuel current = (events, .exhausted final) := by
    intro count
    induction count with
    | zero => intro index current _; exact ⟨0, [], current, rfl, rfl⟩
    | succ count ih =>
        intro index current readback
        have source : SourceStep strategy root current.readback (terms (index + 1)) := by
          rw [readback]
          exact advances index
        obtain ⟨first, middle, _, _, firstRun, nextReadback⟩ :=
          credits.trace_source_step root determinate normal current _ source
        obtain ⟨later, events, final, length, restRun⟩ :=
          ih (index + 1) middle nextReadback
        refine ⟨first + later, (current.readback, terms (index + 1)) :: events, final, ?_, ?_⟩
        · simp [length]
        · rw [(machine strategy root).run_add, firstRun]
          simp [Machine.continueRun, restRun]
  intro count
  exact prefixes count 0 state initial.symm

/-- Exact divergence correspondence under the same independently checkable
strategy conditions used for finite reverse tracing. -/
theorem SearchCredits.divergence_iff_source_reduction {g : Signature} {strategy : Strategy g}
    (credits : SearchCredits strategy) (root : g.Kind)
    (determinate : ∀ first second third, SourceStep strategy root first second →
      SourceStep strategy root first third → second = third)
    (normal : ∀ state : State g root, transition strategy state = none →
      ∀ target, ¬ SourceStep strategy root state.readback target)
    (state : State g root) :
    (machine strategy root).DivergesWithin state ↔
      ∃ terms : Nat → g.Term, terms 0 = state.readback ∧
        ∀ n, SourceStep strategy root (terms n) (terms (n + 1)) := by
  constructor
  · exact credits.divergence_has_source_reduction state
  · rintro ⟨terms, initial, advances⟩
    exact credits.diverges_of_source_reduction root determinate normal state terms initial advances

/-! ## Existing authored MeTTaIL contexts as the frame provider

This adapter preserves the existing frame-authority predicate. It does not
execute rule matching, instantiate metavariables, or discharge additional
premises on a rewrite rule. Those are obligations of a language's operational
strategy, not consequences of its context representation.
-/

namespace Authored

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.DerivedContexts

def signature (lang : LanguageDef) (Value Redex : String → Type)
    (valueTerm : {kind : String} → Value kind → Pattern)
    (redexTerm : {kind : String} → Redex kind → Pattern) : Signature where
  Term := Pattern
  Kind := String
  Frame outer inner := { context : OneHoleContext // AuthoredContextFrame lang inner outer context }
  Value := Value
  Redex := Redex
  plugFrame frame term := frame.val.fill term
  valueTerm := valueTerm
  redexTerm := redexTerm

variable {lang : LanguageDef} {Value Redex : String → Type}
  {valueTerm : {kind : String} → Value kind → Pattern}
  {redexTerm : {kind : String} → Redex kind → Pattern}

def decode {root : String} : {kind : String} →
    Context (signature lang Value Redex @valueTerm @redexTerm) root kind →
    OneHoleContext
  | _, .nil => .hole
  | _, .cons rest frame => (decode rest).comp frame.val

theorem decode_plug {root kind : String}
    (context : Context (signature lang Value Redex @valueTerm @redexTerm) root kind)
    (term : Pattern) : (decode context).fill term = context.plug term := by
  induction context generalizing term with
  | nil => rfl
  | cons rest frame ih =>
      simp only [decode, OneHoleContext.fill_comp]
      exact ih (frame.val.fill term)

theorem decode_comp {outer middle inner : String}
    (first : Context (signature lang Value Redex @valueTerm @redexTerm) outer middle)
    (second : Context (signature lang Value Redex @valueTerm @redexTerm) middle inner) :
    decode (first.comp second) = (decode first).comp (decode second) := by
  induction second with
  | nil =>
      change decode first = (decode first).comp .hole
      exact (OneHoleContext.comp_hole _).symm
  | cons rest frame ih =>
      change (decode (first.comp rest)).comp frame.val =
        (decode first).comp ((decode rest).comp frame.val)
      rw [ih, OneHoleContext.comp_assoc]

theorem decode_admissible {root kind : String}
    (context : Context (signature lang Value Redex @valueTerm @redexTerm) root kind) :
    AdmissibleContext lang kind root (decode context) := by
  induction context with
  | nil => exact .hole _
  | @cons middle inner rest frame ih =>
      have licensed : AdmissibleContext lang inner middle frame.val := by
        simpa only [OneHoleContext.comp_hole] using
          (AdmissibleContext.comp frame.property (.hole _))
      exact ih.compose licensed

/-- Every context generated by authored frames has a typed stack witness.
No quotient by term equality or by result value is taken. -/
theorem of_admissible {root kind : String} {context : OneHoleContext}
    (licensed : AdmissibleContext lang kind root context) :
    ∃ stack : Context (signature lang Value Redex @valueTerm @redexTerm) root kind,
      decode stack = context := by
  induction licensed with
  | hole => exact ⟨.nil, rfl⟩
  | @comp middle target outer inner frame rest ih =>
      obtain ⟨stack, decoded⟩ := ih
      let first : Context (signature lang Value Redex @valueTerm @redexTerm) target middle :=
        Quiver.Path.nil.cons ⟨outer, frame⟩
      refine ⟨first.comp stack, ?_⟩
      rw [decode_comp, decoded]
      rfl

end Authored

end Mettapedia.Machines.Refocusing
