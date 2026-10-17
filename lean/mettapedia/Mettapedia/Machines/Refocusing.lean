import Mathlib.Combinatorics.Quiver.Path
import Mettapedia.Machines.ProductiveCoreAdapters
import Mettapedia.Machines.ProductiveCoreOrdered
import Mettapedia.OSLF.MeTTaIL.DerivedContexts
import Mettapedia.GSLT.Distinction.OrderedAdministration
import Mettapedia.GSLT.Distinction.FrontierObservation
import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.GSLT.Contracts.AdministrationJoins

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

Ordered branching strategies share the traversal and replace the partial
contraction by ordered candidates, each yielding its ordered instantiations
(`BranchingStrategy`). The reduction semantics decomposes the whole term
independently (`Decomposition`); the machine refocuses in place. Inspection,
resumption and candidate attempts are administration, ranked by the
traversal's search credits; a rejected candidate is an empty block; the step
out of a focused redex, which enumerates its candidates in order, is the
observable step, and its successors are the candidates' instantiations, each
refocused in place to its next decision point. Local unique-decomposition
laws prove refocusing completeness (`refocusingComplete`), and the machine is
then a block simulation of the reduction semantics
(`BranchingStrategy.blockSimulation`). Complete ordered frontiers, pending
occurrences and outcomes, faults included, are related at every fuel
(`BranchingStrategy.frontiers`, `BranchingStrategy.outcomes`). Every observable
configuration is stable, and every erased dead end is a rejected candidate.
A deterministic strategy is the single-candidate case
(`Strategy.branching_source_iff`). Without frames the machine is an ordered
candidate scan at the root (`BranchingStrategy.root`); one layer of the authored
contextual rewriting engine is such a scan over the language's rules
(`Authored.ruleScan_simulation`).
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

/-- Executable local traversal data, with local readback equations: how a
term is inspected and how a returned value resumes its frame. Deterministic
and ordered branching strategies share it. -/
structure Traversal (g : Signature) where
  inspect : (kind : g.Kind) → g.Term → Decision g kind
  resume : {outer inner : g.Kind} → g.Frame outer inner → g.Value inner → Decision g outer
  inspect_correct : ∀ kind term, (inspect kind term).reconstruct = term
  resume_correct : ∀ {outer inner} (frame : g.Frame outer inner) value,
    (resume frame value).reconstruct = g.plugFrame frame (g.valueTerm value)

/-- A deterministic strategy: a traversal and a partial contraction. No
machine/source correspondence or termination theorem is assumed. -/
structure Strategy (g : Signature) extends Traversal g where
  contract : {kind : g.Kind} → g.Redex kind → Option g.Term

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
structure SearchCredits {g : Signature} (traversal : Traversal g) where
  term : g.Kind → g.Term → Nat
  frame : {outer inner : g.Kind} → g.Frame outer inner → Nat
  inspect_value : ∀ kind input value, traversal.inspect kind input = .value value → 0 < term kind input
  inspect_descend : ∀ outer input inner child (context : g.Frame outer inner),
    traversal.inspect outer input = .descend child context →
    term inner child + frame context < term outer input
  resume_value : ∀ outer inner (context : g.Frame outer inner) value result,
    traversal.resume context value = .value result → 0 < frame context
  resume_descend : ∀ outer inner next (context : g.Frame outer inner) value child
      (following : g.Frame outer next),
    traversal.resume context value = .descend child following →
    term next child + frame following < frame context

def SearchCredits.context {g : Signature} {traversal : Traversal g} (credits : SearchCredits traversal)
    {root : g.Kind} : {kind : g.Kind} → Context g root kind → Nat
  | _, .nil => 0
  | _, .cons rest frame => credits.context rest + credits.frame frame

def SearchCredits.work {g : Signature} {traversal : Traversal g} (credits : SearchCredits traversal)
    {root : g.Kind} : State g root → Nat
  | .eval (kind := kind) term context => credits.term kind term + credits.context context
  | .ret _ context => credits.context context

theorem SearchCredits.administration_decreases {g : Signature} {strategy : Strategy g}
    (credits : SearchCredits strategy.toTraversal) {root : g.Kind} {state next : State g root}
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
    (credits : SearchCredits strategy.toTraversal) (root : g.Kind)
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
    (credits : SearchCredits strategy.toTraversal) {root : g.Kind} (states : Nat → State g root) :
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
    (credits : SearchCredits strategy.toTraversal) {root : g.Kind} (state : State g root)
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
    (credits : SearchCredits strategy.toTraversal) {root : g.Kind} (state : State g root)
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
    (credits : SearchCredits strategy.toTraversal) {root : g.Kind} (state : State g root) :
    (machine strategy root).DivergesWithin state ↔
      ∀ count : Nat, ∃ fuel events final, events.length = count ∧
        (machine strategy root).run fuel state = (events, .exhausted final) :=
  ⟨fun diverges count => credits.divergence_has_event_prefixes state diverges count,
    diverges_of_event_prefixes strategy root state⟩

/-- Search credits turn machine divergence into a genuine infinite source
reduction. The source relation is the independently defined contextual closure
of contraction, and consecutive terms need not be unequal. -/
theorem SearchCredits.divergence_has_source_reduction {g : Signature} {strategy : Strategy g}
    (credits : SearchCredits strategy.toTraversal) {root : g.Kind} (state : State g root)
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
    (credits : SearchCredits strategy.toTraversal) (root : g.Kind)
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
    (credits : SearchCredits strategy.toTraversal) (root : g.Kind)
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
    (credits : SearchCredits strategy.toTraversal) (root : g.Kind)
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
    (credits : SearchCredits strategy.toTraversal) (root : g.Kind)
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
    (credits : SearchCredits strategy.toTraversal) (root : g.Kind)
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
    (credits : SearchCredits strategy.toTraversal) (root : g.Kind)
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

section Branching

open Mettapedia.GSLT.Distinction (OrderedSystem OrderedSimulation BlockSimulation)

/-! ## Ordered branching refocusing

The deterministic machine above contracts a focused redex to at most one term.
An ordered branching strategy keeps the traversal and tries an ordered list of
candidates at a focused redex; each candidate yields its ordered
instantiations, and a candidate with none is rejected. The reduction semantics
decomposes the whole term (`Decomposition`) independently of the machine; the
machine refocuses in place after every contraction.

Administration (inspection, resumption, candidate attempts) is ranked by the
traversal's `SearchCredits`. Saturation reads the machine at its decision
points: answers, focused redexes and blocked terms.
-/

/-- An ordered branching strategy: a traversal, and at each redex the ordered
candidates together with each candidate's ordered instantiations. A candidate
with no instantiation is a rejected candidate (a failed head match, say). -/
structure BranchingStrategy (g : Signature) (Candidate : Type) extends Traversal g where
  candidates : {kind : g.Kind} → g.Redex kind → List Candidate
  attempt : {kind : g.Kind} → g.Redex kind → Candidate → List g.Term

/-- A decomposition of a root term in a reduction semantics: a value, a redex
in a context, or a term the strategy blocks on, in a context. -/
inductive Decomposition (g : Signature) (root : g.Kind) where
  | value (value : g.Value root)
  | redex {kind : g.Kind} (context : Context g root kind) (redex : g.Redex kind)
  | blocked {kind : g.Kind} (context : Context g root kind) (term : g.Term)

def Decomposition.plug {g : Signature} {root : g.Kind} : Decomposition g root → g.Term
  | .value answer => g.valueTerm answer
  | .redex context focused => context.plug (g.redexTerm focused)
  | .blocked context stuck => context.plug stuck

/-- Unique decomposition, stated against the traversal's own decisions: a value
decomposes as itself, every redex in every context decomposes as that redex in
that context, and so does every term the traversal blocks on. -/
structure Traversal.UniqueDecomposition {g : Signature} (traversal : Traversal g) {root : g.Kind}
    (decompose : g.Term → Decomposition g root) : Prop where
  value : ∀ value : g.Value root, decompose (g.valueTerm value) = .value value
  redex : ∀ {kind : g.Kind} (context : Context g root kind) (redex : g.Redex kind),
    decompose (context.plug (g.redexTerm redex)) = .redex context redex
  inspect_blocked : ∀ {kind : g.Kind} (context : Context g root kind) (term blocked : g.Term),
    traversal.inspect kind term = .blocked blocked →
      decompose (context.plug blocked) = .blocked context blocked
  resume_blocked : ∀ {outer inner : g.Kind} (context : Context g root outer)
    (frame : g.Frame outer inner) (value : g.Value inner) (blocked : g.Term),
    traversal.resume frame value = .blocked blocked →
      decompose (context.plug blocked) = .blocked context blocked

/-- Configurations of the ordered branching machine: a traversal state, a
focused redex, a candidate attempt at a focused redex, or a blocked term. -/
inductive Configuration (g : Signature) (Candidate : Type) (root : g.Kind) where
  | search (state : State g root)
  | focus {kind : g.Kind} (context : Context g root kind) (redex : g.Redex kind)
  | attempt {kind : g.Kind} (context : Context g root kind) (redex : g.Redex kind)
      (candidate : Candidate)
  | blocked {kind : g.Kind} (context : Context g root kind) (term : g.Term)

namespace Configuration

variable {g : Signature} {Candidate : Type} {root : g.Kind}

def readback : Configuration g Candidate root → g.Term
  | .search state => state.readback
  | .focus context redex => context.plug (g.redexTerm redex)
  | .attempt context redex _ => context.plug (g.redexTerm redex)
  | .blocked context term => context.plug term

/-- Decision points: a returned answer, a focused redex, a blocked term. -/
def stable : Configuration g Candidate root → Bool
  | .search state => (answer state).isSome
  | .focus _ _ => true
  | .attempt _ _ _ => false
  | .blocked _ _ => true

/-- One local decision, placed in its context. -/
def dispatch {kind : g.Kind} (context : Context g root kind) :
    Decision g kind → Configuration g Candidate root
  | .value value => .search (.ret value context)
  | .redex redex => .focus context redex
  | .descend term frame => .search (.eval term (context.cons frame))
  | .blocked term => .blocked context term

/-- The loaded configuration of a term. -/
def load (term : g.Term) : Configuration g Candidate root :=
  .search (.eval term .nil)

theorem dispatch_readback {kind : g.Kind} (context : Context g root kind)
    (decision : Decision g kind) :
    (dispatch (Candidate := Candidate) context decision).readback =
      context.plug decision.reconstruct := by
  cases decision <;> rfl

end Configuration

namespace BranchingStrategy

variable {g : Signature} {Candidate : Type} (strategy : BranchingStrategy g Candidate)

/-- The ordered contracta of a redex: each candidate's instantiations, in
candidate order. -/
def contract {kind : g.Kind} (redex : g.Redex kind) : List g.Term :=
  (strategy.candidates redex).flatMap (strategy.attempt redex)

/-- The traversal as a deterministic strategy that never contracts: the
branching machine's traversal steps are exactly its administrative
transitions (`searchStep_transition`). -/
def searchOnly : Strategy g where
  toTraversal := strategy.toTraversal
  contract _ := none

/-- **The reduction semantics with ordered redex choices.** Decompose the whole
term; a redex steps to every candidate instantiation plugged back into its
context, in candidate order, duplicates kept. -/
def source {root : g.Kind} (decompose : g.Term → Decomposition g root) :
    OrderedSystem g.Term where
  step term := match decompose term with
    | .redex context redex => (strategy.contract redex).map context.plug
    | _ => []
  halted term := match decompose term with
    | .value _ => true
    | _ => false

/-- The traversal's next configuration; a returned root answer has none. -/
def searchStep {root : g.Kind} : State g root → Option (Configuration g Candidate root)
  | .eval (kind := kind) term context =>
      some (Configuration.dispatch context (strategy.inspect kind term))
  | .ret _ .nil => none
  | .ret value (.cons context frame) =>
      some (Configuration.dispatch context (strategy.resume frame value))

/-- **The ordered branching refocused machine.** A focused redex branches over
its candidates in order; an attempt continues the traversal in place from each
instantiation, or has no successor when the candidate is rejected. -/
def machine (root : g.Kind) : OrderedSystem (Configuration g Candidate root) where
  step
    | .search state => (strategy.searchStep state).toList
    | .focus context redex => (strategy.candidates redex).map (.attempt context redex)
    | .attempt context redex candidate =>
        (strategy.attempt redex candidate).map fun term => .search (.eval term context)
    | .blocked _ _ => []
  halted
    | .search state => (answer state).isSome
    | _ => false

/-- The configuration the traversal reaches at its next decision point, with
the decomposition it exhibits there. -/
inductive Searches {root : g.Kind} :
    Configuration g Candidate root → Decomposition g root → Prop where
  | answer (value : g.Value root) : Searches (.search (.ret value .nil)) (.value value)
  | focus {kind : g.Kind} (context : Context g root kind) (redex : g.Redex kind) :
      Searches (.focus context redex) (.redex context redex)
  | blocked {kind : g.Kind} (context : Context g root kind) (term : g.Term) :
      Searches (.blocked context term) (.blocked context term)
  | step {state : State g root} {next : Configuration g Candidate root}
      {decomposition : Decomposition g root} :
      strategy.searchStep state = some next → Searches next decomposition →
        Searches (.search state) decomposition

/-- **Refocusing completeness**: from any term in any context, the in-place
traversal reaches the reduction semantics' decomposition of the plugged term. -/
def RefocusingComplete {root : g.Kind} (decompose : g.Term → Decomposition g root) : Prop :=
  ∀ {kind : g.Kind} (context : Context g root kind) (term : g.Term),
    strategy.Searches (.search (.eval term context)) (decompose (context.plug term))

/-- The block relation: an attempt stands for its candidate's instantiations
in context (none when rejected); every other configuration stands for its own
readback, and its traversal reaches that readback's decomposition. -/
def Block {root : g.Kind} (decompose : g.Term → Decomposition g root)
    (occurrences : List g.Term) (configuration : Configuration g Candidate root) : Prop :=
  match configuration with
  | .attempt context redex candidate =>
      occurrences = (strategy.attempt redex candidate).map context.plug
  | _ => occurrences = [configuration.readback] ∧
      strategy.Searches configuration (decompose configuration.readback)

/-- Administration rank: search states by the traversal's credits, attempts by
the credits of all their instantiations, decision points by zero. -/
def rank (credits : SearchCredits strategy.toTraversal) {root : g.Kind} :
    Configuration g Candidate root → ℕ
  | .search state => credits.work state + 1
  | .focus _ _ => 0
  | .attempt context redex candidate =>
      ((strategy.attempt redex candidate).map
        fun term => credits.work (State.eval term context) + 1).sum + 1
  | .blocked _ _ => 0

/-- **The macro-step machine**: one primitive step, then administration
settled to the next decision points. -/
abbrev saturated (credits : SearchCredits strategy.toTraversal) (root : g.Kind) :
    OrderedSystem (Configuration g Candidate root) :=
  (strategy.machine root).saturate Configuration.stable (strategy.rank credits)

/-- The decision points reached by settling the loaded configuration of a term. -/
abbrev entry (credits : SearchCredits strategy.toTraversal) (root : g.Kind) (term : g.Term) :
    List (Configuration g Candidate root) :=
  (strategy.machine root).settle Configuration.stable
    (strategy.rank credits (Configuration.load (Candidate := Candidate) (root := root) term) + 1)
    (Configuration.load term)

variable {strategy}

theorem searchStep_readback {root : g.Kind} {state : State g root}
    {next : Configuration g Candidate root} (stepped : strategy.searchStep state = some next) :
    next.readback = state.readback := by
  cases state with
  | eval term context =>
      simp only [searchStep, Option.some.injEq] at stepped
      subst next
      rw [Configuration.dispatch_readback, strategy.inspect_correct]
      rfl
  | ret value context =>
      cases context with
      | nil => cases stepped
      | cons context frame =>
          simp only [searchStep, Option.some.injEq] at stepped
          subst next
          rw [Configuration.dispatch_readback, strategy.resume_correct]
          rfl

theorem searchStep_none {root : g.Kind} {state : State g root}
    (none : strategy.searchStep state = none) : (answer state).isSome = true := by
  cases state with
  | eval => cases none
  | ret value context =>
      cases context with
      | nil => rfl
      | cons => cases none

/-- A traversal step to another traversal state is an administrative step of
the deterministic traversal. -/
theorem searchStep_transition {root : g.Kind} {state next : State g root}
    (stepped : strategy.searchStep state = some (.search next)) :
    transition strategy.searchOnly state = some (false, next) := by
  cases state with
  | @eval kind term context =>
      simp only [searchStep, Option.some.injEq] at stepped
      change advance strategy.searchOnly context (strategy.inspect kind term) = _
      generalize strategy.inspect kind term = decision at stepped ⊢
      cases decision <;>
        simp only [Configuration.dispatch, Configuration.search.injEq, reduceCtorEq] at stepped <;>
        subst stepped <;> rfl
  | ret value context =>
      cases context with
      | nil => cases stepped
      | cons context frame =>
          simp only [searchStep, Option.some.injEq] at stepped
          change advance strategy.searchOnly context (strategy.resume frame value) = _
          generalize strategy.resume frame value = decision at stepped ⊢
          cases decision <;>
            simp only [Configuration.dispatch, Configuration.search.injEq,
              reduceCtorEq] at stepped <;>
            subst stepped <;> rfl

theorem searchStep_not_attempt {root kind : g.Kind} {state : State g root}
    {context : Context g root kind} {redex : g.Redex kind} {candidate : Candidate} :
    strategy.searchStep state ≠ some (.attempt context redex candidate) := by
  intro stepped
  cases state with
  | @eval kind' term context' =>
      simp only [searchStep, Option.some.injEq] at stepped
      generalize strategy.inspect kind' term = decision at stepped
      cases decision <;> simp [Configuration.dispatch] at stepped
  | ret value context' =>
      cases context' with
      | nil => cases stepped
      | cons context' frame =>
          simp only [searchStep, Option.some.injEq] at stepped
          generalize strategy.resume frame value = decision at stepped
          cases decision <;> simp [Configuration.dispatch] at stepped

/-- Every traversal step decreases the administration rank. -/
theorem searchStep_rank (credits : SearchCredits strategy.toTraversal) {root : g.Kind}
    {state : State g root} {next : Configuration g Candidate root}
    (stepped : strategy.searchStep state = some next) :
    strategy.rank credits next < credits.work state + 1 := by
  cases next with
  | search next =>
      have decrease : credits.work next < credits.work state :=
        credits.administration_decreases (searchStep_transition stepped)
      simp only [rank]
      omega
  | focus => exact Nat.succ_pos _
  | attempt => exact absurd stepped searchStep_not_attempt
  | blocked => exact Nat.succ_pos _

/-- **Administration is ranked.** -/
theorem ranked (credits : SearchCredits strategy.toTraversal) (root : g.Kind) :
    (strategy.machine root).AdministrationRanked Configuration.stable (strategy.rank credits) := by
  intro configuration administrative next member
  cases configuration with
  | search state =>
      cases stepped : strategy.searchStep state with
      | none =>
          simp [Configuration.stable, searchStep_none stepped] at administrative
      | some next' =>
          simp only [machine, stepped, Option.toList_some, List.mem_singleton] at member
          subst next
          exact searchStep_rank credits stepped
  | focus => cases administrative
  | attempt context redex candidate =>
      simp only [machine, List.mem_map] at member
      obtain ⟨term, member, rfl⟩ := member
      simp only [rank]
      have bound : ∀ (terms : List g.Term), term ∈ terms →
          credits.work (State.eval term context) + 1 ≤
            (terms.map fun term => credits.work (State.eval term context) + 1).sum := by
        intro terms member
        induction terms with
        | nil => cases member
        | cons head tail ih =>
            rw [List.map_cons, List.sum_cons]
            rcases List.mem_cons.mp member with rfl | member
            · omega
            · have := ih member
              omega
      have := bound _ member
      omega
  | blocked => cases administrative

/-- **Macro-step cost**: every successor of the macro-step machine is reached
from a primitive successor by at most that successor's rank of administrative
steps, so one observable step costs at most `1 + rank` primitive steps per
branch. -/
theorem saturated_cost (credits : SearchCredits strategy.toTraversal) {root : g.Kind}
    {configuration next : Configuration g Candidate root}
    (member : next ∈ (strategy.saturated credits root).step configuration) :
    ∃ first ∈ (strategy.machine root).step configuration, ∃ count ≤ strategy.rank credits first,
      (strategy.machine root).AdministrativeReach Configuration.stable count first next := by
  obtain ⟨first, primitive, settled⟩ := List.mem_flatMap.mp member
  obtain ⟨count, _, reach⟩ := (strategy.machine root).settle_reach _ settled
  have bound := reach.count_le_rank (ranked credits root)
  exact ⟨first, primitive, count, by omega, reach⟩

theorem Searches.plug {root : g.Kind} {configuration : Configuration g Candidate root}
    {decomposition : Decomposition g root}
    (searches : strategy.Searches configuration decomposition) :
    decomposition.plug = configuration.readback := by
  induction searches with
  | answer => rfl
  | focus => rfl
  | blocked => rfl
  | step stepped _ ih => exact ih.trans (searchStep_readback stepped)

theorem Searches.block {root : g.Kind} {decompose : g.Term → Decomposition g root}
    {configuration : Configuration g Candidate root}
    (searches : strategy.Searches configuration (decompose configuration.readback)) :
    strategy.Block decompose [configuration.readback] configuration := by
  cases configuration with
  | attempt => cases searches
  | search => exact ⟨rfl, searches⟩
  | focus => exact ⟨rfl, searches⟩
  | blocked => exact ⟨rfl, searches⟩

theorem Searches.answer_eq {root : g.Kind} {value : g.Value root}
    {decomposition : Decomposition g root}
    (searches : strategy.Searches (.search (.ret value .nil)) decomposition) :
    decomposition = .value value := by
  cases searches with
  | answer => rfl
  | step stepped => cases stepped

theorem Searches.focus_eq {root kind : g.Kind} {context : Context g root kind}
    {redex : g.Redex kind} {decomposition : Decomposition g root}
    (searches : strategy.Searches (.focus context redex) decomposition) :
    decomposition = .redex context redex := by
  cases searches
  rfl

theorem Searches.blocked_eq {root kind : g.Kind} {context : Context g root kind}
    {term : g.Term} {decomposition : Decomposition g root}
    (searches : strategy.Searches (.blocked context term) decomposition) :
    decomposition = .blocked context term := by
  cases searches
  rfl

/-- **Unique decomposition proves refocusing completeness**, by induction on the
traversal's search credits. No termination of contraction is assumed. -/
theorem refocusingComplete (credits : SearchCredits strategy.toTraversal) {root : g.Kind}
    {decompose : g.Term → Decomposition g root}
    (unique : strategy.toTraversal.UniqueDecomposition decompose) :
    strategy.RefocusingComplete decompose := by
  suffices every : ∀ n (state : State g root), credits.work state < n →
      strategy.Searches (.search state) (decompose state.readback) by
    intro kind context term
    exact every _ (.eval term context) (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro _ bound; exact absurd bound (Nat.not_lt_zero _)
  | succ n ih =>
      intro state bound
      have dispatched : ∀ {kind : g.Kind} (context : Context g root kind)
          (decision : Decision g kind),
          strategy.searchStep state = some (Configuration.dispatch context decision) →
          strategy.Searches (.search state) (decompose state.readback) := by
        intro kind context decision stepped
        have readback := searchStep_readback stepped
        rw [Configuration.dispatch_readback] at readback
        refine .step stepped ?_
        cases decision with
        | value value =>
            have decrease : credits.work (.ret value context) < credits.work state :=
              credits.administration_decreases (searchStep_transition stepped)
            have next := ih (.ret value context) (by omega)
            rwa [← readback]
        | descend term frame =>
            have decrease : credits.work (.eval term (context.cons frame)) < credits.work state :=
              credits.administration_decreases (searchStep_transition stepped)
            have next := ih (.eval term (context.cons frame)) (by omega)
            rwa [← readback]
        | redex redex =>
            rw [← readback]
            change strategy.Searches (.focus context redex)
              (decompose (context.plug (g.redexTerm redex)))
            rw [unique.redex]
            exact .focus context redex
        | blocked blocked =>
            rw [← readback]
            change strategy.Searches (.blocked context blocked)
              (decompose (context.plug blocked))
            cases state with
            | @eval kind' term context' =>
                simp only [searchStep, Option.some.injEq] at stepped
                cases inspected : strategy.inspect kind' term <;>
                  rw [inspected] at stepped <;> cases stepped
                rw [unique.inspect_blocked context term blocked inspected]
                exact .blocked context blocked
            | ret value context' =>
                cases context' with
                | nil => cases stepped
                | cons context' frame =>
                    simp only [searchStep, Option.some.injEq] at stepped
                    cases resumed : strategy.resume frame value <;>
                      rw [resumed] at stepped <;> cases stepped
                    rw [unique.resume_blocked context frame value blocked resumed]
                    exact .blocked context blocked
      cases state with
      | @eval kind term context => exact dispatched context _ rfl
      | ret value context =>
          cases context with
          | nil =>
              change strategy.Searches _ (decompose (g.valueTerm value))
              rw [unique.value]
              exact .answer value
          | cons context frame => exact dispatched context _ rfl

/-- Unique decomposition reads back: every term is the plug of its
decomposition. This follows from refocusing completeness. -/
theorem decompose_plug {root : g.Kind} {decompose : g.Term → Decomposition g root}
    (complete : strategy.RefocusingComplete decompose) (term : g.Term) :
    (decompose term).plug = term :=
  (complete .nil term).plug

/-- **The ordered branching refocused machine is a block simulation of the
reduction semantics with ordered redex choices.** -/
theorem blockSimulation {root : g.Kind} {decompose : g.Term → Decomposition g root}
    (complete : strategy.RefocusingComplete decompose) :
    BlockSimulation (strategy.source decompose) (strategy.machine root)
      Configuration.stable (strategy.Block decompose) where
  stable_single := by
    intro occurrences configuration blocked isStable
    cases configuration with
    | attempt => cases isStable
    | search state =>
        obtain ⟨rfl, searches⟩ := blocked
        refine ⟨_, rfl, ?_⟩
        cases state with
        | eval => cases isStable
        | ret value context =>
            cases context with
            | cons => cases isStable
            | nil =>
                have decomposed := searches.answer_eq
                simp only [source, decomposed]
                rfl
    | focus context redex =>
        obtain ⟨rfl, searches⟩ := blocked
        have decomposed := searches.focus_eq
        exact ⟨_, rfl, by simp only [source, decomposed]; rfl⟩
    | blocked context term =>
        obtain ⟨rfl, searches⟩ := blocked
        have decomposed := searches.blocked_eq
        exact ⟨_, rfl, by simp only [source, decomposed]; rfl⟩
  stable_step := by
    intro term configuration blocked isStable
    cases configuration with
    | attempt => cases isStable
    | search state =>
        obtain ⟨single, searches⟩ := blocked
        obtain rfl := List.singleton_inj.mp single
        cases state with
        | eval => cases isStable
        | ret value context =>
            cases context with
            | cons => cases isStable
            | nil =>
                have decomposed := searches.answer_eq
                refine ⟨[], .nil, ?_⟩
                simp only [source, decomposed]
                rfl
    | focus context redex =>
        obtain ⟨single, searches⟩ := blocked
        obtain rfl := List.singleton_inj.mp single
        have decomposed := searches.focus_eq
        refine ⟨(strategy.candidates redex).map
          fun candidate => (strategy.attempt redex candidate).map context.plug, ?_, ?_⟩
        · simp only [machine, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
          exact List.forall₂_same.mpr fun _ _ => rfl
        · simp only [source, decomposed]
          rw [contract, List.map_flatMap, List.flatMap_def]
    | blocked context term' =>
        obtain ⟨single, searches⟩ := blocked
        obtain rfl := List.singleton_inj.mp single
        have decomposed := searches.blocked_eq
        refine ⟨[], .nil, ?_⟩
        simp only [source, decomposed]
        rfl
  administrative_split := by
    intro occurrences configuration blocked administrative
    cases configuration with
    | focus => cases administrative
    | blocked => cases administrative
    | search state =>
        obtain ⟨rfl, searches⟩ := blocked
        cases stepped : strategy.searchStep state with
        | none =>
            simp [Configuration.stable, searchStep_none stepped] at administrative
        | some next =>
            refine ⟨[[state.readback]], ?_, rfl⟩
            simp only [machine, stepped, Option.toList_some]
            refine .cons ?_ .nil
            have same := searchStep_readback stepped
            generalize decomposed :
              decompose (Configuration.search state : Configuration g Candidate root).readback =
                decomposition at searches
            cases searches with
            | answer => cases stepped
            | step stepped' searches' =>
                rw [stepped] at stepped'
                cases stepped'
                have decomposed' : decompose next.readback = decomposition := by
                  rw [same]
                  exact decomposed
                rw [← decomposed'] at searches'
                rw [← same]
                exact searches'.block
    | attempt context redex candidate =>
        refine ⟨(strategy.attempt redex candidate).map fun term => [context.plug term], ?_, ?_⟩
        · simp only [machine, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
          exact List.forall₂_same.mpr fun term _ => ⟨rfl, complete context term⟩
        · change _ = (strategy.attempt redex candidate).map context.plug at blocked
          rw [blocked]
          induction strategy.attempt redex candidate with
          | nil => rfl
          | cons head tail ih => simp [ih]

/-- The loaded term is the block of its loaded configuration. -/
theorem loaded {root : g.Kind} {decompose : g.Term → Decomposition g root}
    (complete : strategy.RefocusingComplete decompose) (term : g.Term) :
    strategy.Block decompose [term] (Configuration.load term : Configuration g Candidate root) :=
  ⟨rfl, complete .nil term⟩

/-- **The macro-step machine is an ordered simulation of the reduction
semantics**, at decision points standing for one occurrence. It composes
with other ordered simulations and stable-boundary adapters. -/
theorem orderedSimulation (credits : SearchCredits strategy.toTraversal) {root : g.Kind}
    {decompose : g.Term → Decomposition g root}
    (unique : strategy.toTraversal.UniqueDecomposition decompose) :
    OrderedSimulation (strategy.source decompose) (strategy.saturated credits root)
      (BlockSimulation.StableRelated Configuration.stable (strategy.Block decompose)) :=
  (blockSimulation (refocusingComplete credits unique)).saturated (ranked credits root)

/-- **Ordered frontiers at every fuel.** From the loaded term, the reduction
semantics' frontier and the saturated machine's frontier agree position by
position: answers in order, multiplicity, pending occurrences and stuck
occurrences included. -/
theorem frontiers (credits : SearchCredits strategy.toTraversal) {root : g.Kind}
    {decompose : g.Term → Decomposition g root}
    (unique : strategy.toTraversal.UniqueDecomposition decompose) (fuel : ℕ) (term : g.Term) :
    List.Forall₂ (BlockSimulation.StableRelated Configuration.stable (strategy.Block decompose))
      ((strategy.source decompose).runFrontier fuel [term])
      ((strategy.saturated credits root).runFrontier fuel (strategy.entry credits root term)) :=
  (blockSimulation (refocusingComplete credits unique)).frontiers (ranked credits root) fuel
    (loaded (refocusingComplete credits unique) term)

/-- The same frontiers, from the machine back to the reduction semantics. -/
theorem frontiers_back (credits : SearchCredits strategy.toTraversal) {root : g.Kind}
    {decompose : g.Term → Decomposition g root}
    (unique : strategy.toTraversal.UniqueDecomposition decompose) (fuel : ℕ) (term : g.Term) :
    List.Forall₂ (fun configuration term' =>
        BlockSimulation.StableRelated Configuration.stable (strategy.Block decompose)
          term' configuration)
      ((strategy.saturated credits root).runFrontier fuel (strategy.entry credits root term))
      ((strategy.source decompose).runFrontier fuel [term]) :=
  (blockSimulation (refocusingComplete credits unique)).frontiers_back (ranked credits root) fuel
    (loaded (refocusingComplete credits unique) term)

/-! ### Outcomes: answers, blocked terms and unmatched redexes -/

/-- A terminal observation: an answer, a blocked term (a fault), or a redex at
which every candidate was rejected. -/
inductive Outcome (g : Signature) (root : g.Kind) where
  | value (value : g.Value root)
  | blocked (term : g.Term)
  | unmatched (term : g.Term)

variable (strategy)

/-- The reduction semantics' outcome of a term. -/
def sourceOutcome {root : g.Kind} (decompose : g.Term → Decomposition g root) (term : g.Term) :
    Option (Outcome g root) :=
  match decompose term with
  | .value value => some (.value value)
  | .blocked _ _ => some (.blocked term)
  | .redex _ redex => if (strategy.contract redex).isEmpty then some (.unmatched term) else none

/-- The machine's outcome of a configuration, read independently of halting. -/
def outcome {root : g.Kind} : Configuration g Candidate root → Option (Outcome g root)
  | .search state => (answer state).map .value
  | .focus context redex =>
      if (strategy.contract redex).isEmpty then
        some (.unmatched (context.plug (g.redexTerm redex)))
      else none
  | .attempt _ _ _ => none
  | .blocked context term => some (.blocked (context.plug term))

/-- An erased dead end is a rejected candidate. -/
def RejectedCandidate {root : g.Kind} (configuration : Configuration g Candidate root) : Prop :=
  ∃ (kind : g.Kind) (context : Context g root kind) (redex : g.Redex kind)
    (candidate : Candidate),
    configuration = .attempt context redex candidate ∧ strategy.attempt redex candidate = []

variable {strategy}

/-- **Observable configurations are stable**: saturation never erases an
answer, a blocked term or an unmatched redex. -/
theorem observable_stable {root : g.Kind} :
    OrderedSystem.ObservableStable (Configuration.stable (Candidate := Candidate) (root := root))
      strategy.outcome := by
  intro configuration visible
  cases configuration with
  | search state =>
      cases observed : answer state with
      | none => simp [outcome, observed] at visible
      | some => simp [Configuration.stable, observed]
  | focus => rfl
  | attempt => simp [outcome] at visible
  | blocked => rfl

/-- **Every erased dead end is a rejected candidate**, and it has no outcome. -/
theorem erasure_licensed (root : g.Kind) :
    (strategy.machine root).ErasureLicensed Configuration.stable
      (fun configuration => strategy.RejectedCandidate configuration ∧
        strategy.outcome configuration = none) := by
  intro configuration administrative empty
  cases configuration with
  | search state =>
      cases stepped : strategy.searchStep state with
      | none => simp [Configuration.stable, searchStep_none stepped] at administrative
      | some next => simp [machine, stepped] at empty
  | focus => cases administrative
  | attempt context redex candidate =>
      simp only [machine, List.map_eq_nil_iff] at empty
      exact ⟨⟨_, context, redex, candidate, rfl, empty⟩, rfl⟩
  | blocked => cases administrative

variable (strategy)

/-- A configuration whose outcome is an answer. -/
def succeeded {root : g.Kind} (configuration : Configuration g Candidate root) : Bool :=
  match strategy.outcome configuration with
  | some (.value _) => true
  | _ => false

variable {strategy}

/-- Halted configurations of the saturated machine are inert, so ordered
frontiers split at any position (`OrderedSystem.runFrontier_append`). -/
theorem saturate_halted_inert (credits : SearchCredits strategy.toTraversal) (root : g.Kind) :
    (strategy.saturated credits root).HaltedInert := by
  intro configuration halts
  cases configuration with
  | search state =>
      cases stepped : strategy.searchStep state with
      | none => simp [OrderedSystem.saturate, machine, stepped]
      | some next =>
          cases state with
          | eval => simp [OrderedSystem.saturate, machine, answer] at halts
          | ret value context =>
              cases context with
              | nil => cases stepped
              | cons => simp [OrderedSystem.saturate, machine, answer] at halts
  | focus => cases halts
  | attempt => cases halts
  | blocked => cases halts

/-- Successful configurations are halted; faults and unmatched redexes are not
successes, so the first terminal need not be the first success. -/
theorem succeeded_halts {root : g.Kind} {configuration : Configuration g Candidate root}
    (success : strategy.succeeded configuration = true) :
    (strategy.machine root).halted configuration = true := by
  cases configuration with
  | search state =>
      cases observed : answer state with
      | none => simp [succeeded, outcome, observed] at success
      | some => simp [machine, observed]
  | focus context redex =>
      simp only [succeeded, outcome] at success
      split at success <;> simp_all
  | attempt => simp [succeeded, outcome] at success
  | blocked => simp [succeeded, outcome] at success

/-- Outcomes agree at related configurations. -/
theorem outcome_agreement {root : g.Kind} {decompose : g.Term → Decomposition g root}
    {term : g.Term} {configuration : Configuration g Candidate root}
    (related : BlockSimulation.StableRelated Configuration.stable (strategy.Block decompose)
      term configuration) :
    Option.Rel (· = ·) (strategy.sourceOutcome decompose term)
      (strategy.outcome configuration) := by
  obtain ⟨blocked, isStable⟩ := related
  cases configuration with
  | attempt => cases isStable
  | search state =>
      obtain ⟨single, searches⟩ := blocked
      obtain rfl := List.singleton_inj.mp single
      cases state with
      | eval => cases isStable
      | ret value context =>
          cases context with
          | cons => cases isStable
          | nil =>
              have decomposed := searches.answer_eq
              simp only [sourceOutcome, outcome, answer, decomposed]
              exact .some rfl
  | focus context redex =>
      obtain ⟨single, searches⟩ := blocked
      obtain rfl := List.singleton_inj.mp single
      have decomposed : decompose (context.plug (g.redexTerm redex)) = _ := searches.focus_eq
      simp only [sourceOutcome, outcome, Configuration.readback, decomposed]
      cases (strategy.contract redex).isEmpty
      · exact .none
      · exact .some rfl
  | blocked context term' =>
      obtain ⟨single, searches⟩ := blocked
      obtain rfl := List.singleton_inj.mp single
      have decomposed : decompose (context.plug term') = _ := searches.blocked_eq
      simp only [sourceOutcome, outcome, Configuration.readback, decomposed]
      exact .some rfl

/-- **Ordered outcomes are equal at every fuel**: answers, faults and unmatched
redexes, in order and with multiplicity, read off the reduction semantics and
off the saturated machine. -/
theorem outcomes (credits : SearchCredits strategy.toTraversal) {root : g.Kind}
    {decompose : g.Term → Decomposition g root}
    (unique : strategy.toTraversal.UniqueDecomposition decompose) (fuel : ℕ) (term : g.Term) :
    ((strategy.source decompose).runFrontier fuel [term]).filterMap
        (strategy.sourceOutcome decompose) =
      ((strategy.saturated credits root).runFrontier fuel
        (strategy.entry credits root term)).filterMap
        strategy.outcome :=
  by
    have related := (blockSimulation (refocusingComplete credits unique)).outcomes_loaded
      (ranked credits root) outcome_agreement fuel (loaded (refocusingComplete credits unique) term)
    rwa [List.forall₂_eq_eq_eq] at related

/-! ### Source steps are contextual contractions -/

/-- Every source successor is a candidate instantiation of a redex, plugged
back into that redex's context. -/
theorem source_step_sound {root : g.Kind} {decompose : g.Term → Decomposition g root}
    (complete : strategy.RefocusingComplete decompose) {term next : g.Term}
    (member : next ∈ (strategy.source decompose).step term) :
    ∃ (kind : g.Kind) (context : Context g root kind) (redex : g.Redex kind)
      (contractum : g.Term), contractum ∈ strategy.contract redex ∧
        term = context.plug (g.redexTerm redex) ∧ next = context.plug contractum := by
  have plugged := decompose_plug complete term
  simp only [source] at member
  generalize decompose term = decomposition at member plugged
  cases decomposition with
  | value => cases member
  | blocked => cases member
  | redex context redex =>
      obtain ⟨contractum, contracted, rfl⟩ := List.mem_map.mp member
      exact ⟨_, context, redex, contractum, contracted, plugged.symm, rfl⟩

end BranchingStrategy

/-- A deterministic strategy is the ordered branching strategy with a single
candidate per redex, which yields the contraction when it is defined. -/
def Strategy.branching {g : Signature} (strategy : Strategy g) : BranchingStrategy g Unit where
  toTraversal := strategy.toTraversal
  candidates _ := [()]
  attempt redex _ := (strategy.contract redex).toList

theorem Strategy.branching_contract {g : Signature} (strategy : Strategy g) {kind : g.Kind}
    (redex : g.Redex kind) :
    strategy.branching.contract redex = (strategy.contract redex).toList := by
  simp [BranchingStrategy.contract, Strategy.branching]

/-- **For a deterministic strategy, the ordered reduction semantics is its
contextual closure**: under unique decomposition, a term steps to exactly the
`SourceStep` successors of its decomposition. -/
theorem Strategy.branching_source_iff {g : Signature} (strategy : Strategy g)
    (credits : SearchCredits strategy.toTraversal) {root : g.Kind}
    {decompose : g.Term → Decomposition g root}
    (unique : strategy.toTraversal.UniqueDecomposition decompose) (term next : g.Term) :
    next ∈ (strategy.branching.source decompose).step term ↔
      SourceStep strategy root term next := by
  constructor
  · intro member
    obtain ⟨_, context, redex, contractum, contracted, rfl, rfl⟩ :=
      BranchingStrategy.source_step_sound
        (BranchingStrategy.refocusingComplete credits unique) member
    rw [Strategy.branching_contract, Option.mem_toList] at contracted
    exact SourceStep.context context (.contract redex contractum contracted)
  · intro step
    suffices every : ∀ {kind : g.Kind} {first second : g.Term},
        SourceStep strategy kind first second → ∀ context : Context g root kind,
          context.plug second ∈
            (strategy.branching.source decompose).step (context.plug first) from
      every step .nil
    intro kind first second step
    induction step with
    | contract redex contractum contracted =>
        intro context
        simp only [BranchingStrategy.source, unique.redex, Strategy.branching_contract,
          contracted, Option.toList_some, List.map_cons, List.map_nil, List.mem_singleton]
    | frame frame _ ih => exact fun context => ih (context.cons frame)

/-! ### Root scans

Without frames, and with every term its own redex, the ordered branching
machine scans candidates at the root: each term is a decision point, each
candidate attempt is administration, and a term none of whose candidates
yields an instantiation is unmatched (normal). The block laws then hold for
any ordered successor function presented as candidates and attempts. -/

/-- The frame-free signature over a term type: every term is its own redex. -/
def rootSignature (Term : Type) : Signature where
  Term := Term
  Kind := Unit
  Frame _ _ := Empty
  Value _ := Empty
  Redex _ := Term
  plugFrame frame _ := frame.elim
  valueTerm value := value.elim
  redexTerm redex := redex

/-- The root traversal focuses the whole term at once. -/
def rootTraversal (Term : Type) : Traversal (rootSignature Term) where
  inspect _ term := .redex term
  resume frame _ := frame.elim
  inspect_correct _ _ := rfl
  resume_correct frame _ := frame.elim

/-- The root traversal performs no search. -/
def rootCredits (Term : Type) : SearchCredits (rootTraversal Term) where
  term _ _ := 0
  frame frame := frame.elim
  inspect_value _ _ _ inspected := by cases inspected
  inspect_descend _ _ _ _ _ inspected := by cases inspected
  resume_value _ _ frame := frame.elim
  resume_descend _ _ _ frame := frame.elim

/-- The only decomposition at the root. -/
def rootDecompose {Term : Type} (term : Term) : Decomposition (rootSignature Term) () :=
  .redex .nil term

theorem rootUnique (Term : Type) :
    (rootTraversal Term).UniqueDecomposition (rootDecompose (Term := Term)) where
  value value := value.elim
  redex context redex := by
    cases context with
    | nil => rfl
    | cons _ frame => exact frame.elim
  inspect_blocked _ _ _ inspected := by cases inspected
  resume_blocked _ frame := frame.elim

/-- The ordered branching strategy scanning the given candidates at the root. -/
def BranchingStrategy.root {Term Candidate : Type} (candidates : Term → List Candidate)
    (attempt : Term → Candidate → List Term) : BranchingStrategy (rootSignature Term) Candidate where
  toTraversal := rootTraversal Term
  candidates redex := candidates redex
  attempt redex candidate := attempt redex candidate

/-- The root scan's reduction semantics is the given ordered successor function. -/
theorem BranchingStrategy.root_source {Term Candidate : Type} (candidates : Term → List Candidate)
    (attempt : Term → Candidate → List Term) :
    (BranchingStrategy.root candidates attempt).source rootDecompose =
      { step := fun term => (candidates term).flatMap (attempt term), halted := fun _ => false } := by
  simp only [BranchingStrategy.source, rootDecompose, BranchingStrategy.contract,
    BranchingStrategy.root]
  congr 1
  funext term
  exact (List.map_congr_left fun _ _ => rfl).trans (List.map_id _)

end Branching

/-! ## Query-stage emissions

An emitted result is complete for this query stage even when its payload still
needs evaluation. Failure classification and an evaluated-result observer are
explicit policies. This adapter neither evaluates emitted payloads nor proves
that native rejected attempts preserve effects, ownership or execution cost.
-/

namespace QueryEmission

inductive Term (Query Result Failure : Type) where
  | pending (query : Query)
  | emitted (result : Result)
  | failed (result : Result) (failure : Failure)
  deriving DecidableEq, Repr

variable {Query Result Failure Candidate : Type}

def signature (Query Result Failure : Type) : Signature where
  Term := Term Query Result Failure
  Kind := Unit
  Frame _ _ := Empty
  Value _ := Result
  Redex _ := Query
  plugFrame frame _ := frame.elim
  valueTerm := Term.emitted
  redexTerm := Term.pending

def traversal : Traversal (signature Query Result Failure) where
  inspect _
    | .pending query => .redex query
    | .emitted result => .value result
    | .failed result failure => .blocked (.failed result failure)
  resume frame _ := frame.elim
  inspect_correct _ term := by cases term <;> rfl
  resume_correct frame _ := frame.elim

/-- Failure records retain the original result or receipt beside its classifier. -/
def classify (failure : Result → Option Failure) (result : Result) : Term Query Result Failure :=
  match failure result with
  | none => .emitted result
  | some reason => .failed result reason

def strategy (candidates : Query → List Candidate) (attempt : Query → Candidate → List Result)
    (failure : Result → Option Failure) : BranchingStrategy (signature Query Result Failure) Candidate where
  toTraversal := traversal
  candidates := candidates
  attempt query candidate := (attempt query candidate).map (classify failure)

def decompose : Term Query Result Failure → Decomposition (signature Query Result Failure) ()
  | .pending query => .redex .nil query
  | .emitted result => .value result
  | .failed result failure => .blocked .nil (.failed result failure)

def credits : SearchCredits (traversal (Query := Query) (Result := Result) (Failure := Failure)) where
  term _ term := match term with | .emitted _ => 1 | _ => 0
  frame frame := frame.elim
  inspect_value := by
    intro kind term result inspected
    cases term <;> simp_all [traversal]
  inspect_descend := by
    intro outer term inner child frame
    exact frame.elim
  resume_value _ _ frame := frame.elim
  resume_descend _ _ _ frame := frame.elim

theorem unique :
    (traversal (Query := Query) (Result := Result) (Failure := Failure)).UniqueDecomposition decompose where
  value _ := rfl
  redex context query := by
    cases context with
    | nil => rfl
    | cons _ frame => exact frame.elim
  inspect_blocked context term blocked inspected := by
    cases context with
    | nil =>
        cases term with
        | pending query => simp [traversal] at inspected
        | emitted result => simp [traversal] at inspected
        | failed result failure =>
            have same : Term.failed result failure = blocked := Decision.blocked.inj inspected
            subst blocked
            rfl
    | cons _ frame => exact frame.elim
  resume_blocked _ frame := frame.elim

/-- An independent one-layer specification: candidates produce an ordered
flatMap of results; emitted and declared failure records do not run again. -/
def source (candidates : Query → List Candidate) (attempt : Query → Candidate → List Result)
    (failure : Result → Option Failure) : Mettapedia.GSLT.Distinction.OrderedSystem
      (Term Query Result Failure) where
  step
    | .pending query => ((candidates query).flatMap (attempt query)).map (classify failure)
    | _ => []
  halted
    | .emitted _ => true
    | _ => false

theorem source_agreement (candidates : Query → List Candidate)
    (attempt : Query → Candidate → List Result) (failure : Result → Option Failure) :
    (strategy candidates attempt failure).source decompose = source candidates attempt failure := by
  apply congrArg₂ (@Mettapedia.GSLT.Distinction.OrderedSystem.mk (Term Query Result Failure))
  · funext term
    cases term with
    | pending query =>
        change (((candidates query).flatMap fun candidate =>
          (attempt query candidate).map (classify failure)).map id) =
            ((candidates query).flatMap (attempt query)).map (classify failure)
        rw [List.map_id, List.map_flatMap]
    | emitted => rfl
    | failed => rfl
  · funext term
    cases term <;> rfl

theorem orderedSimulation (candidates : Query → List Candidate)
    (attempt : Query → Candidate → List Result) (failure : Result → Option Failure) :
    Mettapedia.GSLT.Distinction.OrderedSimulation (source candidates attempt failure)
      ((strategy candidates attempt failure).saturated credits ())
      (Mettapedia.GSLT.Distinction.BlockSimulation.StableRelated Configuration.stable
        ((strategy candidates attempt failure).Block decompose)) :=
  source_agreement candidates attempt failure ▸
    BranchingStrategy.orderedSimulation (strategy := strategy candidates attempt failure)
      (root := ()) (decompose := decompose) credits unique

theorem outcomes (candidates : Query → List Candidate)
    (attempt : Query → Candidate → List Result) (failure : Result → Option Failure)
    (fuel : Nat) (term : Term Query Result Failure) :
    ((source candidates attempt failure).runFrontier fuel [term]).filterMap
        ((strategy candidates attempt failure).sourceOutcome decompose) =
      (((strategy candidates attempt failure).saturated credits ()).runFrontier fuel
        ((strategy candidates attempt failure).entry credits () term)).filterMap
        (strategy candidates attempt failure).outcome := by
  rw [← source_agreement candidates attempt failure]
  exact BranchingStrategy.outcomes (strategy := strategy candidates attempt failure)
    (root := ()) (decompose := decompose) credits unique fuel term

def querySuccess (candidates : Query → List Candidate) (attempt : Query → Candidate → List Result)
    (failure : Result → Option Failure) :
    Configuration (signature Query Result Failure) Candidate () → Bool :=
  (strategy candidates attempt failure).succeeded

/-- This stricter observer uses a caller's declared evaluated-result predicate;
it does not supply an evaluator or equate evaluation with query completion. -/
def evaluatedSuccess (candidates : Query → List Candidate) (attempt : Query → Candidate → List Result)
    (failure : Result → Option Failure) (evaluated : Result → Bool)
    (configuration : Configuration (signature Query Result Failure) Candidate ()) : Bool :=
  match (strategy candidates attempt failure).outcome configuration with
  | some (.value result) => evaluated result
  | _ => false

theorem query_success_halts (candidates : Query → List Candidate)
    (attempt : Query → Candidate → List Result) (failure : Result → Option Failure)
    {configuration : Configuration (signature Query Result Failure) Candidate ()}
    (success : querySuccess candidates attempt failure configuration = true) :
    ((strategy candidates attempt failure).saturated credits ()).halted configuration = true :=
  BranchingStrategy.succeeded_halts (strategy := strategy candidates attempt failure) success

theorem evaluated_success_implies_query (candidates : Query → List Candidate)
    (attempt : Query → Candidate → List Result) (failure : Result → Option Failure)
    (evaluated : Result → Bool) (configuration : Configuration (signature Query Result Failure) Candidate ())
    (success : evaluatedSuccess candidates attempt failure evaluated configuration = true) :
    querySuccess candidates attempt failure configuration = true := by
  unfold evaluatedSuccess at success
  unfold querySuccess BranchingStrategy.succeeded
  cases observed : (strategy candidates attempt failure).outcome configuration with
  | none => simp [observed] at success
  | some outcome => cases outcome <;> simp_all

/-- Pruning is licensed at an emitted query result, including a payload that
the separate evaluated-result observer does not yet accept. -/
theorem first_success_prune (candidates : Query → List Candidate)
    (attempt : Query → Candidate → List Result) (failure : Result → Option Failure)
    (fuel : Nat) (before after : List (Configuration (signature Query Result Failure) Candidate ()))
    {answer : Configuration (signature Query Result Failure) Candidate ()}
    (success : querySuccess candidates attempt failure answer = true) :
    Mettapedia.GSLT.Contracts.Joins.firstSuccess (querySuccess candidates attempt failure)
        (((strategy candidates attempt failure).saturated credits ()).runFrontier fuel
          (before ++ answer :: after)) =
      Mettapedia.GSLT.Contracts.Joins.firstSuccess (querySuccess candidates attempt failure)
        (((strategy candidates attempt failure).saturated credits ()).runFrontier fuel
          (before ++ [answer])) :=
  Mettapedia.GSLT.Contracts.Joins.firstSuccess_prune
    (BranchingStrategy.saturate_halted_inert (strategy := strategy candidates attempt failure) credits ())
    (fun _ accepted => query_success_halts candidates attempt failure accepted)
    fuel before after success

end QueryEmission

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

/-! ### Authored rewrite rules as ordered candidates

At a focused redex the language's rewrite rules are tried in declaration
order. A rule whose head does not match, or whose premises fail, is a rejected
candidate; a matching rule yields its instantiated right-hand sides. The rule
is applied at the redex itself: contextual authority comes from the authored
frames of the traversal, so congruence premises have no recursive reducts
there. The ordered contracta are then exactly one layer of the existing
contextual rewriting engine. -/

open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator applyRuleUsing rewriteAt)

/-- The ordered branching strategy whose candidates are the language's
authored rewrite rules, over a traversal by authored frames. -/
def rules (base : BasePremiseEvaluator)
    (traversal : Traversal (signature lang Value Redex @valueTerm @redexTerm)) :
    BranchingStrategy (signature lang Value Redex @valueTerm @redexTerm) RewriteRule where
  toTraversal := traversal
  candidates _ := lang.rewrites
  attempt redex rule := applyRuleUsing base lang (fun _ => []) rule (redexTerm redex)

/-- The ordered contracta of a redex are the existing engine's one-layer
reducts, in rule order and with multiplicity. -/
theorem rules_contract (base : BasePremiseEvaluator)
    (traversal : Traversal (signature lang Value Redex @valueTerm @redexTerm))
    {kind : String} (redex : Redex kind) :
    (rules base traversal).contract redex = rewriteAt base lang 1 (redexTerm redex) :=
  rfl

/-- **One layer of the contextual rewriting engine as an ordered rule scan.**
The language's rules are the candidates at a term, in declaration order; a
rule whose head does not match or whose premises fail is rejected; congruence
premises are evaluated by the engine one context layer down. -/
def ruleScan (base : BasePremiseEvaluator) (lang : LanguageDef) (contextFuel : ℕ) :
    BranchingStrategy (rootSignature Pattern) RewriteRule :=
  BranchingStrategy.root (fun _ => lang.rewrites)
    (fun term rule => applyRuleUsing base lang (rewriteAt base lang contextFuel) rule term)

/-- The rule scan's reduction semantics is the engine's ordered reducts. -/
theorem ruleScan_source (base : BasePremiseEvaluator) (lang : LanguageDef) (contextFuel : ℕ) :
    (ruleScan base lang contextFuel).source rootDecompose =
      { step := rewriteAt base lang (contextFuel + 1), halted := fun _ => false } := by
  rw [ruleScan, BranchingStrategy.root_source]
  rfl

/-- **The rule-scan machine simulates the engine's ordered rewriting**: rule
attempts are administration, rejected rules are erased empty blocks, and each
saturated step yields exactly the engine's reducts, in order and with
multiplicity. -/
theorem ruleScan_simulation (base : BasePremiseEvaluator) (lang : LanguageDef)
    (contextFuel : ℕ) :
    Mettapedia.GSLT.Distinction.OrderedSimulation
      { step := rewriteAt base lang (contextFuel + 1), halted := fun _ => false }
      ((ruleScan base lang contextFuel).saturated (rootCredits Pattern) ())
      (Mettapedia.GSLT.Distinction.BlockSimulation.StableRelated Configuration.stable
        ((ruleScan base lang contextFuel).Block rootDecompose)) :=
  ruleScan_source base lang contextFuel ▸
    BranchingStrategy.orderedSimulation (strategy := ruleScan base lang contextFuel)
      (root := ()) (decompose := rootDecompose) (rootCredits Pattern) (rootUnique Pattern)

/-- The actual authored engine supplies one query layer; its outputs become
query-stage terminals under the explicit failure classifier. -/
def queryEmission (base : BasePremiseEvaluator) (lang : LanguageDef) (contextFuel : Nat)
    {Failure : Type} (failure : Pattern → Option Failure) :
    BranchingStrategy (QueryEmission.signature Pattern Pattern Failure) RewriteRule :=
  QueryEmission.strategy (fun _ => lang.rewrites)
    (fun term rule => applyRuleUsing base lang (rewriteAt base lang contextFuel) rule term) failure

theorem queryEmission_source (base : BasePremiseEvaluator) (lang : LanguageDef) (contextFuel : Nat)
    {Failure : Type} (failure : Pattern → Option Failure) (term : Pattern) :
    ((queryEmission base lang contextFuel failure).source QueryEmission.decompose).step
        (.pending term) =
      (rewriteAt base lang (contextFuel + 1) term).map (QueryEmission.classify failure) := by
  rw [queryEmission, QueryEmission.source_agreement]
  rfl

theorem queryEmission_simulation (base : BasePremiseEvaluator) (lang : LanguageDef)
    (contextFuel : Nat) {Failure : Type} (failure : Pattern → Option Failure) :
    Mettapedia.GSLT.Distinction.OrderedSimulation
      (QueryEmission.source (fun _ => lang.rewrites)
        (fun term rule => applyRuleUsing base lang (rewriteAt base lang contextFuel) rule term) failure)
      ((queryEmission base lang contextFuel failure).saturated QueryEmission.credits ())
      (Mettapedia.GSLT.Distinction.BlockSimulation.StableRelated Configuration.stable
        ((queryEmission base lang contextFuel failure).Block QueryEmission.decompose)) :=
  QueryEmission.orderedSimulation _ _ failure

end Authored

end Mettapedia.Machines.Refocusing
