import Mettapedia.GSLT.Distinction.DependentComposition
import Mettapedia.Machines.ExecutionHints
import Mathlib.CategoryTheory.Functor.Basic

/-!
# Composing cost simulations

`ProductiveBlocks.CostSimulation` relates the actual states of two
deterministic machines by a relation that need not be a function, with an
explicit per-transition cost bound.  A multi-stage compiler is a chain of such
relations.  This module proves that they compose, what the composite
preserves, and which premises reflect completion through it.

`Machine.run_one_related_comp` composes local finite implementations without
a uniform cost bound, through their actual middle state and existing
`OutcomeRel`. The costed stages below retain their stronger resource contract.

* **The composite** (`CostSimulation.comp`).  Simulations with relations `R`
  and `S` and costs `cost` and `cost'` compose to a simulation along the
  relational composite `SpanTransport.compose R S` at cost `cost' * cost`.
  The product is the bound: one source transition costs at most `cost` middle
  transitions, each of which costs at most `cost'` target transitions; the sum
  does not bound it (the controls).  The identity relation is a simulation at
  cost one (`CostSimulation.refl`).  Observations are carried through the
  composite (`comp_observe_prefix`, prefixes at `cost' * cost * fuel`), and two
  final observations of related states coincide under the forward simulation
  alone (`final_eq_forward`, `comp_final_eq`).  Backward simulations compose in
  the other order (`comp_backward`, `comp_never_completes`), and simulations
  along graphs of functions compose along the graph of the composite function
  (`comp_graph`).
* **The middle state as data** (`comp_segment_path`, `comp_run_staged`,
  `observe_prefix_staged`).  For a path through a middle state
  (`DependentComposition.Path`), every source run segment is matched by an
  actual middle run and a target run of at most `cost'` times the middle run's
  length, and the new path's middle point is the middle run's own residual;
  complete runs keep their middle outcome.  Choice enters nowhere in this
  module: the composite relation is a proposition and its proofs destructure
  it.  A function selecting middle states for bare composite pairs is a
  separate matter, supplied by `DependentComposition.MiddleSelection.classical`
  with `Classical.choice`, or choice-free for graphs
  (`DependentComposition.MiddleSelection.graph`).
* **Completion reflection** (`ReflectsCompletion`).  Every final observation
  of a related target run is the observation of some source run.  It follows
  from a backward simulation (`reflectsCompletion_of_backward`), or from the
  forward simulation together with progress (`Progress`,
  `CostSimulation.reflectsCompletion`): stuck source states have stuck targets,
  and a rank on source states decreases whenever a source transition is
  matched without moving the target, so the target cannot finish while the
  source stutters forever.  Reflection composes (`ReflectsCompletion.comp`)
  without composing ranks.  A simulation that moves the target on every
  silent and publishing transition has progress at every rank
  (`Progress.of_positive`), or with matched stuck endpoints
  (`Progress.of_positive_and_stuck`).
* **The interface of a compilation stage** (`Stage`, `Stage.comp`).  A stage
  discharges a relation between the actual states of its source and target
  machines, a forward cost-bounded simulation, and completion reflection.
  Identity stages and composition obey the unit and associativity laws at the
  actual relation and cost (`Stage.refl_comp`, `Stage.comp_refl`,
  `Stage.comp_assoc`). These equalities do not identify retained middle paths.
  Chains of stages compose with the product cost, and every chain carries
  observation prefixes, equal final observations, reflected completion and
  preserved non-completion (`Stage.observe_prefix`, `Stage.final_eq`,
  `Stage.reflected`, `Stage.never_completes`).  For a compiler whose stages
  are operational realizations of nondeterministic calculi, each stage proof
  discharges: a deterministic machine presentation of both calculi (a
  scheduler) whose transitions publish the observable events; the relation on
  actual states (the compiler's graph is the functional case); the
  per-transition cost bound; and reflection, either by a backward simulation
  over the scheduled target or by progress, where a lower bound of one target
  transition per source transition is `Progress.of_positive`.
* **Resumable services** (`Stage.ofHandler`). A service that actually computes
  the declared callback response within a uniform bound realizes an atomic
  call at that bound plus one entry transition. The source caller may be
  partial or diverging; positive target work and matched stuck endpoints
  establish completion reflection. Calls with further external interaction
  first use `Machine.handle_close` and discharge the resulting service law.
* **The category of observed machines** (`ObservedMachine`). Objects retain
  the actual state carrier and stepper at a fixed event/verdict/request
  interface; morphisms are the existing stages. The category uses their proved
  identity and composition laws. `ObservedMachine.relabelFunctor` carries a
  common observation-label map through both machines and stages. This
  contract reflects completion; distinguishing stuckness from silent
  divergence additionally needs the stated endpoint obligations.
* **Span transport** (`segmentComposite`, `comp_segment_sourceForthOcc`,
  `comp_segment_sourceBackOcc`, `comp_future_related`).  The event-relation
  composite of the two segment relations relates segments through a middle
  segment publishing the same events.  It is contained in the segment relation
  of the composite relation (`segmentComposite_events`), and each of the four
  occurrence laws transfers along that containment
  (`segmentComposite_sourceForthOcc` and its three companions, from
  `SpanRelation.SourceForthOcc.mono` and its companions).  Forward simulations
  give the composite source forth law, backward simulations the composite
  source back law, and both together the agreement of every future formula
  through the middle machine.  No target (past) law is claimed from
  simulations.

The controls are in `SimulationCompositionControls`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.SpanTransport

open Mettapedia.OSLF.Framework.DerivedModalities

universe u v w e f

/-! ## Monotonicity of the occurrence laws -/

namespace SpanRelation

variable {X : Type u} {Y : Type v} {A : ReductionSpan.{u, e} X} {B : ReductionSpan.{v, f} Y}
variable {R R' : SpanRelation A B}

/-- The source forth law holds for fewer related states and more related events. -/
theorem SourceForthOcc.mono (states : ∀ ⦃x y⦄, R'.states x y → R.states x y)
    (events : ∀ ⦃a b⦄, R.events a b → R'.events a b) (forth : R.SourceForthOcc) :
    R'.SourceForthOcc :=
  fun _ _ related a sourceEq =>
    let ⟨b, sourceEq', matched⟩ := forth (states related) a sourceEq
    ⟨b, sourceEq', events matched⟩

theorem SourceBackOcc.mono (states : ∀ ⦃x y⦄, R'.states x y → R.states x y)
    (events : ∀ ⦃a b⦄, R.events a b → R'.events a b) (back : R.SourceBackOcc) :
    R'.SourceBackOcc :=
  fun _ _ related b sourceEq =>
    let ⟨a, sourceEq', matched⟩ := back (states related) b sourceEq
    ⟨a, sourceEq', events matched⟩

theorem TargetForthOcc.mono (states : ∀ ⦃x y⦄, R'.states x y → R.states x y)
    (events : ∀ ⦃a b⦄, R.events a b → R'.events a b) (forth : R.TargetForthOcc) :
    R'.TargetForthOcc :=
  fun _ _ related a targetEq =>
    let ⟨b, targetEq', matched⟩ := forth (states related) a targetEq
    ⟨b, targetEq', events matched⟩

theorem TargetBackOcc.mono (states : ∀ ⦃x y⦄, R'.states x y → R.states x y)
    (events : ∀ ⦃a b⦄, R.events a b → R'.events a b) (back : R.TargetBackOcc) :
    R'.TargetBackOcc :=
  fun _ _ related b targetEq =>
    let ⟨a, targetEq', matched⟩ := back (states related) b targetEq
    ⟨a, targetEq', events matched⟩

end SpanRelation

/-- Predicates related along two relations are related along their composite. -/
theorem Related.compose {X : Type u} {Y : Type v} {Z : Type w} {R : X → Y → Prop} {S : Y → Z → Prop}
    {φ : X → Prop} {ψ : Y → Prop} {χ : Z → Prop} (first : Related R φ ψ) (second : Related S ψ χ) :
    Related (compose R S) φ χ := by
  rintro x z ⟨y, relatedFirst, relatedSecond⟩
  exact (first relatedFirst).trans (second relatedSecond)

end Mettapedia.GSLT.Distinction.SpanTransport

namespace Mettapedia.GSLT.Distinction.ProductiveBlocks

open Mettapedia.GSLT.Dynamics.OrderedDemand (Status Observation)
open Mettapedia.GSLT.Distinction.SpanTransport
  (compose SpanRelation Related Tense Tense.sat sat_related_future)
open Mettapedia.GSLT.Distinction.DependentComposition (Path)

/-! ## Final observations of one machine -/

namespace Machine

variable {State Event Verdict Request : Type} (machine : Machine State Event Verdict Request)

/-- **Two final observations of one state coincide.** -/
theorem observe_final_eq {fuel fuel' : ℕ} {state : State}
    (final : (machine.observe fuel state).status.Final)
    (final' : (machine.observe fuel' state).status.Final) :
    machine.observe fuel state = machine.observe fuel' state := by
  rcases le_total fuel fuel' with le | le
  · exact (machine.observe_prefix_of_le le state).2 final
  · exact ((machine.observe_prefix_of_le le state).2 final').symm

/-- A run that ended without exhausting its fuel is every final observation of
its state. -/
theorem observe_eq_of_ended {fuel fuel' : ℕ} {state : State}
    (ended : ∀ residual, (machine.run fuel state).2 ≠ .exhausted residual)
    (final' : (machine.observe fuel' state).status.Final) :
    machine.observe fuel' state = machine.observe fuel state := by
  rcases le_total fuel fuel' with le | le
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
    simp only [observe, machine.run_stable fuel extra state ended]
  · exact (machine.observe_prefix_of_le le state).2 final'

/-- **A final observation splits after a segment**: it runs past the segment,
publishes the segment's events, and continues with a final observation of the
segment's residual. -/
theorem observe_split {fuel k : ℕ} {state residual : State} {events : List Event}
    (ran : machine.run k state = (events, .exhausted residual))
    (final : (machine.observe fuel state).status.Final) :
    ∃ rest, fuel = k + rest ∧ (machine.observe rest residual).status.Final ∧
      machine.observe fuel state =
        ⟨events ++ (machine.observe rest residual).events, (machine.observe rest residual).status⟩ := by
  rcases le_total k fuel with le | le
  · obtain ⟨rest, rfl⟩ := Nat.exists_eq_add_of_le le
    have split : machine.observe (k + rest) state =
        ⟨events ++ (machine.observe rest residual).events, (machine.observe rest residual).status⟩ := by
      simp only [observe, machine.established_and_pending k rest state residual events ran]
    refine ⟨rest, rfl, ?_, split⟩
    rw [split] at final
    exact final
  · have same := (machine.observe_prefix_of_le le state).2 final
    rw [same] at final
    simp only [observe, ran, Outcome.status, Status.Final] at final

end Machine

/-! ## Related outcomes compose -/

section Outcomes

variable {Source Middle Target Verdict Request : Type}
  {R : Source → Middle → Prop} {S : Middle → Target → Prop}

theorem OutcomeRel.ne_stuck {outcome : Outcome Source Verdict Request}
    {outcome' : Outcome Middle Verdict Request} (relatedOutcomes : OutcomeRel R outcome outcome')
    (sourceNotStuck : ∀ state, outcome ≠ .stuck state)
    (stuckAt : Middle) : outcome' ≠ .stuck stuckAt := by
  cases relatedOutcomes with
  | stuck related => exact False.elim (sourceNotStuck _ rfl)
  | _ => intro same; cases same

theorem OutcomeRel.finished_inv {verdict : Verdict} {outcome' : Outcome Middle Verdict Request}
    (relatedOutcomes : OutcomeRel R (.finished verdict) outcome') : outcome' = .finished verdict := by
  cases relatedOutcomes
  rfl

theorem OutcomeRel.faulted_inv {outcome' : Outcome Middle Verdict Request}
    (relatedOutcomes : OutcomeRel R (Outcome.faulted (State := Source)) outcome') :
    outcome' = .faulted := by
  cases relatedOutcomes
  rfl

theorem OutcomeRel.suspended_inv {request : Request} {saved : Source}
    {outcome' : Outcome Middle Verdict Request}
    (relatedOutcomes : OutcomeRel R (.suspended request saved) outcome') :
    ∃ saved', outcome' = .suspended request saved' ∧ R saved saved' := by
  cases relatedOutcomes with
  | suspended _ relatedSaved => exact ⟨_, rfl, relatedSaved⟩

/-- **Related outcomes compose along the composite relation.** -/
theorem OutcomeRel.comp {outcome : Outcome Source Verdict Request}
    {outcome' : Outcome Middle Verdict Request} {outcome'' : Outcome Target Verdict Request}
    (first : OutcomeRel R outcome outcome') (second : OutcomeRel S outcome' outcome'') :
    OutcomeRel (compose R S) outcome outcome'' := by
  cases first with
  | finished verdict =>
      cases second
      exact .finished verdict
  | faulted =>
      cases second
      exact .faulted
  | suspended request relatedSaved =>
      cases second with
      | suspended _ relatedSaved' => exact .suspended request ⟨_, relatedSaved, relatedSaved'⟩
  | stuck relatedStopped =>
      cases second with
      | stuck relatedStopped' => exact .stuck ⟨_, relatedStopped, relatedStopped'⟩
  | exhausted relatedResidual =>
      cases second with
      | exhausted relatedResidual' => exact .exhausted ⟨_, relatedResidual, relatedResidual'⟩

end Outcomes

namespace Machine

open Mettapedia.GSLT.Distinction.SpanTransport (compose)

/-- Finite local operation implementations compose through the actual middle
state. Their event lists and saved outcomes compose without a uniform bound
on internal work. -/
theorem run_one_related_comp
    {Source Middle Target Event Verdict Request : Type}
    (source : Machine Source Event Verdict Request)
    (middle : Machine Middle Event Verdict Request)
    (target : Machine Target Event Verdict Request)
    (firstRelated : Source → Middle → Prop) (secondRelated : Middle → Target → Prop)
    (first : ∀ {state state'}, firstRelated state state' →
      ∃ count, (middle.run count state').1 = (source.run 1 state).1 ∧
        OutcomeRel firstRelated (source.run 1 state).2 (middle.run count state').2)
    (second : ∀ {state state'}, secondRelated state state' →
      ∃ count, (target.run count state').1 = (middle.run 1 state).1 ∧
        OutcomeRel secondRelated (middle.run 1 state).2 (target.run count state').2)
    {state : Source} {state' : Target}
    (retained : compose firstRelated secondRelated state state') :
    ∃ count, (target.run count state').1 = (source.run 1 state).1 ∧
      OutcomeRel (compose firstRelated secondRelated)
        (source.run 1 state).2 (target.run count state').2 := by
  obtain ⟨between, retainedFirst, retainedSecond⟩ := retained
  obtain ⟨middleCount, firstEvents, firstOutcome⟩ := first retainedFirst
  obtain ⟨count, secondEvents, secondOutcome⟩ :=
    middle.run_related_of_one target secondRelated second middleCount retainedSecond
  exact ⟨count, secondEvents.trans firstEvents, firstOutcome.comp secondOutcome⟩

end Machine

/-! ## The composite simulation -/

namespace CostSimulation

variable {Source Middle Target Event Verdict Request : Type}
  {source : Machine Source Event Verdict Request} {middle : Machine Middle Event Verdict Request}
  {target : Machine Target Event Verdict Request}
  {R : Source → Middle → Prop} {S : Middle → Target → Prop} {cost cost' : ℕ}

/-- A simulation along a relation is a simulation along every equivalent
relation. -/
theorem of_iff {related related' : Source → Middle → Prop}
    (simulation : CostSimulation source middle related cost)
    (same : ∀ state state', related state state' ↔ related' state state') :
    CostSimulation source middle related' cost where
  silent relatedStates stepped :=
    let ⟨k, bound, next', ran, relatedNext⟩ := simulation.silent ((same _ _).mpr relatedStates) stepped
    ⟨k, bound, next', ran, (same _ _).mp relatedNext⟩
  publish relatedStates stepped :=
    let ⟨k, bound, next', ran, relatedNext⟩ := simulation.publish ((same _ _).mpr relatedStates) stepped
    ⟨k, bound, next', ran, (same _ _).mp relatedNext⟩
  finish relatedStates stepped := simulation.finish ((same _ _).mpr relatedStates) stepped
  fail relatedStates stepped := simulation.fail ((same _ _).mpr relatedStates) stepped
  call relatedStates stepped :=
    let ⟨k, bound, saved', ran, relatedSaved⟩ := simulation.call ((same _ _).mpr relatedStates) stepped
    ⟨k, bound, saved', ran, (same _ _).mp relatedSaved⟩

/-- **The identity simulation**: every transition is matched by itself, at cost
one. -/
theorem refl (machine : Machine Source Event Verdict Request) :
    CostSimulation machine machine Eq 1 where
  silent := by
    rintro state _ next rfl stepped
    exact ⟨1, le_rfl, next, machine.run_succ_silent stepped, rfl⟩
  publish := by
    rintro state _ events next rfl stepped
    have ran : machine.run 1 state = (events ++ [], .exhausted next) :=
      machine.run_succ_publish stepped
    rw [List.append_nil] at ran
    exact ⟨1, le_rfl, next, ran, rfl⟩
  finish := by
    rintro state _ verdict rfl stepped
    exact ⟨1, le_rfl, machine.run_succ_finish stepped⟩
  fail := by
    rintro state _ events rfl stepped
    exact ⟨1, le_rfl, machine.run_succ_fail stepped⟩
  call := by
    rintro state _ request saved rfl stepped
    exact ⟨1, le_rfl, saved, machine.run_succ_call stepped, rfl⟩

/-- **Cost simulations compose**: along the relational composite, at the
product of the costs. -/
theorem comp (first : CostSimulation source middle R cost)
    (second : CostSimulation middle target S cost') :
    CostSimulation source target (compose R S) (cost' * cost) where
  silent := by
    rintro state state'' next ⟨mid, relatedFirst, relatedSecond⟩ stepped
    obtain ⟨k, bound, mid', ran, relatedNext⟩ := first.silent relatedFirst stepped
    obtain ⟨j, bound', next'', ran', relatedNext'⟩ := second.segment relatedSecond ran
    exact ⟨j, bound'.trans (Nat.mul_le_mul (le_refl cost') bound), next'', ran',
      mid', relatedNext, relatedNext'⟩
  publish := by
    rintro state state'' events next ⟨mid, relatedFirst, relatedSecond⟩ stepped
    obtain ⟨k, bound, mid', ran, relatedNext⟩ := first.publish relatedFirst stepped
    obtain ⟨j, bound', next'', ran', relatedNext'⟩ := second.segment relatedSecond ran
    exact ⟨j, bound'.trans (Nat.mul_le_mul (le_refl cost') bound), next'', ran',
      mid', relatedNext, relatedNext'⟩
  finish := by
    rintro state state'' verdict ⟨mid, relatedFirst, relatedSecond⟩ stepped
    obtain ⟨k, bound, ran⟩ := first.finish relatedFirst stepped
    obtain ⟨j, bound', eventsEq, outcome⟩ := second.run_related k relatedSecond (by
      intro stuckAt stuck
      rw [ran] at stuck
      cases stuck)
    rw [ran] at eventsEq outcome
    exact ⟨j, bound'.trans (Nat.mul_le_mul (le_refl cost') bound),
      Prod.ext eventsEq outcome.finished_inv⟩
  fail := by
    rintro state state'' events ⟨mid, relatedFirst, relatedSecond⟩ stepped
    obtain ⟨k, bound, ran⟩ := first.fail relatedFirst stepped
    obtain ⟨j, bound', eventsEq, outcome⟩ := second.run_related k relatedSecond (by
      intro stuckAt stuck
      rw [ran] at stuck
      cases stuck)
    rw [ran] at eventsEq outcome
    exact ⟨j, bound'.trans (Nat.mul_le_mul (le_refl cost') bound),
      Prod.ext eventsEq outcome.faulted_inv⟩
  call := by
    rintro state state'' request saved ⟨mid, relatedFirst, relatedSecond⟩ stepped
    obtain ⟨k, bound, saved', ran, relatedSaved⟩ := first.call relatedFirst stepped
    obtain ⟨j, bound', eventsEq, outcome⟩ := second.run_related k relatedSecond (by
      intro stuckAt stuck
      rw [ran] at stuck
      cases stuck)
    rw [ran] at eventsEq outcome
    obtain ⟨saved'', outcomeEq, relatedSaved'⟩ := outcome.suspended_inv
    exact ⟨j, bound'.trans (Nat.mul_le_mul (le_refl cost') bound), saved'',
      Prod.ext eventsEq outcomeEq, saved', relatedSaved, relatedSaved'⟩

/-- **Observations are carried through the composite**: a source observation is
a prefix of the related target observation at `cost' * cost` times the fuel. -/
theorem comp_observe_prefix (first : CostSimulation source middle R cost)
    (second : CostSimulation middle target S cost') (fuel : ℕ) {state : Source} {state'' : Target}
    (relatedStates : compose R S state state'') :
    (source.observe fuel state).Prefix (target.observe (cost' * cost * fuel) state'') :=
  (first.comp second).observe_prefix fuel relatedStates

/-- **Final observations coincide under the forward simulation alone**: a final
source observation is carried to the target, and a state has one final
observation. -/
theorem final_eq_forward {related : Source → Target → Prop}
    (simulation : CostSimulation source target related cost) {state : Source} {state' : Target}
    (relatedStates : related state state') {fuel fuel' : ℕ}
    (final : (source.observe fuel state).status.Final)
    (final' : (target.observe fuel' state').status.Final) :
    source.observe fuel state = target.observe fuel' state' := by
  have carried := (simulation.observe_prefix fuel relatedStates).2 final
  have carriedFinal : (target.observe (cost * fuel) state').status.Final := by
    rw [← carried]
    exact final
  exact carried.trans (target.observe_final_eq carriedFinal final')

/-- **Equal final observations through the composite.** -/
theorem comp_final_eq (first : CostSimulation source middle R cost)
    (second : CostSimulation middle target S cost') {state : Source} {state'' : Target}
    (relatedStates : compose R S state state'') {fuel fuel'' : ℕ}
    (final : (source.observe fuel state).status.Final)
    (final'' : (target.observe fuel'' state'').status.Final) :
    source.observe fuel state = target.observe fuel'' state'' :=
  (first.comp second).final_eq_forward relatedStates final final''

/-- **Backward simulations compose in the other order**, along the converse of
the composite relation, at the product of their costs. -/
theorem comp_backward {back back' : ℕ}
    (firstBack : CostSimulation middle source (fun mid state => R state mid) back)
    (secondBack : CostSimulation target middle (fun state'' mid => S mid state'') back') :
    CostSimulation target source (fun state'' state => compose R S state state'') (back * back') :=
  (secondBack.comp firstBack).of_iff fun _ _ =>
    ⟨fun ⟨mid, relatedSecond, relatedFirst⟩ => ⟨mid, relatedFirst, relatedSecond⟩,
      fun ⟨mid, relatedFirst, relatedSecond⟩ => ⟨mid, relatedSecond, relatedFirst⟩⟩

/-- **Non-completion is preserved through the composite**, given the two
backward simulations. -/
theorem comp_never_completes {back back' : ℕ}
    (firstBack : CostSimulation middle source (fun mid state => R state mid) back)
    (secondBack : CostSimulation target middle (fun state'' mid => S mid state'') back')
    {state : Source} {state'' : Target} (relatedStates : compose R S state state'')
    (never : ∀ fuel, ¬ (source.observe fuel state).status.Final) (fuel'' : ℕ) :
    ¬ (target.observe fuel'' state'').status.Final :=
  never_completes (comp_backward firstBack secondBack) relatedStates never fuel''

/-- **Simulations along graphs compose along the graph of the composite
function**, choice-free. -/
theorem comp_graph {map : Source → Middle} {map' : Middle → Target}
    (first : CostSimulation source middle (DependentComposition.graph map) cost)
    (second : CostSimulation middle target (DependentComposition.graph map') cost') :
    CostSimulation source target (DependentComposition.graph (map' ∘ map)) (cost' * cost) :=
  (first.comp second).of_iff fun state _ =>
    ⟨fun ⟨_, mapped, mapped'⟩ => by subst mapped; exact mapped',
      fun mapped => ⟨map state, rfl, mapped⟩⟩

/-! ### The middle state as data -/

/-- **The composite keeps its middle run.**  Along a path through a middle
state, a source run segment is matched by an actual middle run of at most
`cost` times its fuel and a target run of at most `cost'` times the middle
run's length, publishing the same events; the new path passes through the
middle run's residual. -/
theorem comp_segment_path (first : CostSimulation source middle R cost)
    (second : CostSimulation middle target S cost') {fuel : ℕ} {state residual : Source}
    {state'' : Target} {events : List Event} (path : Path R S state state'')
    (ran : source.run fuel state = (events, .exhausted residual)) :
    ∃ k ≤ cost * fuel, ∃ j ≤ cost' * k, ∃ residual'' : Target, ∃ path' : Path R S residual residual'',
      middle.run k path.1 = (events, .exhausted path'.1) ∧
        target.run j state'' = (events, .exhausted residual'') := by
  obtain ⟨k, bound, residual', middleRun, relatedResidual⟩ := first.segment path.2.1 ran
  obtain ⟨j, bound', residual'', targetRun, relatedResidual'⟩ := second.segment path.2.2 middleRun
  exact ⟨k, bound, j, bound', residual'', ⟨residual', relatedResidual, relatedResidual'⟩,
    middleRun, targetRun⟩

/-- **Complete runs keep their middle outcome.**  Along a path, a source run
that does not end stuck is matched by a middle run and a target run publishing
its events, with the middle outcome related to both ends. -/
theorem comp_run_staged (first : CostSimulation source middle R cost)
    (second : CostSimulation middle target S cost') (fuel : ℕ) {state : Source} {state'' : Target}
    (path : Path R S state state'')
    (notStuck : ∀ stuckAt, (source.run fuel state).2 ≠ .stuck stuckAt) :
    ∃ k ≤ cost * fuel, ∃ j ≤ cost' * k,
      (middle.run k path.1).1 = (source.run fuel state).1 ∧
        OutcomeRel R (source.run fuel state).2 (middle.run k path.1).2 ∧
        (target.run j state'').1 = (source.run fuel state).1 ∧
        OutcomeRel S (middle.run k path.1).2 (target.run j state'').2 := by
  obtain ⟨k, bound, eventsEq, outcome⟩ := first.run_related fuel path.2.1 notStuck
  obtain ⟨j, bound', eventsEq', outcome'⟩ :=
    second.run_related k path.2.2 fun stuckAt => outcome.ne_stuck notStuck stuckAt
  exact ⟨k, bound, j, bound', eventsEq, outcome, eventsEq'.trans eventsEq, outcome'⟩

/-- Stuck-endpoint transport retains the actual middle run and its outcome,
just as every other finite outcome does. -/
theorem comp_run_staged_all (first : CostSimulation source middle R cost)
    (firstStuck : MatchesStuck source middle R cost)
    (second : CostSimulation middle target S cost')
    (secondStuck : MatchesStuck middle target S cost')
    (fuel : Nat) {state : Source} {state'' : Target} (path : Path R S state state'') :
    ∃ count ≤ cost * fuel, ∃ count' ≤ cost' * count,
      (middle.run count path.1).1 = (source.run fuel state).1 ∧
        OutcomeRel R (source.run fuel state).2 (middle.run count path.1).2 ∧
        (target.run count' state'').1 = (source.run fuel state).1 ∧
        OutcomeRel S (middle.run count path.1).2 (target.run count' state'').2 := by
  obtain ⟨count, bound, events, outcome⟩ := first.run_related_all firstStuck fuel path.2.1
  obtain ⟨count', bound', events', outcome'⟩ :=
    second.run_related_all secondStuck count path.2.2
  exact ⟨count, bound, count', bound', events, outcome, events'.trans events, outcome'⟩

/-- **The observation chain through the middle**: the source observation is a
prefix of the middle observation at `cost` times the fuel, which is a prefix of
the target observation at `cost'` times that. -/
theorem observe_prefix_staged (first : CostSimulation source middle R cost)
    (second : CostSimulation middle target S cost') (fuel : ℕ) {state : Source} {state'' : Target}
    (path : Path R S state state'') :
    (source.observe fuel state).Prefix (middle.observe (cost * fuel) path.1) ∧
      (middle.observe (cost * fuel) path.1).Prefix (target.observe (cost' * (cost * fuel)) state'') :=
  ⟨first.observe_prefix fuel path.2.1, second.observe_prefix (cost * fuel) path.2.2⟩

end CostSimulation

namespace MatchesStuck

variable {Source Middle Target Event Verdict Request : Type}
  {source : Machine Source Event Verdict Request} {middle : Machine Middle Event Verdict Request}
  {target : Machine Target Event Verdict Request}
  {R : Source → Middle → Prop} {S : Middle → Target → Prop} {cost cost' : Nat}

/-- A matched stuck endpoint cannot also finish or fault at another budget.
The proof uses determinism of runs, rather than totality of the source. -/
theorem not_final {related : Source → Target → Prop}
    (stuck : MatchesStuck source target related cost) {state : Source} {state' : Target}
    (retained : related state state') (blocked : source.step state = none) (fuel : Nat) :
    ¬ (target.observe fuel state').status.Final := by
  intro final
  obtain ⟨count, _, stopped, ran, _⟩ := stuck retained blocked
  have ended : ∀ residual, (target.run count state').2 ≠ .exhausted residual := by
    intro residual impossible
    rw [ran] at impossible
    cases impossible
  have same := target.observe_eq_of_ended ended final
  rw [same] at final
  simp only [Machine.observe, ran, Outcome.status, Status.Final] at final

/-- Matching absent transitions composes with the same product cost as
ordinary transition simulation. The intermediate stuck endpoint is retained. -/
theorem comp (first : MatchesStuck source middle R cost)
    (second : CostSimulation middle target S cost')
    (secondStuck : MatchesStuck middle target S cost') :
    MatchesStuck source target (compose R S) (cost' * cost) := by
  rintro state state'' ⟨mid, relatedFirst, relatedSecond⟩ blocked
  obtain ⟨count, bound, stopped, middleRun, retainedFirst⟩ := first relatedFirst blocked
  obtain ⟨count', bound', events, outcomes⟩ := second.run_related_all secondStuck count relatedSecond
  rw [middleRun] at events outcomes
  obtain ⟨stopped', targetOutcome, retainedSecond⟩ := outcomes.stuck_inv
  exact ⟨count', bound'.trans (Nat.mul_le_mul_left _ bound), stopped',
    Prod.ext events targetOutcome, ⟨stopped, retainedFirst, retainedSecond⟩⟩

end MatchesStuck

/-! ## Completion reflection -/

section Reflection

variable {Source Middle Target Event Verdict Request : Type}
  {source : Machine Source Event Verdict Request} {middle : Machine Middle Event Verdict Request}
  {target : Machine Target Event Verdict Request}

/-- **Completion is reflected** along a relation: every final observation of a
related target run is the observation of some source run. -/
def ReflectsCompletion (source : Machine Source Event Verdict Request)
    (target : Machine Target Event Verdict Request) (related : Source → Target → Prop) : Prop :=
  ∀ ⦃state state'⦄, related state state' → ∀ fuel', (target.observe fuel' state').status.Final →
    ∃ fuel, source.observe fuel state = target.observe fuel' state'

/-- **Reflection composes**, through the middle point of each composite pair. -/
theorem ReflectsCompletion.comp {R : Source → Middle → Prop} {S : Middle → Target → Prop}
    (first : ReflectsCompletion source middle R) (second : ReflectsCompletion middle target S) :
    ReflectsCompletion source target (compose R S) := by
  rintro state state'' ⟨mid, relatedFirst, relatedSecond⟩ fuel'' final
  obtain ⟨fuel', reached'⟩ := second relatedSecond fuel'' final
  have final' : (middle.observe fuel' mid).status.Final := by
    rw [reached']
    exact final
  obtain ⟨fuel, reached⟩ := first relatedFirst fuel' final'
  exact ⟨fuel, reached.trans reached'⟩

/-- Relabeling both observers preserves completion reflection. Injectivity is
unnecessary for this direction; it is needed to recover distinctions erased
by an observer. -/
theorem ReflectsCompletion.relabel {Event' Verdict' Request' : Type}
    {related : Source → Target → Prop}
    (reflects : ReflectsCompletion source target related)
    (events : Event → Event') (verdicts : Verdict → Verdict') (requests : Request → Request') :
    ReflectsCompletion (source.relabel events verdicts requests)
      (target.relabel events verdicts requests) related := by
  intro state state' relatedStates fuel' final'
  obtain ⟨fuel, same⟩ := reflects relatedStates fuel'
    ((target.relabel_final_iff events verdicts requests fuel' state').mp final')
  exact ⟨fuel, source.relabel_observation_eq target events verdicts requests fuel fuel'
    state state' same⟩

/-- Under reflection, a source state that never completes has related target
states that never complete. -/
theorem ReflectsCompletion.never_completes {related : Source → Target → Prop}
    (reflects : ReflectsCompletion source target related) {state : Source} {state' : Target}
    (relatedStates : related state state')
    (never : ∀ fuel, ¬ (source.observe fuel state).status.Final) (fuel' : ℕ) :
    ¬ (target.observe fuel' state').status.Final := by
  intro final
  obtain ⟨fuel, reached⟩ := reflects relatedStates fuel' final
  apply never fuel
  rw [reached]
  exact final

/-- **A backward simulation reflects completion.** -/
theorem reflectsCompletion_of_backward {related : Source → Target → Prop} {back : ℕ}
    (backward : CostSimulation target source (fun state' state => related state state') back) :
    ReflectsCompletion source target related := by
  intro state state' relatedStates fuel' final
  exact ⟨back * fuel',
    ((backward.observe_prefix fuel'
      (relatedStates : (fun state' state => related state state') state' state)).2 final).symm⟩

/-- **Progress of a forward simulation**: stuck source states have stuck
targets, and a rank on source states decreases on every silent or publishing
source transition that is matched without a target transition. Neither
machine is required to terminate or to have a transition in every state. -/
structure Progress (source : Machine Source Event Verdict Request)
    (target : Machine Target Event Verdict Request) (related : Source → Target → Prop)
    (cost : ℕ) (rank : Source → ℕ) : Prop where
  stuck : MatchesStuck source target related cost
  silent : ∀ {state state' next}, related state state' → source.step state = some (.silent next) →
    ∃ k ≤ cost, ∃ next', target.run k state' = ([], .exhausted next') ∧ related next next' ∧
      (k = 0 → rank next < rank state)
  publish : ∀ {state state' events next}, related state state' →
    source.step state = some (.publish events next) →
    ∃ k ≤ cost, ∃ next', target.run k state' = (events, .exhausted next') ∧ related next next' ∧
      (k = 0 → rank next < rank state)

/-- Matching stuck endpoints and moving the target on every silent and
publishing source transition gives progress at every rank. -/
theorem Progress.of_positive_and_stuck {related : Source → Target → Prop} {cost : ℕ} (rank : Source → ℕ)
    (stuck : MatchesStuck source target related cost)
    (silent : ∀ {state state' next}, related state state' →
      source.step state = some (.silent next) →
      ∃ k ≤ cost, 0 < k ∧ ∃ next', target.run k state' = ([], .exhausted next') ∧ related next next')
    (publish : ∀ {state state' events next}, related state state' →
      source.step state = some (.publish events next) →
      ∃ k ≤ cost, 0 < k ∧ ∃ next', target.run k state' = (events, .exhausted next') ∧
        related next next') :
    Progress source target related cost rank where
  stuck := stuck
  silent relatedStates stepped :=
    let ⟨k, bound, positive, next', ran, relatedNext⟩ := silent relatedStates stepped
    ⟨k, bound, next', ran, relatedNext, fun zero => absurd zero (Nat.pos_iff_ne_zero.mp positive)⟩
  publish relatedStates stepped :=
    let ⟨k, bound, positive, next', ran, relatedNext⟩ := publish relatedStates stepped
    ⟨k, bound, next', ran, relatedNext, fun zero => absurd zero (Nat.pos_iff_ne_zero.mp positive)⟩

/-- The total-source specialization: positive target work on every silent and
publishing source transition gives progress without an endpoint obligation. -/
theorem Progress.of_positive {related : Source → Target → Prop} {cost : ℕ} (rank : Source → ℕ)
    (moves : ∀ {state state'}, related state state' → source.step state ≠ none)
    (silent : ∀ {state state' next}, related state state' →
      source.step state = some (.silent next) →
      ∃ k ≤ cost, 0 < k ∧ ∃ next', target.run k state' = ([], .exhausted next') ∧ related next next')
    (publish : ∀ {state state' events next}, related state state' →
      source.step state = some (.publish events next) →
      ∃ k ≤ cost, 0 < k ∧ ∃ next', target.run k state' = (events, .exhausted next') ∧
        related next next') :
    Progress source target related cost rank :=
  .of_positive_and_stuck rank (by
    intro state state' retained blocked
    exact (moves retained blocked).elim) silent publish

/-- **A forward simulation with progress reflects completion**: a target that
finishes or faults is matched by a source run with the same observation.  The
target is deterministic, so a target run past a matched segment continues
from its residual; the rank excludes a source that stutters forever while the
target stands still. -/
theorem CostSimulation.reflectsCompletion {related : Source → Target → Prop} {cost : ℕ}
    (simulation : CostSimulation source target related cost) {rank : Source → ℕ}
    (progress : Progress source target related cost rank) :
    ReflectsCompletion source target related := by
  suffices key : ∀ fuel' r (state : Source) (state' : Target), rank state = r →
      related state state' → (target.observe fuel' state').status.Final →
        ∃ fuel, source.observe fuel state = target.observe fuel' state' by
    intro state state' relatedStates fuel' final
    exact key fuel' _ state state' rfl relatedStates final
  intro fuel'
  induction fuel' using Nat.strong_induction_on with
  | _ fuel' ihFuel =>
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ihRank =>
  intro state state' ranked relatedStates final
  cases found : source.step state with
  | none => exact False.elim (progress.stuck.not_final relatedStates found fuel' final)
  | some transition =>
      cases transition with
      | silent next =>
          have sourceRun : ∀ fuel, source.observe (fuel + 1) state = source.observe fuel next := by
            intro fuel
            simp only [Machine.observe, source.run_succ_silent found]
          obtain ⟨k, _, next', ran, relatedNext, decreases⟩ := progress.silent relatedStates found
          cases k with
          | zero =>
              have zeroRun : target.run 0 state' = ([], .exhausted state') := rfl
              rw [zeroRun, Prod.mk.injEq] at ran
              obtain rfl : state' = next' := Outcome.exhausted.inj ran.2
              obtain ⟨fuel, reached⟩ :=
                ihRank (rank next) (ranked ▸ decreases rfl) next _ rfl relatedNext final
              exact ⟨fuel + 1, (sourceRun fuel).trans reached⟩
          | succ k =>
              obtain ⟨rest, split, final', observed⟩ := target.observe_split ran final
              obtain ⟨fuel, reached⟩ :=
                ihFuel rest (by omega) (rank next) next next' rfl relatedNext final'
              refine ⟨fuel + 1, ?_⟩
              rw [sourceRun fuel, reached, observed]
              rfl
      | publish events next =>
          have sourceRun : ∀ fuel, source.observe (fuel + 1) state =
              ⟨events ++ (source.observe fuel next).events, (source.observe fuel next).status⟩ := by
            intro fuel
            simp only [Machine.observe, source.run_succ_publish found]
          obtain ⟨k, _, next', ran, relatedNext, decreases⟩ := progress.publish relatedStates found
          cases k with
          | zero =>
              have zeroRun : target.run 0 state' = ([], .exhausted state') := rfl
              rw [zeroRun, Prod.mk.injEq] at ran
              obtain ⟨rfl, same⟩ := ran
              obtain rfl : state' = next' := Outcome.exhausted.inj same
              obtain ⟨fuel, reached⟩ :=
                ihRank (rank next) (ranked ▸ decreases rfl) next _ rfl relatedNext final
              refine ⟨fuel + 1, ?_⟩
              rw [sourceRun fuel, reached]
              rfl
          | succ k =>
              obtain ⟨rest, split, final', observed⟩ := target.observe_split ran final
              obtain ⟨fuel, reached⟩ :=
                ihFuel rest (by omega) (rank next) next next' rfl relatedNext final'
              refine ⟨fuel + 1, ?_⟩
              rw [sourceRun fuel, reached, observed]
      | finish verdict =>
          obtain ⟨k, _, ran⟩ := simulation.finish relatedStates found
          have ended : ∀ residual, (target.run k state').2 ≠ .exhausted residual := by
            intro residual same
            rw [ran] at same
            cases same
          have sourceRun : source.run 1 state = ([], .finished verdict) := source.run_succ_finish found
          refine ⟨1, ?_⟩
          rw [target.observe_eq_of_ended ended final]
          simp only [Machine.observe, sourceRun, ran, Outcome.status]
      | fail events =>
          obtain ⟨k, _, ran⟩ := simulation.fail relatedStates found
          have ended : ∀ residual, (target.run k state').2 ≠ .exhausted residual := by
            intro residual same
            rw [ran] at same
            cases same
          have sourceRun : source.run 1 state = (events, .faulted) := source.run_succ_fail found
          refine ⟨1, ?_⟩
          rw [target.observe_eq_of_ended ended final]
          simp only [Machine.observe, sourceRun, ran, Outcome.status]
      | call request saved =>
          obtain ⟨k, _, saved', ran, _⟩ := simulation.call relatedStates found
          have ended : ∀ residual, (target.run k state').2 ≠ .exhausted residual := by
            intro residual same
            rw [ran] at same
            cases same
          have same := target.observe_eq_of_ended ended final
          rw [same] at final
          simp only [Machine.observe, ran, Outcome.status, Status.Final] at final

/-- A bounded service realizes atomic callbacks with positive target work.
The caller may loop, fault or become stuck; only each service invocation
must compute the stated reply within the bound. -/
theorem Progress.close_handle {State Service Value Failure : Type}
    (machine : Machine State Event Verdict Request)
    (callback : Callback State Event Request Value Failure)
    (service : Machine Service Event (Reply Value Failure) Empty) (load : Request → Service)
    (environment : Environment Request Event Value Failure) (bound : Nat)
    (answers : ∀ request, service.run bound (load request) =
      ((environment request).1, .finished (environment request).2)) :
    Progress (machine.close callback environment) (machine.handle callback service load)
      (fun state retained => retained = .running state) (bound + 1) (fun _ => 0) := by
  apply Progress.of_positive_and_stuck
  · exact machine.close_handle_matchesStuck callback load service environment bound
  · rintro state _ next rfl stepped
    cases found : machine.step state with
    | none => simp [Machine.close, found] at stepped
    | some transition =>
        cases transition <;> simp [Machine.close, found] at stepped
        subst next
        refine ⟨1, by omega, by omega, .running _, ?_, rfl⟩
        simp [Machine.run, Machine.handle, found]
  · rintro state _ events next rfl stepped
    cases found : machine.step state with
    | none => simp [Machine.close, found] at stepped
    | some transition =>
        cases transition with
        | silent next => simp [Machine.close, found] at stepped
        | publish published retained =>
            simp only [Machine.close, found, Option.map_some, Option.some.injEq,
              Transition.publish.injEq] at stepped
            obtain ⟨rfl, rfl⟩ := stepped
            refine ⟨1, by omega, by omega, .running retained, ?_, rfl⟩
            simp [Machine.run, Machine.handle, found]
        | finish verdict => simp [Machine.close, found] at stepped
        | fail faults => simp [Machine.close, found] at stepped
        | call request saved =>
            simp only [Machine.close, found, Option.map_some, Option.some.injEq,
              Transition.publish.injEq] at stepped
            obtain ⟨rfl, rfl⟩ := stepped
            obtain ⟨used, within, ran⟩ := machine.handle_call_run callback service load state saved request
              found bound (environment request).1 (environment request).2 (answers request)
            have positive : 0 < used := by
              cases used with
              | zero => simp [Machine.run] at ran
              | succ used => exact Nat.succ_pos used
            exact ⟨used, within, positive, .running _, ran, rfl⟩

end Reflection

/-! ## The interface of a compilation stage -/

/-- **A compilation stage between two machines**: a relation between their
actual states, a forward simulation with a per-transition cost, and completion
reflection. -/
structure Stage {Source Target Event Verdict Request : Type}
    (source : Machine Source Event Verdict Request) (target : Machine Target Event Verdict Request) where
  related : Source → Target → Prop
  cost : ℕ
  forward : CostSimulation source target related cost
  reflects : ReflectsCompletion source target related

namespace Stage

variable {Source Middle Target Event Verdict Request : Type}
  {source : Machine Source Event Verdict Request} {middle : Machine Middle Event Verdict Request}
  {target : Machine Target Event Verdict Request}

/-- Stage equality retains the state relation and the numeric cost. The
simulation and completion-reflection fields are proofs of those contracts. -/
@[ext] theorem ext {first second : Stage source target}
    (related : first.related = second.related) (cost : first.cost = second.cost) :
    first = second := by
  cases first
  cases second
  cases related
  cases cost
  rfl

/-- Every machine realizes itself at unit cost, including stuck, faulting,
diverging and suspended executions. -/
def refl (machine : Machine Source Event Verdict Request) : Stage machine machine where
  related := Eq
  cost := 1
  forward := CostSimulation.refl machine
  reflects := by
    rintro _ _ rfl fuel _
    exact ⟨fuel, rfl⟩

@[simp] theorem refl_related (machine : Machine Source Event Verdict Request) :
    (refl machine).related = Eq := rfl

@[simp] theorem refl_cost (machine : Machine Source Event Verdict Request) :
    (refl machine).cost = 1 := rfl

/-- A stage from a forward and a backward simulation. -/
def ofBackward (related : Source → Target → Prop) (cost : ℕ)
    (forward : CostSimulation source target related cost) {back : ℕ}
    (backward : CostSimulation target source (fun state' state => related state state') back) :
    Stage source target :=
  ⟨related, cost, forward, reflectsCompletion_of_backward backward⟩

/-- A stage from a forward simulation with progress. -/
def ofProgress (related : Source → Target → Prop) (cost : ℕ)
    (forward : CostSimulation source target related cost) {rank : Source → ℕ}
    (progress : Progress source target related cost rank) : Stage source target :=
  ⟨related, cost, forward, forward.reflectsCompletion progress⟩

/-- Expand an atomic callback into its actual bounded service machine. This
stage preserves finite observations and reflects completed runs, and can be
composed with other compilation stages. The service's execution equation is
a premise to establish for the particular implementation. -/
def ofHandler {State Service Value Failure : Type}
    (machine : Machine State Event Verdict Request)
    (callback : Callback State Event Request Value Failure)
    (service : Machine Service Event (Reply Value Failure) Empty) (load : Request → Service)
    (environment : Environment Request Event Value Failure) (bound : Nat)
    (answers : ∀ request, service.run bound (load request) =
      ((environment request).1, .finished (environment request).2)) :
    Stage (machine.close callback environment) (machine.handle callback service load) :=
  .ofProgress (fun state retained => retained = .running state) (bound + 1)
    (machine.close_handle_costSimulation callback load service environment bound answers)
    (Progress.close_handle machine callback service load environment bound answers)

/-- A checked partial state representation is a real stage at one logical
transition per source transition. The cost counts machine advances, not the
physical work of encoding and decoding. Malformed target data lies outside
the related-state image and is rejected by the adapter. -/
def ofRepresentation {Data : Type} (machine : Machine Source Event Verdict Request)
    (encode : Source → Data) (decode : Data → Option Source)
    (roundtrip : ∀ state, decode (encode state) = some state) :
    Stage machine (machine.represent encode decode) where
  related state data := data = encode state
  cost := 1
  forward := machine.represent_costSimulation encode decode roundtrip
  reflects := by
    rintro state _ rfl fuel _
    exact ⟨fuel, (machine.observe_represent encode decode roundtrip fuel state).symm⟩

theorem ofRepresentation_stuck {Data : Type}
    (machine : Machine Source Event Verdict Request) (encode : Source → Data)
    (decode : Data → Option Source)
    (roundtrip : ∀ state, decode (encode state) = some state) :
    MatchesStuck machine (machine.represent encode decode)
      (ofRepresentation machine encode decode roundtrip).related 1 :=
  machine.represent_matchesStuck encode decode roundtrip

/-- **Stages compose**, along the composite relation at the product cost. -/
def comp (first : Stage source middle) (second : Stage middle target) : Stage source target where
  related := compose first.related second.related
  cost := second.cost * first.cost
  forward := first.forward.comp second.forward
  reflects := first.reflects.comp second.reflects

@[simp] theorem comp_related (first : Stage source middle) (second : Stage middle target) :
    (first.comp second).related = compose first.related second.related :=
  rfl

@[simp] theorem comp_cost (first : Stage source middle) (second : Stage middle target) :
    (first.comp second).cost = second.cost * first.cost :=
  rfl

@[simp] theorem refl_comp (stage : Stage source target) : (refl source).comp stage = stage := by
  apply ext
  · exact SpanTransport.compose_eq_left stage.related
  · exact Nat.mul_one stage.cost

@[simp] theorem comp_refl (stage : Stage source target) : stage.comp (refl target) = stage := by
  apply ext
  · exact SpanTransport.compose_eq_right stage.related
  · exact Nat.one_mul stage.cost

/-- A chain's endpoint contract and multiplicative cost are independent of
parenthesization. This does not assert that a stage is invertible. -/
theorem comp_assoc {Final : Type} {last : Machine Final Event Verdict Request}
    (first : Stage source middle) (second : Stage middle target) (third : Stage target last) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  apply ext
  · exact SpanTransport.compose_assoc first.related second.related third.related
  · exact (Nat.mul_assoc third.cost second.cost first.cost).symm

/-- A common observation map transports a checked stage without changing its
actual state relation or cost account. -/
def relabel {Event' Verdict' Request' : Type} (stage : Stage source target)
    (events : Event → Event') (verdicts : Verdict → Verdict') (requests : Request → Request') :
    Stage (source.relabel events verdicts requests) (target.relabel events verdicts requests) where
  related := stage.related
  cost := stage.cost
  forward := stage.forward.relabel events verdicts requests
  reflects := stage.reflects.relabel events verdicts requests

@[simp] theorem relabel_related {Event' Verdict' Request' : Type} (stage : Stage source target)
    (events : Event → Event') (verdicts : Verdict → Verdict') (requests : Request → Request') :
    (stage.relabel events verdicts requests).related = stage.related := rfl

@[simp] theorem relabel_cost {Event' Verdict' Request' : Type} (stage : Stage source target)
    (events : Event → Event') (verdicts : Verdict → Verdict') (requests : Request → Request') :
    (stage.relabel events verdicts requests).cost = stage.cost := rfl

@[simp] theorem relabel_refl {Event' Verdict' Request' : Type}
    (events : Event → Event') (verdicts : Verdict → Verdict') (requests : Request → Request') :
    (refl source).relabel events verdicts requests = refl (source.relabel events verdicts requests) := by
  apply ext <;> rfl

/-- Observation transport commutes with stage composition. -/
theorem relabel_comp {Event' Verdict' Request' : Type}
    (first : Stage source middle) (second : Stage middle target)
    (events : Event → Event') (verdicts : Verdict → Verdict') (requests : Request → Request') :
    (first.comp second).relabel events verdicts requests =
      (first.relabel events verdicts requests).comp (second.relabel events verdicts requests) := by
  apply ext <;> rfl

variable (stage : Stage source target)

theorem observe_prefix (fuel : ℕ) {state : Source} {state' : Target}
    (relatedStates : stage.related state state') :
    (source.observe fuel state).Prefix (target.observe (stage.cost * fuel) state') :=
  stage.forward.observe_prefix fuel relatedStates

theorem final_eq {state : Source} {state' : Target} (relatedStates : stage.related state state')
    {fuel fuel' : ℕ} (final : (source.observe fuel state).status.Final)
    (final' : (target.observe fuel' state').status.Final) :
    source.observe fuel state = target.observe fuel' state' :=
  stage.forward.final_eq_forward relatedStates final final'

theorem reflected {state : Source} {state' : Target} (relatedStates : stage.related state state')
    {fuel' : ℕ} (final' : (target.observe fuel' state').status.Final) :
    ∃ fuel, source.observe fuel state = target.observe fuel' state' :=
  stage.reflects relatedStates fuel' final'

theorem never_completes {state : Source} {state' : Target} (relatedStates : stage.related state state')
    (never : ∀ fuel, ¬ (source.observe fuel state).status.Final) (fuel' : ℕ) :
    ¬ (target.observe fuel' state').status.Final :=
  stage.reflects.never_completes relatedStates never fuel'

end Stage

/-! ## The category of machines at a fixed observation interface -/

/-- A machine together with its actual state carrier. Event, verdict and
request types name the common observation interface of this category. -/
structure ObservedMachine (Event Verdict Request : Type) where
  State : Type
  machine : Machine State Event Verdict Request

namespace ObservedMachine

variable {Event Verdict Request : Type}

/-- Bundle an existing machine without changing its transitions or state. -/
def of {State : Type} (machine : Machine State Event Verdict Request) :
    ObservedMachine Event Verdict Request :=
  ⟨State, machine⟩

/-- Morphisms are the existing cost-bounded realization stages. Composition
keeps their relational state correspondence, multiplicative bound and
completion reflection. It does not identify their intermediate executions. -/
instance : CategoryTheory.Category (ObservedMachine Event Verdict Request) where
  Hom source target := Stage source.machine target.machine
  id source := Stage.refl source.machine
  comp first second := first.comp second
  id_comp stage := Stage.refl_comp stage
  comp_id stage := Stage.comp_refl stage
  assoc first second third := Stage.comp_assoc first second third

/-- A common map of observation labels acts functorially on machines and
realization stages while keeping every underlying state carrier. -/
def relabelFunctor {Event' Verdict' Request' : Type}
    (events : Event → Event') (verdicts : Verdict → Verdict')
    (requests : Request → Request') :
    CategoryTheory.Functor (ObservedMachine Event Verdict Request)
      (ObservedMachine Event' Verdict' Request') where
  obj source := ⟨source.State, source.machine.relabel events verdicts requests⟩
  map stage := stage.relabel events verdicts requests
  map_id _ := Stage.relabel_refl events verdicts requests
  map_comp first second := Stage.relabel_comp first second events verdicts requests

end ObservedMachine

/-! ## Reproducible checkpoints over retained execution -/

namespace Machine

open Mettapedia.Machines.ExecutionHints

variable {State Event Verdict Request View : Type}
    (machine : Machine State Event Verdict Request)

/-- The specified strategy is one call of the existing retained runner.
Terminal outcomes remain terminal and suspended requests remain unanswered.
The equality counts runner budgets; it does not count native instructions. -/
theorem continueRun_iterate (budget : Nat)
    (result : List Event × Outcome State Verdict Request) :
    (machine.continueRun 1)^[budget] result = machine.continueRun budget result := by
  induction budget generalizing result with
  | zero => simp
  | succ budget ih =>
      rw [Function.iterate_succ_apply, ih, ← machine.continueRun_add]
      rw [Nat.add_comm 1 budget]

/-- Checkpoint replay computes the original machine's entire internal
residual. Only the named view is supplied by the certificate. -/
theorem checkpoint_endpoint [DecidableEq View]
    (view : (List Event × Outcome State Verdict Request) → View)
    (source target : List Event × Outcome State Verdict Request)
    (points : List (Checkpoint View))
    (accepted : (replay (machine.continueRun 1) view source points).2 = some target) :
    target = machine.continueRun (fuel points) source ∧
      (replay (machine.continueRun 1) view source points).1 = fuel points := by
  obtain ⟨endpoint, calls⟩ := replay_result (machine.continueRun 1) view points source target accepted
  exact ⟨endpoint.trans (machine.continueRun_iterate _ source), calls⟩

/-- For the fixed machine and observation, finite checkpoint evidence exists
exactly for the observed budgeted run. This includes exhausted and suspended
outcomes; neither is promoted to an accepted proof. -/
theorem exists_checkpoints_iff [DecidableEq View]
    (view : (List Event × Outcome State Verdict Request) → View)
    (source : State) (wanted : View) (budget : Nat) :
    (∃ points, fuel points = budget ∧
      check (machine.continueRun 1) view (machine.run 0 source, wanted) points = true) ↔
      view (machine.run budget source) = wanted := by
  rw [exists_check_iff, machine.continueRun_iterate,
    ← machine.run_add, Nat.zero_add]

end Machine

/-! ## Span transport of the composite -/

section Segments

variable {Source Middle Target Event Verdict Request : Type}
  {source : Machine Source Event Verdict Request} {middle : Machine Middle Event Verdict Request}
  {target : Machine Target Event Verdict Request}
  {R : Source → Middle → Prop} {S : Middle → Target → Prop}

variable (source middle target R S) in
/-- **The event-relation composite of two segment relations**: segments
related through a middle segment with the same events. -/
abbrev segmentComposite : SpanRelation source.segmentSpan target.segmentSpan :=
  (segmentRelation source middle R).comp (segmentRelation middle target S)

/-- **The event composite is contained in the segment relation of the composite
relation**; the two have the same related states. -/
theorem segmentComposite_events {first : Segment source} {last : Segment target}
    (matched : (segmentComposite source middle target R S).events first last) :
    (segmentRelation source target (compose R S)).events first last := by
  obtain ⟨mid, ⟨starts, residuals, eventsEq⟩, starts', residuals', eventsEq'⟩ := matched
  exact ⟨⟨mid.start, starts, starts'⟩, ⟨mid.residual, residuals, residuals'⟩, eventsEq.trans eventsEq'⟩

theorem segmentComposite_sourceForthOcc
    (forth : (segmentComposite source middle target R S).SourceForthOcc) :
    (segmentRelation source target (compose R S)).SourceForthOcc :=
  SpanRelation.SourceForthOcc.mono (R := segmentComposite source middle target R S)
    (fun _ _ related => related) (fun _ _ matched => segmentComposite_events matched) forth

theorem segmentComposite_sourceBackOcc
    (back : (segmentComposite source middle target R S).SourceBackOcc) :
    (segmentRelation source target (compose R S)).SourceBackOcc :=
  SpanRelation.SourceBackOcc.mono (R := segmentComposite source middle target R S)
    (fun _ _ related => related) (fun _ _ matched => segmentComposite_events matched) back

theorem segmentComposite_targetForthOcc
    (forth : (segmentComposite source middle target R S).TargetForthOcc) :
    (segmentRelation source target (compose R S)).TargetForthOcc :=
  SpanRelation.TargetForthOcc.mono (R := segmentComposite source middle target R S)
    (fun _ _ related => related) (fun _ _ matched => segmentComposite_events matched) forth

theorem segmentComposite_targetBackOcc
    (back : (segmentComposite source middle target R S).TargetBackOcc) :
    (segmentRelation source target (compose R S)).TargetBackOcc :=
  SpanRelation.TargetBackOcc.mono (R := segmentComposite source middle target R S)
    (fun _ _ related => related) (fun _ _ matched => segmentComposite_events matched) back

/-- The event composite keeps the published events. -/
theorem segmentComposite_keeps :
    (segmentComposite source middle target R S).Keeps (Segment.events (machine := source))
      (Segment.events (machine := target)) :=
  SpanRelation.Keeps.comp (CostSimulation.segmentRelation_keeps (source := source) (target := middle))
    (CostSimulation.segmentRelation_keeps (source := middle) (target := target))

namespace CostSimulation

variable {cost cost' : ℕ}

/-- **Forward simulations give the composite source forth law**, with the
middle segment retained. -/
theorem comp_segment_sourceForthOcc (first : CostSimulation source middle R cost)
    (second : CostSimulation middle target S cost') :
    (segmentComposite source middle target R S).SourceForthOcc :=
  SpanRelation.SourceForthOcc.comp first.segment_sourceForthOcc second.segment_sourceForthOcc

/-- **Backward simulations give the composite source back law.** -/
theorem comp_segment_sourceBackOcc {back back' : ℕ}
    (firstBack : CostSimulation middle source (fun mid state => R state mid) back)
    (secondBack : CostSimulation target middle (fun state'' mid => S mid state'') back') :
    (segmentComposite source middle target R S).SourceBackOcc :=
  SpanRelation.SourceBackOcc.comp (segment_sourceBackOcc firstBack) (segment_sourceBackOcc secondBack)

/-- **Every future formula over published events agrees through the composite**,
given a simulation each way at each stage and atoms that read alike along each
stage.  No past formula is claimed. -/
theorem comp_future_related {back back' : ℕ} (first : CostSimulation source middle R cost)
    (firstBack : CostSimulation middle source (fun mid state => R state mid) back)
    (second : CostSimulation middle target S cost')
    (secondBack : CostSimulation target middle (fun state'' mid => S mid state'') back')
    {Atom : Type} (sourceObserves : Atom → Source → Prop) (middleObserves : Atom → Middle → Prop)
    (targetObserves : Atom → Target → Prop)
    (atoms : ∀ atom, Related R (sourceObserves atom) (middleObserves atom))
    (atoms' : ∀ atom, Related S (middleObserves atom) (targetObserves atom))
    {formula : Tense Atom (List Event)} (future : formula.IsFuture) :
    Related (compose R S) (Tense.sat (source.segments sourceObserves) formula)
      (Tense.sat (target.segments targetObserves) formula) :=
  sat_related_future (source.segments sourceObserves) (target.segments targetObserves)
    (segmentComposite source middle target R S) segmentComposite_keeps
    (fun atom => (atoms atom).compose (atoms' atom))
    (first.comp_segment_sourceForthOcc second) (comp_segment_sourceBackOcc firstBack secondBack) future

end CostSimulation

end Segments

end Mettapedia.GSLT.Distinction.ProductiveBlocks
