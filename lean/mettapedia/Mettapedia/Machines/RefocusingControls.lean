import Mettapedia.Machines.Refocusing
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep

/-!
# Refocusing controls and an arithmetic adequacy instance

The source evaluator is an independent structural function. Its exact
correspondence covers every term in this arithmetic instance, including
arbitrarily nested sums. A looping contraction and an invalid term separate
divergence from stuckness. This instance makes no claim about MeTTa's choices,
effects, binders or scheduling.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RefocusingControls

open Refocusing Mettapedia.GSLT.Distinction.ProductiveBlocks

inductive Expr where
  | number (value : Nat)
  | add (left right : Expr)
  | spin
  | invalid
deriving Repr, DecidableEq

inductive Frame where
  | left (right : Expr)
  | right (left : Nat)

inductive Redex where
  | add (left right : Nat)
  | spin

def signature : Signature where
  Term := Expr
  Kind := Unit
  Frame _ _ := Frame
  Value _ := Nat
  Redex _ := Redex
  plugFrame
    | .left right, term => .add term right
    | .right left, term => .add (.number left) term
  valueTerm := Expr.number
  redexTerm
    | .add left right => .add (.number left) (.number right)
    | .spin => .spin

def inspect (kind : Unit) : Expr → Decision signature kind
  | .number value => .value value
  | .add left right => .descend (inner := ()) left (.left right)
  | .spin => .redex .spin
  | .invalid => .blocked .invalid

def resume {outer inner : Unit} : signature.Frame outer inner → Nat → Decision signature outer
  | .left right, value => .descend (inner := ()) right (.right value)
  | .right left, value => .redex (.add left value)

def strategy : Strategy signature where
  inspect := inspect
  resume := resume
  contract
    | .add left right => some (.number (left + right))
    | .spin => some .spin
  inspect_correct := by intro kind term; cases term <;> rfl
  resume_correct := by intro outer inner frame value; cases frame <;> rfl

def termWork : Expr → Nat
  | .add left right => termWork left + termWork right + 3
  | _ => 1

def frameWork : Frame → Nat
  | .left right => termWork right + 2
  | .right _ => 1

def credits : SearchCredits strategy where
  term _ := termWork
  frame := frameWork
  inspect_value := by
    intro kind term value inspected
    cases term <;> simp_all [strategy, inspect, termWork]
  inspect_descend := by
    intro outer input inner child context inspected
    cases inner
    cases input with
    | add left right =>
        cases inspected
        simp only [termWork, frameWork]
        omega
    | number => cases inspected
    | spin => cases inspected
    | invalid => cases inspected
  resume_value := by
    intro outer inner context value result resumed
    cases context <;> simp_all [strategy, resume]
  resume_descend := by
    intro outer inner next context value child following resumed
    cases next
    cases context with
    | left right => cases resumed; simp [frameWork]
    | right left => cases resumed

/-- Absence of a returned arithmetic value includes both spin and invalid;
the machine observations below keep their operational difference. -/
def evaluate : Expr → Option Nat
  | .number value => some value
  | .add left right => do
      let a ← evaluate left
      let b ← evaluate right
      pure (a + b)
  | .spin | .invalid => none

inductive Evaluates : Expr → Nat → Prop where
  | number (value : Nat) : Evaluates (.number value) value
  | add {left right : Expr} {a b : Nat} :
      Evaluates left a → Evaluates right b → Evaluates (.add left right) (a + b)

/-- Independent left-to-right reduction semantics. Navigation is absent:
each successful call performs one source contraction. -/
def reduce : Expr → Option Expr
  | .number _ | .invalid => none
  | .spin => some .spin
  | .add left right =>
      match left, right with
      | .number a, .number b => some (.number (a + b))
      | .number a, right => (reduce right).map fun next => .add (.number a) next
      | left, right => (reduce left).map fun next => .add next right

theorem reduce_add_left {left next : Expr} (right : Expr)
    (reduced : reduce left = some next) :
    reduce (.add left right) = some (.add next right) := by
  cases left with
  | number => cases reduced
  | _ =>
      change (reduce _).map (fun term => Expr.add term right) = some (Expr.add next right)
      simp only [reduced, Option.map_some]

theorem reduce_add_right (left : Nat) {right next : Expr}
    (reduced : reduce right = some next) :
    reduce (.add (.number left) right) = some (.add (.number left) next) := by
  cases right with
  | number => cases reduced
  | _ =>
      change (reduce _).map (fun term => Expr.add (Expr.number left) term) =
        some (Expr.add (Expr.number left) next)
      simp only [reduced, Option.map_some]

theorem reduce_of_source_step {kind : signature.Kind} {first second : signature.Term}
    (step : SourceStep strategy kind first second) : reduce first = some second := by
  induction step with
  | contract redex term contracted =>
      cases redex <;> simp only [strategy] at contracted <;> cases contracted <;> rfl
  | frame frame _ ih =>
      cases frame with
      | left right => exact reduce_add_left right ih
      | right left => exact reduce_add_right left ih

theorem source_step_of_reduce (kind : Unit) (first second : Expr)
    (reduced : reduce first = some second) : SourceStep strategy kind first second := by
  induction first generalizing second with
  | number => cases reduced
  | invalid => cases reduced
  | spin =>
      cases reduced
      exact SourceStep.contract (g := signature) (strategy := strategy) (kind := kind)
        Redex.spin Expr.spin rfl
  | add left right ihLeft ihRight =>
      cases left with
      | number a =>
          cases right with
          | number b =>
              cases reduced
              exact SourceStep.contract (g := signature) (strategy := strategy) (kind := kind)
                (Redex.add a b) (Expr.number (a + b)) rfl
          | _ =>
              obtain ⟨next, child, rfl⟩ := Option.map_eq_some_iff.mp reduced
              exact SourceStep.frame (g := signature) (strategy := strategy)
                (outer := kind) (inner := kind) (Frame.right a) (ihRight next child)
      | _ =>
          obtain ⟨next, child, rfl⟩ := Option.map_eq_some_iff.mp reduced
          exact SourceStep.frame (g := signature) (strategy := strategy)
            (outer := kind) (inner := kind) (Frame.left right) (ihLeft next child)

theorem source_step_iff_reduce (kind : Unit) (first second : Expr) :
    SourceStep strategy kind first second ↔ reduce first = some second :=
  ⟨reduce_of_source_step, source_step_of_reduce kind first second⟩

theorem source_step_determinate (kind : Unit) (first second third : Expr)
    (left : SourceStep strategy kind first second)
    (right : SourceStep strategy kind first third) : second = third :=
  Option.some.inj ((reduce_of_source_step left).symm.trans (reduce_of_source_step right))

theorem frame_normal_nonvalue (frame : Frame) (term : Expr)
    (normal : reduce term = none) (nonvalue : ∀ value, term ≠ .number value) :
    reduce (signature.plugFrame (outer := ()) (inner := ()) frame term) = none ∧
      ∀ value, signature.plugFrame (outer := ()) (inner := ()) frame term ≠ .number value := by
  constructor
  · cases frame with
    | left right =>
        cases term with
        | number value => exact False.elim (nonvalue value rfl)
        | _ =>
            change (reduce _).map (fun child => Expr.add child right) = none
            rw [normal]
            rfl
    | right left =>
        cases term with
        | number value => exact False.elim (nonvalue value rfl)
        | _ =>
            change (reduce _).map (fun child => Expr.add (Expr.number left) child) = none
            rw [normal]
            rfl
  · intro value equal
    cases frame <;> cases equal

theorem context_normal_nonvalue {outer inner : signature.Kind}
    (context : Context signature outer inner) (term : Expr)
    (normal : reduce term = none) (nonvalue : ∀ value, term ≠ .number value) :
    reduce (context.plug term) = none ∧ ∀ value, context.plug term ≠ .number value := by
  induction context generalizing term with
  | nil => exact ⟨normal, nonvalue⟩
  | cons rest frame ih =>
      obtain ⟨normal, nonvalue⟩ := frame_normal_nonvalue frame term normal nonvalue
      exact ih _ normal nonvalue

/-- This terminal-normality proof uses the independent source reducer and
the frame grammar, rather than assuming reverse tracing. -/
theorem terminal_source_normal (state : State signature ())
    (stopped : transition strategy state = none) (target : Expr) :
    ¬ SourceStep strategy () state.readback target := by
  have normal : reduce state.readback = none := by
    cases state with
    | eval term context =>
        cases term with
        | invalid =>
            exact (context_normal_nonvalue context .invalid rfl (by intro value equal; cases equal)).1
        | _ => simp [transition, strategy, inspect, advance] at stopped
    | ret value context =>
        cases context with
        | nil => rfl
        | cons rest frame =>
            cases frame <;> simp [transition, strategy, resume, advance] at stopped
  intro step
  have reduced := reduce_of_source_step step
  rw [normal] at reduced
  cases reduced

theorem source_paths_trace_exactly (state : State signature ()) (targets : List Expr)
    (path : List.IsChain (SourceStep strategy ()) (state.readback :: targets)) :
    ∃ fuel final, (machine strategy ()).run fuel state =
      ((state.readback :: targets).zip targets, .exhausted final) ∧
      final.readback = targets.getLastD state.readback :=
  credits.trace_source_path () (source_step_determinate ()) terminal_source_normal state targets path

theorem independent_source_paths_are_schedulable {n : Nat}
    (states : Fin n → State signature ()) (targets : Fin n → List Expr)
    (paths : ∀ id, List.IsChain (SourceStep strategy ()) ((states id).readback :: targets id)) :
    ∃ clocks : Fin n → Nat, ∃ schedule : List
        (Mettapedia.GSLT.Distinction.ScheduledFrontier.Command n),
      (Mettapedia.GSLT.Distinction.ScheduledFrontier.view
        (Mettapedia.GSLT.Distinction.ScheduledFrontier.execute
          (ProductiveCoreOrdered.orderedCore (core strategy ())) schedule
          (Mettapedia.GSLT.Distinction.ScheduledFrontier.reserve clocks
            (fun id ↦ [states id])))).map State.readback =
        List.ofFn (fun id ↦ (targets id).getLastD (states id).readback) :=
  credits.scheduled_source_realization () (source_step_determinate ()) terminal_source_normal
    states targets paths

namespace Scheduled

def sum : Expr := .add (.number 2) (.number 3)

def states (id : Fin 3) : State signature () :=
  .eval (if id = 1 then .spin else sum) .nil

def clocks (id : Fin 3) : Nat := if id = 1 then 3 else 5

def readout (rounds : Nat) : List Expr :=
  (Mettapedia.GSLT.Distinction.ScheduledFrontier.view
    (Mettapedia.GSLT.Distinction.ScheduledFrontier.execute
      (ProductiveCoreOrdered.orderedCore (core strategy ()))
      (Mettapedia.GSLT.Distinction.ScheduledFrontier.rounds 1 rounds)
      (Mettapedia.GSLT.Distinction.ScheduledFrontier.reserve clocks
        (fun id ↦ [states id])))).map State.readback

/-- Two equal arithmetic branches keep their occurrence positions around a
finite prefix of a diverging branch. Service beyond a reservation leaves its
exact residual at the reserved boundary. -/
theorem unequal_clocks_preserve_order_and_duplicates :
    readout 5 = [.number 5, .spin, .number 5] ∧
      readout 8 = readout 5 := by decide +kernel

/-- An underserviced branch keeps its pending computation. Finite allocation
is not itself evidence that a requested source contraction has occurred. -/
theorem insufficient_service_preserves_pending_work :
    readout 4 = [sum, .spin, sum] ∧
      readout 4 ≠ [.number 5, .spin, .number 5] := by decide +kernel

end Scheduled

theorem divergence_iff_source_reduction (state : State signature ()) :
    (machine strategy ()).DivergesWithin state ↔
      ∃ terms : Nat → Expr, terms 0 = state.readback ∧
        ∀ n, SourceStep strategy () (terms n) (terms (n + 1)) :=
  credits.divergence_iff_source_reduction () (source_step_determinate ()) terminal_source_normal state

namespace Incomplete

/-- A locally reconstructing strategy can still refuse a genuine redex. -/
def strategy : Strategy signature := {
  RefocusingControls.strategy with
  inspect := fun _ term => .blocked term
  inspect_correct := fun _ _ => rfl
}

theorem reconstruction_does_not_supply_terminal_normality :
    ¬ (∀ state : State signature (), transition strategy state = none →
      ∀ target, ¬ SourceStep strategy () state.readback target) := by
  intro normal
  have contracts : SourceStep strategy () (.add (.number 1) (.number 2)) (.number 3) :=
    SourceStep.contract (g := signature) (strategy := strategy) (kind := ())
      (Redex.add 1 2) (.number 3) rfl
  exact normal (.eval (.add (.number 1) (.number 2)) .nil) rfl (.number 3) contracts

end Incomplete

theorem evaluate_iff (term : Expr) (value : Nat) :
    evaluate term = some value ↔ Evaluates term value := by
  constructor
  · intro evaluated
    induction term generalizing value with
    | number n => simp only [evaluate, Option.some.injEq] at evaluated; cases evaluated; exact .number n
    | spin => cases evaluated
    | invalid => cases evaluated
    | add left right ihLeft ihRight =>
        cases leftResult : evaluate left with
        | none => simp [evaluate, leftResult] at evaluated
        | some a =>
            cases rightResult : evaluate right with
            | none => simp [evaluate, leftResult, rightResult] at evaluated
            | some b =>
                simp only [evaluate, leftResult, rightResult, pure] at evaluated
                cases evaluated
                exact .add (ihLeft a leftResult) (ihRight b rightResult)
  · intro evaluated
    induction evaluated with
    | number => rfl
    | add left right ihLeft ihRight => simp [evaluate, ihLeft, ihRight]

theorem evaluate_to_machine {term : Expr} {value : Nat} (evaluated : Evaluates term value)
    (context : Context signature () ()) :
    (core strategy ()).Steps (.eval term context) (.ret value context) := by
  induction evaluated generalizing context with
  | number n => exact .single rfl
  | @add left right a b leftEval rightEval ihLeft ihRight =>
      exact .head rfl
        ((ihLeft (context.cons (.left right))).trans
          (.head rfl ((ihRight (context.cons (.right a))).trans
            (.head rfl (.single rfl)))))

theorem source_step_preserves_evaluate {kind : signature.Kind} {first second : signature.Term}
    (step : SourceStep strategy kind first second) : evaluate first = evaluate second := by
  induction step with
  | contract redex term contracts =>
      cases redex <;> simp only [strategy] at contracts <;>
        cases contracts <;> rfl
  | frame frame step ih =>
      cases frame <;> simp only [signature, evaluate] <;> rw [ih]

theorem source_steps_preserve_evaluate {kind : Unit} {first second : Expr}
    (ran : Relation.ReflTransGen (SourceStep strategy kind) first second) :
    evaluate first = evaluate second := by
  induction ran with
  | refl => rfl
  | tail _ last ih => exact ih.trans (source_step_preserves_evaluate last)

theorem answer_evaluate {state : State signature ()} {value : Nat}
    (observed : answer state = some value) : evaluate state.readback = some value := by
  cases state with
  | eval => cases observed
  | ret result context =>
      cases context with
      | nil => cases observed; rfl
      | cons => cases observed

/-- Exact terminating-answer correspondence for arbitrary arithmetic terms.
Neither side is defined by running the other. -/
theorem produces_iff_evaluate (term : Expr) (value : Nat) :
    (answerCore strategy ()).Produces term value ↔ evaluate term = some value := by
  constructor
  · rintro ⟨final, ran, observed⟩
    exact (source_steps_preserve_evaluate (core_steps_sound strategy ran)).trans
      (answer_evaluate observed)
  · intro evaluated
    exact ⟨.ret value .nil, evaluate_to_machine ((evaluate_iff term value).mp evaluated) .nil, rfl⟩

def program : Expr := .add (.add (.number 20) (.number 1)) (.add (.number 18) (.number 3))

theorem nested_arithmetic_answer : (answerCore strategy ()).Produces program (42 : Nat) :=
  (produces_iff_evaluate program 42).mpr rfl

theorem nested_arithmetic_execution :
    ((machine strategy ()).run 17 (.eval program .nil)).2 = .finished (42 : Nat) ∧
    ((machine strategy ()).run 17 (.eval program .nil)).1.length = 3 := ⟨rfl, rfl⟩

theorem nested_source_path_is_traced :
    ∃ fuel final, (machine strategy ()).run fuel (.eval program .nil) =
      ([(program, .add (.number 21) (.add (.number 18) (.number 3))),
        (.add (.number 21) (.add (.number 18) (.number 3)), .add (.number 21) (.number 21)),
        (.add (.number 21) (.number 21), .number 42)], .exhausted final) ∧
      final.readback = .number 42 := by
  apply source_paths_trace_exactly (.eval program .nil)
    [.add (.number 21) (.add (.number 18) (.number 3)),
      .add (.number 21) (.number 21), .number 42]
  change List.IsChain (SourceStep strategy ())
    [program, .add (.number 21) (.add (.number 18) (.number 3)),
      .add (.number 21) (.number 21), .number 42]
  apply List.isChain_cons_cons.mpr
  refine ⟨source_step_of_reduce () _ _ rfl, ?_⟩
  apply List.isChain_cons_cons.mpr
  refine ⟨source_step_of_reduce () _ _ rfl, ?_⟩
  apply List.isChain_cons_cons.mpr
  exact ⟨source_step_of_reduce () _ _ rfl, .singleton _⟩

theorem instruction_cost_survives_observation_erasure :
    (machine strategy ()).spent (fun _ => 1) 17 (.eval program .nil) = 17 ∧
    ((machine strategy ()).run 17 (.eval program .nil)).1.length = 3 := ⟨rfl, rfl⟩

theorem event_answers_iff_evaluate (term : Expr) (value : Nat) :
    (∃ fuel events, (machine strategy ()).run fuel (.eval term .nil) =
      (events, .finished value)) ↔ evaluate term = some value :=
  (Refocusing.produces_iff_finished strategy () term value).symm.trans
    (produces_iff_evaluate term value)

theorem administrative_prefix_is_pending :
    (machine strategy ()).run 2 (.eval program .nil) =
      ([], .exhausted (.eval (.number 20)
        (@Quiver.Path.cons signature.Kind signature.frameQuiver () () ()
          (@Quiver.Path.cons signature.Kind signature.frameQuiver () () ()
            .nil (Frame.left (.add (.number 18) (.number 3))))
          (Frame.left (.number 1))))) := rfl

theorem prefix_resumption (first more : Nat) (state : State signature ()) :
    (machine strategy ()).run (first + more) state =
      (machine strategy ()).continueRun more ((machine strategy ()).run first state) :=
  (machine strategy ()).run_add first more state

/-! ## Coarser observations retain the actual continuation

The existing event-machine relabeling supplies the generic laws. This instance
keeps one occurrence marker per contraction while hiding its source terms.
It does not erase pending frames or re-execute the source to obtain a view.
-/

def occurrenceView : Machine (State signature ()) Unit Nat Empty :=
  machineWithObserver strategy () fun _ _ => ()

theorem occurrence_view_is_projection :
    occurrenceView = (machine strategy ()).relabel (fun _ => ()) id id :=
  machineWithObserver_relabel strategy () (fun state next => (state.readback, next.readback))
    (fun _ => ())

theorem occurrence_view_keeps_residual (fuel : Nat) (state : State signature ()) :
    occurrenceView.run fuel state =
      (((machine strategy ()).run fuel state).1.map (fun _ => ()),
        ((machine strategy ()).run fuel state).2) := by
  have relabeled := (machine strategy ()).run_relabel (fun _ => ()) id id fuel state
  exact occurrence_view_is_projection ▸ relabeled.trans
    (congrArg (fun outcome =>
      (((machine strategy ()).run fuel state).1.map (fun _ => ()), outcome))
        (Outcome.relabel_id ((machine strategy ()).run fuel state).2))

theorem occurrence_view_keeps_cost (price : State signature () → Nat)
    (fuel : Nat) (state : State signature ()) :
    occurrenceView.spent price fuel state = (machine strategy ()).spent price fuel state := by
  rw [occurrence_view_is_projection]
  exact (machine strategy ()).spent_relabel (fun _ => ()) id id price fuel state

theorem occurrence_view_keeps_divergence (state : State signature ()) :
    occurrenceView.DivergesWithin state ↔ (machine strategy ()).DivergesWithin state := by
  rw [occurrence_view_is_projection]
  exact (machine strategy ()).relabel_divergesWithin_iff (fun _ => ()) id id state

/-- The summary cannot recover an erased history: two actual executions have
the same result and occurrence markers, but different source-step events. -/
theorem occurrence_summary_does_not_reconstruct_history :
    occurrenceView.run 7 (.eval (.add (.number 2) (.number 3)) .nil) =
      occurrenceView.run 7 (.eval (.add (.number 1) (.number 4)) .nil) ∧
    ((machine strategy ()).run 7 (.eval (.add (.number 2) (.number 3)) .nil)).1 ≠
      ((machine strategy ()).run 7 (.eval (.add (.number 1) (.number 4)) .nil)).1 := by
  constructor
  · rfl
  · change [(Expr.add (.number 2) (.number 3), Expr.number 5)] ≠
      [(Expr.add (.number 1) (.number 4), Expr.number 5)]
    decide

theorem invalid_stays_stuck :
    (machine strategy ()).run 1 (.eval .invalid .nil) =
      ([], .stuck (.eval .invalid .nil)) := rfl

theorem self_contraction_is_computation :
    transition strategy (.eval .spin (.nil : Context signature () ())) =
      some (true, .eval .spin .nil) ∧
    (machine strategy ()).step (.eval .spin .nil) =
      some (.publish [(.spin, .spin)] (.eval .spin .nil)) := ⟨rfl, rfl⟩

theorem spin_runs (fuel : Nat) :
    (machine strategy ()).run fuel (.eval .spin .nil) =
      (List.replicate fuel (.spin, .spin), .exhausted (.eval .spin .nil)) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      change ((.spin, .spin) :: ((machine strategy ()).run fuel (.eval .spin .nil)).1,
        ((machine strategy ()).run fuel (.eval .spin .nil)).2) = _
      rw [ih]
      rfl

theorem spin_diverges : (machine strategy ()).DivergesWithin (.eval .spin .nil) := by
  intro fuel
  exact ⟨.eval .spin .nil, congrArg Prod.snd (spin_runs fuel)⟩

theorem spin_has_every_event_prefix (count : Nat) :
    ∃ fuel events final, events.length = count ∧
      (machine strategy ()).run fuel (.eval .spin .nil) = (events, .exhausted final) :=
  credits.divergence_has_event_prefixes (.eval .spin .nil) spin_diverges count

theorem spin_has_infinite_source_reduction :
    ∃ terms : Nat → Expr, terms 0 = .spin ∧
      ∀ n, SourceStep strategy () (terms n) (terms (n + 1)) :=
  credits.divergence_has_source_reduction (.eval .spin .nil) spin_diverges

theorem administrative_loops_are_impossible (states : Nat → State signature ()) :
    ¬ (∀ n, transition strategy (states n) = some (false, states (n + 1))) :=
  credits.no_infinite_administration states

theorem different_terminal_observations :
    ((machine strategy ()).run 1 (.eval .invalid .nil)).2 ≠
      ((machine strategy ()).run 2 (.eval (.number 0) .nil)).2 := by
  intro same
  cases same

/-! ## Existing rho frame authority is preserved by the adapter -/

namespace AuthoredRho

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep

variable (Value Redex : String → Type)
  (valueTerm : {kind : String} → Value kind → Pattern)
  (redexTerm : {kind : String} → Redex kind → Pattern)

def parallelStack : Context (Authored.signature rhoCalc Value Redex @valueTerm @redexTerm) "Proc" "Proc" :=
  Quiver.Path.nil.cons ⟨rhoParallelContext, rhoParallelContext_authored⟩

theorem parallel_stack_decodes :
    Authored.decode (parallelStack Value Redex @valueTerm @redexTerm) = rhoParallelContext := rfl

theorem parallel_stack_readback (term : Pattern) :
    (parallelStack Value Redex @valueTerm @redexTerm).plug term =
      .collection .hashBag [term] (some "rest") := rfl

def quoteContext : OneHoleContext := .apply "NQuote" [] .hole []

theorem quotation_is_not_an_authored_frame :
    ¬ AuthoredContextFrame rhoCalc "Proc" "Name" quoteContext := by
  rintro ⟨_, rule, member, licensed⟩
  have compiled := compileRuleContexts_complete licensed
  simp only [rhoCalc_rewrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rw [compile_rhoCommRewrite_nil] at compiled
    exact List.not_mem_nil compiled
  · rw [compile_rhoParCongRewrite] at compiled
    simp [quoteContext, rhoParallelContext] at compiled

end AuthoredRho

/-! Local reconstruction alone permits a strategy that keeps descending
through an identity frame. The search-credit obligation rejects it. -/

namespace Unproductive

def signature : Signature where
  Term := Nat
  Kind := Unit
  Frame _ _ := Unit
  Value _ := Nat
  Redex _ := Nat
  plugFrame _ term := term
  valueTerm value := value
  redexTerm redex := redex

def strategy : Strategy signature where
  inspect _ term := .descend (inner := ()) term ()
  resume _ value := .value value
  contract _ := none
  inspect_correct _ _ := rfl
  resume_correct _ _ := rfl

theorem local_correctness_does_not_supply_search_credits : ¬ Nonempty (SearchCredits strategy) := by
  rintro ⟨credits⟩
  have impossible := credits.inspect_descend () (0 : Nat) () (0 : Nat) () rfl
  omega

def stack : Nat → Context signature () ()
  | 0 => .nil
  | n + 1 => @Quiver.Path.cons signature.Kind signature.frameQuiver () () () (stack n) ()

theorem endless_administration (n : Nat) :
    transition strategy (.eval (0 : Nat) (stack n)) =
      some (false, .eval (0 : Nat) (stack (n + 1))) := rfl

theorem silent_runs (fuel n : Nat) :
    (machine strategy ()).run fuel (.eval (0 : Nat) (stack n)) =
      ([], .exhausted (.eval (0 : Nat) (stack (n + fuel)))) := by
  induction fuel generalizing n with
  | zero => simp [Machine.run]
  | succ fuel ih =>
      change (machine strategy ()).run fuel (.eval (0 : Nat) (stack (n + 1))) = _
      rw [ih]
      rw [show n + 1 + fuel = n + (fuel + 1) by omega]

/-- Without the search-credit hypothesis, divergence can publish no events. -/
theorem divergence_without_events :
    (machine strategy ()).DivergesWithin (.eval (0 : Nat) (stack 0)) ∧
    ∀ fuel, ((machine strategy ()).run fuel (.eval (0 : Nat) (stack 0))).1 = [] := by
  constructor
  · intro fuel
    exact ⟨.eval (0 : Nat) (stack (0 + fuel)), congrArg Prod.snd (silent_runs fuel 0)⟩
  · intro fuel
    exact congrArg Prod.fst (silent_runs fuel 0)

theorem silent_divergence_has_no_complete_event_prefixes :
    ¬ (∀ count : Nat, ∃ fuel events final, events.length = count ∧
      (machine strategy ()).run fuel (.eval (0 : Nat) (stack 0)) =
        (events, .exhausted final)) := by
  intro prefixes
  obtain ⟨fuel, events, _, length, ran⟩ := prefixes 1
  have empty := divergence_without_events.2 fuel
  rw [ran] at empty
  simp only at empty
  rw [empty] at length
  cases length

end Unproductive

end Mettapedia.Machines.RefocusingControls
