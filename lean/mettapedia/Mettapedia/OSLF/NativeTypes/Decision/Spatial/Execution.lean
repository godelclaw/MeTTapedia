import Mettapedia.OSLF.NativeTypes.Decision.Spatial.BagModel

/-!
# A resumable strategy for the finite bag fragment

The syntax is the shared native formula. The continuation retains pending
formulas, bags and split choices. A budget counts strategy transitions; it is
not an instruction bound for the host evaluator or for split enumeration.
The strategy is admitted only for propositions, bag leaves and separation at
index zero. Unsupported formulas do not acquire a semantic judgment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Spatial.Execution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
open BagModel

abbrev Expression := Formula Leaf
abbrev Bag := List Pattern
abbrev Splits := List (Bag × Bag)

def admitted : Expression → Bool
  | .atom _ | .top | .bottom => true
  | .conj left right | .disj left right | .imp left right => admitted left && admitted right
  | .neg inner => admitted inner
  | .separating index left right => index == 0 && admitted left && admitted right
  | .possibility _ | .outgoingUniversal _ => false

/-- Independent recursive evaluation of the admitted finite fragment. -/
def evaluate : Expression → Bag → Bool
  | .atom leaf, bag => evalLeaf leaf bag
  | .top, _ => true
  | .bottom, _ => false
  | .conj left right, bag => evaluate left bag && evaluate right bag
  | .disj left right, bag => evaluate left bag || evaluate right bag
  | .imp left right, bag => !evaluate left bag || evaluate right bag
  | .neg inner, bag => !evaluate inner bag
  | .separating index left right, bag =>
      index == 0 && (BagSplits.enumerate bag).any fun pair =>
        evaluate left pair.1 && evaluate right pair.2
  | .possibility _, _ | .outgoingUniversal _, _ => false

theorem evaluate_exact (formula : Expression) (bag : Bag) (accepted : admitted formula = true) :
    evaluate formula bag = true ↔ BagModel.holds formula bag := by
  induction formula generalizing bag with
  | atom leaf => exact BagModel.evalLeaf_exact leaf bag
  | top => simp [evaluate, BagModel.holds, denotation]
  | bottom => simp [evaluate, BagModel.holds, denotation]
  | neg inner ih =>
    simp only [admitted] at accepted
    change ((!evaluate inner bag) = true) ↔ ¬ BagModel.holds inner bag
    have exactInner := ih bag accepted
    cases value : evaluate inner bag <;> simp_all
  | conj left right ihLeft ihRight =>
    simp only [admitted, Bool.and_eq_true] at accepted
    change ((evaluate left bag && evaluate right bag) = true) ↔
      BagModel.holds left bag ∧ BagModel.holds right bag
    simp only [Bool.and_eq_true, ihLeft bag accepted.1, ihRight bag accepted.2]
  | disj left right ihLeft ihRight =>
    simp only [admitted, Bool.and_eq_true] at accepted
    change ((evaluate left bag || evaluate right bag) = true) ↔
      BagModel.holds left bag ∨ BagModel.holds right bag
    simp only [Bool.or_eq_true, ihLeft bag accepted.1, ihRight bag accepted.2]
  | imp left right ihLeft ihRight =>
    simp only [admitted, Bool.and_eq_true] at accepted
    change ((!evaluate left bag || evaluate right bag) = true) ↔
      (BagModel.holds left bag → BagModel.holds right bag)
    have exactLeft := ihLeft bag accepted.1
    have exactRight := ihRight bag accepted.2
    cases first : evaluate left bag <;> cases second : evaluate right bag <;> simp_all
  | possibility _ ih | outgoingUniversal _ ih => simp [admitted] at accepted
  | separating index left right ihLeft ihRight =>
    simp only [admitted, Bool.and_eq_true, beq_iff_eq] at accepted
    obtain ⟨⟨rfl, acceptsLeft⟩, acceptsRight⟩ := accepted
    change ((true && (BagSplits.enumerate bag).any (fun pair => evaluate left pair.1 && evaluate right pair.2)) = true) ↔
      (spatialPredicate spatial 0 (denotation tests left spatial) (denotation tests right spatial)).1 bag
    refine Iff.trans ?_ (splitBackend.spatial_iff 0
      (denotation tests left spatial) (denotation tests right spatial) bag).symm
    simp only [Bool.true_and, List.any_eq_true, Bool.and_eq_true, splitBackend, ↓reduceIte,
      ihLeft _ acceptsLeft, ihRight _ acceptsRight, BagModel.holds]

/-- The compiled finite strategy and the public compositional checker give the
same answer once the latter has its independently proved sufficient horizon. -/
theorem shared_check_exact (formula : Expression) (bag : Bag) (accepted : admitted formula = true)
    (budget : Nat) (enough : workBound backend tests formula bag ≤ budget) :
    (check backend tests formula bag budget).answer = some (evaluate formula bag) := by
  have decided := checked_complete backend tests formula bag trivial budget enough
  have exactMeaning := evaluate_exact formula bag accepted
  cases checked : check backend tests formula bag budget with
  | proved proof =>
    have evaluated : evaluate formula bag = true := exactMeaning.mpr proof
    simp only [Outcome.answer, evaluated]
  | refuted negative =>
    have evaluated : evaluate formula bag = false := by
      cases value : evaluate formula bag
      · rfl
      · exact False.elim (negative (exactMeaning.mp value))
    simp only [Outcome.answer, evaluated]
  | unknown =>
    rw [checked] at decided
    simp [Outcome.Decided, Outcome.answer] at decided

inductive Binary where
  | conj | disj | imp
  deriving DecidableEq, Repr

def Binary.apply : Binary → Bool → Bool → Bool
  | .conj, left, right => left && right
  | .disj, left, right => left || right
  | .imp, left, right => !left || right

inductive Continuation where
  | halt
  | negate (next : Continuation)
  | binaryLeft (op : Binary) (right : Expression) (bag : Bag) (next : Continuation)
  | binaryRight (op : Binary) (left : Bool) (next : Continuation)
  | splitLeft (left right : Expression) (rightBag : Bag) (rest : Splits) (next : Continuation)
  | splitRight (left right : Expression) (result : Bool) (rest : Splits) (next : Continuation)
  | splitRest (found : Bool) (next : Continuation)

inductive State where
  | eval (formula : Expression) (bag : Bag) (next : Continuation)
  | choose (left right : Expression) (remaining : Splits) (next : Continuation)
  | ret (value : Bool) (next : Continuation)

def begin (formula : Expression) (bag : Bag) : State := .eval formula bag .halt

def step : State → State
  | .eval (.atom leaf) bag next => .ret (evalLeaf leaf bag) next
  | .eval .top _ next => .ret true next
  | .eval .bottom _ next => .ret false next
  | .eval (.neg inner) bag next => .eval inner bag (.negate next)
  | .eval (.conj left right) bag next => .eval left bag (.binaryLeft .conj right bag next)
  | .eval (.disj left right) bag next => .eval left bag (.binaryLeft .disj right bag next)
  | .eval (.imp left right) bag next => .eval left bag (.binaryLeft .imp right bag next)
  | .eval (.separating index left right) bag next =>
      if index == 0 then .choose left right (BagSplits.enumerate bag) next else .ret false next
  | .eval (.possibility _) _ next | .eval (.outgoingUniversal _) _ next => .ret false next
  | .choose _ _ [] next => .ret false next
  | .choose left right (pair :: rest) next =>
      .eval left pair.1 (.splitLeft left right pair.2 rest next)
  | .ret value .halt => .ret value .halt
  | .ret value (.negate next) => .ret (!value) next
  | .ret value (.binaryLeft op right bag next) => .eval right bag (.binaryRight op value next)
  | .ret value (.binaryRight op left next) => .ret (op.apply left value) next
  | .ret value (.splitLeft left right rightBag rest next) =>
      .eval right rightBag (.splitRight left right value rest next)
  | .ret value (.splitRight left right first rest next) =>
      .choose left right rest (.splitRest (first && value) next)
  | .ret value (.splitRest found next) => .ret (found || value) next

def run : Nat → State → State
  | 0, state => state
  | fuel + 1, state => run fuel (step state)

/-- Only a returned value with an empty continuation is conclusive. -/
def answer : State → Option Bool
  | .ret result .halt => some result
  | _ => none

def Continuation.meaning : Continuation → Bool → Bool
  | .halt, value => value
  | .negate next, value => next.meaning (!value)
  | .binaryLeft op right bag next, value => next.meaning (op.apply value (evaluate right bag))
  | .binaryRight op left next, value => next.meaning (op.apply left value)
  | .splitLeft left right rightBag rest next, value =>
      next.meaning ((value && evaluate right rightBag) ||
        rest.any (fun pair => evaluate left pair.1 && evaluate right pair.2))
  | .splitRight left right first rest next, value =>
      next.meaning ((first && value) || rest.any (fun pair => evaluate left pair.1 && evaluate right pair.2))
  | .splitRest found next, value => next.meaning (found || value)

def State.meaning : State → Bool
  | .eval formula bag next => next.meaning (evaluate formula bag)
  | .choose left right remaining next =>
      next.meaning (remaining.any fun pair => evaluate left pair.1 && evaluate right pair.2)
  | .ret value next => next.meaning value

theorem step_meaning (state : State) : (step state).meaning = state.meaning := by
  cases state with
  | eval formula bag next =>
    cases formula <;> simp [step, State.meaning, evaluate, Continuation.meaning, Binary.apply]
    rename_i index left right
    cases index <;> simp
  | choose left right remaining next =>
    cases remaining <;> simp [step, State.meaning, Continuation.meaning]
  | ret value next =>
    cases next <;> simp [step, State.meaning, Continuation.meaning]

theorem run_meaning (fuel : Nat) (state : State) : (run fuel state).meaning = state.meaning := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih => exact (ih (step state)).trans (step_meaning state)

theorem run_add (first extra : Nat) (state : State) :
    run (first + extra) state = run extra (run first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, run]
  | succ first ih => simpa only [Nat.succ_add, run] using ih (step state)

theorem run_return (fuel : Nat) (value : Bool) : run fuel (.ret value .halt) = .ret value .halt := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact ih

theorem answer_correct {state : State} {result : Bool} (read : answer state = some result) :
    state.meaning = result := by
  cases state with
  | eval _ _ _ | choose _ _ _ _ => cases read
  | ret value next =>
    cases next <;> simp only [answer, Option.some.injEq, reduceCtorEq] at read
    subst value
    rfl

theorem run_answer {formula : Expression} {bag : Bag} {fuel : Nat} {result : Bool}
    (read : answer (run fuel (begin formula bag)) = some result) :
    evaluate formula bag = result := by
  change (begin formula bag).meaning = result
  rw [← run_meaning fuel (begin formula bag)]
  exact answer_correct read

/-- Finite strategy paths are witnesses of an actual number of transitions. -/
def Reaches (before after : State) : Prop := ∃ fuel, run fuel before = after

theorem Reaches.one (state : State) : Reaches state (step state) := ⟨1, rfl⟩

theorem Reaches.trans {first middle last : State} (left : Reaches first middle)
    (right : Reaches middle last) : Reaches first last := by
  obtain ⟨a, ha⟩ := left
  obtain ⟨b, hb⟩ := right
  exact ⟨a+b, by rw [run_add, ha, hb]⟩

theorem Reaches.before {state last : State} (path : Reaches (step state) last) : Reaches state last :=
  (Reaches.one state).trans path

private theorem choose_reaches (left right : Expression)
    (first : ∀ bag next, Reaches (.eval left bag next) (.ret (evaluate left bag) next))
    (second : ∀ bag next, Reaches (.eval right bag next) (.ret (evaluate right bag) next))
    (remaining : Splits) (next : Continuation) :
    Reaches (.choose left right remaining next)
      (.ret (remaining.any fun pair => evaluate left pair.1 && evaluate right pair.2) next) := by
  induction remaining generalizing next with
  | nil => exact Reaches.one _
  | cons pair rest ih =>
    apply Reaches.before
    apply (first pair.1 _).trans
    apply Reaches.before
    apply (second pair.2 _).trans
    apply Reaches.before
    apply (ih _).trans
    exact Reaches.one _

theorem evaluate_reaches (formula : Expression) (bag : Bag) (next : Continuation) :
    Reaches (.eval formula bag next) (.ret (evaluate formula bag) next) := by
  induction formula generalizing bag next with
  | atom leaf | top | bottom | possibility _ | outgoingUniversal _ => exact Reaches.one _
  | neg inner ih =>
    apply Reaches.before
    exact (ih bag _).trans (Reaches.one _)
  | conj left right ihLeft ihRight | disj left right ihLeft ihRight | imp left right ihLeft ihRight =>
    apply Reaches.before
    apply (ihLeft bag _).trans
    apply Reaches.before
    exact (ihRight bag _).trans (Reaches.one _)
  | separating index left right ihLeft ihRight =>
    apply Reaches.before
    by_cases zero : index = 0
    · subst index
      simpa [step, evaluate] using choose_reaches left right ihLeft ihRight (BagSplits.enumerate bag) next
    · exact ⟨0, by simp [run, step, evaluate, zero]⟩

theorem eventually_decided (formula : Expression) (bag : Bag) :
    ∃ fuel, answer (run fuel (begin formula bag)) = some (evaluate formula bag) := by
  obtain ⟨fuel, finish⟩ := evaluate_reaches formula bag .halt
  exact ⟨fuel, by rw [begin, finish]; rfl⟩

theorem proved_sound (formula : Expression) (bag : Bag) (accepted : admitted formula = true)
    (fuel : Nat) (proved : answer (run fuel (begin formula bag)) = some true) :
    BagModel.holds formula bag :=
  (evaluate_exact formula bag accepted).mp (run_answer proved)

theorem refuted_sound (formula : Expression) (bag : Bag) (accepted : admitted formula = true)
    (fuel : Nat) (refuted : answer (run fuel (begin formula bag)) = some false) :
    ¬ BagModel.holds formula bag := by
  intro holds
  have positive := (evaluate_exact formula bag accepted).mpr holds
  have negative := run_answer refuted
  rw [positive] at negative
  cases negative

@[simp] theorem no_budget_unknown (formula : Expression) (bag : Bag) :
    answer (run 0 (begin formula bag)) = none := rfl

/-- A resumed cursor is evidence only within its admitted originating request.
Arbitrary wire data is not automatically a value of this structure. -/
structure Session where
  formula : Expression
  bag : Bag
  cursor : State
  accepted : admitted formula = true
  reached : Reaches (begin formula bag) cursor

def Session.begin (formula : Expression) (bag : Bag) (accepted : admitted formula = true) : Session :=
  ⟨formula, bag, Execution.begin formula bag, accepted, ⟨0, rfl⟩⟩

def Session.resume (session : Session) (fuel : Nat) : Session :=
  ⟨session.formula, session.bag, run fuel session.cursor, session.accepted,
    session.reached.trans ⟨fuel, rfl⟩⟩

theorem Session.resume_add (session : Session) (first extra : Nat) :
    (session.resume first).resume extra = session.resume (first + extra) := by
  cases session
  simp only [Session.resume, run_add]

theorem Session.proved (session : Session) (positive : answer session.cursor = some true) :
    BagModel.holds session.formula session.bag := by
  obtain ⟨fuel, reached⟩ := session.reached
  apply proved_sound session.formula session.bag session.accepted fuel
  rw [reached]
  exact positive

theorem Session.refuted (session : Session) (negative : answer session.cursor = some false) :
    ¬ BagModel.holds session.formula session.bag := by
  obtain ⟨fuel, reached⟩ := session.reached
  apply refuted_sound session.formula session.bag session.accepted fuel
  rw [reached]
  exact negative

theorem Session.eventually_decided (session : Session) :
    ∃ fuel, answer (session.resume fuel).cursor = some (evaluate session.formula session.bag) := by
  obtain ⟨past, reached⟩ := session.reached
  obtain ⟨fuel, finish⟩ := evaluate_reaches session.formula session.bag .halt
  refine ⟨fuel, ?_⟩
  change answer (run fuel session.cursor) = _
  rw [← reached, ← run_add, Nat.add_comm past fuel, run_add]
  change answer (run past (run fuel (.eval session.formula session.bag .halt))) = _
  rw [finish, run_return]
  rfl

end Mettapedia.OSLF.NativeTypes.Decision.Spatial.Execution
