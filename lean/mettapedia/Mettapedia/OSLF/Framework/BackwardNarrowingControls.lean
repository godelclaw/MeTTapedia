import Mettapedia.OSLF.Framework.BackwardNarrowingGround

/-!
# Controls: backward narrowing on first-order counters

Three counter languages over `zero`, `succ`, `counter` and `halted`, with every symbolic
predecessor computed by narrowing (no hand-written presentation):

- `crashing` (`counter x ~> counter (succ x)`, `counter x ~> halted`): from `halted`, breadth-first
  search finds `halted` and `counter x₁`, then `counter x₂`, an instance of `counter x₁`, and
  saturates. Every counter can halt; `zero` and `succ zero` cannot.
- `halting` (`counter x ~> counter (succ x)`, `counter 3 ~> halted`): the predecessors are the ground
  counters 3, 2, 1, 0; the search saturates with an empty frontier. `counter 0` can halt;
  `counter 4` cannot, although the counter runs forever.
- `counting` (only `counter x ~> counter (succ x)`): `halted` has no predecessor; nothing halts.

The backward box: every predecessor of `halted` is a counter (crashing), and a positive one
(halting); not every predecessor of `halted` is `counter 0` (halting, refuted by the ground
predecessor `counter 3`); `counter 0` has no predecessor at all (counting). An open premise that
is neither covered nor ground stays unknown.

Over ground states, splitting the open premise `counter x` of the crashing counter decides it: with
the cases `counter zero`, `counter (succ x)`, `counter halted` and `counter (counter x)` every
ground predecessor of `halted` is covered; without `counter halted`, the ground predecessor
`counter halted` refutes the box, since unsorted terms include it. Over well-sorted states the
variable is a numeral, it splits into `zero` and `succ x` only, and the two numeral shapes cover
every predecessor; `counter 0` alone does not, refuted by `counter 1`.

The counter rules are linear, so breadth-first search answers `reaches` from every ground counter
that halts (`halting_complete`). Without linearity both facts fail: under `a ~> b` the pattern
`pair x x` has no symbolic predecessor although `pair a b` steps into it (`twin_incomplete`), and a
rule repeating a variable on its left side gives a non-linear predecessor (`merge`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.BackwardNarrowing.Controls

open Mettapedia.Logic.LP
open Mettapedia.Logic.LP.FirstOrderRewriting (Equation)
open Mettapedia.OSLF.Framework.BackwardSearch
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.GSLT.Core.BranchingTemporal (Scheduler)

inductive Const where
  | zero
  | halted
  deriving DecidableEq

inductive Fn where
  | succ
  | counter
  deriving DecidableEq

def arity : Fn → ℕ := fun _ => 1

abbrev Counters : LPSignature := Signature Const Fn arity

def variable_ (index : ℕ) : Term Counters := .var index
def zero : Term Counters := .const .zero
def halted : Term Counters := .const .halted
def succ (term : Term Counters) : Term Counters := .app .succ fun _ => term
def counter (term : Term Counters) : Term Counters := .app .counter fun _ => term

def numeral : ℕ → Term Counters
  | 0 => zero
  | count + 1 => succ (numeral count)

def advance : Equation Counters := ⟨counter (variable_ 0), counter (succ (variable_ 0))⟩
def crash : Equation Counters := ⟨counter (variable_ 0), halted⟩
def stopAtThree : Equation Counters := ⟨counter (numeral 3), halted⟩

def counting : List (Equation Counters) := [advance]
def crashing : List (Equation Counters) := [advance, crash]
def halting : List (Equation Counters) := [advance, stopAtThree]

def ask (rules : List (Equation Counters)) (fuel : ℕ) (state : Term Counters) : Presentation.Answer :=
  answer rules [halted] Scheduler.breadthFirst fuel state

/-! ## Reaching `halted` -/

#guard ask crashing 2 (counter (numeral 2)) == .reaches
#guard ask crashing 2 zero == .cannotReach
#guard ask crashing 2 (succ zero) == .cannotReach
#guard ask crashing 1 zero == .unknown

#guard ask halting 6 (counter (numeral 0)) == .reaches
#guard ask halting 6 (counter (numeral 3)) == .reaches
#guard ask halting 6 (counter (numeral 4)) == .cannotReach
#guard ask halting 6 (counter (numeral 7)) == .cannotReach

#guard ask counting 1 (counter zero) == .cannotReach

/-! ## The backward box -/

#guard pastBox crashing halted [counter (variable_ 0)] == .proved
#guard pastBox halting halted [counter (succ (variable_ 0))] == .proved
#guard pastBox halting halted [counter zero] == .refuted
#guard pastBox counting (counter zero) [] == .proved
#guard pastBox crashing halted [counter zero] == .unknown

/-! ## What the answers mean -/

theorem numeral_ground : ∀ count, Ground (numeral count)
  | 0 => rfl
  | count + 1 => by
    have earlier := numeral_ground count
    unfold Ground at earlier ⊢
    simp only [numeral, succ, Term.freeVars, earlier]
    ext v
    simp

theorem counter_ground (count : ℕ) : Ground (counter (numeral count)) := by
  have inner := numeral_ground count
  unfold Ground at inner ⊢
  simp only [counter, Term.freeVars, inner]
  ext v
  simp

theorem halted_ground : Ground halted := rfl

/-- **The counter at four never halts**, although it runs forever. -/
theorem four_cannot_halt (read : ask halting 6 (counter (numeral 4)) = .cannotReach) :
    ¬ Reaches (span halting) (fun state => ∃ goal ∈ [halted], Instance goal state) (counter (numeral 4)) :=
  answer_cannotReach (counter_ground 4) read

/-- **Every predecessor of `halted` is a positive counter.** -/
theorem halted_after_positive (read : pastBox halting halted [counter (succ (variable_ 0))] = .proved) :
    derivedBox (span halting) (fun state => ∃ type ∈ [counter (succ (variable_ 0))], Instance type state) halted :=
  pastBox_proved halted_ground read

/-- **Not every predecessor of `halted` is `counter 0`.** -/
theorem halted_not_only_after_zero (read : pastBox halting halted [counter zero] = .refuted) :
    ¬ derivedBox (span halting) (fun state => ∃ type ∈ [counter zero], Instance type state) halted :=
  pastBox_refuted halted_ground read

/-! ## The backward box over ground states, with case splitting -/

def counterSignature : Enumeration Const Fn where
  constants := [.zero, .halted]
  symbols := [.succ, .counter]
  constants_complete constant := by cases constant <;> simp
  symbols_complete symbol := by cases symbol <;> simp

def everyShape : List (Term Counters) :=
  [counter zero, counter (succ (variable_ 0)), counter halted, counter (counter (variable_ 0))]

def numeralShapes : List (Term Counters) := [counter zero, counter (succ (variable_ 0))]

def unsorted : Splitting Const Fn arity := Splitting.unsorted counterSignature

#guard splitPastBox crashing unsorted everyShape halted 1 == .proved
#guard splitPastBox crashing unsorted everyShape halted 0 == .unknown
#guard splitPastBox crashing unsorted numeralShapes halted 1 == .refuted

/-- **Every ground predecessor of `halted` has one of four shapes**, found by splitting. -/
theorem halted_after_every_shape (read : splitPastBox crashing unsorted everyShape halted 1 = .proved) :
    derivedBox (herbrandSpan crashing Ground) (fun state => ∃ type ∈ everyShape, Instance type state) halted :=
  splitPastBox_proved halted_ground halted_ground read

/-- **Not every ground predecessor of `halted` is the counter of a numeral**: `counter halted` is
one, among unsorted terms. -/
theorem halted_not_only_after_numerals (read : splitPastBox crashing unsorted numeralShapes halted 1 = .refuted) :
    ¬ derivedBox (herbrandSpan crashing Ground) (fun state => ∃ type ∈ numeralShapes, Instance type state) halted :=
  splitPastBox_refuted halted_ground halted_ground read

/-! ## Sorts: numerals and states -/

inductive CounterSort where
  | nat
  | state
  deriving DecidableEq

def counterSorting : Sorting Const Fn CounterSort arity where
  constant
    | .zero => some .nat
    | .halted => some .state
  symbol
    | .succ => some .nat
    | .counter => some .state
  argument _ _ := .nat
  constantsOf
    | .nat => [.zero]
    | .state => [.halted]
  symbolsOf
    | .nat => [.succ]
    | .state => [.counter]
  constants_complete constant sort read := by cases constant <;> cases sort <;> simp_all
  symbols_complete symbol sort read := by cases symbol <;> cases sort <;> simp_all

def states : Splitting Const Fn arity := Splitting.sorted counterSorting .state

theorem halted_state : WellSorted counterSorting halted .state := rfl

-- Among well-sorted states the junk shape is gone: the numeral shapes cover every predecessor.
#guard splitPastBox crashing states numeralShapes halted 1 == .proved
#guard splitPastBox crashing states [counter zero] halted 1 == .unknown
#guard splitPastBox crashing states [counter zero] halted 2 == .refuted
#guard splitPastBox halting states [counter (succ (variable_ 0))] halted 0 == .proved

/-- **Every well-sorted predecessor of `halted` is the counter of a numeral.** -/
theorem halted_after_numerals (read : splitPastBox crashing states numeralShapes halted 1 = .proved) :
    derivedBox (herbrandSpan crashing (WellSorted counterSorting · .state))
      (fun state => ∃ type ∈ numeralShapes, Instance type state) halted :=
  splitPastBox_proved halted_ground halted_state read

/-- **Not every well-sorted predecessor of `halted` is `counter 0`**: `counter 1` is one. -/
theorem halted_not_only_after_zero_sorted (read : splitPastBox crashing states [counter zero] halted 2 = .refuted) :
    ¬ derivedBox (herbrandSpan crashing (WellSorted counterSorting · .state))
      (fun state => ∃ type ∈ [counter zero], Instance type state) halted :=
  splitPastBox_refuted halted_ground halted_state read

/-! ## Linear rules: fair search is complete -/

theorem halting_linear : LinearRules halting := LinearRules.of_check (by decide +kernel)

theorem halted_linear : ∀ goal ∈ [halted], goal.Linear := fun goal member => by
  rw [List.mem_singleton.mp member]
  trivial

#guard (backward crashing (counter (variable_ 0))).all Term.linearCheck

/-- **Breadth-first search answers `reaches` from every ground counter that halts.** -/
theorem halting_complete {state : Term Counters} (ground : Ground state)
    (reaches : Reaches (span halting) (fun state => ∃ goal ∈ [halted], Instance goal state) state) :
    ∃ fuel, ask halting fuel state = .reaches :=
  answer_complete halting_linear halted_linear
    (Mettapedia.GSLT.Core.BranchingTemporal.breadthFirst_fair _ _) ground reaches

/-! ## Without linearity -/

inductive Atom where
  | a
  | b
  deriving DecidableEq

inductive Shape where
  | pair
  | wrap
  deriving DecidableEq

def shapeArity : Shape → ℕ
  | .pair => 2
  | .wrap => 1

abbrev Shapes : LPSignature := Signature Atom Shape shapeArity

def slot (index : ℕ) : Term Shapes := .var index
def atomA : Term Shapes := .const .a
def atomB : Term Shapes := .const .b
def pairOf (first second : Term Shapes) : Term Shapes := .app .pair fun i => if i.val = 0 then first else second
def wrapOf (term : Term Shapes) : Term Shapes := .app .wrap fun _ => term

/-- `a ~> b`. -/
def swap : List (Equation Shapes) := [⟨atomA, atomB⟩]

/-- `pair x x ~> wrap x`: the left side repeats a variable. -/
def merge : List (Equation Shapes) := [⟨pairOf (slot 0) (slot 0), wrapOf (slot 0)⟩]

/-- The non-linear pattern `pair x x`. -/
def twin : Term Shapes := pairOf (slot 0) (slot 0)

#guard (backward swap twin).isEmpty
#guard !(backward merge (wrapOf (slot 0))).isEmpty
#guard (backward merge (wrapOf (slot 0))).all fun previous => !previous.linearCheck

theorem merge_not_linear : ¬ LinearRules merge := by
  intro linear
  obtain ⟨_, apart⟩ := (linear _ (List.mem_singleton_self _)).1
  have repeated := apart ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
  simp [slot, Term.freeVars] at repeated

/-- **Without linearity, completeness fails**: `pair a b` steps into an instance of `pair x x`
(`a ~> b` at the first position), is not one itself, and `pair x x` has no symbolic predecessor. -/
theorem twin_incomplete (read : backward swap twin = []) :
    derivedDiamond (span swap) (Instance twin) (pairOf atomA atomB) ∧ ¬ Instance twin (pairOf atomA atomB) ∧
      ∀ previous ∈ backward swap twin, ¬ Instance previous (pairOf atomA atomB) := by
  let context : FirstOrderRewriting.Context Shapes :=
    .app .pair (fun i => if i.val = 0 then atomA else atomB) ⟨0, by decide⟩ .hole
  have filled : ∀ term : Term Shapes, context.fill term = pairOf term atomB := fun term => by
    simp only [context, FirstOrderRewriting.Context.fill, pairOf]
    congr 1
    funext i
    by_cases first : i = ⟨0, by decide⟩
    · subst first
      simp
    · have : i.val ≠ 0 := fun zero => first (Fin.ext zero)
      simp [Function.update_of_ne first, this]
  refine ⟨?_, ?_, by simp [read]⟩
  · refine ⟨⟨(context.fill atomA, context.fill atomB),
      .rule ⟨atomA, atomB⟩ (List.mem_singleton_self _) (Subst.id _) context⟩, filled atomA, ?_⟩
    refine ⟨fun _ => atomB, ?_⟩
    change Term.app _ _ = context.fill atomB
    rw [filled atomB]
    simp only [pairOf]
    congr 1
    funext i
    split_ifs <;> rfl
  · rintro ⟨substitution, same⟩
    have arguments := congrFun (eq_of_heq (Term.app.inj same).2)
    have first : substitution 0 = atomA := by simpa [slot, Subst.applyTerm_var] using arguments ⟨0, by decide⟩
    have second : substitution 0 = atomB := by simpa [slot, Subst.applyTerm_var] using arguments ⟨1, by decide⟩
    cases first.symm.trans second

end Mettapedia.OSLF.Framework.BackwardNarrowing.Controls
