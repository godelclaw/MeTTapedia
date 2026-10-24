import Mettapedia.OSLF.NativeTypes.Executable.CounterAbstractions
import Mettapedia.OSLF.Framework.HerbrandSorts
import Mettapedia.Machines.LevinSearch

/-!
# Backward search on counters: symbolic states, the Herbrand bridge, and a Levin portfolio

The counter that may crash at every value (`crashing`) halts from infinitely many states:
every `counter n` steps to `halted`. Its ground backward search cannot list the predecessors of
`halted`. Two ways describe them finitely.

- **Through the Herbrand bridge**, with no presentation written by hand: the language's rules
  become Herbrand rules, backward narrowing computes the symbolic predecessors, and the answers are
  facts about the plan GSLT → MeTTa compiles (`compiled_four_cannot_halt`). The run itself is
  evaluated: unification is defined by well-founded recursion, which the kernel does not unfold.
  The backward box over well-sorted states splits open premises by the grammar's sorts: every
  well-sorted state that crashes is a counter of zero or of a successor
  (`crashes_only_from_numerals`), and not only of zero (`crashes_not_only_from_zero`).
- **By a certificate checked in the kernel**: two nodes, `halted` and `anyCounter` (the pattern
  `counter ?n`), with exact predecessors (`crashPresentation`). Breadth-first search saturates
  after two steps (`crash_saturated`), and `zero_cannot_halt` and `counter_can_halt` are proved
  outright.

A Levin portfolio of three search plans (breadth-first, reversed breadth-first, depth-first)
gives the same answers as the certificate, and each of its answers is a theorem (`levin_reaches`,
`levin_cannotReach`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Executable.Explored.BackwardCounters

open Mettapedia.OSLF.MeTTaIL Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction (rootReducts)
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.BackwardSearch
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.Machines.LevinSearch
open Mettapedia.OSLF.Framework.HerbrandBridge (languageSpan languageSpan_diamond)
open CounterAbstractions

/-! ## Matching `counter ?n` -/

/-- Whether a pattern is a counter, and of what. -/
def counterArgument? : Pattern → Option Pattern
  | .apply "Counter" [argument] => some argument
  | _ => none

theorem match_counter (state : Pattern) :
    matchPattern (.apply "Counter" [.fvar "n"]) state =
      (match counterArgument? state with
        | some argument => [[("n", argument)]]
        | none => []) := by
  cases state with
  | apply label arguments =>
    by_cases isCounter : label = "Counter"
    · subst isCounter
      match arguments with
      | [] => simp [matchPattern, counterArgument?]
      | [argument] => simp [matchPattern, matchArgs, mergeBindings, counterArgument?]
      | first :: second :: rest => simp [matchPattern, counterArgument?]
    · have : counterArgument? (.apply label arguments) = none := by
        unfold counterArgument?
        split
        · rename_i heq; cases heq; exact absurd rfl isCounter
        · rfl
      rw [this]
      simp [matchPattern, Ne.symm isCounter]
  | _ => simp [matchPattern, counterArgument?]

theorem counterArgument_some {state argument : Pattern} (read : counterArgument? state = some argument) :
    state = .apply "Counter" [argument] := by
  unfold counterArgument? at read
  split at read
  · cases read; rfl
  · cases read

theorem crashing_rootReducts (state : Pattern) :
    rootReducts crashing state =
      (match counterArgument? state with
        | some argument => [.apply "Counter" [.apply "Succ" [argument]], halted]
        | none => []) := by
  simp only [rootReducts, crashing, language, advance, crash, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, match_counter]
  cases counterArgument? state <;> simp [applyBindings, halted]

/-! ## The symbolic presentation -/

/-- Two descriptions: the halted state, and every counter. -/
inductive CrashNode where
  | halted
  | anyCounter
  deriving DecidableEq, Repr

def CrashNode.denote : CrashNode → Pattern → Prop
  | .halted, state => state = CounterAbstractions.halted
  | .anyCounter, state => (counterArgument? state).isSome

def CrashNode.member : CrashNode → Pattern → Bool
  | .halted, state => decide (state = CounterAbstractions.halted)
  | .anyCounter, state => (counterArgument? state).isSome

theorem CrashNode.member_exact (node : CrashNode) (state : Pattern) :
    node.member state = true ↔ node.denote state := by
  cases node <;> simp [member, denote]

def CrashNode.predecessors : CrashNode → List CrashNode
  | _ => [.anyCounter]

theorem diamond_halted (state : Pattern) :
    derivedDiamond (languageSpan crashing) (CrashNode.denote .halted) state ↔ (counterArgument? state).isSome := by
  rw [languageSpan_diamond, crashing_rootReducts]
  cases counterArgument? state <;> simp [CrashNode.denote, CounterAbstractions.halted]

theorem diamond_anyCounter (state : Pattern) :
    derivedDiamond (languageSpan crashing) (CrashNode.denote .anyCounter) state ↔ (counterArgument? state).isSome := by
  rw [languageSpan_diamond, crashing_rootReducts]
  cases counterArgument? state <;> simp [CrashNode.denote, counterArgument?]

/-- **The symbolic presentation of backward search to `halted`.** -/
def crashPresentation : Presentation (languageSpan crashing) (· = CounterAbstractions.halted) CrashNode :=
  Presentation.ofExact CrashNode.denote [.halted] CrashNode.predecessors
    (fun state => by simp [CrashNode.denote])
    (fun node state => by
      cases node
      · rw [diamond_halted]; simp [CrashNode.predecessors, CrashNode.denote]
      · rw [diamond_anyCounter]; simp [CrashNode.predecessors, CrashNode.denote])

def crashCovering : crashPresentation.Covering where
  covers node others := others.contains node
  sound node others covered state holds := ⟨node, by simpa using covered, holds⟩
  isGood _ := true
  isGood_sound _ _ := trivial

/-! ## Answers -/

def zero : Pattern := .apply "Zero" []
def succZero : Pattern := .apply "Succ" [zero]

def ask (scheduler : Scheduler CrashNode) (fuel : Nat) (state : Pattern) : Presentation.Answer :=
  crashPresentation.answer scheduler crashCovering CrashNode.member fuel state

#guard ask Scheduler.breadthFirst 2 (counter 5) == .reaches
#guard ask Scheduler.breadthFirst 2 CounterAbstractions.halted == .reaches
#guard ask Scheduler.breadthFirst 2 zero == .cannotReach
#guard ask Scheduler.breadthFirst 2 succZero == .cannotReach
-- One step is not enough to saturate.
#guard ask Scheduler.breadthFirst 1 zero == .unknown

/-- Two breadth-first steps: `halted` and `anyCounter` emitted, `anyCounter` live again. -/
theorem two_steps : crashPresentation.runFrom Scheduler.breadthFirst 2 =
    ⟨[⟨.halted, .halted⟩, ⟨.anyCounter, .anyCounter⟩], [.anyCounter]⟩ := by
  rfl

theorem crash_saturated :
    Presentation.saturated crashCovering (crashPresentation.runFrom Scheduler.breadthFirst 2) = true := by
  rw [two_steps]
  rfl

/-- **The numeral `zero` cannot halt**: a finite certificate on an infinite state space. -/
theorem zero_cannot_halt : ¬ Reaches (languageSpan crashing) (· = CounterAbstractions.halted) zero := by
  apply Presentation.answer_cannotReach (fun node => (CrashNode.member_exact node _).mpr) (scheduler := Scheduler.breadthFirst)
    (covering := crashCovering) (fuel := 2)
  rw [Presentation.answer, if_neg, if_pos crash_saturated]
  rw [two_steps]
  simp [CrashNode.member, zero, counterArgument?, CounterAbstractions.halted]

/-- **Every counter can halt.** -/
theorem counter_can_halt (count : Nat) :
    Reaches (languageSpan crashing) (· = CounterAbstractions.halted) (counter count) := by
  apply Presentation.answer_reaches (fun node state => (CrashNode.member_exact node state).mp) (scheduler := Scheduler.breadthFirst)
    (covering := crashCovering) (fuel := 2)
  rw [Presentation.answer, if_pos]
  rw [two_steps]
  simp [CrashNode.member, counter, counterArgument?]

/-! ## A Levin portfolio of plans -/

/-- A plan as a searcher: what it answers, once it answers. -/
def planSearcher (scheduler : Scheduler CrashNode) (state : Pattern) : Searcher Presentation.Answer :=
  Searcher.ofProbe fun fuel =>
    match ask scheduler fuel state with
    | .unknown => none
    | answer => some answer

/-- Three plans with lengths 1, 2, 2: Kraft sum exactly one. -/
def plans (state : Pattern) : List (Nat × Searcher Presentation.Answer) :=
  [(1, planSearcher Scheduler.breadthFirst state), (2, planSearcher Scheduler.reverseBreadthFirst state),
    (2, planSearcher Scheduler.depthFirst state)]

def portfolio (state : Pattern) : Family (Fin ((plans state).map Prod.fst).length) Presentation.Answer :=
  Family.ofList (plans state) 2 (by simp [plans]) (by simp [plans])

#guard (portfolio (counter 5)).search 4 == some .reaches
#guard (portfolio zero).search 4 == some .cannotReach

theorem plan_answer_sound {scheduler : Scheduler CrashNode} {state : Pattern} {work : Nat}
    {answer : Presentation.Answer} (found : (planSearcher scheduler state).result work = some answer) :
    ∃ fuel, ask scheduler fuel state = answer ∧ answer ≠ .unknown := by
  obtain ⟨fuel, probe⟩ := Searcher.ofProbe_sound found
  refine ⟨fuel, ?_⟩
  cases read : ask scheduler fuel state <;> simp [read] at probe <;> subst probe <;> simp

/-- **A Levin answer `reaches` is a theorem.** -/
theorem portfolio_members (state : Pattern) (member : Fin ((plans state).map Prod.fst).length) :
    ∃ scheduler, (portfolio state).searcher member = planSearcher scheduler state := by
  obtain ⟨index, below⟩ := member
  have small : index < 3 := by simpa [plans] using below
  interval_cases index <;> exact ⟨_, rfl⟩

theorem levin_reaches {state : Pattern} {rounds : Nat}
    (read : (portfolio state).search rounds = some .reaches) :
    Reaches (languageSpan crashing) (· = CounterAbstractions.halted) state := by
  obtain ⟨member, work, found⟩ := (portfolio state).search_sound rounds _ read
  obtain ⟨scheduler, same⟩ := portfolio_members state member
  rw [same] at found
  obtain ⟨fuel, answered, _⟩ := plan_answer_sound found
  exact Presentation.answer_reaches (fun node state => (CrashNode.member_exact node state).mp) answered

/-- **A Levin answer `cannotReach` is a theorem.** -/
theorem levin_cannotReach {state : Pattern} {rounds : Nat}
    (read : (portfolio state).search rounds = some .cannotReach) :
    ¬ Reaches (languageSpan crashing) (· = CounterAbstractions.halted) state := by
  obtain ⟨member, work, found⟩ := (portfolio state).search_sound rounds _ read
  obtain ⟨scheduler, same⟩ := portfolio_members state member
  rw [same] at found
  obtain ⟨fuel, answered, _⟩ := plan_answer_sound found
  exact Presentation.answer_cannotReach (fun node => (CrashNode.member_exact node _).mpr) answered

/-! ## Through the Herbrand bridge -/

section Herbrand

open Mettapedia.OSLF.Framework.HerbrandBridge (answer Goal goalsCheck Profile compiled compiled_cannotReach
  compiled_reaches)
open Mettapedia.OSLF.Framework.BackwardNarrowing (PastBox)
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement (RootProfile)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (gsltSpan)

def haltedGoal : List Pattern := [CounterAbstractions.halted]

def askHerbrand (rules : LanguageDef) (fuel : ℕ) (state : Pattern) : Presentation.Answer :=
  answer rules haltedGoal Scheduler.breadthFirst fuel state

#guard askHerbrand crashing 2 (counter 5) == .reaches
#guard askHerbrand crashing 2 zero == .cannotReach
#guard askHerbrand halting 6 (counter 0) == .reaches
#guard askHerbrand halting 6 (counter 4) == .cannotReach
#guard askHerbrand counting 1 (counter 0) == .cannotReach

theorem halting_herbrand : Profile halting :=
  Mettapedia.OSLF.Framework.HerbrandBridge.Profile.of_check (by cbv)

theorem halted_goal : goalsCheck haltedGoal = true := by decide

/-- **The compiled counter that halts only at three never halts from four**, read from an automatic
backward search. -/
theorem compiled_four_cannot_halt (read : askHerbrand halting 6 (counter 4) = .cannotReach) :
    ¬ Reaches (gsltSpan (compiled halting stateSort)) (Goal haltedGoal) (counter 4) :=
  compiled_cannotReach (RootProfile.of_check halting_profile) halting_herbrand halted_goal
    (sorted_of_check (by cbv)) read

/-- **The compiled counter that halts at three halts from zero.** -/
theorem compiled_zero_halts (read : askHerbrand halting 6 (counter 0) = .reaches) :
    Reaches (gsltSpan (compiled halting stateSort)) (Goal haltedGoal) (counter 0) :=
  compiled_reaches (RootProfile.of_check halting_profile) halting_herbrand halted_goal
    (sorted_of_check (by cbv)) read

/-! ### The backward box over well-sorted states -/

open Mettapedia.OSLF.Framework.HerbrandBridge (pastBox Grammar compiled_pastBox_iff pastBox_proved
  pastBox_refuted)

/-- The counters of zero and of a successor. -/
def numeralCounters : List Pattern :=
  [.apply "Counter" [.apply "Zero" []], .apply "Counter" [.apply "Succ" [.fvar "n"]]]

def askPast (rules : LanguageDef) (types : List Pattern) (allowance : ℕ) : PastBox :=
  pastBox rules types "State" allowance halted

#guard askPast crashing numeralCounters 1 == .proved
#guard askPast crashing [counter 0] 1 == .unknown
#guard askPast crashing [counter 0] 2 == .refuted
#guard askPast halting [counter 3] 0 == .proved
#guard askPast halting [counter 0] 0 == .refuted

theorem crashing_grammar : Grammar crashing := Mettapedia.OSLF.Framework.HerbrandBridge.Grammar.of_check (by cbv)

theorem crashing_herbrand : Profile crashing := Mettapedia.OSLF.Framework.HerbrandBridge.Profile.of_check (by cbv)

/-- **Every well-sorted state from which the compiled crashing counter halts is a counter of a
numeral shape**, read from the sorted backward box. -/
theorem crashes_only_from_numerals (read : askPast crashing numeralCounters 1 = .proved) :
    derivedBox (between (gsltSpan (compiled crashing stateSort)) (Sorted crashing)) (Goal numeralCounters) halted :=
  (compiled_pastBox_iff (RootProfile.of_check crashing_profile) _ _).mpr
    (pastBox_proved crashing_grammar crashing_herbrand (by cbv) (sorted_of_check (by cbv)) read)

/-- **Not every one is the counter of zero.** -/
theorem crashes_not_only_from_zero (read : askPast crashing [counter 0] 2 = .refuted) :
    ¬ derivedBox (between (gsltSpan (compiled crashing stateSort)) (Sorted crashing)) (Goal [counter 0]) halted :=
  fun holds => pastBox_refuted crashing_grammar crashing_herbrand (by decide) (sorted_of_check (by cbv)) read
    ((compiled_pastBox_iff (RootProfile.of_check crashing_profile) _ _).mp holds)

end Herbrand

end Mettapedia.OSLF.NativeTypes.Executable.Explored.BackwardCounters
