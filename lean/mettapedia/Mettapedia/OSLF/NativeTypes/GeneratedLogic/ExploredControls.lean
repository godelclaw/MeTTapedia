import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ExploredDecider
import Mettapedia.OSLF.NativeTypes.Executable.CounterAbstractions
import Mettapedia.OSLF.NativeTypes.Executable.FiniteModelKripkeControls

/-!
# Controls: explored graphs and backward search at the front door

The three counters over `zero` and `succ` (`counting` counts forever, `crashing` may halt at every value, `halting` may
halt only at three) have infinitely many reachable states.

**Backward search** (evidence `backward`), kernel-evaluated:
- the halting counter never halts from four, though it runs forever (`four_never_halts`), and the dual says it is safe
  (`four_safe`); from zero it halts, found forward first (`zero_halts`);
- the counting counter never halts (`counting_never_halts`); four is never reached from three (`three_not_back`).

**Explored graphs** (a certified decider, evidence `decided`): the explored graph's verdicts on the counters, read
through the abstraction of counts by parity or by a cap at four, are front-door answers about the generated formulas
(`counting_never_deadlocks`, `counting_recurs`, `counting_may_not_halt`, `halting_may_halt`,
`halting_may_deadlock`, `halting_may_not_halt_always`). The explorer's search runs by well-founded recursion, which
the kernel does not evaluate; as for the explored graphs themselves, the answers are evaluated by `#guard`, and each
theorem takes the explorer's read as its hypothesis. Without the decider the front door leaves the questions open.

**Lassos** (evidence `exploration`), kernel-evaluated: beside a branch that grows forever, a cycle proves that some run
of `Loop` goes on forever and meets `Loop` infinitely often (`loop_runs_forever`, `loop_recurs`); on the growing branch
the recurrence stays open.

**The finite models' questions** about a level that only rises (`Low ⇒ Mid ⇒ High`), asked at the front door through
the embedding of the μ-calculus, and read back as the μ-calculus statements about the language's runs:
`Low` never reaches `High` and afterwards `Mid` (a closed region, `low_never_high_then_mid_asked`); `High` has no step
(`high_stuck_asked`, `high_no_step_asked`); no ancestor of `Mid` is `High`, by backward search from `Mid`
(`mid_has_no_high_ancestor_asked`). The backward answers run unification by well-founded recursion and are evaluated by
`#guard`; the backward search's unification is the same as in the backward controls.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.ExploredControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.Executable.Explored (Atoms)
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula (Traversal)
open Mettapedia.OSLF.NativeTypes.Executable.Explored.CounterAbstractions (counter halted numeral counting crashing
  halting stateSort abstract abstract_shape abstract_counter count_numeral CountClasses parityClasses capClasses
  counting_profile' halting_profile' counting_parity halting_cap checked)
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement (rootPlan)
open ExploredDecider

/-! ## Backward search -/

def zero : Pattern := .apply "Zero" []

/-- Some run halts. -/
def halts : Formula 0 := reachFormula [halted]

#guard ask RelationEnv.empty [] halting 2 halts (counter 4) none 6 == .refuted (.backward 6)
#guard ask RelationEnv.empty [] halting 2 halts.dual (counter 4) none 6 == .proved (.backward 6)
#guard ask RelationEnv.empty [] halting 2 halts (counter 0) none 6 == .proved (.exploration 6)
#guard ask RelationEnv.empty [] counting 2 halts (counter 0) none 2 == .refuted (.backward 2)
#guard ask RelationEnv.empty [] halting 2 (reachFormula [counter 2]) (counter 3) none 4 == .refuted (.backward 4)
-- Without backward search, four rounds leave the first question open: the region never closes.
#guard ask RelationEnv.empty [] halting 2 halts (counter 4) none 6 != .unknown 6

/-- **The halting counter never halts from four**: a saturated backward search from `halted`. -/
theorem four_never_halts (read : ask RelationEnv.empty [] halting 2 halts (counter 4) none 6 = .refuted (.backward 6)) :
    ¬ (referenceStructure RelationEnv.empty halting).sat Env.closed halts (counter 4) := ask_refuted read

/-- **So it is safe**: the dual, proved by the same search. -/
theorem four_safe (read : ask RelationEnv.empty [] halting 2 halts.dual (counter 4) none 6 = .proved (.backward 6)) :
    (referenceStructure RelationEnv.empty halting).sat Env.closed halts.dual (counter 4) := ask_proved read

theorem zero_answer : ask RelationEnv.empty [] halting 2 halts (counter 0) none 6 = .proved (.exploration 6) := by
  decide +kernel

/-- **From zero it halts**, found forward first, kernel-evaluated. -/
theorem zero_halts : (referenceStructure RelationEnv.empty halting).sat Env.closed halts (counter 0) :=
  ask_proved zero_answer

/-- **The counting counter never halts.** -/
theorem counting_never_halts (read : ask RelationEnv.empty [] counting 2 halts (counter 0) none 2 = .refuted (.backward 2)) :
    ¬ (referenceStructure RelationEnv.empty counting).sat Env.closed halts (counter 0) := ask_refuted read

/-- **Two is never reached from three**: counters only count up. -/
theorem three_not_back
    (read : ask RelationEnv.empty [] halting 2 (reachFormula [counter 2]) (counter 3) none 4 = .refuted (.backward 4)) :
    ¬ (referenceStructure RelationEnv.empty halting).sat Env.closed (reachFormula [counter 2]) (counter 3) :=
  ask_refuted read

/-! ## Atoms -/

theorem counting_free : counting.isEquationFree = true := by decide
theorem halting_free : halting.isEquationFree = true := by decide

theorem counting_aligned : Mettapedia.OSLF.MeTTaIL.ReferenceStep.ReferenceProfile counting :=
  fun rule member => List.all_eq_true.mp (show counting.rewrites.all Mettapedia.OSLF.MeTTaIL.ReferenceStep.ruleAligned =
    true by decide) rule member

theorem halting_aligned : Mettapedia.OSLF.MeTTaIL.ReferenceStep.ReferenceProfile halting :=
  fun rule member => List.all_eq_true.mp (show halting.rewrites.all Mettapedia.OSLF.MeTTaIL.ReferenceStep.ruleAligned =
    true by decide) rule member

theorem counter_ne_halted (count : ℕ) : counter count ≠ halted := by
  simp [counter, halted]

/-- **Halted, as an atom**: the abstraction of a state is `halted` exactly where `is halted` holds. -/
theorem halted_atom {rules : LanguageDef} (free : rules.isEquationFree = true) (classes : CountClasses) (state : Pattern) :
    (abstract classes state == halted) = true ↔
      (referenceStructure RelationEnv.empty rules).sat Env.closed (.is halted) state := by
  show _ ↔ IsObject state ∧ _
  rw [objectEquivalent_iff_eq_of_isEquationFree free, beq_iff_eq]
  rcases abstract_shape classes state with same | ⟨count, rfl, reduced⟩
  · rw [same]
    constructor
    · rintro rfl
      exact ⟨rfl, rfl⟩
    · exact fun holds => holds.2
  · rw [reduced]
    exact ⟨fun impossible => absurd impossible (counter_ne_halted _),
      fun holds => absurd holds.2 (counter_ne_halted count)⟩

/-- An even numeral: zero, or two successors of one. -/
def evenNumeral : Formula 0 :=
  .mu (.or (.is zero) (.built "Succ" (.cons (.built "Succ" (.cons (.var 0) .nil)) .nil)))

/-- A counter of an even numeral. -/
def evenCounter : Formula 0 := .built "Counter" (.cons evenNumeral .nil)

theorem numeral_object : ∀ count, IsObject (numeral count)
  | 0 => rfl
  | count + 1 => by
    show Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPatternList [numeral count] = true
    simp only [Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPatternList, Bool.and_true]
    exact numeral_object count

theorem sat_evenNumeral (pattern : Pattern) :
    (referenceStructure RelationEnv.empty counting).sat Env.closed evenNumeral pattern ↔
      ∃ half, pattern = numeral (2 * half) := by
  have equal := fun first second =>
    (objectEquivalent_iff_eq_of_isEquationFree (relEnv := RelationEnv.empty) (reading := .syntax) counting_free
      (first := first) (second := second))
  constructor
  · intro holds
    refine holds {other | ∃ half, other = numeral (2 * half)} fun other prefixed => ?_
    rcases prefixed with ⟨_, named⟩ | ⟨parts, ⟨_, outer⟩, all⟩
    · exact ⟨0, (equal _ _).mp named⟩
    · rw [(equal _ _).mp outer]
      match parts, all with
      | [inner], ⟨⟨innerParts, ⟨_, innerSame⟩, innerAll⟩, _⟩ =>
        rw [(equal _ _).mp innerSame]
        match innerParts, innerAll with
        | [deepest], ⟨⟨half, deepestIs⟩, _⟩ =>
          refine ⟨half + 1, ?_⟩
          rw [deepestIs, show 2 * (half + 1) = 2 * half + 1 + 1 by omega]
          rfl
  · rintro ⟨half, rfl⟩ closed prefixed
    induction half with
    | zero => exact prefixed _ (.inl ⟨rfl, Relation.EqvGen.refl _⟩)
    | succ half ih =>
      refine prefixed _ (.inr ⟨[numeral (2 * half + 1)], ⟨numeral_object _, ?_⟩, ?_⟩)
      · rw [show 2 * (half + 1) = 2 * half + 1 + 1 by omega]
        exact Relation.EqvGen.refl _
      · exact ⟨⟨[numeral (2 * half)], ⟨numeral_object _, Relation.EqvGen.refl _⟩, ⟨ih, trivial⟩⟩, trivial⟩

theorem numeral_injective {first second : ℕ} (same : numeral first = numeral second) : first = second := by
  have := congrArg Mettapedia.OSLF.NativeTypes.Executable.Explored.CounterAbstractions.count? same
  simpa [count_numeral] using this

/-- **The class of zero under parity, as an atom**: a counter of an even numeral. -/
theorem even_atom (state : Pattern) :
    (abstract parityClasses state == counter 0) = true ↔
      (referenceStructure RelationEnv.empty counting).sat Env.closed evenCounter state := by
  have equal := fun first second =>
    (objectEquivalent_iff_eq_of_isEquationFree (relEnv := RelationEnv.empty) (reading := .syntax) counting_free
      (first := first) (second := second))
  rw [beq_iff_eq]
  constructor
  · intro classIs
    have even : ∃ half, state = counter (2 * half) := by
      rcases abstract_shape parityClasses state with same | ⟨count, rfl, reduced⟩
      · exact ⟨0, same.symm.trans classIs⟩
      · rw [reduced] at classIs
        have heads := congrArg List.head? (Pattern.apply.inj classIs).2
        simp only [List.head?_cons, Option.some.injEq] at heads
        have parity : count % 2 = 0 := numeral_injective heads
        exact ⟨count / 2, by rw [show 2 * (count / 2) = count by omega]⟩
    obtain ⟨half, rfl⟩ := even
    exact ⟨[numeral (2 * half)], ⟨numeral_object (2 * half) |> fun object => by
      show Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPatternList [numeral (2 * half)] = true
      simp only [Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPatternList, Bool.and_true]
      exact object, Relation.EqvGen.refl _⟩, ⟨(sat_evenNumeral _).mpr ⟨half, rfl⟩, trivial⟩⟩
  · rintro ⟨parts, ⟨_, same⟩, all⟩
    rw [(equal _ _).mp same]
    match parts, all with
    | [part], ⟨partEven, _⟩ =>
      obtain ⟨half, rfl⟩ := (sat_evenNumeral part).mp partEven
      show abstract parityClasses (counter (2 * half)) = counter 0
      rw [abstract_counter]
      show counter ((2 * half) % 2) = counter 0
      rw [show (2 * half) % 2 = 0 by omega]

/-! ## Explored graphs -/

/-- No atoms. -/
def noAtoms (same : Setoid Pattern) : Atoms same 0 := ⟨fun index => index.elim0, fun index => index.elim0⟩

/-- The atom `halted`, read through an abstraction of counts. -/
def haltedAtom (classes : CountClasses) : Atoms (Setoid.ker (abstract classes)) 1 where
  holds _ state := abstract classes state == halted
  invariant _ left right related := by
    show (abstract classes left == halted) = (abstract classes right == halted)
    rw [show abstract classes left = abstract classes right from related]

/-- The atom "in the class of zero" under parity. -/
def evenAtom : Atoms (Setoid.ker (abstract parityClasses)) 1 where
  holds _ state := abstract parityClasses state == counter 0
  invariant _ left right related := by
    show (abstract parityClasses left == counter 0) = (abstract parityClasses right == counter 0)
    rw [show abstract parityClasses left = abstract parityClasses right from related]

/-- Every reachable state has a successor. -/
def neverDeadlocks : Mettapedia.Logic.ModalMuCalculus.Formula Traversal 0 :=
  .nu (.conj (.diamond .future .tt) (.box .future (.var 0)))

/-- Some path reaches the atom. -/
def mayReach : Mettapedia.Logic.ModalMuCalculus.Formula Traversal 1 := .mu (.disj (.var 1) (.diamond .future (.var 0)))

/-- Every path reaches the atom. -/
def mustReach : Mettapedia.Logic.ModalMuCalculus.Formula Traversal 1 :=
  .mu (.disj (.var 1) (.conj (.diamond .future .tt) (.box .future (.var 0))))

/-- Some path meets the atom infinitely often. -/
def recurs : Mettapedia.Logic.ModalMuCalculus.Formula Traversal 1 :=
  .nu (.mu (.disj (.conj (.var 2) (.diamond .future (.var 1))) (.diamond .future (.var 0))))

/-- A query about the counting counter, through parity. -/
def countingQuery {atomCount : ℕ} (formula : Mettapedia.Logic.ModalMuCalculus.Formula Traversal atomCount)
    (atomFormulas : Fin atomCount → Formula 0) (atoms : Atoms (Setoid.ker (abstract parityClasses)) atomCount) :
    Query :=
  ⟨atomCount, formula, atomFormulas, abstract parityClasses, Setoid.ker (abstract parityClasses), atoms, 100, 100000⟩

/-- A query about the halting counter, through the cap at four. -/
def haltingQuery {atomCount : ℕ} (formula : Mettapedia.Logic.ModalMuCalculus.Formula Traversal atomCount)
    (atomFormulas : Fin atomCount → Formula 0) (atoms : Atoms (Setoid.ker (abstract (capClasses 4))) atomCount) :
    Query :=
  ⟨atomCount, formula, atomFormulas, abstract (capClasses 4), Setoid.ker (abstract (capClasses 4)), atoms, 100, 100000⟩

def countingDeadlock : Query := countingQuery neverDeadlocks (fun index => index.elim0) (noAtoms _)
def countingHalts : Query := countingQuery mayReach (fun _ => .is halted) (haltedAtom parityClasses)
def countingRecurs : Query := countingQuery recurs (fun _ => evenCounter) evenAtom
def haltingHalts : Query := haltingQuery mayReach (fun _ => .is halted) (haltedAtom (capClasses 4))
def haltingDeadlock : Query := haltingQuery neverDeadlocks (fun index => index.elim0) (noAtoms _)
def haltingMustHalt : Query := haltingQuery mustReach (fun _ => .is halted) (haltedAtom (capClasses 4))

theorem countingQueries_valid :
    ∀ query ∈ [countingDeadlock, countingHalts, countingRecurs], query.Valid RelationEnv.empty counting stateSort := by
  intro query member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨counting_profile', counting_aligned, checked counting_profile', counting_parity, by decide,
      fun index => index.elim0⟩
  · exact ⟨counting_profile', counting_aligned, checked counting_profile', counting_parity, by decide,
      fun _ state => halted_atom counting_free parityClasses state⟩
  · exact ⟨counting_profile', counting_aligned, checked counting_profile', counting_parity, by decide,
      fun _ state => even_atom state⟩

theorem haltingQueries_valid :
    ∀ query ∈ [haltingHalts, haltingDeadlock, haltingMustHalt], query.Valid RelationEnv.empty halting stateSort := by
  intro query member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨halting_profile', halting_aligned, checked halting_profile', halting_cap, by decide,
      fun _ state => halted_atom halting_free (capClasses 4) state⟩
  · exact ⟨halting_profile', halting_aligned, checked halting_profile', halting_cap, by decide,
      fun index => index.elim0⟩
  · exact ⟨halting_profile', halting_aligned, checked halting_profile', halting_cap, by decide,
      fun _ state => halted_atom halting_free (capClasses 4) state⟩

/-- **The explored graph of the counting counter through parity, as a certified decider.** -/
def countingDecider : Decider RelationEnv.empty counting :=
  decider [countingDeadlock, countingHalts, countingRecurs] countingQueries_valid

/-- **The explored graph of the halting counter through the cap at four, as a certified decider.** -/
def haltingDecider : Decider RelationEnv.empty halting :=
  decider [haltingHalts, haltingDeadlock, haltingMustHalt] haltingQueries_valid

/-- The front door with the counting decider. -/
def askCounting (query : Query) : Answer :=
  askWith RelationEnv.empty [] counting 2 query.native (counter 0) countingDecider none 4

/-- The front door with the halting decider. -/
def askHalting (query : Query) : Answer :=
  askWith RelationEnv.empty [] halting 2 query.native (counter 0) haltingDecider none 4

#guard askCounting countingDeadlock == .proved .decided
#guard askCounting countingRecurs == .proved .decided
#guard askCounting countingHalts == .refuted .decided
#guard askHalting haltingHalts == .proved .decided
#guard askHalting haltingDeadlock == .refuted .decided
#guard askHalting haltingMustHalt == .refuted .decided
-- Without the decider the front door leaves them open: the counters' regions never close.
#guard ask RelationEnv.empty [] counting 2 countingDeadlock.native (counter 0) none 4 == .unknown 4
#guard ask RelationEnv.empty [] counting 2 countingRecurs.native (counter 0) none 4 == .unknown 4

/-- **The counting counter never deadlocks.** -/
theorem counting_never_deadlocks (read : askCounting countingDeadlock = .proved .decided) :
    (referenceStructure RelationEnv.empty counting).sat Env.closed countingDeadlock.native (counter 0) :=
  askWith_proved (forms := none) rfl read

/-- **The counting counter meets an even count infinitely often**: recurrence, through the parity quotient. -/
theorem counting_recurs (read : askCounting countingRecurs = .proved .decided) :
    (referenceStructure RelationEnv.empty counting).sat Env.closed countingRecurs.native (counter 0) :=
  askWith_proved (forms := none) rfl read

/-- **The counting counter cannot halt.** -/
theorem counting_may_not_halt (read : askCounting countingHalts = .refuted .decided) :
    ¬ (referenceStructure RelationEnv.empty counting).sat Env.closed countingHalts.native (counter 0) :=
  askWith_refuted (forms := none) rfl read

/-- **The halting counter may halt.** -/
theorem halting_may_halt (read : askHalting haltingHalts = .proved .decided) :
    (referenceStructure RelationEnv.empty halting).sat Env.closed haltingHalts.native (counter 0) :=
  askWith_proved (forms := none) rfl read

/-- **The halting counter may deadlock**: once halted, it has no step. -/
theorem halting_may_deadlock (read : askHalting haltingDeadlock = .refuted .decided) :
    ¬ (referenceStructure RelationEnv.empty halting).sat Env.closed haltingDeadlock.native (counter 0) :=
  askWith_refuted (forms := none) rfl read

/-- **The halting counter need not halt**: it may count forever. -/
theorem halting_may_not_halt_always (read : askHalting haltingMustHalt = .refuted .decided) :
    ¬ (referenceStructure RelationEnv.empty halting).sat Env.closed haltingMustHalt.native (counter 0) :=
  askWith_refuted (forms := none) rfl read

/-! ## Lassos -/

/-- A constant of a sort. -/
def constantRule (label category : String) : GrammarRule :=
  { label := label, category := category, params := [], syntaxPattern := [] }

/-- A constructor with one parameter. -/
def unaryRule (label category parameter parameterType : String) : GrammarRule :=
  { label := label, category := category, params := [.simple parameter (.base parameterType)], syntaxPattern := [] }

/-- `Loop ⇒ Back`, `Back ⇒ Loop`, `Loop ⇒ Grow(Z)`, `Grow(n) ⇒ Grow(S(n))`: a cycle beside a branch that grows forever. -/
def spinner : LanguageDef :=
  { name := "Spinner", types := ["State", "Nat"],
    terms := [constantRule "Loop" "State", constantRule "Back" "State", unaryRule "Grow" "State" "n" "Nat",
      constantRule "Z" "Nat", unaryRule "S" "Nat" "n" "Nat"],
    equations := [],
    rewrites := [
      { name := "Spin", typeContext := [], premises := [], left := .apply "Loop" [], right := .apply "Back" [],
        bindings := none },
      { name := "Return", typeContext := [], premises := [], left := .apply "Back" [], right := .apply "Loop" [],
        bindings := none },
      { name := "Leave", typeContext := [], premises := [], left := .apply "Loop" [],
        right := .apply "Grow" [.apply "Z" []], bindings := none },
      { name := "Growth", typeContext := [("n", .base "Nat")], premises := [], left := .apply "Grow" [.fvar "n"],
        right := .apply "Grow" [.apply "S" [.fvar "n"]], bindings := none }] }

def loop : Pattern := .apply "Loop" []

/-- Some run goes on forever. -/
def forever : Formula 0 := .nu (.possibly .any (.var 0))

/-- Some run meets `Loop` infinitely often. -/
def loopsForever : Formula 0 := .nu (.mu (.or (.and (.is loop) (.possibly .any (.var 1))) (.possibly .any (.var 0))))

theorem forever_answer : ask RelationEnv.empty [] spinner 2 forever loop none 3 = .proved (.exploration 3) := by
  decide +kernel

/-- **A lasso**: some run of `Loop` goes on forever, proved by the cycle in the explored region, although the region
`Loop` reaches never closes. -/
theorem loop_runs_forever : (referenceStructure RelationEnv.empty spinner).sat Env.closed forever loop :=
  ask_proved forever_answer

theorem loops_answer : ask RelationEnv.empty [] spinner 2 loopsForever loop none 3 = .proved (.exploration 3) := by
  decide +kernel

/-- **Recurrence**: some run meets `Loop` infinitely often. -/
theorem loop_recurs : (referenceStructure RelationEnv.empty spinner).sat Env.closed loopsForever loop :=
  ask_proved loops_answer

-- The growing branch never meets `Loop`; its region never closes and has no lasso, so the recurrence stays open there.
#guard ask RelationEnv.empty [] spinner 2 loopsForever (.apply "Grow" [.apply "Z" []]) none 3 == .unknown 3

/-! ## The finite models' questions -/

section Levels

open Mettapedia.OSLF.NativeTypes.Executable.FiniteModelControls (levels low mid high highThenMid highAncestor canStep
  noStep levelRuns highMid)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.Embeddings (ofMu traversal)
open Mettapedia.Logic.ModalMuCalculus (satisfies)
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula (transitionSystem)

theorem levels_free : levels.isEquationFree = true := by decide
theorem levels_unconditional : Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction.isUnconditionalAligned levels = true := by
  decide
theorem levels_aligned : Mettapedia.OSLF.MeTTaIL.ReferenceStep.ReferenceProfile levels :=
  fun rule member => List.all_eq_true.mp (show levels.rewrites.all Mettapedia.OSLF.MeTTaIL.ReferenceStep.ruleAligned =
    true by decide) rule member

/-- A constant, named: the states the reference structure names it. -/
theorem named_constant {label : String} (state : Pattern) :
    (referenceStructure RelationEnv.empty levels).sat Env.closed (.is (.apply label [])) state ↔ state = .apply label [] := by
  show IsObject state ∧ _ ↔ _
  rw [objectEquivalent_iff_eq_of_isEquationFree levels_free]
  constructor
  · exact fun holds => holds.2
  · rintro rfl
    exact ⟨rfl, rfl⟩

/-- A constant goal: its instances are itself. -/
theorem goal_constant {label : String} (state : Pattern) :
    Mettapedia.OSLF.Framework.HerbrandBridge.Goal [.apply label []] state ↔ state = .apply label [] := by
  constructor
  · rintro ⟨goal, member, bindings, rfl⟩
    rw [List.mem_singleton] at member
    subst member
    exact applyBindings_of_encode bindings (encoded := .const label) rfl
  · rintro rfl
    exact ⟨_, List.mem_singleton_self _, [], applyBindings_of_encode [] (encoded := .const label) rfl⟩

/-- `High` and `Mid`, as atoms. -/
def highMidFormulas : Fin 2 → Formula 0 := ![.is high, .is mid]

theorem highMid_env : Mettapedia.OSLF.Framework.FiniteModels.Certificate.goalEnv highMid =
    fun index => {other | (referenceStructure RelationEnv.empty levels).sat Env.closed (highMidFormulas index) other} := by
  funext index
  ext state
  refine Fin.cases ?_ (fun index' => ?_) index
  · exact (goal_constant state).trans (named_constant state).symm
  · rw [Fin.fin_one_eq_zero index']
    exact (goal_constant state).trans (named_constant state).symm

theorem high_then_mid_answer :
    ask RelationEnv.empty [] levels 2 ((ofMu traversal true highThenMid).subst highMidFormulas) low none 4 =
      .refuted (.closedRegion 4) := by
  decide +kernel

/-- **`Low` never reaches `High` and afterwards `Mid`**, asked at the front door and read back about the runs. -/
theorem low_never_high_then_mid_asked :
    ¬ satisfies (transitionSystem levelRuns)
      (Mettapedia.OSLF.Framework.FiniteModels.Certificate.goalEnv highMid) highThenMid low := by
  rw [highMid_env, satisfies_runs_iff_sat levels_free levels_aligned levels_unconditional highThenMid (by decide)]
  exact ask_refuted high_then_mid_answer

theorem high_step_answer :
    ask RelationEnv.empty [] levels 2 ((ofMu traversal true canStep).subst (fun index => index.elim0)) high none 4 =
      .refuted (.closedRegion 4) := by
  decide +kernel

theorem empty_env : (Mettapedia.Logic.ModalMuCalculus.Env.empty : Mettapedia.Logic.ModalMuCalculus.Env Pattern 0) =
    fun index => {other | (referenceStructure RelationEnv.empty levels).sat Env.closed
      ((fun index => index.elim0 : Fin 0 → Formula 0) index) other} :=
  funext fun index => index.elim0

/-- **`High` has no step**, asked at the front door. -/
theorem high_stuck_asked : ¬ satisfies (transitionSystem levelRuns) Mettapedia.Logic.ModalMuCalculus.Env.empty canStep high := by
  rw [empty_env, satisfies_runs_iff_sat levels_free levels_aligned levels_unconditional canStep (by decide)]
  exact ask_refuted high_step_answer

theorem high_no_step_answer :
    ask RelationEnv.empty [] levels 2 ((ofMu traversal true noStep).subst (fun index => index.elim0)) high none 4 =
      .proved (.closedRegion 4) := by
  decide +kernel

/-- **Every step of `High` leads nowhere**, asked at the front door. -/
theorem high_no_step_asked : satisfies (transitionSystem levelRuns) Mettapedia.Logic.ModalMuCalculus.Env.empty noStep high := by
  rw [empty_env, satisfies_runs_iff_sat levels_free levels_aligned levels_unconditional noStep (by decide)]
  exact ask_proved high_no_step_answer

/-- The ancestry formula of `High`: the embedding of `μX. high ∨ ⧫X`. -/
def highAncestorFormula : Formula 0 := (ofMu traversal true highAncestor).subst (fun _ => .is high)

theorem highAncestor_is_past : pastReachGoals? highAncestorFormula = some [high] := by decide

#guard ask RelationEnv.empty [] levels 2 highAncestorFormula mid none 4 == .refuted (.backward 4)

/-- **No ancestor of `Mid` is `High`**, by backward search from `Mid`, read back about the runs. -/
theorem mid_has_no_high_ancestor_asked
    (read : ask RelationEnv.empty [] levels 2 highAncestorFormula mid none 4 = .refuted (.backward 4)) :
    ¬ satisfies (transitionSystem levelRuns) (fun _ => {high}) highAncestor mid := by
  have env : (fun _ => {high} : Mettapedia.Logic.ModalMuCalculus.Env Pattern 1) =
      fun index => {other | (referenceStructure RelationEnv.empty levels).sat Env.closed
        ((fun _ => .is high : Fin 1 → Formula 0) index) other} := by
    funext _
    ext state
    exact (named_constant state).symm
  rw [env, satisfies_runs_iff_sat levels_free levels_aligned levels_unconditional highAncestor (by decide)]
  exact ask_refuted read

end Levels

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.ExploredControls
