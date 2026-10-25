import Mettapedia.OSLF.NativeTypes.Executable.ExploredCompiled
import Mettapedia.OSLF.Framework.HerbrandBridge

/-!
# Unbounded counters, decided through abstractions of their counts

A counter advances forever: `counter n ~> counter (succ n)`. Its reachable states are infinite, so
the explorer never settles on them. An abstraction of counts (`CountClasses`) maps each count to
the representative of its class; read through it (`abstract`), the explorer settles on finitely
many classes, and its verdicts are properties of the counter's own steps whenever the abstraction
matches futures on well-sorted states (`counterAbstraction`).

Matching reduces to one condition on root reducts: at two counts of one class, the reducts have the
same classes (`abstract_matching`).

- Parity (`parityClasses`) matches futures for the counter that counts forever (`counting`) and for
  the counter that may halt at every value (`crashing`).
- For the counter that may halt only at three (`halting`), parity does not match futures: three and
  one have one parity, three may halt and one may not (`halting_parity_not_matching`). Read through
  parity anyway, the explorer never meets the halting rule and answers that the counter cannot
  halt, which is false. Capping counts at four (`capClasses 4`) matches futures, and its answer is
  that the counter may halt.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Executable.Explored.CounterAbstractions

open Mettapedia.OSLF.MeTTaIL Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction (rootReducts)
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement (rootPlan checkRootProfile RootProfile)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (gsltSpan)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.ObservationSpans
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Compiled

/-! ## The language -/

def natSort : TypeExpr := .base "Nat"
def stateSort : TypeExpr := .base "State"

def terms : List GrammarRule := [
  { label := "Zero", category := "Nat", params := [], syntaxPattern := [.terminal "zero"] },
  { label := "Succ", category := "Nat", params := [.simple "n" natSort],
    syntaxPattern := [.terminal "succ", .nonTerminal "n"] },
  { label := "Counter", category := "State", params := [.simple "n" natSort],
    syntaxPattern := [.terminal "counter", .nonTerminal "n"] },
  { label := "Halted", category := "State", params := [], syntaxPattern := [.terminal "halted"] }]

def numeral : Nat → Pattern
  | 0 => .apply "Zero" []
  | count + 1 => .apply "Succ" [numeral count]

def counter (count : Nat) : Pattern := .apply "Counter" [numeral count]

def halted : Pattern := .apply "Halted" []

def advance : RewriteRule :=
  { name := "Advance", typeContext := [("n", natSort)], premises := [],
    left := .apply "Counter" [.fvar "n"], right := .apply "Counter" [.apply "Succ" [.fvar "n"]] }

def crash : RewriteRule :=
  { name := "Crash", typeContext := [("n", natSort)], premises := [],
    left := .apply "Counter" [.fvar "n"], right := halted }

def stopAtThree : RewriteRule :=
  { name := "StopAtThree", typeContext := [], premises := [], left := counter 3, right := halted }

def language (rewrites : List RewriteRule) : LanguageDef :=
  { name := "Counter", types := ["Nat", "State"], terms := terms, equations := [], rewrites := rewrites }

/-- Counts forever. -/
def counting : LanguageDef := language [advance]
/-- Counts, and may halt at every value. -/
def crashing : LanguageDef := language [advance, crash]
/-- Counts, and may halt at three. -/
def halting : LanguageDef := language [advance, stopAtThree]

theorem counting_profile : checkRootProfile counting stateSort = true := by cbv
theorem crashing_profile : checkRootProfile crashing stateSort = true := by cbv
theorem halting_profile : checkRootProfile halting stateSort = true := by cbv

/-! ## Parity -/

/-- The number a numeral denotes. -/
def count? : Pattern → Option Nat
  | .apply "Zero" [] => some 0
  | .apply "Succ" [inner] => (count? inner).map (· + 1)
  | _ => none

theorem count_numeral (count : Nat) : count? (numeral count) = some count := by
  induction count with
  | zero => rfl
  | succ count ih => simp [numeral, count?, ih]

theorem eq_numeral_of_count : ∀ (pattern : Pattern) (count : Nat), count? pattern = some count →
    pattern = numeral count := by
  intro pattern
  induction pattern using count?.induct with
  | case1 => intro count read; cases read; rfl
  | case2 inner ih =>
    intro count read
    simp only [count?, Option.map_eq_some_iff] at read
    obtain ⟨previous, inner_read, rfl⟩ := read
    rw [ih previous inner_read]
    rfl
  | case3 other notZero notSucc =>
    intro count read
    rw [count?.eq_3 other notZero notSucc] at read
    cases read

/-! ## Abstractions of counts -/

/-- Each count mapped to the representative of its class. -/
structure CountClasses where
  classOf : Nat → Nat
  idempotent : ∀ count, classOf (classOf count) = classOf count

/-- Parity: two classes. -/
def parityClasses : CountClasses := ⟨(· % 2), fun count => Nat.mod_mod count 2⟩

/-- Counts up to a cap, and everything at or beyond it. -/
def capClasses (cap : Nat) : CountClasses := ⟨(min · cap), fun count => by simp⟩

variable (classes : CountClasses)

/-- **The abstraction of a state**: the numeral under `counter` replaced by its class's
representative. -/
def abstract (pattern : Pattern) : Pattern :=
  match pattern with
  | .apply "Counter" [argument] =>
      match count? argument with
      | some count => counter (classes.classOf count)
      | none => pattern
  | _ => pattern

theorem abstract_counter (count : Nat) : abstract classes (counter count) = counter (classes.classOf count) := by
  simp [abstract, counter, count_numeral]

/-- A state is its own abstraction, or a counter whose abstraction is the counter of its class. -/
theorem abstract_shape (pattern : Pattern) : abstract classes pattern = pattern ∨
    ∃ count, pattern = counter count ∧ abstract classes pattern = counter (classes.classOf count) := by
  unfold abstract
  split
  · rename_i argument
    split
    · rename_i count read
      exact Or.inr ⟨count, by rw [eq_numeral_of_count argument count read]; rfl, rfl⟩
    · exact Or.inl rfl
  · exact Or.inl rfl

theorem abstract_idempotent (pattern : Pattern) :
    abstract classes (abstract classes pattern) = abstract classes pattern := by
  rcases abstract_shape classes pattern with same | ⟨count, _, reduced⟩
  · rw [same, same]
  · rw [reduced, abstract_counter, classes.idempotent]

/-- Two states of one class are equal, or counters of counts of one class. -/
theorem abstract_eq_cases {left right : Pattern} (same : abstract classes left = abstract classes right) :
    left = right ∨ ∃ first second, left = counter first ∧ right = counter second ∧
      classes.classOf first = classes.classOf second := by
  rcases abstract_shape classes left with leftSame | ⟨first, rfl, leftClass⟩ <;>
    rcases abstract_shape classes right with rightSame | ⟨second, rfl, rightClass⟩
  · exact Or.inl (leftSame.symm.trans (same.trans rightSame))
  · rw [leftSame, rightClass] at same
    subst same
    exact Or.inr ⟨classes.classOf second, second, rfl, rfl, classes.idempotent second⟩
  · rw [rightSame, leftClass] at same
    subst same
    exact Or.inr ⟨first, classes.classOf first, rfl, rfl, (classes.idempotent first).symm⟩
  · rw [leftClass, rightClass] at same
    refine Or.inr ⟨first, second, rfl, rfl, ?_⟩
    have numeralSame := congrArg count? (List.head_eq_of_cons_eq (Pattern.apply.inj same).2)
    simpa [count_numeral] using numeralSame

/-! ## Well-sorted states -/

variable (rules : LanguageDef)

/-- The well-sorted states of a counter language. -/
abbrev Sorted : Pattern → Prop := Mettapedia.OSLF.Framework.HerbrandBridge.Sorted rules stateSort

variable {rules}

theorem equation_free (profile : RootProfile rules stateSort) {left right : Pattern}
    (related : (theory (rootPlan rules) [] stateSort).equations.r left right) : left = right :=
  profile.equivalence_is_equality [] related

theorem sorted_closed (profile : RootProfile rules stateSort) :
    ForwardClosed (gsltSpan (theory (rootPlan rules) [] stateSort)) (Sorted rules) :=
  Mettapedia.OSLF.Framework.HerbrandBridge.sorted_closed profile

theorem checked (profile : RootProfile rules stateSort) :
    Mettapedia.OSLF.MeTTaIL.Complete.Predecessors.equationsChecked (rootPlan rules) = true := by
  rw [Mettapedia.OSLF.MeTTaIL.Complete.Predecessors.equationsChecked, profile.equations]
  rfl

/-! ## Abstractions that match futures -/

/-- The condition on root reducts: at two counts of one class, the reducts have the same classes. -/
def ReductsRespect : Prop :=
  ∀ first second, classes.classOf first = classes.classOf second →
    (rootReducts rules (counter first)).map (abstract classes) =
      (rootReducts rules (counter second)).map (abstract classes)

/-- **The abstraction matches futures** on well-sorted states when the reducts respect it. -/
theorem abstract_matching (profile : RootProfile rules stateSort) (reducts : ReductsRespect (rules := rules) classes) :
    FutureMatchingOn (gsltSpan (theory (rootPlan rules) [] stateSort)) (Setoid.ker (abstract classes))
      (Sorted rules) := by
  intro left right leftSorted rightSorted related event starts
  have stepped : (theory (rootPlan rules) [] stateSort).Step left event.target := starts ▸ event.step
  have member : event.target ∈ rootReducts rules left :=
    (profile.general_step_iff_rootReducts [] leftSorted).mp stepped
  have sameReducts : (rootReducts rules left).map (abstract classes) =
      (rootReducts rules right).map (abstract classes) := by
    rcases abstract_eq_cases classes related with rfl | ⟨first, second, rfl, rfl, sameClass⟩
    · rfl
    · exact reducts first second sameClass
  have image : abstract classes event.target ∈ (rootReducts rules right).map (abstract classes) :=
    sameReducts ▸ List.mem_map_of_mem member
  obtain ⟨target, reached, sameClass⟩ := List.mem_map.mp image
  have step : (theory (rootPlan rules) [] stateSort).Step right target :=
    (profile.general_step_iff_rootReducts [] rightSorted).mpr reached
  exact ⟨⟨right, target, step⟩, rfl, sameClass.symm⟩

/-- **The obligations of a counter abstraction**, from the root profile, the condition on reducts
and the well-sortedness of the representatives. -/
theorem counterAbstraction (profile : RootProfile rules stateSort) (reducts : ReductsRespect (rules := rules) classes)
    (representatives : ∀ count, Sorted rules (counter (classes.classOf count))) :
    Abstraction (rootPlan rules) [] stateSort (abstract classes) (Setoid.ker (abstract classes)) (Sorted rules) where
  committed pattern := abstract_idempotent classes pattern
  normalGood pattern sorted := by
    rcases abstract_shape classes pattern with same | ⟨count, _, reduced⟩
    · rw [same]; exact sorted
    · rw [reduced]; exact representatives count
  targetGood _ _ valid := GeneralOccurrenceSemantics.Receipt.target_sorted _ _ _ valid
  within related := congrArg (abstract classes) (equation_free profile related)
  closed := sorted_closed profile
  matching := abstract_matching classes profile reducts

/-! ## Root reducts of the three counters -/

theorem matchPattern_numeral (first second : Nat) :
    matchPattern (numeral first) (numeral second) = if first = second then [[]] else [] := by
  induction first generalizing second with
  | zero => cases second <;> simp [numeral, matchPattern, matchArgs]
  | succ first ih =>
    cases second with
    | zero => simp [numeral, matchPattern]
    | succ second =>
      simp only [numeral, matchPattern, matchArgs, ih]
      by_cases equal : first = second <;> simp [equal, mergeBindings]

theorem counting_reducts (count : Nat) : rootReducts counting (counter count) = [counter (count + 1)] := by
  simp [rootReducts, counting, language, advance, counter, matchPattern, matchArgs, mergeBindings,
    applyBindings, numeral]

theorem crashing_reducts (count : Nat) :
    rootReducts crashing (counter count) = [counter (count + 1), halted] := by
  simp [rootReducts, crashing, language, advance, crash, halted, counter, matchPattern, matchArgs,
    mergeBindings, applyBindings, numeral]

theorem halting_reducts (count : Nat) :
    rootReducts halting (counter count) = counter (count + 1) :: (if count = 3 then [halted] else []) := by
  have three : matchPattern (counter 3) (counter count) = if 3 = count then [[]] else [] := by
    simp only [counter, matchPattern, matchArgs, matchPattern_numeral]
    by_cases equal : 3 = count <;> simp [equal, mergeBindings]
  simp only [rootReducts, halting, language, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [show stopAtThree.left = counter 3 from rfl, three]
  by_cases equal : count = 3
  · subst equal
    simp [advance, stopAtThree, counter, matchPattern, matchArgs, mergeBindings, applyBindings, numeral, halted]
  · simp [advance, stopAtThree, counter, matchPattern, matchArgs, mergeBindings, applyBindings, numeral,
      equal, Ne.symm equal]

/-! ## The three counters -/

theorem sorted_of_check {pattern : Pattern}
    (checked : checkOpenPatternWellSorted
      (rootPlan rules).snapshot.language (rootPlan rules).snapshot.free [] stateSort pattern = true) :
    Sorted rules pattern :=
  (checkOpenPatternWellSorted_eq_true_iff _ _ _ _ _).mp checked

theorem parity_representatives (zero : Sorted rules (counter 0)) (one : Sorted rules (counter 1)) :
    ∀ count, Sorted rules (counter (parityClasses.classOf count)) := by
  intro count
  rcases Nat.mod_two_eq_zero_or_one count with even | odd
  · change Sorted rules (counter (count % 2)); rw [even]; exact zero
  · change Sorted rules (counter (count % 2)); rw [odd]; exact one

theorem counting_respects : ReductsRespect (rules := counting) parityClasses := by
  intro first second same
  change first % 2 = second % 2 at same
  simp only [counting_reducts, List.map_cons, List.map_nil, abstract_counter, parityClasses]
  rw [show (first + 1) % 2 = (second + 1) % 2 by omega]

theorem crashing_respects : ReductsRespect (rules := crashing) parityClasses := by
  intro first second same
  change first % 2 = second % 2 at same
  simp only [crashing_reducts, List.map_cons, List.map_nil, abstract_counter, parityClasses]
  rw [show (first + 1) % 2 = (second + 1) % 2 by omega]

theorem halting_respects_cap : ReductsRespect (rules := halting) (capClasses 4) := by
  intro first second same
  change min first 4 = min second 4 at same
  rcases (by omega : first = second ∨ (4 ≤ first ∧ 4 ≤ second)) with rfl | ⟨large, large'⟩
  · rfl
  · have notThree : first ≠ 3 := by omega
    have notThree' : second ≠ 3 := by omega
    simp only [halting_reducts, notThree, notThree', if_false, List.map_cons, List.map_nil,
      abstract_counter, capClasses]
    rw [show min (first + 1) 4 = min (second + 1) 4 by omega]

theorem counting_profile' : RootProfile counting stateSort := RootProfile.of_check counting_profile
theorem crashing_profile' : RootProfile crashing stateSort := RootProfile.of_check crashing_profile
theorem halting_profile' : RootProfile halting stateSort := RootProfile.of_check halting_profile

theorem counting_parity :
    Abstraction (rootPlan counting) [] stateSort (abstract parityClasses) (Setoid.ker (abstract parityClasses))
      (Sorted counting) :=
  counterAbstraction parityClasses counting_profile' counting_respects
    (parity_representatives (sorted_of_check (by cbv)) (sorted_of_check (by cbv)))

theorem crashing_parity :
    Abstraction (rootPlan crashing) [] stateSort (abstract parityClasses) (Setoid.ker (abstract parityClasses))
      (Sorted crashing) :=
  counterAbstraction parityClasses crashing_profile' crashing_respects
    (parity_representatives (sorted_of_check (by cbv)) (sorted_of_check (by cbv)))

theorem halting_cap :
    Abstraction (rootPlan halting) [] stateSort (abstract (capClasses 4)) (Setoid.ker (abstract (capClasses 4)))
      (Sorted halting) := by
  refine counterAbstraction (capClasses 4) halting_profile' halting_respects_cap ?_
  intro count
  change Sorted halting (counter (min count 4))
  have small : min count 4 ≤ 4 := Nat.min_le_right count 4
  generalize min count 4 = capped at small
  interval_cases capped
  all_goals exact sorted_of_check (by cbv)

/-- **Parity does not match futures for the counter that halts at three.** -/
theorem halting_parity_not_matching :
    ¬ FutureMatchingOn (gsltSpan (theory (rootPlan halting) [] stateSort))
      (Setoid.ker (abstract parityClasses)) (Sorted halting) := by
  intro matching
  have three : Sorted halting (counter 3) := sorted_of_check (by cbv)
  have one : Sorted halting (counter 1) := sorted_of_check (by cbv)
  have related : abstract parityClasses (counter 3) = abstract parityClasses (counter 1) := by
    simp [abstract_counter, parityClasses]
  have halts : (theory (rootPlan halting) [] stateSort).Step (counter 3) halted :=
    (halting_profile'.general_step_iff_rootReducts [] three).mpr (by rw [halting_reducts]; simp)
  obtain ⟨matched, matchedSource, sameClass⟩ := matching three one related ⟨counter 3, halted, halts⟩ rfl
  obtain ⟨target, isTarget⟩ : ∃ target : Pattern,
      (gsltSpan (theory (rootPlan halting) [] stateSort)).target matched = target := ⟨_, rfl⟩
  have stepped : (theory (rootPlan halting) [] stateSort).Step (counter 1) target := by
    rw [← isTarget]
    have fired := (show (theory (rootPlan halting) [] stateSort).LabeledStep from matched).step
    rw [← matchedSource]
    exact fired
  have classes : abstract parityClasses halted = abstract parityClasses target := by
    rw [← isTarget]; exact sameClass
  have reached : target ∈ rootReducts halting (counter 1) :=
    (halting_profile'.general_step_iff_rootReducts [] one).mp stepped
  rw [halting_reducts] at reached
  simp only [show (1 : Nat) ≠ 3 by decide, if_false, List.mem_singleton] at reached
  rw [reached, abstract_counter] at classes
  simp [abstract, halted, counter, parityClasses, numeral] at classes

/-! ## Verdicts -/

/-- Two atoms: halted (0), and the class of zero (1). -/
def atomOf : Fin 2 → Pattern → Bool
  | 0, state => state == halted
  | _, state => state == counter 0

def atoms : Atoms (Setoid.ker (abstract classes)) 2 where
  holds index state := atomOf index (abstract classes state)
  invariant index left right related := by
    have same : abstract classes left = abstract classes right := related
    rw [same]

/-- Every reachable state has a successor. -/
def neverDeadlocks : Formula Traversal 2 := .nu (.conj (.diamond .future .tt) (.box .future (.var 0)))

/-- Some path halts. -/
def mayHalt : Formula Traversal 2 := .mu (.disj (.var 1) (.diamond .future (.var 0)))

/-- Every path halts. -/
def mustHalt : Formula Traversal 2 :=
  .mu (.disj (.var 1) (.conj (.diamond .future .tt) (.box .future (.var 0))))

/-- Some path visits the class of zero infinitely often. -/
def zeroInfinitelyOften : Formula Traversal 2 :=
  .nu (.mu (.disj (.conj (.var 3) (.diamond .future (.var 1))) (.diamond .future (.var 0))))

def ask (rules : LanguageDef) (classes : CountClasses) (formula : Formula Traversal 2)
    (work : Nat := 100) (budget : Nat := 100000) : Verdict :=
  verdict (rootPlan rules) [] stateSort (abstract classes) (counter 0) work formula (atoms classes) budget

/-- Exploration without an abstraction. -/
def askPlain (rules : LanguageDef) (formula : Formula Traversal 2) (work : Nat) : Verdict :=
  verdict (rootPlan rules) [] stateSort id (counter 0) work formula (atoms ⟨id, fun _ => rfl⟩) 100000

-- The counter that counts forever: two parity classes.
#guard ask counting parityClasses neverDeadlocks == .proved
#guard ask counting parityClasses zeroInfinitelyOften == .proved
#guard ask counting parityClasses mayHalt == .refuted
#guard ask counting parityClasses mustHalt == .refuted
-- Without an abstraction its exploration never settles.
#guard askPlain counting neverDeadlocks 60 == .unknown .unsettled

-- The counter that may halt at every value.
#guard ask crashing parityClasses neverDeadlocks == .refuted
#guard ask crashing parityClasses mayHalt == .proved
#guard ask crashing parityClasses mustHalt == .refuted
#guard ask crashing parityClasses zeroInfinitelyOften == .proved

-- The counter that may halt at three: parity does not match futures and answers wrongly;
-- capping at four matches futures and answers correctly.
#guard ask halting parityClasses mayHalt == .refuted
#guard ask halting (capClasses 4) mayHalt == .proved
#guard ask halting (capClasses 4) neverDeadlocks == .refuted
#guard ask halting (capClasses 4) mustHalt == .refuted

theorem start_sorted_counting : Sorted counting (counter 0) := sorted_of_check (by cbv)
theorem start_sorted_halting : Sorted halting (counter 0) := sorted_of_check (by cbv)

/-- **A proved verdict: the unbounded counter never deadlocks.** -/
theorem counting_never_deadlocks (read : ask counting parityClasses neverDeadlocks = .proved) :
    satisfies (transitionSystem (gsltSpan (theory (rootPlan counting) [] stateSort)))
      (atoms parityClasses).meaning neverDeadlocks (counter 0) :=
  verdict_proved (checked counting_profile') counting_parity start_sorted_counting read

/-- **A proved verdict: the counter that halts at three may halt.** -/
theorem halting_may_halt (read : ask halting (capClasses 4) mayHalt = .proved) :
    satisfies (transitionSystem (gsltSpan (theory (rootPlan halting) [] stateSort)))
      (atoms (capClasses 4)).meaning mayHalt (counter 0) :=
  verdict_proved (checked halting_profile') halting_cap start_sorted_halting read

end Mettapedia.OSLF.NativeTypes.Executable.Explored.CounterAbstractions
