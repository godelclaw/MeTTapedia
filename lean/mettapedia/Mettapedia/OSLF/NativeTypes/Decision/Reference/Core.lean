import Mettapedia.OSLF.NativeTypes.Semantics.Operational
import Mathlib.Data.List.NatAntidiagonal

open Mettapedia.OSLF.Framework

/-!
# Compositional native decision from local coverage

The formula meaning uses the equation predicates and operational modalities
of an independently supplied GSLT. Executable leaf tests and retained local
frontiers supply primitive evidence. Coverage is used only for absence and
universal conclusions; an unfinished frontier remains unresolved.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Reference.Core

open GSLTTypeSynthesis
open Mettapedia.GSLT

universe u v w

/-- A conclusive result carries a proof of its stated polarity. -/
inductive Outcome (statement : Prop) : Type where
  | proved : statement → Outcome statement
  | refuted : (¬ statement) → Outcome statement
  | unknown : Outcome statement

namespace Outcome

def answer {statement : Prop} : Outcome statement → Option Bool
  | .proved _ => some true
  | .refuted _ => some false
  | .unknown => none

def Decided {statement : Prop} (result : Outcome statement) : Prop :=
  ∃ answer, result.answer = some answer

theorem positive {statement : Prop} (result : Outcome statement)
    (read : result.answer = some true) : statement := by
  cases result with
  | proved proof => exact proof
  | refuted refutation => simp [answer] at read
  | unknown => simp [answer] at read

theorem negative {statement : Prop} (result : Outcome statement)
    (read : result.answer = some false) : ¬ statement := by
  cases result with
  | proved proof => simp [answer] at read
  | refuted refutation => exact refutation
  | unknown => simp [answer] at read

def map {first second : Prop} (equivalent : first ↔ second) :
    Outcome first → Outcome second
  | .proved proof => .proved (equivalent.mp proof)
  | .refuted refutation => .refuted (fun proof => refutation (equivalent.mpr proof))
  | .unknown => .unknown

theorem map_decided {first second : Prop} (equivalent : first ↔ second)
    (result : Outcome first) (decided : result.Decided) :
    (map equivalent result).Decided := by
  cases result <;> simp_all [Decided, answer, map]

def negation {statement : Prop} : Outcome statement → Outcome (¬ statement)
  | .proved proof => .refuted (fun refutation => refutation proof)
  | .refuted refutation => .proved refutation
  | .unknown => .unknown

def conjunction {first second : Prop} :
    Outcome first → Outcome second → Outcome (first ∧ second)
  | .proved left, .proved right => .proved ⟨left, right⟩
  | .refuted left, _ => .refuted (fun proof => left proof.1)
  | _, .refuted right => .refuted (fun proof => right proof.2)
  | _, _ => .unknown

def disjunction {first second : Prop} :
    Outcome first → Outcome second → Outcome (first ∨ second)
  | .proved left, _ => .proved (.inl left)
  | _, .proved right => .proved (.inr right)
  | .refuted left, .refuted right => .refuted (fun proof => proof.elim left right)
  | _, _ => .unknown

def implication {first second : Prop} :
    Outcome first → Outcome second → Outcome (first → second)
  | .refuted left, _ => .proved (fun proof => False.elim (left proof))
  | _, .proved right => .proved (fun _ => right)
  | .proved left, .refuted right => .refuted (fun proof => right (proof left))
  | _, _ => .unknown

def lazyConjunction {first second : Prop} (left : Outcome first)
    (right : Unit → Outcome second) : Outcome (first ∧ second) :=
  match left with
  | .refuted refutation => .refuted (fun proof => refutation proof.1)
  | .proved proof => match right () with
    | .proved other => .proved ⟨proof, other⟩
    | .refuted refutation => .refuted (fun proof => refutation proof.2)
    | .unknown => .unknown
  | .unknown => match right () with
    | .refuted refutation => .refuted (fun proof => refutation proof.2)
    | _ => .unknown

def lazyDisjunction {first second : Prop} (left : Outcome first)
    (right : Unit → Outcome second) : Outcome (first ∨ second) :=
  match left with
  | .proved proof => .proved (.inl proof)
  | .refuted refutation => match right () with
    | .proved proof => .proved (.inr proof)
    | .refuted other => .refuted (fun proof => proof.elim refutation other)
    | .unknown => .unknown
  | .unknown => match right () with
    | .proved proof => .proved (.inr proof)
    | _ => .unknown

def lazyImplication {first second : Prop} (left : Outcome first)
    (right : Unit → Outcome second) : Outcome (first → second) :=
  match left with
  | .refuted refutation => .proved (fun proof => False.elim (refutation proof))
  | .proved proof => match right () with
    | .proved other => .proved (fun _ => other)
    | .refuted refutation => .refuted (fun function => refutation (function proof))
    | .unknown => .unknown
  | .unknown => match right () with
    | .proved proof => .proved (fun _ => proof)
    | _ => .unknown

theorem lazyConjunction_eq {first second : Prop} (left : Outcome first)
    (right : Unit → Outcome second) : lazyConjunction left right = conjunction left (right ()) := by
  cases left <;> simp only [lazyConjunction, conjunction] <;>
    cases right () <;> rfl

theorem lazyDisjunction_eq {first second : Prop} (left : Outcome first)
    (right : Unit → Outcome second) : lazyDisjunction left right = disjunction left (right ()) := by
  cases left <;> simp only [lazyDisjunction, disjunction] <;>
    cases right () <;> rfl

theorem lazyImplication_eq {first second : Prop} (left : Outcome first)
    (right : Unit → Outcome second) : lazyImplication left right = implication left (right ()) := by
  cases left <;> simp only [lazyImplication, implication] <;>
    cases right () <;> rfl

theorem negation_decided {statement : Prop} (result : Outcome statement)
    (decided : result.Decided) : (negation result).Decided := by
  cases result <;> simp_all [Decided, answer, negation]

theorem conjunction_decided {first second : Prop}
    (left : Outcome first) (right : Outcome second)
    (leftDecided : left.Decided) (rightDecided : right.Decided) :
    (conjunction left right).Decided := by
  cases left <;> cases right <;> simp_all [Decided, answer, conjunction]

theorem disjunction_decided {first second : Prop}
    (left : Outcome first) (right : Outcome second)
    (leftDecided : left.Decided) (rightDecided : right.Decided) :
    (disjunction left right).Decided := by
  cases left <;> cases right <;> simp_all [Decided, answer, disjunction]

theorem implication_decided {first second : Prop}
    (left : Outcome first) (right : Outcome second)
    (leftDecided : left.Decided) (rightDecided : right.Decided) :
    (implication left right).Decided := by
  cases left <;> cases right <;> simp_all [Decided, answer, implication]

def existsIn {Item : Type v} (predicate : Item → Prop)
    (check : ∀ item, Outcome (predicate item)) :
    (items : List Item) → Outcome (∃ item, item ∈ items ∧ predicate item)
  | [] => .refuted (by simp)
  | item :: rest => map (by simp [List.mem_cons])
      (lazyDisjunction (check item) (fun _ => existsIn predicate check rest))

def forallIn {Item : Type v} (predicate : Item → Prop)
    (check : ∀ item, Outcome (predicate item)) :
    (items : List Item) → Outcome (∀ item, item ∈ items → predicate item)
  | [] => .proved (by simp)
  | item :: rest => map (by simp [List.mem_cons, forall_eq_or_imp])
      (lazyConjunction (check item) (fun _ => forallIn predicate check rest))

theorem existsIn_decided {Item : Type v} (predicate : Item → Prop)
    (check : ∀ item, Outcome (predicate item)) (items : List Item)
    (complete : ∀ item, item ∈ items → (check item).Decided) :
    (existsIn predicate check items).Decided := by
  induction items with
  | nil => simp [existsIn, Decided, answer]
  | cons item rest ih =>
    apply map_decided
    rw [lazyDisjunction_eq]
    apply disjunction_decided
    · exact complete item (by simp)
    · exact ih (fun other listed => complete other (by simp [listed]))

theorem forallIn_decided {Item : Type v} (predicate : Item → Prop)
    (check : ∀ item, Outcome (predicate item)) (items : List Item)
    (complete : ∀ item, item ∈ items → (check item).Decided) :
    (forallIn predicate check items).Decided := by
  induction items with
  | nil => simp [forallIn, Decided, answer]
  | cons item rest ih =>
    apply map_decided
    rw [lazyConjunction_eq]
    apply conjunction_decided
    · exact complete item (by simp)
    · exact ih (fun other listed => complete other (by simp [listed]))

end Outcome

/-- Primitive leaf tests concern their own independently specified invariant
meaning. Completion above the stated bound must be earned by their evaluator. -/
structure Test (system : GSLT.{u}) (admitted : system.Term → Prop) where
  predicate : EquationPredicate system
  evaluate : Nat → system.Term → Option Bool
  positive : ∀ budget source, evaluate budget source = some true → predicate source
  negative : ∀ budget source, evaluate budget source = some false → ¬ predicate source
  completionBudget : system.Term → Nat
  complete_at : ∀ source, admitted source →
    ∃ answer, evaluate (completionBudget source) source = some answer
  complete_above : ∀ source, admitted source → ∀ budget, completionBudget source ≤ budget →
    ∃ answer, evaluate budget source = some answer

def Test.ofBoolean {system : GSLT.{u}} {admitted : system.Term → Prop}
    (predicate : EquationPredicate system) (accepts : system.Term → Bool)
    (correct : ∀ source, accepts source = true ↔ predicate source) : Test system admitted where
  predicate := predicate
  evaluate _ source := some (accepts source)
  positive _ source read := correct source |>.mp (Option.some.inj read)
  negative _ source read := by
    intro holds
    have accepted := (correct source).mpr holds
    have refused := Option.some.inj read
    rw [accepted] at refused
    cases refused
  completionBudget _ := 0
  complete_at source _ := ⟨accepts source, rfl⟩
  complete_above source _ _ _ := ⟨accepts source, rfl⟩

def Test.onProfile {system : GSLT.{u}} {old : system.Term → Prop}
    (test : Test system old) (admitted : system.Term → Prop)
    (included : ∀ source, admitted source → old source) : Test system admitted where
  predicate := test.predicate
  evaluate := test.evaluate
  positive := test.positive
  negative := test.negative
  completionBudget := test.completionBudget
  complete_at source accepted := test.complete_at source (included source accepted)
  complete_above source accepted budget enough := test.complete_above source (included source accepted) budget enough

def Test.run {system : GSLT.{u}} {admitted : system.Term → Prop}
    (test : Test system admitted) (budget : Nat) (source : system.Term) :
    Outcome (test.predicate source) :=
  if positive : test.evaluate budget source = some true then
    .proved (test.positive budget source positive)
  else if negative : test.evaluate budget source = some false then
    .refuted (test.negative budget source negative)
  else .unknown

theorem Test.run_decided {system : GSLT.{u}} {admitted : system.Term → Prop}
    (test : Test system admitted) (budget : Nat) (source : system.Term)
    (sourceAdmitted : admitted source) (enough : test.completionBudget source ≤ budget) :
    (test.run budget source).Decided := by
  obtain ⟨answer, evaluated⟩ := test.complete_above source sourceAdmitted budget enough
  cases answer <;> simp [Test.run, evaluated, Outcome.Decided, Outcome.answer]

/-- A local executable frontier retains its physical receipts. Closed coverage
is modulo the supplied GSLT equations; recursive targets stay in the profile. -/
structure Backend (system : GSLT.{u}) (admitted : system.Term → Prop) where
  Receipt : system.Term → Type v
  target : ∀ source, Receipt source → system.Term
  frontier : Nat → (source : system.Term) → List (Receipt source)
  closed : Nat → system.Term → Bool
  sound : ∀ budget source receipt, receipt ∈ frontier budget source →
    system.Step source (target source receipt)
  coverage : ∀ budget source, closed budget source = true →
    ∀ actual, system.Step source actual →
      ∃ receipt, receipt ∈ frontier budget source ∧ system.Equiv actual (target source receipt)
  target_admitted : ∀ budget source, admitted source →
    ∀ receipt, receipt ∈ frontier budget source → admitted (target source receipt)
  completionBudget : system.Term → Nat
  complete_at : ∀ source, admitted source → closed (completionBudget source) source = true
  frontier_stable : ∀ source budget, completionBudget source ≤ budget →
    frontier budget source = frontier (completionBudget source) source
  closed_stable : ∀ source budget, completionBudget source ≤ budget →
    closed budget source = closed (completionBudget source) source

inductive Formula (Leaf : Type w) : Type w where
  | atom : Leaf → Formula Leaf
  | top : Formula Leaf
  | bottom : Formula Leaf
  | conj : Formula Leaf → Formula Leaf → Formula Leaf
  | disj : Formula Leaf → Formula Leaf → Formula Leaf
  | neg : Formula Leaf → Formula Leaf
  | imp : Formula Leaf → Formula Leaf → Formula Leaf
  | possibility : Formula Leaf → Formula Leaf
  | outgoingUniversal : Formula Leaf → Formula Leaf

def meet (system : GSLT.{u}) (first second : EquationPredicate system) :
    EquationPredicate system where
  val source := first source ∧ second source
  property := by intro _ _ related; exact and_congr (first.2 related) (second.2 related)

def join (system : GSLT.{u}) (first second : EquationPredicate system) :
    EquationPredicate system where
  val source := first source ∨ second source
  property := by intro _ _ related; exact or_congr (first.2 related) (second.2 related)

def complement (system : GSLT.{u}) (predicate : EquationPredicate system) :
    EquationPredicate system where
  val source := ¬ predicate source
  property := by intro _ _ related; exact not_congr (predicate.2 related)

def implies (system : GSLT.{u}) (first second : EquationPredicate system) :
    EquationPredicate system where
  val source := first source → second source
  property := by intro _ _ related; exact imp_congr (first.2 related) (second.2 related)

def denotation {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (tests : Leaf → Test system admitted) : Formula Leaf → EquationPredicate system
  | .atom leaf => (tests leaf).predicate
  | .top => ⟨fun _ => True, by intro _ _ _; rfl⟩
  | .bottom => ⟨fun _ => False, by intro _ _ _; rfl⟩
  | .conj first second => meet system (denotation tests first) (denotation tests second)
  | .disj first second => join system (denotation tests first) (denotation tests second)
  | .neg formula => complement system (denotation tests formula)
  | .imp first second => implies system (denotation tests first) (denotation tests second)
  | .possibility formula => semanticDiamond system (denotation tests formula)
  | .outgoingUniversal formula =>
      Mettapedia.OSLF.NativeTypes.Semantics.Operational.outgoingUniversal system (denotation tests formula)

def nativeType {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (tests : Leaf → Test system admitted) (formula : Formula Leaf) : GSLTNativeType system where
  sort := ()
  pred := denotation tests formula

def possibilityOutcome {system : GSLT.{u}} {admitted : system.Term → Prop}
    (backend : Backend.{u,v} system admitted) (predicate : EquationPredicate system)
    (budget : Nat) (source : system.Term)
    (check : ∀ receipt : backend.Receipt source, Outcome (predicate (backend.target source receipt))) :
    Outcome (semanticDiamond system predicate source) :=
  match Outcome.existsIn (fun receipt => predicate (backend.target source receipt)) check
      (backend.frontier budget source) with
  | .proved witness => .proved (by
      obtain ⟨receipt, listed, holds⟩ := witness
      exact (gsltDiamond_spec system predicate.1 source).mpr
        ⟨backend.target source receipt, backend.sound budget source receipt listed, holds⟩)
  | .refuted absent =>
      if closed : backend.closed budget source = true then
        .refuted (fun holds => by
          obtain ⟨actual, step, satisfies⟩ := (gsltDiamond_spec system predicate.1 source).mp holds
          obtain ⟨receipt, listed, related⟩ := backend.coverage budget source closed actual step
          exact absent ⟨receipt, listed, (predicate.2 related).mp satisfies⟩)
      else .unknown
  | .unknown => .unknown

def universalOutcome {system : GSLT.{u}} {admitted : system.Term → Prop}
    (backend : Backend.{u,v} system admitted) (predicate : EquationPredicate system)
    (budget : Nat) (source : system.Term)
    (check : ∀ receipt : backend.Receipt source, Outcome (predicate (backend.target source receipt))) :
    Outcome (Mettapedia.OSLF.NativeTypes.Semantics.Operational.outgoingUniversal system predicate source) :=
  match Outcome.forallIn (fun receipt => predicate (backend.target source receipt)) check
      (backend.frontier budget source) with
  | .proved all =>
      if closed : backend.closed budget source = true then
        .proved (fun actual step => by
          obtain ⟨receipt, listed, related⟩ := backend.coverage budget source closed actual step
          exact (predicate.2 related).mpr (all receipt listed))
      else .unknown
  | .refuted counterexample => .refuted (fun all =>
      counterexample (fun receipt listed => all (backend.target source receipt)
        (backend.sound budget source receipt listed)))
  | .unknown => .unknown

theorem possibilityOutcome_decided {system : GSLT.{u}} {admitted : system.Term → Prop}
    (backend : Backend.{u,v} system admitted) (predicate : EquationPredicate system)
    (budget : Nat) (source : system.Term)
    (check : ∀ receipt : backend.Receipt source, Outcome (predicate (backend.target source receipt)))
    (closed : backend.closed budget source = true)
    (complete : ∀ receipt, receipt ∈ backend.frontier budget source → (check receipt).Decided) :
    (possibilityOutcome backend predicate budget source check).Decided := by
  have decided := Outcome.existsIn_decided _ check (backend.frontier budget source) complete
  unfold possibilityOutcome
  generalize Outcome.existsIn _ check (backend.frontier budget source) = result at decided ⊢
  cases result <;> simp_all [Outcome.Decided, Outcome.answer]

theorem universalOutcome_decided {system : GSLT.{u}} {admitted : system.Term → Prop}
    (backend : Backend.{u,v} system admitted) (predicate : EquationPredicate system)
    (budget : Nat) (source : system.Term)
    (check : ∀ receipt : backend.Receipt source, Outcome (predicate (backend.target source receipt)))
    (closed : backend.closed budget source = true)
    (complete : ∀ receipt, receipt ∈ backend.frontier budget source → (check receipt).Decided) :
    (universalOutcome backend predicate budget source check).Decided := by
  have decided := Outcome.forallIn_decided _ check (backend.frontier budget source) complete
  unfold universalOutcome
  generalize Outcome.forallIn _ check (backend.frontier budget source) = result at decided ⊢
  cases result <;> simp_all [Outcome.Decided, Outcome.answer]

def raw {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted) :
    (budget : Nat) → (formula : Formula Leaf) → (source : system.Term) →
      Outcome (denotation tests formula source)
  | 0, _, _ => .unknown
  | budget + 1, .atom leaf, source => (tests leaf).run (budget + 1) source
  | _ + 1, .top, _ => .proved trivial
  | _ + 1, .bottom, _ => .refuted id
  | budget + 1, .conj first second, source =>
      Outcome.lazyConjunction (raw backend tests budget first source) (fun _ => raw backend tests budget second source)
  | budget + 1, .disj first second, source =>
      Outcome.lazyDisjunction (raw backend tests budget first source) (fun _ => raw backend tests budget second source)
  | budget + 1, .neg formula, source => Outcome.negation (raw backend tests budget formula source)
  | budget + 1, .imp first second, source =>
      Outcome.lazyImplication (raw backend tests budget first source) (fun _ => raw backend tests budget second source)
  | budget + 1, .possibility formula, source =>
      possibilityOutcome backend (denotation tests formula) (budget + 1) source
        (fun receipt => raw backend tests budget formula (backend.target source receipt))
  | budget + 1, .outgoingUniversal formula, source =>
      universalOutcome backend (denotation tests formula) (budget + 1) source
        (fun receipt => raw backend tests budget formula (backend.target source receipt))

/-- The bound inspects only complete local frontiers along the finite formula.
It does not enumerate an ambient term universe. -/
def workBound {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted) :
    Formula Leaf → system.Term → Nat
  | .atom leaf, source => 1 + (tests leaf).completionBudget source
  | .top, _ => 1
  | .bottom, _ => 1
  | .conj first second, source => 1 + max (workBound backend tests first source) (workBound backend tests second source)
  | .disj first second, source => 1 + max (workBound backend tests first source) (workBound backend tests second source)
  | .neg formula, source => 1 + workBound backend tests formula source
  | .imp first second, source => 1 + max (workBound backend tests first source) (workBound backend tests second source)
  | .possibility formula, source => 1 + backend.completionBudget source +
      ((backend.frontier (backend.completionBudget source) source).map
        (fun receipt => workBound backend tests formula (backend.target source receipt))).sum
  | .outgoingUniversal formula, source => 1 + backend.completionBudget source +
      ((backend.frontier (backend.completionBudget source) source).map
        (fun receipt => workBound backend tests formula (backend.target source receipt))).sum

private theorem member_le_sum {Item : Type v} (weight : Item → Nat)
    (items : List Item) (item : Item) (listed : item ∈ items) :
    weight item ≤ (items.map weight).sum := by
  induction items with
  | nil => simp at listed
  | cons first rest ih =>
    simp only [List.mem_cons] at listed
    simp only [List.map_cons, List.sum_cons]
    rcases listed with equal | listed
    · subst item; omega
    · have := ih listed; omega

theorem raw_complete {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) (sourceAdmitted : admitted source)
    (budget : Nat) (enough : workBound backend tests formula source ≤ budget) :
    (raw backend tests budget formula source).Decided := by
  induction formula generalizing source budget with
  | atom leaf =>
    cases budget with
    | zero => simp [workBound] at enough
    | succ budget =>
      apply Test.run_decided _ _ _ sourceAdmitted
      simp only [workBound] at enough
      omega
  | top =>
    cases budget <;> simp_all [workBound, raw, Outcome.Decided, Outcome.answer]
  | bottom =>
    cases budget <;> simp_all [workBound, raw, Outcome.Decided, Outcome.answer]
  | conj first second left right =>
    cases budget with
    | zero => simp [workBound] at enough
    | succ budget =>
      simp only [workBound] at enough
      simp only [raw, Outcome.lazyConjunction_eq]
      apply Outcome.conjunction_decided
      · exact left source sourceAdmitted budget (by omega)
      · exact right source sourceAdmitted budget (by omega)
  | disj first second left right =>
    cases budget with
    | zero => simp [workBound] at enough
    | succ budget =>
      simp only [workBound] at enough
      simp only [raw, Outcome.lazyDisjunction_eq]
      apply Outcome.disjunction_decided
      · exact left source sourceAdmitted budget (by omega)
      · exact right source sourceAdmitted budget (by omega)
  | neg formula ih =>
    cases budget with
    | zero => simp [workBound] at enough
    | succ budget =>
      apply Outcome.negation_decided
      apply ih source sourceAdmitted budget
      simp only [workBound] at enough
      omega
  | imp first second left right =>
    cases budget with
    | zero => simp [workBound] at enough
    | succ budget =>
      simp only [workBound] at enough
      simp only [raw, Outcome.lazyImplication_eq]
      apply Outcome.implication_decided
      · exact left source sourceAdmitted budget (by omega)
      · exact right source sourceAdmitted budget (by omega)
  | possibility formula ih =>
    cases budget with
    | zero => simp [workBound] at enough
    | succ budget =>
      simp only [workBound] at enough
      have covers : backend.completionBudget source ≤ budget + 1 := by omega
      simp only [raw]
      apply possibilityOutcome_decided
      · rw [backend.closed_stable source (budget + 1) covers]
        exact backend.complete_at source sourceAdmitted
      · intro receipt listed
        rw [backend.frontier_stable source (budget + 1) covers] at listed
        apply ih (backend.target source receipt)
          (backend.target_admitted _ source sourceAdmitted receipt listed) budget
        have := member_le_sum
          (fun receipt => workBound backend tests formula (backend.target source receipt))
          (backend.frontier (backend.completionBudget source) source) receipt listed
        omega
  | outgoingUniversal formula ih =>
    cases budget with
    | zero => simp [workBound] at enough
    | succ budget =>
      simp only [workBound] at enough
      have covers : backend.completionBudget source ≤ budget + 1 := by omega
      simp only [raw]
      apply universalOutcome_decided
      · rw [backend.closed_stable source (budget + 1) covers]
        exact backend.complete_at source sourceAdmitted
      · intro receipt listed
        rw [backend.frontier_stable source (budget + 1) covers] at listed
        apply ih (backend.target source receipt)
          (backend.target_admitted _ source sourceAdmitted receipt listed) budget
        have := member_le_sum
          (fun receipt => workBound backend tests formula (backend.target source receipt))
          (backend.frontier (backend.completionBudget source) source) receipt listed
        omega

/-- Keep the first conclusive result. Its compiled implementation is the
tail-recursive stream below, which starts at one unit of actual local work. -/
def check {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) :
    Nat → Outcome (denotation tests formula source)
  | 0 => .unknown
  | budget + 1 => match check backend tests formula source budget with
    | .proved proof => .proved proof
    | .refuted refutation => .refuted refutation
    | .unknown => raw backend tests (budget + 1) formula source

namespace Outcome

def keep {statement : Prop} (first second : Outcome statement) : Outcome statement :=
  match first with
  | .proved proof => .proved proof
  | .refuted refutation => .refuted refutation
  | .unknown => second

theorem keep_assoc {statement : Prop} (first second third : Outcome statement) :
    keep (keep first second) third = keep first (keep second third) := by
  cases first <;> rfl

def accumulate {statement : Prop} (evaluate : Nat → Outcome statement) (start : Nat) :
    Nat → Outcome statement
  | 0 => .unknown
  | budget + 1 => keep (accumulate evaluate start budget) (evaluate (start + budget))

private theorem accumulate_head {statement : Prop} (evaluate : Nat → Outcome statement)
    (start budget : Nat) :
    accumulate evaluate start (budget + 1) = keep (evaluate start) (accumulate evaluate (start + 1) budget) := by
  induction budget with
  | zero => cases evaluated : evaluate start <;> simp [accumulate, keep, evaluated]
  | succ budget ih =>
    rw [accumulate, ih, keep_assoc, accumulate]
    rw [show start + (budget + 1) = (start + 1) + budget by omega]

/-- This tail recursion checks increasing local budgets and exits on the first
proof or refutation. Neither completion bounds nor their expansion forests
are evaluated by the stream. -/
def streamFrom {statement : Prop} (evaluate : Nat → Outcome statement) (start : Nat) :
    Nat → Outcome statement
  | 0 => .unknown
  | remaining + 1 => match evaluate start with
    | .proved proof => .proved proof
    | .refuted refutation => .refuted refutation
    | .unknown => streamFrom evaluate (start + 1) remaining

theorem streamFrom_eq_accumulate {statement : Prop} (evaluate : Nat → Outcome statement)
    (start budget : Nat) : streamFrom evaluate start budget = accumulate evaluate start budget := by
  induction budget generalizing start with
  | zero => rfl
  | succ budget ih =>
    rw [accumulate_head]
    simp only [streamFrom]
    cases evaluated : evaluate start <;> simp [keep, ih]

end Outcome

def stream {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat) :
    Outcome (denotation tests formula source) :=
  Outcome.streamFrom (fun work => raw backend tests work formula source) 1 budget

theorem stream_eq_check {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat) :
    stream backend tests formula source budget = check backend tests formula source budget := by
  rw [stream, Outcome.streamFrom_eq_accumulate]
  induction budget with
  | zero => rfl
  | succ budget ih =>
    simp only [Outcome.accumulate, ih, check, Outcome.keep, Nat.add_comm 1 budget]
    cases check backend tests formula source budget <;> rfl

@[csimp] theorem check_eq_stream : @check.{u,v,w} = @stream.{u,v,w} := by
  funext system admitted Leaf backend tests formula source budget
  exact (stream_eq_check backend tests formula source budget).symm

theorem checked_positive {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat)
    (read : (check backend tests formula source budget).answer = some true) :
    denotation tests formula source :=
  Outcome.positive _ read

theorem checked_negative {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat)
    (read : (check backend tests formula source budget).answer = some false) :
    ¬ denotation tests formula source :=
  Outcome.negative _ read

theorem checked_complete {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) (sourceAdmitted : admitted source)
    (budget : Nat) (enough : workBound backend tests formula source ≤ budget) :
    (check backend tests formula source budget).Decided := by
  have rawDecided := raw_complete backend tests formula source sourceAdmitted budget enough
  cases budget with
  | zero => simp [raw, Outcome.Decided, Outcome.answer] at rawDecided
  | succ budget =>
    simp only [check]
    generalize check backend tests formula source budget = previous
    cases previous <;> simp_all [Outcome.Decided, Outcome.answer]

theorem conclusive_mono {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) {small large : Nat} (answer : Bool)
    (read : (check backend tests formula source small).answer = some answer)
    (ordered : small ≤ large) :
    (check backend tests formula source large).answer = some answer := by
  induction large, ordered using Nat.le_induction with
  | base => exact read
  | succ budget ordered ih =>
    simp only [check]
    generalize check backend tests formula source budget = previous at ih ⊢
    cases previous <;> simp_all [Outcome.answer]

theorem native_membership {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (tests : Leaf → Test system admitted) (formula : Formula Leaf) (source : system.Term) :
    (gsltOSLF system).satisfies source (nativeType tests formula).pred ↔
      denotation tests formula source := Iff.rfl

end Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
