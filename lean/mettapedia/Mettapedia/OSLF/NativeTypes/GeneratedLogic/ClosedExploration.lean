import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Exploration
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.BoundedMorphism

/-!
# Closed regions decide forward formulas

An exploration proves existential formulas. A **closed** region (`closedRegion`) decides every forward
formula at its terms, in an equation-free language:
- each of its states is completely listed at the fuel (`enough`), and its successors are in the
  region;
- each of its terms has its arguments, halves, members and bodies in the region (`shapeParts`).

Then the region's inclusion is a bounded morphism (`closedMorphism`). The evaluator's verdict on the
region is the verdict in the language, both ways (`closed_check_iff`). This covers stuckness,
invariants, reachability, and alternations such as "every step leads to a term that can still step".

A region is grown from a term by adding the successors of its states and the parts of its terms, for some
rounds (`grow`). When it closes,
`decideFrom` returns the exact verdict (`decideFrom_sound`); otherwise it returns nothing.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.GSLT.LanguageDef.WellSorted
  (isObjectPattern FreeTypeContext)

/-- The splits of a list: every way to write it as a front and a back. -/
def listSplits {α : Type} (list : List α) : List (List α × List α) :=
  (List.range (list.length + 1)).map fun index => (list.take index, list.drop index)

theorem mem_listSplits {α : Type} {list front back : List α} :
    (front, back) ∈ listSplits list ↔ front ++ back = list := by
  simp only [listSplits, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨index, -, rfl, rfl⟩
    exact List.take_append_drop index list
  · rintro rfl
    exact ⟨front.length, by simp only [List.length_append]; omega, by simp, by simp⟩

/-- The parts a term's shapes mention: arguments, members, halves and bodies. -/
def shapeParts : Pattern → List Pattern
  | .apply _ arguments => arguments
  | .collection kind elements none =>
    elements ++ (listSplits elements).flatMap fun split => [.collection kind split.1 none, .collection kind split.2 none]
  | .lambda _ inner => [inner]
  | .multiLambda _ _ inner => [inner]
  | _ => []

theorem isStateBool_of_isState {pattern : Pattern} (state : IsState pattern) : isStateBool pattern = true := by
  simp only [isStateBool, Bool.and_eq_true]
  exact state

variable (relEnv : RelationEnv) (language : LanguageDef) (fuel : ℕ) (region : List Pattern)

/-- **A closed region**: no term is listed twice, every state is completely listed at the fuel, with its
successors in the region, and every term has its parts in the region. -/
def closedRegion : Bool :=
  decide region.Nodup && region.all fun term =>
    (!isStateBool term ||
      (enough relEnv language fuel term && (stepsAt relEnv language fuel term).all fun entry => entry.2 ∈ region)) &&
    (shapeParts term).all (· ∈ region)

variable {relEnv language fuel region}

theorem exists_index {term : Pattern} (member : term ∈ region) : ∃ index : Fin region.length, region[index] = term := by
  obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp member
  exact ⟨⟨index, bound⟩, same⟩

theorem exists_indices : ∀ {terms : List Pattern}, (∀ term ∈ terms, term ∈ region) →
    ∃ indices : List (Fin region.length), indices.map (region[·]) = terms
  | [], _ => ⟨[], rfl⟩
  | term :: terms, inside => by
    obtain ⟨index, same⟩ := exists_index (inside term List.mem_cons_self)
    obtain ⟨indices, sameRest⟩ := exists_indices fun other member => inside other (List.mem_cons_of_mem _ member)
    refine ⟨index :: indices, ?_⟩
    show region[index] :: indices.map (region[·]) = term :: terms
    rw [same, sameRest]

theorem closed_at (closed : closedRegion relEnv language fuel region = true) (index : Fin region.length) :
    (isStateBool region[index] = true →
      enough relEnv language fuel region[index] = true ∧
        ∀ entry ∈ stepsAt relEnv language fuel region[index], entry.2 ∈ region) ∧
    ∀ part ∈ shapeParts region[index], part ∈ region := by
  simp only [closedRegion, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at closed
  obtain ⟨steps, parts⟩ := closed.2 region[index] (List.getElem_mem _)
  refine ⟨fun state => ?_, parts⟩
  rcases steps with notState | listed
  · rw [notState] at state
    cases state
  · exact listed

theorem closed_nodup (closed : closedRegion relEnv language fuel region = true) : region.Nodup := by
  simp only [closedRegion, Bool.and_eq_true, decide_eq_true_eq] at closed
  exact closed.1

/-- **A closed region's inclusion is a bounded morphism**, in an equation-free language. -/
def closedMorphism (free : language.isEquationFree = true) (closed : closedRegion relEnv language fuel region = true) :
    BoundedMorphism (exploration relEnv language fuel region).native (referenceStructure relEnv language) where
  toHom := explorationHom relEnv language fuel region
  stepBack := by
    intro source label target' own step
    obtain ⟨sourceState, targetState, redex, contractum, witness, before, -, valid, -, after, admitted⟩ := step
    rw [placed_iff own] at before
    replace admitted := StepLabel.admits_of_base own admitted
    rw [objectEquivalent_iff_eq_of_isEquationFree free] at before after
    subst before after
    obtain ⟨listed, successors⟩ := (closed_at closed source).1 (isStateBool_of_isState sourceState)
    have member := mem_stepsAt_of_enough listed valid
    obtain ⟨target, same⟩ := exists_index (successors _ member)
    refine ⟨target, ?_, same⟩
    show (_ && _ && _) = true
    simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq]
    exact ⟨⟨isStateBool_of_isState sourceState, same ▸ isStateBool_of_isState targetState⟩, _, member,
      same.symm, admitted⟩
  builtBack := by
    intro element constructor parts' isBuilt
    obtain ⟨object, equivalent⟩ := isBuilt
    rw [objectEquivalent_iff_eq_of_isEquationFree free] at equivalent
    change region[element] = _ at equivalent
    have parts := (closed_at closed element).2
    rw [equivalent] at parts
    obtain ⟨indices, same⟩ := exists_indices (region := region) (terms := parts') parts
    refine ⟨indices, ?_, same⟩
    show (_ && _) = true
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨object, by rw [equivalent, same]⟩
  splitBack := by
    intro element kind first' second' isSplit
    obtain ⟨object, left, right, equivalent, rfl, rfl⟩ := isSplit
    rw [objectEquivalent_iff_eq_of_isEquationFree free] at equivalent
    change region[element] = _ at equivalent
    have parts := (closed_at closed element).2
    rw [equivalent] at parts
    have halves : (left, right) ∈ listSplits (left ++ right) := mem_listSplits.mpr rfl
    obtain ⟨first, firstSame⟩ := exists_index (parts (.collection kind left none) (by
      simp only [shapeParts, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨(left, right), halves, by simp⟩))
    obtain ⟨second, secondSame⟩ := exists_index (parts (.collection kind right none) (by
      simp only [shapeParts, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨(left, right), halves, by simp⟩))
    refine ⟨first, second, ?_, firstSame, secondSame⟩
    show (_ && _) = true
    simp only [Bool.and_eq_true]
    refine ⟨object, ?_⟩
    rw [firstSame, secondSame]
    simp [splitParts, equivalent]
  emptyBack := by
    intro element kind isEmpty
    obtain ⟨object, equivalent⟩ := isEmpty
    rw [objectEquivalent_iff_eq_of_isEquationFree free] at equivalent
    show (_ && _) = true
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨object, equivalent⟩
  singleBack := by
    intro element kind member' isSingle
    obtain ⟨object, equivalent⟩ := isSingle
    rw [objectEquivalent_iff_eq_of_isEquationFree free] at equivalent
    change region[element] = _ at equivalent
    have parts := (closed_at closed element).2
    rw [equivalent] at parts
    obtain ⟨member, same⟩ := exists_index (parts member' (by simp [shapeParts]))
    refine ⟨member, ?_, same⟩
    show (_ && _) = true
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨object, by rw [equivalent, same]⟩
  bodyBack := by
    intro element inner' isBody
    obtain ⟨object, name, equivalent⟩ := isBody
    rw [objectEquivalent_iff_eq_of_isEquationFree free] at equivalent
    change region[element] = _ at equivalent
    have parts := (closed_at closed element).2
    rw [equivalent] at parts
    obtain ⟨inner, same⟩ := exists_index (parts inner' (by simp [shapeParts]))
    refine ⟨inner, ?_, same⟩
    show (_ && _) = true
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨object, by rw [equivalent, same]; rfl⟩
  multiBodyBack := by
    intro element arity inner' isBody
    obtain ⟨object, names, equivalent⟩ := isBody
    rw [objectEquivalent_iff_eq_of_isEquationFree free] at equivalent
    change region[element] = _ at equivalent
    have parts := (closed_at closed element).2
    rw [equivalent] at parts
    obtain ⟨inner, same⟩ := exists_index (parts inner' (by simp [shapeParts]))
    refine ⟨inner, ?_, same⟩
    show (_ && _) = true
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨object, by rw [equivalent, same]; rfl⟩
  boundBack := by
    intro element index isBound
    obtain ⟨object, equivalent⟩ := isBound
    rw [objectEquivalent_iff_eq_of_isEquationFree free] at equivalent
    show (_ && _) = true
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨object, equivalent⟩
  typedBack := by
    intro element type isTyped
    obtain ⟨object, representative, equivalent, wellSorted⟩ := isTyped
    rw [objectEquivalent_iff_eq_of_isEquationFree free] at equivalent
    subst equivalent
    show (_ && _) = true
    simp only [Bool.and_eq_true]
    exact ⟨object, checkCarrierTyped_eq_true_iff.mpr wellSorted⟩
  namedBack := by
    intro element term isNamed
    obtain ⟨object, equivalent⟩ := isNamed
    rw [objectEquivalent_iff_eq_of_isEquationFree free] at equivalent
    show (_ && _) = true
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨object, equivalent⟩
  inRelationBack := by
    intro element relation isIn
    show (_ && _) = true
    simp only [Bool.and_eq_true]
    exact (inRelation_iff_of_isEquationFree free).mp isIn
  sameIff := by
    intro first second
    change decide (first = second) = true ↔ ObjectEquivalent relEnv language .syntax region[first] region[second]
    rw [objectEquivalent_iff_eq_of_isEquationFree free, decide_eq_true_iff]
    constructor
    · rintro rfl
      rfl
    · intro same
      exact Fin.ext ((List.Nodup.getElem_inj_iff (closed_nodup closed)).mp same)

/-- **A closed region decides every forward formula at its terms**, both ways. -/
theorem closed_check_iff (free : language.isEquationFree = true) (closed : closedRegion relEnv language fuel region = true)
    {formula : Formula 0} (forward : formula.forward = true) (index : Fin region.length) :
    (exploration relEnv language fuel region).check formula index = true ↔
      (referenceStructure relEnv language).sat Env.closed formula region[index] := by
  rw [FiniteStructure.check_iff]
  exact (closedMorphism free closed).sat_iff formula forward (BoundedMorphism.envPreimage_closed _) index

/-! ## Growing a region -/

variable (relEnv language fuel)

/-- Grow a region from a term: add the successors of states and the parts of terms for some rounds,
without repetition, the term first. Closedness asks no more. -/
def grow (term : Pattern) : ℕ → List Pattern
  | 0 => [term]
  | rounds + 1 =>
    let earlier := grow term rounds
    addNew earlier (earlier.flatMap fun state =>
      (if isStateBool state then (stepsAt relEnv language fuel state).map (·.2) else []) ++ shapeParts state)

theorem grow_first (term : Pattern) : ∀ rounds, ∃ rest, grow relEnv language fuel term rounds = term :: rest
  | 0 => ⟨[], rfl⟩
  | rounds + 1 => by
    obtain ⟨rest, same⟩ := grow_first term rounds
    obtain ⟨extra, extended⟩ := addNew_extends (grow relEnv language fuel term rounds)
      ((grow relEnv language fuel term rounds).flatMap fun state =>
        (if isStateBool state then (stepsAt relEnv language fuel state).map (·.2) else []) ++ shapeParts state)
    refine ⟨rest ++ extra, ?_⟩
    simp only [grow]
    rw [extended, same, List.cons_append]

theorem grow_length_pos (term : Pattern) (rounds : ℕ) : 0 < (grow relEnv language fuel term rounds).length := by
  obtain ⟨rest, same⟩ := grow_first relEnv language fuel term rounds
  rw [same]
  exact Nat.succ_pos _

/-- **Decide a forward formula at a term** by growing a region for some rounds: the exact verdict when the
region closes, nothing otherwise. -/
def decideFrom (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Option Bool :=
  if closedRegion relEnv language fuel (grow relEnv language fuel term rounds) then
    some ((exploration relEnv language fuel (grow relEnv language fuel term rounds)).check formula
      ⟨0, grow_length_pos relEnv language fuel term rounds⟩)
  else none

variable {relEnv language fuel}

theorem grow_zero (term : Pattern) (rounds : ℕ) :
    (grow relEnv language fuel term rounds)[(⟨0, grow_length_pos relEnv language fuel term rounds⟩ :
      Fin (grow relEnv language fuel term rounds).length)] = term := by
  obtain ⟨rest, same⟩ := grow_first relEnv language fuel term rounds
  simp only [Fin.getElem_fin]
  simp [same]

/-- **A verdict from a closed region is exact**, in every reading of the equations, which are none. -/
theorem decideFrom_sound (free : language.isEquationFree = true) {formula : Formula 0} (forward : formula.forward = true)
    {term : Pattern} {rounds : ℕ} {verdict : Bool} {reading : LanguageReading}
    (decided : decideFrom relEnv language fuel formula term rounds = some verdict)
    (reference : reading.rules = .reference := by rfl) :
    (verdict = true ↔ (referenceStructure relEnv language reading).sat Env.closed formula term) := by
  rw [referenceStructure_eq_of_isEquationFree free reading, reference]
  unfold decideFrom at decided
  split at decided
  · rename_i closed
    cases decided
    rw [closed_check_iff free closed forward, grow_zero]
  · cases decided

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
