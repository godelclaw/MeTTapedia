import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Finite
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Transfer
import Mettapedia.OSLF.MeTTaIL.ReferenceStepExecution
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-!
# Explorations as evidence

A finite-model certificate maps the language's structure onto a finite one, so it proves universal
formulas and refutes existential ones. The other side of the evidence is an exploration: a listed
region of the language's terms, with the steps among them that the step enumerator lists and the
shapes they have as written (`exploration`). The region sits inside the language's structure
(`explorationHom`).

- **Existential formulas** that hold in the region hold in the language (`explores_sound`): a step
  witness, a path to a goal, a decomposition, a typed witness.
- **Universal formulas** whose dual holds in the region fail in the language (`exploresAgainst_sound`).

A region is any list of terms; a strategy chooses it, for instance by listing what a term reaches
(`reachable`), and the check alone carries the proof.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.GSLT.LanguageDef.WellSorted
  (isObjectPattern FreeTypeContext)

/-- Whether a pattern is a state. -/
def isStateBool (pattern : Pattern) : Bool := pattern.isWellScopedAt 0 && isObjectPattern pattern

theorem isState_of_bool {pattern : Pattern} (checked : isStateBool pattern = true) : IsState pattern := by
  simp only [isStateBool, Bool.and_eq_true] at checked
  exact checked

/-- The two parts of a split, as written: both collections of the kind without a tail. -/
def splitParts (kind : CollType) : Pattern → Pattern → Option (List Pattern × List Pattern)
  | .collection firstKind first none, .collection secondKind second none =>
    if firstKind = kind ∧ secondKind = kind then some (first, second) else none
  | _, _ => none

theorem splitParts_some {kind : CollType} {first second : Pattern} {left right : List Pattern}
    (split : splitParts kind first second = some (left, right)) :
    first = .collection kind left none ∧ second = .collection kind right none := by
  cases first <;> cases second <;> simp [splitParts] at split
  rename_i firstKind firstElements firstRest secondKind secondElements secondRest
  cases firstRest <;> cases secondRest <;> simp at split
  obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := split
  exact ⟨rfl, rfl⟩

/-- An abstraction's body, as written. -/
def bodyOf : Pattern → Option Pattern
  | .lambda _ inner => some inner
  | _ => none

/-- A multi-abstraction's arity and body, as written. -/
def multiBodyOf : Pattern → Option (ℕ × Pattern)
  | .multiLambda arity _ inner => some (arity, inner)
  | _ => none

variable (relEnv : RelationEnv) (language : LanguageDef) (fuel : ℕ) (region : List Pattern)

/-- **The explored region**: listed terms, the steps among them that the step enumerator lists at the
fuel, and the shapes they have as written. -/
def exploration : FiniteStructure (Fin region.length) where
  elements := List.finRange region.length
  complete := List.mem_finRange
  step source label target := isStateBool region[source] && isStateBool region[target] &&
    (stepsAt relEnv language fuel region[source]).any fun entry => entry.2 == region[target] && label.admits entry.1
  built element constructor parts := isObjectPattern region[element] &&
    region[element] == .apply constructor (parts.map (region[·]))
  split element kind first second := isObjectPattern region[element] &&
    match splitParts kind region[first] region[second] with
    | some (left, right) => region[element] == .collection kind (left ++ right) none
    | none => false
  empty element kind := isObjectPattern region[element] && region[element] == .collection kind [] none
  single element kind member := isObjectPattern region[element] &&
    region[element] == .collection kind [region[member]] none
  body element inner := isObjectPattern region[element] && bodyOf region[element] == some region[inner]
  multiBody element arity inner := isObjectPattern region[element] &&
    multiBodyOf region[element] == some (arity, region[inner])
  bound element index := isObjectPattern region[element] && region[element] == .bvar index
  typed element type := isObjectPattern region[element] &&
    checkCarrierTyped language type region[element]
  named element term := isObjectPattern region[element] && region[element] == term
  same first second := decide (first = second)
  apply inner _ := inner
  inRelation element relation := isObjectPattern region[element] && relationHolds relEnv language relation region[element]

/-- **The region sits inside the language's structure**, in every reading of its equations with the reference relation
for its rules: it relates terms only by what they are. -/
def explorationHom (reading : LanguageReading := .syntax) (reference : reading.rules = .reference := by rfl) :
    Hom (exploration relEnv language fuel region).native (referenceStructure relEnv language reading) where
  map element := region[element]
  step := by
    intro source label target _ checked
    change (_ && _ && _) = true at checked
    simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at checked
    obtain ⟨⟨sourceState, targetState⟩, ⟨witness, result⟩, member, same, admitted⟩ := checked
    simp only at same
    subst same
    refine ⟨isState_of_bool sourceState, isState_of_bool targetState, _, _, witness, placed_self admitted _,
      isState_of_bool sourceState, ?_, isState_of_bool targetState, Relation.EqvGen.refl _,
      StepLabel.base_admits admitted⟩
    rw [reference]
    exact stepValid_of_mem_stepsAt relEnv language member
  built := by
    intro element constructor parts checked
    change (_ && _) = true at checked
    simp only [Bool.and_eq_true, beq_iff_eq] at checked
    obtain ⟨object, same⟩ := checked
    refine ⟨object, ?_⟩
    rw [same]
    exact Relation.EqvGen.refl _
  split := by
    intro element kind first second checked
    change (_ && _) = true at checked
    simp only [Bool.and_eq_true] at checked
    obtain ⟨object, parts⟩ := checked
    cases splitting : splitParts kind region[first] region[second] with
    | none => rw [splitting] at parts; cases parts
    | some pieces =>
      obtain ⟨left, right⟩ := pieces
      rw [splitting] at parts
      simp only [beq_iff_eq] at parts
      obtain ⟨firstIs, secondIs⟩ := splitParts_some splitting
      exact ⟨object, left, right, parts ▸ Relation.EqvGen.refl _, firstIs, secondIs⟩
  empty := by
    intro element kind checked
    change (_ && _) = true at checked
    simp only [Bool.and_eq_true, beq_iff_eq] at checked
    obtain ⟨object, same⟩ := checked
    exact ⟨object, same ▸ Relation.EqvGen.refl _⟩
  single := by
    intro element kind member checked
    change (_ && _) = true at checked
    simp only [Bool.and_eq_true, beq_iff_eq] at checked
    obtain ⟨object, same⟩ := checked
    exact ⟨object, same ▸ Relation.EqvGen.refl _⟩
  body := by
    intro element inner checked
    change (_ && _) = true at checked
    simp only [Bool.and_eq_true, beq_iff_eq] at checked
    obtain ⟨object, same⟩ := checked
    refine ⟨object, ?_⟩
    revert same
    cases shape : region[element] with
    | lambda name body =>
      intro same
      simp only [bodyOf, Option.some.injEq] at same
      exact ⟨name, same ▸ Relation.EqvGen.refl _⟩
    | _ => intro same; simp [bodyOf] at same
  multiBody := by
    intro element arity inner checked
    change (_ && _) = true at checked
    simp only [Bool.and_eq_true, beq_iff_eq] at checked
    obtain ⟨object, same⟩ := checked
    refine ⟨object, ?_⟩
    revert same
    cases shape : region[element] with
    | multiLambda arity' names body =>
      intro same
      simp only [multiBodyOf, Option.some.injEq, Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      exact ⟨names, Relation.EqvGen.refl _⟩
    | _ => intro same; simp [multiBodyOf] at same
  bound := by
    intro element index checked
    change (_ && _) = true at checked
    simp only [Bool.and_eq_true, beq_iff_eq] at checked
    obtain ⟨object, same⟩ := checked
    exact ⟨object, same ▸ Relation.EqvGen.refl _⟩
  typed := by
    intro element type checked
    change (_ && _) = true at checked
    simp only [Bool.and_eq_true] at checked
    obtain ⟨object, wellSorted⟩ := checked
    exact ⟨object, region[element], Relation.EqvGen.refl _, checkCarrierTyped_eq_true_iff.mp wellSorted⟩
  named := by
    intro element term checked
    change (_ && _) = true at checked
    simp only [Bool.and_eq_true, beq_iff_eq] at checked
    obtain ⟨object, same⟩ := checked
    exact ⟨object, same ▸ Relation.EqvGen.refl _⟩
  inRelation := by
    intro element relation checked
    change (_ && _) = true at checked
    simp only [Bool.and_eq_true] at checked
    exact inRelation_of_relationHolds checked.1 checked.2

/-- **An exploration proves an existential formula** at a listed term: the formula holds in the region. -/
def explores (formula : Formula 0) (index : Fin region.length) : Bool :=
  formula.existential && (exploration relEnv language fuel region).check formula index

/-- **An exploration refutes a universal formula** at a listed term: its dual holds in the region. -/
def exploresAgainst (formula : Formula 0) (index : Fin region.length) : Bool :=
  explores relEnv language fuel region formula.dual index

variable {relEnv language fuel region} {reading : LanguageReading}

theorem explores_sound {formula : Formula 0} {index : Fin region.length}
    (checked : explores relEnv language fuel region formula index = true)
    (reference : reading.rules = .reference := by rfl) :
    (referenceStructure relEnv language reading).sat Env.closed formula region[index] := by
  simp only [explores, Bool.and_eq_true] at checked
  exact (explorationHom relEnv language fuel region reading reference).sat_of_hom formula checked.1
    (sourceEnv := Env.closed)
    (targetEnv := Env.closed) (fun index => index.elim0) index
    (((exploration relEnv language fuel region).check_iff formula index).mp checked.2)

theorem exploresAgainst_sound {formula : Formula 0} {index : Fin region.length}
    (checked : exploresAgainst relEnv language fuel region formula index = true)
    (reference : reading.rules = .reference := by rfl) :
    ¬ (referenceStructure relEnv language reading).sat Env.closed formula region[index] :=
  ((referenceStructure relEnv language reading).sat_dual_closed formula _).mp (explores_sound checked reference)

/-! ## A region a term reaches -/

/-- Append the terms not seen yet, in order. -/
def addNew (seen : List Pattern) : List Pattern → List Pattern
  | [] => seen
  | term :: terms => if term ∈ seen then addNew seen terms else addNew (seen ++ [term]) terms

theorem addNew_extends : ∀ (seen terms : List Pattern), ∃ extra, addNew seen terms = seen ++ extra
  | seen, [] => ⟨[], by simp [addNew]⟩
  | seen, term :: terms => by
    unfold addNew
    split
    · exact addNew_extends seen terms
    · obtain ⟨extra, same⟩ := addNew_extends (seen ++ [term]) terms
      exact ⟨term :: extra, by rw [same]; simp⟩

variable (relEnv language fuel)

/-- The terms a term reaches in at most some rounds of steps, without repetition, the term first. -/
def reachable (term : Pattern) : ℕ → List Pattern
  | 0 => [term]
  | rounds + 1 =>
    let earlier := reachable term rounds
    addNew earlier (earlier.flatMap fun state => (stepsAt relEnv language fuel state).map (·.2))

theorem reachable_first (term : Pattern) : ∀ rounds, ∃ rest, reachable relEnv language fuel term rounds = term :: rest
  | 0 => ⟨[], rfl⟩
  | rounds + 1 => by
    obtain ⟨rest, same⟩ := reachable_first term rounds
    obtain ⟨extra, extended⟩ := addNew_extends (reachable relEnv language fuel term rounds)
      ((reachable relEnv language fuel term rounds).flatMap fun state =>
        (stepsAt relEnv language fuel state).map (·.2))
    refine ⟨rest ++ extra, ?_⟩
    simp only [reachable]
    rw [extended, same, List.cons_append]

theorem reachable_length_pos (term : Pattern) (rounds : ℕ) : 0 < (reachable relEnv language fuel term rounds).length := by
  obtain ⟨rest, same⟩ := reachable_first relEnv language fuel term rounds
  rw [same]
  exact Nat.succ_pos _

/-- **Explore from a term**: an existential formula holds in the region the term reaches in some
rounds. -/
def exploresFrom (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Bool :=
  explores relEnv language fuel (reachable relEnv language fuel term rounds) formula
    ⟨0, reachable_length_pos relEnv language fuel term rounds⟩

/-- **Explore against a term**: the dual of a universal formula holds in the region the term reaches. -/
def exploresAgainstFrom (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Bool :=
  exploresFrom relEnv language fuel formula.dual term rounds

variable {relEnv language fuel} {reading : LanguageReading}

theorem reachable_zero (term : Pattern) (rounds : ℕ) :
    (reachable relEnv language fuel term rounds)[(⟨0, reachable_length_pos relEnv language fuel term rounds⟩ :
      Fin (reachable relEnv language fuel term rounds).length)] = term := by
  obtain ⟨rest, same⟩ := reachable_first relEnv language fuel term rounds
  simp only [Fin.getElem_fin]
  simp [same]

theorem exploresFrom_sound {formula : Formula 0} {term : Pattern} {rounds : ℕ}
    (checked : exploresFrom relEnv language fuel formula term rounds = true)
    (reference : reading.rules = .reference := by rfl) :
    (referenceStructure relEnv language reading).sat Env.closed formula term := by
  have holds := explores_sound (reading := reading) checked reference
  rwa [reachable_zero] at holds

theorem exploresAgainstFrom_sound {formula : Formula 0} {term : Pattern} {rounds : ℕ}
    (checked : exploresAgainstFrom relEnv language fuel formula term rounds = true)
    (reference : reading.rules = .reference := by rfl) :
    ¬ (referenceStructure relEnv language reading).sat Env.closed formula term :=
  ((referenceStructure relEnv language reading).sat_dual_closed formula term).mp
    (exploresFrom_sound checked reference)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
