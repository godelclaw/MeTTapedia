import Mettapedia.OSLF.NativeTypes.GeneratedLogic.DriverBridge
import Mettapedia.OSLF.NativeTypes.Runtime.Atoms

/-!
# Observations as declared relations

A driver may observe its terms beyond its constructor tests (`Runtime.Atoms.extend`). Such an observation is declared
with the language as a unary relation: the relation of its name holds of exactly the terms it observes
(`observationEnv`). In the generated logic it is the atom `inRelation name`, whose meaning in the language's reference
structure is the observation, on object terms of an equation-free language (`sat_observed_iff`).

A reading of a driver extends to its declared observations (`Faithful.observe`, `FaithfulSteps.observe`): each
observation's atom closes to the relation atom of its name, and the reading's other tests are unchanged. So the
driver's formulas that mention observations are again native types of the language, now read with its declared
relations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.Observations

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.Runtime.Description (Driver)
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core (Test)
open Mettapedia.OSLF.NativeTypes.Decision.Admission (LeafAdmission)

/-- **An observation declared with a language**: a name, and the decidable predicate of terms it observes. -/
structure Observation where
  name : String
  observe : Pattern → Bool

/-- **The relation environment declaring observations**: each observation is the unary relation of its name, which
holds of the terms it observes; every other query is the base environment's. -/
def observationEnv (base : RelationEnv) (observations : List Observation) : RelationEnv where
  tuples relation arguments :=
    match arguments, observations.find? (fun observation => observation.name == relation) with
    | [term], some observation => if observation.observe term then [[term]] else []
    | _, _ => base.tuples relation arguments

/-- An observation is declared when it is the first one listed under its name. -/
def Declared (observations : List Observation) (observation : Observation) : Prop :=
  observations.find? (fun other => other.name == observation.name) = some observation

theorem relationHolds_observationEnv (base : RelationEnv) {observations : List Observation}
    {observation : Observation} (declared : Declared observations observation) (language : LanguageDef)
    (term : Pattern) :
    relationHolds (observationEnv base observations) language observation.name term = observation.observe term := by
  rw [Bool.eq_iff_iff, relationHolds_iff]
  simp only [observationEnv, Declared] at declared ⊢
  rw [declared]
  dsimp only
  split_ifs with observed <;> simp [observed]

/-- **A declared observation is its relation atom**, at object terms of an equation-free language. -/
theorem sat_observed_iff (base : RelationEnv) {observations : List Observation} {observation : Observation}
    (declared : Declared observations observation) {language : LanguageDef} (free : language.isEquationFree = true)
    (term : Pattern) :
    (referenceStructure (observationEnv base observations) language).sat Env.closed (.inRelation observation.name)
        term ↔ IsObject term ∧ observation.observe term = true := by
  show (referenceStructure _ _).inRelation term _ ↔ _
  rw [inRelation_iff_of_isEquationFree free, relationHolds_observationEnv base declared]

/-! ## Readings with observations -/

variable {driver : Driver} {base : RelationEnv} {observations : List Observation} {language : LanguageDef} {m k : ℕ}
  {positive negative : driver.Leaf → Fin m}

/-- The variables of a driver's tests and of its observations: the observations' pairs follow the tests'. -/
def observedPositive (positive : driver.Leaf → Fin m) : Sum driver.Leaf (Fin k) → Fin (m + 2 * k)
  | .inl leaf => Fin.castAdd _ (positive leaf)
  | .inr atom => Fin.natAdd m ⟨2 * atom.val, by omega⟩

def observedNegative (negative : driver.Leaf → Fin m) : Sum driver.Leaf (Fin k) → Fin (m + 2 * k)
  | .inl leaf => Fin.castAdd _ (negative leaf)
  | .inr atom => Fin.natAdd m ⟨2 * atom.val + 1, by omega⟩

/-- The closing formulas with observations: a test's as before, and each observation's relation atom and its dual. -/
def observedClosing (closing : Fin m → Formula 0) (declared : Fin k → Observation) (slot : Fin (m + 2 * k)) :
    Formula 0 :=
  Fin.addCases closing (fun observed : Fin (2 * k) =>
    if observed.val % 2 = 0 then .inRelation (declared ⟨observed.val / 2, by omega⟩).name
    else .notInRelation (declared ⟨observed.val / 2, by omega⟩).name) slot

theorem observedClosing_positive (closing : Fin m → Formula 0) (declared : Fin k → Observation)
    (positive : driver.Leaf → Fin m) (atom : Fin k) :
    observedClosing closing declared (observedPositive (k := k) positive (.inr atom)) = .inRelation (declared atom).name := by
  have parity : (2 * atom.val) % 2 = 0 := by omega
  have same : (⟨2 * atom.val / 2, by omega⟩ : Fin k) = atom := Fin.ext (show 2 * atom.val / 2 = atom.val by omega)
  simp only [observedClosing, observedPositive, Fin.addCases_right, parity, if_true]
  rw [same]

theorem observedClosing_negative (closing : Fin m → Formula 0) (declared : Fin k → Observation)
    (negative : driver.Leaf → Fin m) (atom : Fin k) :
    observedClosing closing declared (observedNegative (k := k) negative (.inr atom)) =
      .notInRelation (declared atom).name := by
  have parity : (2 * atom.val + 1) % 2 = 1 := by omega
  have same : (⟨(2 * atom.val + 1) / 2, by omega⟩ : Fin k) = atom :=
    Fin.ext (show (2 * atom.val + 1) / 2 = atom.val by omega)
  simp only [observedClosing, observedNegative, Fin.addCases_right, parity, one_ne_zero, if_false]
  rw [same]

theorem observedClosing_forward (closing : Fin m → Formula 0) (declared : Fin k → Observation)
    (forward : ∀ index, (closing index).forward = true) (slot : Fin (m + 2 * k)) :
    (observedClosing closing declared slot).forward = true := by
  refine Fin.addCases (fun index => ?_) (fun observed => ?_) slot
  · simp only [observedClosing, Fin.addCases_left]
    exact forward index
  · simp only [observedClosing, Fin.addCases_right]
    split_ifs <;> rfl

/-- **A faithful reading extends to declared observations**, in an equation-free language: each observation's atom is
its relation atom, when the observation's test holds exactly at the terms whose renderings are observed objects. -/
def _root_.Mettapedia.OSLF.NativeTypes.GeneratedLogic.Embeddings.Faithful.observe
    (faithful : Embeddings.Faithful driver (observationEnv base observations) language positive negative)
    (tests : Fin k → Test driver.system driver.admitted) (atomic : LeafAdmission (Fin k))
    (declaredAs : Fin k → Observation) (declared : ∀ atom, Declared observations (declaredAs atom))
    (free : language.isEquationFree = true)
    (agrees : ∀ atom source, faithful.region source →
      ((tests atom).predicate.1 source ↔ IsObject (driver.render source) ∧
        (declaredAs atom).observe (driver.render source) = true)) :
    Embeddings.Faithful (Mettapedia.OSLF.NativeTypes.Runtime.Atoms.extend driver tests atomic)
      (observationEnv base observations) language (observedPositive positive) (observedNegative negative) where
  structure_ := faithful.structure_
  region := faithful.region
  steps := faithful.steps
  closed := faithful.closed
  rendering := faithful.rendering
  renders := faithful.renders
  covers := Sum.elim faithful.covers fun _ => True
  test := Sum.elim faithful.test fun atom => .inRelation (declaredAs atom).name
  testAgrees
    | .inl leaf, covered, source, inside => faithful.testAgrees leaf covered source inside
    | .inr atom, _, source, inside =>
      (agrees atom source inside).trans (sat_observed_iff base (declared atom) free _).symm
  closing := observedClosing faithful.closing declaredAs
  closesPositive
    | .inl leaf => by
      simp only [observedClosing, observedPositive, Fin.addCases_left, Sum.elim_inl]
      exact faithful.closesPositive leaf
    | .inr atom => observedClosing_positive faithful.closing declaredAs positive atom
  closesNegative
    | .inl leaf => by
      simp only [observedClosing, observedNegative, Fin.addCases_left, Sum.elim_inl]
      exact faithful.closesNegative leaf
    | .inr atom => observedClosing_negative faithful.closing declaredAs negative atom
  closingForward := observedClosing_forward faithful.closing declaredAs faithful.closingForward

/-- **And so does a faithful reading by steps.** -/
def _root_.Mettapedia.OSLF.NativeTypes.GeneratedLogic.Embeddings.FaithfulSteps.observe
    (faithful : Embeddings.FaithfulSteps driver (observationEnv base observations) language positive negative)
    (tests : Fin k → Test driver.system driver.admitted) (atomic : LeafAdmission (Fin k))
    (declaredAs : Fin k → Observation) (declared : ∀ atom, Declared observations (declaredAs atom))
    (free : language.isEquationFree = true)
    (agrees : ∀ atom source, faithful.region source →
      ((tests atom).predicate.1 source ↔ IsObject (driver.render source) ∧
        (declaredAs atom).observe (driver.render source) = true)) :
    Embeddings.FaithfulSteps (Mettapedia.OSLF.NativeTypes.Runtime.Atoms.extend driver tests atomic)
      (observationEnv base observations) language (observedPositive positive) (observedNegative negative) where
  structure_ := faithful.structure_
  region := faithful.region
  steps := faithful.steps
  closed := faithful.closed
  rendering := faithful.rendering
  renders := faithful.renders
  covers := Sum.elim faithful.covers fun _ => True
  test := Sum.elim faithful.test fun atom => .inRelation (declaredAs atom).name
  testAgrees
    | .inl leaf, covered, source, inside => faithful.testAgrees leaf covered source inside
    | .inr atom, _, source, inside =>
      (agrees atom source inside).trans (sat_observed_iff base (declared atom) free _).symm
  closing := observedClosing faithful.closing declaredAs
  closesPositive
    | .inl leaf => by
      simp only [observedClosing, observedPositive, Fin.addCases_left, Sum.elim_inl]
      exact faithful.closesPositive leaf
    | .inr atom => observedClosing_positive faithful.closing declaredAs positive atom
  closesNegative
    | .inl leaf => by
      simp only [observedClosing, observedNegative, Fin.addCases_left, Sum.elim_inl]
      exact faithful.closesNegative leaf
    | .inr atom => observedClosing_negative faithful.closing declaredAs negative atom
  closingForward := observedClosing_forward faithful.closing declaredAs faithful.closingForward

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.Observations
