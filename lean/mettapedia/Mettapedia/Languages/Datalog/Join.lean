import Mettapedia.Languages.Datalog.RangeRestriction
import Mathlib.Data.List.Forall2

/-! Finite positive-body joins retain a shared clause-local environment.
Each premise queries the same fact snapshot, so repeated premises keep facts.
Row positions are validation evidence, separate from logical derivation keys. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.Datalog.Join

abbrev Environment := List (String × Value)

def assignment (environment : Environment) : Assignment := fun identifier => environment.lookup identifier

def Extends (before after : Environment) : Prop :=
  ∀ identifier value, before.lookup identifier = some value → after.lookup identifier = some value

def Agrees (environment : Environment) (model : Assignment) : Prop :=
  ∀ identifier value, environment.lookup identifier = some value → model identifier = some value

theorem Extends.refl (environment : Environment) : Extends environment environment := fun _ _ present => present

theorem Extends.trans {first second third : Environment}
    (left : Extends first second) (right : Extends second third) : Extends first third :=
  fun identifier value present => right identifier value (left identifier value present)

theorem matches_of_extends {before after : Environment} (preserved : Extends before after)
    (argument : Argument) (value : Value) (matched : argument.Matches (assignment before) value) :
    argument.Matches (assignment after) value := by
  cases argument with
  | literal _ => exact matched
  | anonymous => trivial
  | var identifier => exact preserved identifier value matched

def matchArgument (environment : Environment) (argument : Argument) (value : Value) : Option Environment :=
  match argument with
  | .literal expected => if expected = value then some environment else none
  | .var identifier =>
      match environment.lookup identifier with
      | none => some ((identifier, value) :: environment)
      | some previous => if previous = value then some environment else none
  | .anonymous => some environment

theorem matchArgument_sound {before after : Environment} {argument : Argument} {value : Value}
    (checked : matchArgument before argument value = some after) :
    Extends before after ∧ argument.Matches (assignment after) value := by
  cases argument with
  | literal expected =>
    simp only [matchArgument] at checked
    split at checked
    · rename_i same
      cases checked
      exact ⟨Extends.refl _, same⟩
    · cases checked
  | anonymous =>
    cases checked
    exact ⟨Extends.refl _, trivial⟩
  | var identifier =>
    simp only [matchArgument] at checked
    cases found : before.lookup identifier with
    | none =>
      rw [found] at checked
      cases checked
      constructor
      · intro other actual present
        by_cases same : other = identifier
        · subst other
          rw [found] at present
          cases present
        · simpa only [List.lookup_cons,
            show (other == identifier) = false from beq_eq_false_iff_ne.mpr same] using present
      · simp [Argument.Matches, assignment]
    | some previous =>
      simp only [found] at checked
      by_cases same : previous = value
      · rw [if_pos same] at checked
        cases checked
        exact ⟨Extends.refl _, by simpa only [Argument.Matches, assignment, same] using found⟩
      · rw [if_neg same] at checked
        cases checked

theorem matchArgument_complete (before : Environment) (model : Assignment)
    (agrees : Agrees before model) (argument : Argument) (value : Value)
    (matched : argument.Matches model value) :
    ∃ after, matchArgument before argument value = some after ∧ Agrees after model := by
  cases argument with
  | literal expected =>
    change expected = value at matched
    exact ⟨before, by simp [matchArgument, matched], agrees⟩
  | anonymous => exact ⟨before, rfl, agrees⟩
  | var identifier =>
    cases found : before.lookup identifier with
    | none =>
      refine ⟨(identifier, value) :: before, by simp [matchArgument, found], ?_⟩
      intro other actual present
      by_cases same : other = identifier
      · subst other
        simp at present
        subst actual
        exact matched
      · exact agrees other actual (by simpa only [List.lookup_cons,
          show (other == identifier) = false from beq_eq_false_iff_ne.mpr same] using present)
    | some previous =>
      have same : previous = value := Option.some.inj ((agrees identifier previous found).symm.trans matched)
      exact ⟨before, by simp [matchArgument, found, same], agrees⟩

def matchArguments : Environment → List Argument → List Value → Option Environment
  | environment, [], [] => some environment
  | environment, argument :: arguments, value :: values => do
      let next ← matchArgument environment argument value
      matchArguments next arguments values
  | _, _, _ => none

theorem matchArguments_sound {before after : Environment} {arguments : List Argument} {values : List Value}
    (checked : matchArguments before arguments values = some after) :
    Extends before after ∧ List.Forall₂ (Argument.Matches (assignment after)) arguments values := by
  induction arguments generalizing before values with
  | nil =>
    cases values with
    | nil => cases checked; exact ⟨Extends.refl _, .nil⟩
    | cons _ _ => simp [matchArguments] at checked
  | cons argument arguments ih =>
    cases values with
    | nil => simp [matchArguments] at checked
    | cons value values =>
      cases first : matchArgument before argument value with
      | none => simp [matchArguments, first] at checked
      | some middle =>
        simp only [matchArguments, first] at checked
        obtain ⟨preserved, matched⟩ := matchArgument_sound first
        obtain ⟨tailExtends, tailMatches⟩ := ih checked
        exact ⟨preserved.trans tailExtends,
          .cons (matches_of_extends tailExtends argument value matched) tailMatches⟩

theorem matchArguments_complete (before : Environment) (model : Assignment)
    (agrees : Agrees before model) (arguments : List Argument) (values : List Value)
    (matched : List.Forall₂ (Argument.Matches model) arguments values) :
    ∃ after, matchArguments before arguments values = some after ∧ Agrees after model := by
  induction matched generalizing before with
  | nil => exact ⟨before, rfl, agrees⟩
  | cons head tail ih =>
    obtain ⟨middle, first, compatible⟩ := matchArgument_complete before model agrees _ _ head
    obtain ⟨after, rest, agreesAfter⟩ := ih middle compatible
    exact ⟨after, by simp [matchArguments, first, rest], agreesAfter⟩

def matchAtom (environment : Environment) (atom : Atom) (fact : GroundFact) : Option Environment :=
  if atom.relation = fact.relation then matchArguments environment atom.arguments fact.values else none

theorem matchAtom_sound {before after : Environment} {atom : Atom} {fact : GroundFact}
    (checked : matchAtom before atom fact = some after) :
    Extends before after ∧ atom.Matches (assignment after) fact := by
  unfold matchAtom at checked
  split at checked
  · rename_i same
    obtain ⟨preserved, matched⟩ := matchArguments_sound checked
    exact ⟨preserved, same, matched⟩
  · cases checked

theorem matchAtom_complete (before : Environment) (model : Assignment)
    (agrees : Agrees before model) (atom : Atom) (fact : GroundFact) (matched : atom.Matches model fact) :
    ∃ after, matchAtom before atom fact = some after ∧ Agrees after model := by
  obtain ⟨after, checked, compatible⟩ := matchArguments_complete before model agrees _ _ matched.2
  exact ⟨after, by simp [matchAtom, matched.1, checked], compatible⟩

structure Row where
  environment : Environment
  facts : List GroundFact
  rowPositions : List Nat
  deriving Repr, DecidableEq

def join : List Atom → List GroundFact → Environment → List Row
  | [], _, environment => [⟨environment, [], []⟩]
  | atom :: atoms, known, environment =>
      known.zipIdx.flatMap fun (fact, position) =>
        match matchAtom environment atom fact with
        | none => []
        | some next => (join atoms known next).map fun row =>
            ⟨row.environment, fact :: row.facts, position :: row.rowPositions⟩

theorem atom_matches_of_extends {before after : Environment} (preserved : Extends before after)
    (atom : Atom) (fact : GroundFact) (matched : atom.Matches (assignment before) fact) :
    atom.Matches (assignment after) fact := by
  constructor
  · exact matched.1
  · exact List.Forall₂.imp (fun argument value first => matches_of_extends preserved argument value first) matched.2

theorem join_sound (atoms : List Atom) (known : List GroundFact) (before : Environment)
    {row : Row} (member : row ∈ join atoms known before) :
    Extends before row.environment ∧
      List.Forall₂ (Atom.Matches (assignment row.environment)) atoms row.facts ∧
      List.Forall₂ (fun fact position => known[position]? = some fact) row.facts row.rowPositions := by
  induction atoms generalizing before row with
  | nil =>
    have same : row = ⟨before, [], []⟩ := by simpa [join] using member
    cases same
    exact ⟨Extends.refl _, .nil, .nil⟩
  | cons atom atoms ih =>
    simp only [join, List.mem_flatMap] at member
    obtain ⟨⟨fact, position⟩, selected, published⟩ := member
    cases checked : matchAtom before atom fact with
    | none => simp [checked] at published
    | some middle =>
      simp only [checked, List.mem_map] at published
      obtain ⟨tail, included, rfl⟩ := published
      obtain ⟨preserved, matched⟩ := matchAtom_sound checked
      obtain ⟨tailPreserved, tailMatched, positions⟩ := ih middle included
      exact ⟨preserved.trans tailPreserved,
        .cons (atom_matches_of_extends tailPreserved atom fact matched) tailMatched,
        .cons (List.mk_mem_zipIdx_iff_getElem?.mp selected) positions⟩

theorem join_complete (atoms : List Atom) (known choices : List GroundFact)
    (before : Environment) (model : Assignment) (agrees : Agrees before model)
    (available : ∀ fact ∈ choices, fact ∈ known)
    (matched : List.Forall₂ (Atom.Matches model) atoms choices) :
    ∃ row ∈ join atoms known before, row.facts = choices ∧ Agrees row.environment model := by
  induction matched generalizing before with
  | nil => exact ⟨⟨before, [], []⟩, by simp [join], rfl, agrees⟩
  | @cons atom fact atoms choices head tail ih =>
    obtain ⟨middle, checked, compatible⟩ := matchAtom_complete before model agrees atom fact head
    obtain ⟨row, included, same, finalAgrees⟩ :=
      ih middle compatible (fun other inside => available other (List.mem_cons_of_mem _ inside))
    obtain ⟨position, bound, chosen⟩ := List.mem_iff_getElem.mp (available fact List.mem_cons_self)
    have selected : (fact, position) ∈ known.zipIdx :=
      List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_some_iff.mpr ⟨bound, chosen⟩)
    refine ⟨⟨row.environment, fact :: row.facts, position :: row.rowPositions⟩, ?_, ?_, finalAgrees⟩
    · simp only [join, List.mem_flatMap]
      refine ⟨(fact, position), selected, ?_⟩
      simp only [checked, List.mem_map]
      exact ⟨row, included, rfl⟩
    · exact congrArg (fact :: ·) same

#print axioms matchArgument_sound
#print axioms matchArgument_complete
#print axioms matchArguments_sound
#print axioms matchArguments_complete
#print axioms matchAtom_sound
#print axioms matchAtom_complete
#print axioms join_sound
#print axioms join_complete

end Mettapedia.Languages.Datalog.Join
