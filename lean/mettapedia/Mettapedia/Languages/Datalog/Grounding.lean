import Mettapedia.Languages.Datalog.Join

/-! Range restriction turns a successful positive-body join into a total
head instantiation. No default value is assigned to an unbound variable. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.Datalog.Grounding

open Join

private theorem related_member {α β : Type} {relation : α → β → Prop}
    {left : List α} {right : List β} (related : List.Forall₂ relation left right)
    {element : α} (member : element ∈ left) : ∃ other ∈ right, relation element other := by
  induction related with
  | nil => simp at member
  | @cons first other left right head tail ih =>
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨other, List.mem_cons_self, head⟩
    · obtain ⟨value, inside, matched⟩ := ih later
      exact ⟨value, List.mem_cons_of_mem _ inside, matched⟩

theorem joined_body_matches (clause : Clause) (known : List GroundFact) (before : Environment)
    {row : Row} (member : row ∈ join clause.positiveAtoms known before) :
    ∀ atom ∈ clause.positiveAtoms, ∃ fact ∈ ({fact | fact ∈ known} : Set GroundFact),
      atom.Matches (assignment row.environment) fact := by
  obtain ⟨_, matched, positions⟩ := join_sound _ _ _ member
  intro atom inside
  obtain ⟨fact, selected, matched⟩ := related_member matched inside
  obtain ⟨position, _, actual⟩ := related_member positions selected
  obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp actual
  exact ⟨fact, same ▸ List.getElem_mem bound, matched⟩

theorem required_variable_bound (clause : Clause) (restricted : clause.RangeRestricted)
    (known : List GroundFact) (before : Environment) {row : Row}
    (member : row ∈ join clause.positiveAtoms known before) {identifier : String}
    (needed : identifier ∈ clause.requiredVariables) :
    ∃ value, row.environment.lookup identifier = some value := by
  obtain ⟨_, _, value, _, bound⟩ := Clause.required_variable_from_body restricted
    (assignment row.environment) {fact | fact ∈ known} (joined_body_matches clause known before member) needed
  exact ⟨value, bound⟩

def argumentValue? (environment : Environment) : Argument → Option Value
  | .literal value => some value
  | .var identifier => environment.lookup identifier
  | .anonymous => none

theorem argumentValue?_matches {environment : Environment} {argument : Argument} {value : Value}
    (checked : argumentValue? environment argument = some value) :
    argument.Matches (assignment environment) value := by
  cases argument with
  | literal expected => exact Option.some.inj checked
  | var _ => exact checked
  | anonymous => cases checked

def argumentValues? (environment : Environment) : List Argument → Option (List Value)
  | [] => some []
  | argument :: arguments => do
      let value ← argumentValue? environment argument
      let values ← argumentValues? environment arguments
      pure (value :: values)

theorem argumentValues?_sound {environment : Environment} {arguments : List Argument} {values : List Value}
    (checked : argumentValues? environment arguments = some values) :
    List.Forall₂ (Argument.Matches (assignment environment)) arguments values := by
  induction arguments generalizing values with
  | nil => cases checked; exact .nil
  | cons argument arguments ih =>
    cases first : argumentValue? environment argument with
    | none => simp [argumentValues?, first] at checked
    | some value =>
      cases rest : argumentValues? environment arguments with
      | none => simp [argumentValues?, first, rest] at checked
      | some tail =>
        simp only [argumentValues?, first, rest] at checked
        change some (value :: tail) = some values at checked
        cases checked
        exact .cons (argumentValue?_matches first) (ih rest)

theorem argumentValues?_complete (environment : Environment) (arguments : List Argument) (values : List Value)
    (noAnonymous : ∀ argument ∈ arguments, argument ≠ .anonymous)
    (matched : List.Forall₂ (Argument.Matches (assignment environment)) arguments values) :
    argumentValues? environment arguments = some values := by
  induction matched with
  | nil => rfl
  | @cons argument value arguments values first _ ih =>
    have present : argumentValue? environment argument = some value := by
      cases argument with
      | literal expected => exact congrArg some first
      | var _ => exact first
      | anonymous => exact False.elim (noAnonymous .anonymous List.mem_cons_self rfl)
    have rest := ih (fun other inside => noAnonymous other (List.mem_cons_of_mem _ inside))
    simp [argumentValues?, present, rest]

theorem argumentValues?_defined (environment : Environment) (arguments : List Argument)
    (noAnonymous : ∀ argument ∈ arguments, argument ≠ .anonymous)
    (bound : ∀ identifier ∈ arguments.flatMap Argument.vars,
      ∃ value, environment.lookup identifier = some value) :
    ∃ values, argumentValues? environment arguments = some values := by
  induction arguments with
  | nil => exact ⟨[], rfl⟩
  | cons argument arguments ih =>
    obtain ⟨values, rest⟩ := ih (fun other inside => noAnonymous other (List.mem_cons_of_mem _ inside))
      (fun identifier inside => bound identifier (List.mem_append_right _ inside))
    have first : ∃ value, argumentValue? environment argument = some value := by
      cases argument with
      | literal value => exact ⟨value, rfl⟩
      | var identifier =>
        exact bound identifier (by simp [Argument.vars])
      | anonymous => exact False.elim (noAnonymous .anonymous List.mem_cons_self rfl)
    obtain ⟨value, present⟩ := first
    exact ⟨value :: values, by simp [argumentValues?, present, rest]⟩

def head? (environment : Environment) (atom : Atom) : Option GroundFact :=
  (argumentValues? environment atom.arguments).map (GroundFact.mk atom.relation)

theorem head?_sound {environment : Environment} {atom : Atom} {fact : GroundFact}
    (checked : head? environment atom = some fact) : atom.Matches (assignment environment) fact := by
  obtain ⟨values, present, rfl⟩ := Option.map_eq_some_iff.mp checked
  exact ⟨rfl, argumentValues?_sound present⟩

theorem head?_complete (environment : Environment) (atom : Atom) (fact : GroundFact)
    (noAnonymous : ∀ argument ∈ atom.arguments, argument ≠ .anonymous)
    (matched : atom.Matches (assignment environment) fact) : head? environment atom = some fact := by
  have values := argumentValues?_complete environment atom.arguments fact.values noAnonymous matched.2
  cases fact
  simp_all [head?]
  exact matched.1

theorem head?_eq_some_iff (environment : Environment) (atom : Atom) (fact : GroundFact)
    (noAnonymous : ∀ argument ∈ atom.arguments, argument ≠ .anonymous) :
    head? environment atom = some fact ↔ atom.Matches (assignment environment) fact :=
  ⟨head?_sound, head?_complete environment atom fact noAnonymous⟩

theorem head_defined_of_join (clause : Clause) (restricted : clause.RangeRestricted)
    (known : List GroundFact) (before : Environment) {row : Row}
    (member : row ∈ join clause.positiveAtoms known before) :
    ∃ conclusion, head? row.environment clause.head = some conclusion ∧
      clause.head.Matches (assignment row.environment) conclusion := by
  obtain ⟨values, present⟩ := argumentValues?_defined row.environment clause.head.arguments
    (fun argument inside => restricted.1 argument (List.mem_append_left _ inside)) (by
      intro identifier used
      obtain ⟨argument, inside, used⟩ := List.mem_flatMap.mp used
      exact required_variable_bound clause restricted known before member
        (List.mem_flatMap.mpr ⟨argument, List.mem_append_left _ inside, used⟩))
  have checked : head? row.environment clause.head = some ⟨clause.head.relation, values⟩ := by
    simp [head?, present]
  exact ⟨_, checked, head?_sound checked⟩

#print axioms joined_body_matches
#print axioms required_variable_bound
#print axioms argumentValues?_sound
#print axioms head?_sound
#print axioms head?_eq_some_iff
#print axioms head_defined_of_join

end Mettapedia.Languages.Datalog.Grounding
