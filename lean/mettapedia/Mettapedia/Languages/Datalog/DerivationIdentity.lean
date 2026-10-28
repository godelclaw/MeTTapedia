import Mettapedia.Languages.Datalog.Grounding

/-! Logical firing identity projects a joined row onto the clause's named
variables in first-occurrence order. Validation positions stay in the row.
The positional grounding representation is indexed by this clause context. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.Datalog.DerivationIdentity

open Join Grounding

def clauseVariables (clause : Clause) : List String := clause.providedVariables.eraseDups

def readback (environment : Environment) : List String → Option (List (String × Value))
  | [] => some []
  | identifier :: identifiers => do
      let value ← environment.lookup identifier
      let rest ← readback environment identifiers
      pure ((identifier, value) :: rest)

theorem provided_variable_bound (clause : Clause) (known : List GroundFact) (before : Environment)
    {row : Row} (member : row ∈ join clause.positiveAtoms known before) {identifier : String}
    (used : identifier ∈ clause.providedVariables) :
    ∃ value, row.environment.lookup identifier = some value := by
  obtain ⟨atom, inside, used⟩ := List.mem_flatMap.mp used
  obtain ⟨fact, _, matched⟩ := joined_body_matches clause known before member atom inside
  obtain ⟨value, _, bound⟩ := Atom.variable_has_matching_value matched used
  exact ⟨value, bound⟩

theorem readback_defined (environment : Environment) (identifiers : List String)
    (bound : ∀ identifier ∈ identifiers, ∃ value, environment.lookup identifier = some value) :
    ∃ result, readback environment identifiers = some result := by
  induction identifiers with
  | nil => exact ⟨[], rfl⟩
  | cons identifier identifiers ih =>
    obtain ⟨value, first⟩ := bound identifier List.mem_cons_self
    obtain ⟨rest, later⟩ := ih (fun other inside => bound other (List.mem_cons_of_mem _ inside))
    exact ⟨(identifier, value) :: rest, by simp [readback, first, later]⟩

theorem readback_names {environment : Environment} {identifiers : List String}
    {result : List (String × Value)} (checked : readback environment identifiers = some result) :
    result.map Prod.fst = identifiers := by
  induction identifiers generalizing result with
  | nil => cases checked; rfl
  | cons identifier identifiers ih =>
    cases first : environment.lookup identifier with
    | none => simp [readback, first] at checked
    | some value =>
      cases later : readback environment identifiers with
      | none => simp [readback, first, later] at checked
      | some rest =>
        simp only [readback, first, later] at checked
        change some ((identifier, value) :: rest) = some result at checked
        cases checked
        exact congrArg (identifier :: ·) (ih later)

theorem readback_values {environment : Environment} {identifiers : List String}
    {result : List (String × Value)} (checked : readback environment identifiers = some result) :
    ∀ pair ∈ result, environment.lookup pair.1 = some pair.2 := by
  induction identifiers generalizing result with
  | nil => cases checked; simp
  | cons identifier identifiers ih =>
    cases first : environment.lookup identifier with
    | none => simp [readback, first] at checked
    | some value =>
      cases later : readback environment identifiers with
      | none => simp [readback, first, later] at checked
      | some rest =>
        simp only [readback, first, later] at checked
        change some ((identifier, value) :: rest) = some result at checked
        cases checked
        intro pair inside
        rcases List.mem_cons.mp inside with rfl | remaining
        · exact first
        · exact ih later pair remaining

theorem readback_congr (first second : Environment) (identifiers : List String)
    (same : ∀ identifier ∈ identifiers, first.lookup identifier = second.lookup identifier) :
    readback first identifiers = readback second identifiers := by
  induction identifiers with
  | nil => rfl
  | cons identifier identifiers ih =>
    simp only [readback, same identifier List.mem_cons_self,
      ih (fun other inside => same other (List.mem_cons_of_mem _ inside))]

theorem readback_complete (environment : Environment) (identifiers : List String)
    (result : List (String × Value)) (names : result.map Prod.fst = identifiers)
    (values : ∀ pair ∈ result, environment.lookup pair.1 = some pair.2) :
    readback environment identifiers = some result := by
  rw [← names]
  clear names identifiers
  induction result with
  | nil => rfl
  | cons pair rest ih =>
    have first := values pair List.mem_cons_self
    have later := ih (fun other inside => values other (List.mem_cons_of_mem _ inside))
    rcases pair with ⟨identifier, value⟩
    simp [readback, first, later]

def key? (statementIndex : Nat) (clause : Clause) (row : Row) : Option DerivationKey :=
  (readback row.environment (clauseVariables clause)).map fun grounding =>
    ⟨statementIndex, grounding, row.facts⟩

theorem joined_key_defined (statementIndex : Nat) (clause : Clause) (known : List GroundFact)
    (before : Environment) {row : Row} (member : row ∈ join clause.positiveAtoms known before) :
    ∃ key, key? statementIndex clause row = some key := by
  obtain ⟨grounding, present⟩ := readback_defined row.environment (clauseVariables clause) (by
    intro identifier used
    exact provided_variable_bound clause known before member (by simpa [clauseVariables] using used))
  exact ⟨⟨statementIndex, grounding, row.facts⟩, by simp [key?, present]⟩

theorem key_fields {statementIndex : Nat} {clause : Clause} {row : Row} {key : DerivationKey}
    (checked : key? statementIndex clause row = some key) :
    key.statementIndex = statementIndex ∧ key.positivePremises = row.facts ∧
      key.grounding.map Prod.fst = clauseVariables clause ∧
      ∀ pair ∈ key.grounding, row.environment.lookup pair.1 = some pair.2 := by
  obtain ⟨grounding, present, rfl⟩ := Option.map_eq_some_iff.mp checked
  exact ⟨rfl, rfl, readback_names present, readback_values present⟩

theorem validation_positions_do_not_change_key (statementIndex : Nat) (clause : Clause)
    (row : Row) (positions : List Nat) :
    key? statementIndex clause {row with rowPositions := positions} = key? statementIndex clause row := rfl

theorem key_congr (statementIndex : Nat) (clause : Clause) (first second : Row)
    (facts : first.facts = second.facts)
    (bindings : ∀ identifier ∈ clauseVariables clause,
      first.environment.lookup identifier = second.environment.lookup identifier) :
    key? statementIndex clause first = key? statementIndex clause second := by
  simp only [key?, readback_congr first.environment second.environment (clauseVariables clause) bindings, facts]

/-- Decode positional values using the actual clause variable context. A
wrong-length tuple is refused, including trailing or missing values. -/
def decodeGrounding? (clause : Clause) (values : List Value) : Option (List (String × Value)) :=
  if (clauseVariables clause).length = values.length then some ((clauseVariables clause).zip values) else none

theorem positional_readback {environment : Environment} {clause : Clause} {grounding : List (String × Value)}
    (checked : readback environment (clauseVariables clause) = some grounding) :
    decodeGrounding? clause (grounding.map Prod.snd) = some grounding := by
  have names := readback_names checked
  have length : (clauseVariables clause).length = (grounding.map Prod.snd).length := by
    rw [← names]
    simp
  simp only [decodeGrounding?, if_pos length]
  rw [← names]
  congr 1
  clear checked names length
  induction grounding with
  | nil => rfl
  | cons pair rest ih => simpa using congrArg (pair :: ·) ih

#print axioms joined_key_defined
#print axioms key_fields
#print axioms key_congr
#print axioms positional_readback

end Mettapedia.Languages.Datalog.DerivationIdentity
