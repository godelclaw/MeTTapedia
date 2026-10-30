import Mettapedia.Languages.Datalog.StaticTyping
import Mettapedia.Languages.Datalog.GroundInstances

/-! The actual finite join preserves the clause's variable types. Consequently
its ground instruction producer preserves declared relation types, without
assuming that a successful head check retroactively types its environment. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Mettapedia.Languages.Datalog.StaticTyping

open Join Grounding

theorem empty_assignment_typed (context : VariableTypes) :
    AssignmentTyped context (assignment []) := by
  intro identifier value type found
  cases found

theorem matchArgument_typed (context : VariableTypes) {before after : Environment}
    {argument : Argument} {value : Value} {type : AttributeType}
    (beforeTyped : AssignmentTyped context (assignment before))
    (argumentTyped : ArgumentTyped context argument type) (valueTyped : ValueTyped value type)
    (checked : matchArgument before argument value = some after) :
    AssignmentTyped context (assignment after) := by
  cases argument with
  | literal expected =>
    simp only [matchArgument] at checked
    split at checked
    · cases checked; exact beforeTyped
    · cases checked
  | anonymous => cases checked; exact beforeTyped
  | var identifier =>
    cases found : before.lookup identifier with
    | none =>
      simp only [matchArgument, found] at checked
      cases checked
      intro other actual actualType present declared
      by_cases same : other = identifier
      · subst other
        have actualSame : value = actual := by simpa [assignment] using present
        have typeSame : type = actualType := Option.some.inj (argumentTyped.symm.trans declared)
        exact actualSame ▸ typeSame ▸ valueTyped
      · apply beforeTyped other actual actualType ?_ declared
        simpa only [assignment, List.lookup_cons,
          show (other == identifier) = false from beq_eq_false_iff_ne.mpr same] using present
    | some previous =>
      simp only [matchArgument, found] at checked
      split at checked
      · cases checked; exact beforeTyped
      · cases checked

theorem matchArguments_typed (context : VariableTypes) {before after : Environment}
    {arguments : List Argument} {values : List Value} {types : List AttributeType}
    (beforeTyped : AssignmentTyped context (assignment before))
    (argumentsTyped : List.Forall₂ (ArgumentTyped context) arguments types)
    (valuesTyped : List.Forall₂ ValueTyped values types)
    (checked : matchArguments before arguments values = some after) :
    AssignmentTyped context (assignment after) := by
  induction argumentsTyped generalizing before values with
  | nil =>
    cases valuesTyped
    cases checked
    exact beforeTyped
  | @cons argument type arguments types first _ ih =>
    cases valuesTyped with
    | @cons value _ values _ firstValue laterValues =>
      cases next : matchArgument before argument value with
      | none => simp [matchArguments, next] at checked
      | some middle =>
        have middleTyped := matchArgument_typed context beforeTyped first firstValue next
        apply ih middleTyped laterValues
        simpa [matchArguments, next] using checked

theorem matchAtom_typed (signature : Signature) (context : VariableTypes)
    {before after : Environment} {atom : Atom} {fact : GroundFact}
    (beforeTyped : AssignmentTyped context (assignment before))
    (atomTyped : AtomTyped signature context atom) (factTyped : FactTyped signature fact)
    (checked : matchAtom before atom fact = some after) :
    AssignmentTyped context (assignment after) := by
  obtain ⟨types, declared, argumentsTyped⟩ := atomTyped
  obtain ⟨factTypes, factDeclared, valuesTyped⟩ := factTyped
  have same := (matchAtom_sound checked).2.1
  rw [← same] at factDeclared
  have sameTypes : types = factTypes := Option.some.inj (declared.symm.trans factDeclared)
  subst factTypes
  apply matchArguments_typed context beforeTyped argumentsTyped valuesTyped
  simpa only [matchAtom, if_pos same] using checked

theorem join_typed (signature : Signature) (context : VariableTypes)
    (atoms : List Atom) (known : List GroundFact) (before : Environment)
    (beforeTyped : AssignmentTyped context (assignment before))
    (atomsTyped : ∀ atom ∈ atoms, AtomTyped signature context atom)
    (knownTyped : ∀ fact ∈ known, FactTyped signature fact)
    {row : Row} (joined : row ∈ join atoms known before) :
    AssignmentTyped context (assignment row.environment) := by
  induction atoms generalizing before row with
  | nil =>
    have same : row = ⟨before, [], []⟩ := by simpa [join] using joined
    cases same
    exact beforeTyped
  | cons atom atoms ih =>
    obtain ⟨⟨fact, position⟩, selected, published⟩ := List.mem_flatMap.mp joined
    have actual := List.mk_mem_zipIdx_iff_getElem?.mp selected
    obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp actual
    have factKnown : fact ∈ known := same ▸ List.getElem_mem bound
    cases next : matchAtom before atom fact with
    | none => simp [next] at published
    | some middle =>
      simp only [next, List.mem_map] at published
      obtain ⟨tail, included, rfl⟩ := published
      have middleTyped := matchAtom_typed signature context beforeTyped
        (atomsTyped atom List.mem_cons_self) (knownTyped fact factKnown) next
      exact ih (row := tail) middle middleTyped
        (fun other inside => atomsTyped other (List.mem_cons_of_mem _ inside)) included

theorem body_atoms_typed (signature : Signature) (context : VariableTypes) (clause : Clause)
    (typed : ClauseTyped signature context clause) :
    ∀ atom ∈ clause.positiveAtoms, AtomTyped signature context atom := by
  intro atom inside
  obtain ⟨premise, member, selected⟩ := List.mem_filterMap.mp inside
  cases premise with
  | comparison _ => cases selected
  | atom actual =>
    cases selected
    exact typed.2.2 (.atom atom) member

theorem produced_conclusion_typed (signature : Signature) (context : VariableTypes)
    (policy : Comparisons.Policy) (statementIndex : Nat) (clause : Clause)
    (clauseTyped : ClauseTyped signature context clause) (known : List GroundFact)
    (knownTyped : ∀ fact ∈ known, FactTyped signature fact) {instanceData : GroundInstances.Instance}
    (produced : instanceData ∈ GroundInstances.produce policy statementIndex clause known) :
    FactTyped signature instanceData.conclusion := by
  unfold GroundInstances.produce at produced
  split at produced
  · obtain ⟨row, joined, formed⟩ := List.mem_filterMap.mp produced
    have rowTyped := join_typed signature context clause.positiveAtoms known []
      (empty_assignment_typed context) (body_atoms_typed signature context clause clauseTyped)
      knownTyped joined
    exact matched_head_typed signature context clause clauseTyped (assignment row.environment)
      rowTyped instanceData.conclusion (head?_sound (GroundInstances.fromRow?_fields formed).2.1)
  · simp at produced

#print axioms matchAtom_typed
#print axioms join_typed
#print axioms produced_conclusion_typed

end Mettapedia.Languages.Datalog.StaticTyping
