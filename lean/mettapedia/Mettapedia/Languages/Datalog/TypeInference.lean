import Mettapedia.Languages.Datalog.StaticTyping

/-! A clause's positive relation arguments determine its variable types.
Inference retains the first declared type at each named occurrence; the
separate checker rejects inconsistent later occurrences. Range restriction
ensures that every head or guard variable has such a determining occurrence. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Mettapedia.Languages.Datalog.StaticTyping

def argumentRequirements : List Argument → List AttributeType → List (String × AttributeType)
  | .var identifier :: arguments, type :: types =>
      (identifier, type) :: argumentRequirements arguments types
  | _ :: arguments, _ :: types => argumentRequirements arguments types
  | _, _ => []

def atomRequirements (signature : Signature) (atom : Atom) : List (String × AttributeType) :=
  match signature atom.relation with
  | none => []
  | some types => argumentRequirements atom.arguments types

def clauseRequirements (signature : Signature) (clause : Clause) : List (String × AttributeType) :=
  clause.positiveAtoms.flatMap (atomRequirements signature)

def inferredContext (signature : Signature) (clause : Clause) : VariableTypes :=
  fun identifier => (clauseRequirements signature clause).lookup identifier

def inferClause (signature : Signature) (clause : Clause) : Bool :=
  checkClause signature (inferredContext signature clause) clause

private theorem argument_requirements_valid (context : VariableTypes)
    {arguments : List Argument} {types : List AttributeType}
    (typed : List.Forall₂ (ArgumentTyped context) arguments types) :
    ∀ pair ∈ argumentRequirements arguments types, context pair.1 = some pair.2 := by
  induction typed with
  | nil => simp [argumentRequirements]
  | @cons argument type arguments types first _ ih =>
    cases argument with
    | literal _ => exact ih
    | anonymous => exact ih
    | var identifier =>
      intro pair member
      rcases List.mem_cons.mp member with rfl | later
      · exact first
      · exact ih pair later

private theorem argument_requirements_cover (context : VariableTypes)
    {arguments : List Argument} {types : List AttributeType}
    (typed : List.Forall₂ (ArgumentTyped context) arguments types)
    {identifier : String} (used : identifier ∈ arguments.flatMap Argument.vars) :
    ∃ type, (identifier, type) ∈ argumentRequirements arguments types := by
  induction typed with
  | nil => simp at used
  | @cons argument type arguments types _ _ ih =>
    cases argument with
    | literal _ =>
      exact ih (by simpa [Argument.vars] using used)
    | anonymous =>
      exact ih (by simpa [Argument.vars] using used)
    | var actual =>
      rcases (show identifier = actual ∨ identifier ∈ arguments.flatMap Argument.vars by
        simpa [Argument.vars] using used) with same | later
      · subst actual
        exact ⟨type, List.mem_cons_self⟩
      · obtain ⟨other, member⟩ := ih later
        exact ⟨other, List.mem_cons_of_mem _ member⟩

private theorem atom_requirements_valid (signature : Signature) (context : VariableTypes)
    {atom : Atom} (typed : AtomTyped signature context atom) :
    ∀ pair ∈ atomRequirements signature atom, context pair.1 = some pair.2 := by
  obtain ⟨types, declared, argumentsTyped⟩ := typed
  simpa only [atomRequirements, declared] using argument_requirements_valid context argumentsTyped

private theorem atom_requirements_cover (signature : Signature) (context : VariableTypes)
    {atom : Atom} (typed : AtomTyped signature context atom) {identifier : String}
    (used : identifier ∈ atom.variables) :
    ∃ type, (identifier, type) ∈ atomRequirements signature atom := by
  obtain ⟨types, declared, argumentsTyped⟩ := typed
  simpa only [atomRequirements, declared] using argument_requirements_cover context argumentsTyped used

private theorem lookup_valid (context : VariableTypes) (requirements : List (String × AttributeType))
    (valid : ∀ pair ∈ requirements, context pair.1 = some pair.2)
    {identifier : String} {type : AttributeType} (found : requirements.lookup identifier = some type) :
    context identifier = some type := by
  induction requirements with
  | nil => cases found
  | cons pair requirements ih =>
    rcases pair with ⟨name, declaredType⟩
    by_cases same : identifier = name
    · subst name
      have typeSame : declaredType = type := by simpa using found
      exact typeSame ▸ valid (identifier, declaredType) List.mem_cons_self
    · exact ih (fun other inside => valid other (List.mem_cons_of_mem _ inside))
        (by simpa only [List.lookup_cons,
          show (identifier == name) = false from beq_eq_false_iff_ne.mpr same] using found)

private theorem lookup_present (requirements : List (String × AttributeType))
    {identifier : String} {type : AttributeType} (member : (identifier, type) ∈ requirements) :
    ∃ actual, requirements.lookup identifier = some actual := by
  induction requirements with
  | nil => simp at member
  | cons pair requirements ih =>
    rcases pair with ⟨name, declaredType⟩
    by_cases same : identifier = name
    · subst name
      exact ⟨declaredType, by simp⟩
    · have later : (identifier, type) ∈ requirements := by
        rcases List.mem_cons.mp member with first | later
        · exact False.elim (same (congrArg Prod.fst first))
        · exact later
      obtain ⟨actual, found⟩ := ih later
      exact ⟨actual, by simpa only [List.lookup_cons,
        show (identifier == name) = false from beq_eq_false_iff_ne.mpr same] using found⟩

theorem inferred_context_agrees (signature : Signature) (context : VariableTypes) (clause : Clause)
    (typed : ClauseTyped signature context clause) :
    ∀ identifier ∈ clause.providedVariables,
      inferredContext signature clause identifier = context identifier := by
  have bodyTyped : ∀ atom ∈ clause.positiveAtoms, AtomTyped signature context atom := by
    intro atom inside
    obtain ⟨premise, present, selected⟩ := List.mem_filterMap.mp inside
    cases premise with
    | comparison _ => cases selected
    | atom actual => cases selected; exact typed.2.2 (.atom atom) present
  have valid : ∀ pair ∈ clauseRequirements signature clause, context pair.1 = some pair.2 := by
    intro pair inside
    obtain ⟨atom, present, selected⟩ := List.mem_flatMap.mp inside
    exact atom_requirements_valid signature context (bodyTyped atom present) pair selected
  intro identifier used
  obtain ⟨atom, present, variableUsed⟩ := List.mem_flatMap.mp used
  obtain ⟨type, member⟩ := atom_requirements_cover signature context (bodyTyped atom present) variableUsed
  obtain ⟨actual, found⟩ := lookup_present (clauseRequirements signature clause)
    (List.mem_flatMap.mpr ⟨atom, present, member⟩)
  exact found.trans (lookup_valid context _ valid found).symm

private theorem argument_typed_transport (before after : VariableTypes) (argument : Argument)
    (type : AttributeType) (same : ∀ identifier ∈ argument.vars, after identifier = before identifier)
    (typed : ArgumentTyped before argument type) : ArgumentTyped after argument type := by
  cases argument with
  | literal _ => exact typed
  | anonymous => trivial
  | var identifier => exact (same identifier (by simp [Argument.vars])).trans typed

private theorem arguments_typed_transport (before after : VariableTypes)
    {arguments : List Argument} {types : List AttributeType}
    (same : ∀ identifier ∈ arguments.flatMap Argument.vars, after identifier = before identifier)
    (typed : List.Forall₂ (ArgumentTyped before) arguments types) :
    List.Forall₂ (ArgumentTyped after) arguments types := by
  induction typed with
  | nil => exact .nil
  | @cons argument type arguments types first _ ih =>
    exact .cons (argument_typed_transport before after argument type
      (fun identifier inside => same identifier (List.mem_append_left _ inside)) first)
      (ih (fun identifier inside => same identifier (List.mem_append_right _ inside)))

private theorem atom_typed_transport (signature : Signature) (before after : VariableTypes) (atom : Atom)
    (same : ∀ identifier ∈ atom.variables, after identifier = before identifier)
    (typed : AtomTyped signature before atom) : AtomTyped signature after atom := by
  obtain ⟨types, declared, argumentsTyped⟩ := typed
  exact ⟨types, declared, arguments_typed_transport before after same argumentsTyped⟩

theorem inferred_clause_typed (signature : Signature) (context : VariableTypes) (clause : Clause)
    (typed : ClauseTyped signature context clause) :
    ClauseTyped signature (inferredContext signature clause) clause := by
  have agreement := inferred_context_agrees signature context clause typed
  have required : ∀ argument ∈ clause.requiredArguments, ∀ identifier ∈ argument.vars,
      inferredContext signature clause identifier = context identifier := by
    intro argument inside identifier used
    exact agreement identifier (typed.1.2 identifier (List.mem_flatMap.mpr ⟨argument, inside, used⟩))
  refine ⟨typed.1, atom_typed_transport signature context _ clause.head ?_ typed.2.1, ?_⟩
  · intro identifier used
    obtain ⟨argument, inside, variableUsed⟩ := List.mem_flatMap.mp used
    exact required argument (List.mem_append_left _ inside) identifier variableUsed
  · intro premise member
    cases premise with
    | atom atom =>
      apply atom_typed_transport signature context _ atom ?_ (typed.2.2 (.atom atom) member)
      intro identifier used
      exact agreement identifier (List.mem_flatMap.mpr
        ⟨atom, List.mem_filterMap.mpr ⟨.atom atom, member, rfl⟩, used⟩)
    | comparison comparison =>
      obtain ⟨leftNamed, rightNamed, type, leftTyped, rightTyped⟩ :=
        typed.2.2 (.comparison comparison) member
      have requiredComparison : ∀ argument ∈ comparison.arguments, argument ∈ clause.requiredArguments := by
        intro argument inside
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨.comparison comparison, member, inside⟩)
      exact ⟨leftNamed, rightNamed, type,
        argument_typed_transport context _ comparison.left type
          (required comparison.left (requiredComparison comparison.left (by simp [Comparison.arguments]))) leftTyped,
        argument_typed_transport context _ comparison.right type
          (required comparison.right (requiredComparison comparison.right (by simp [Comparison.arguments]))) rightTyped⟩

/-- Inference is exact for the independently specified clause typing judgment.
No search over candidate type assignments is used. -/
theorem inferClause_iff (signature : Signature) (clause : Clause) :
    inferClause signature clause = true ↔ ∃ context, ClauseTyped signature context clause := by
  constructor
  · intro checked
    exact ⟨inferredContext signature clause, (checkClause_iff _ _ _).mp checked⟩
  · rintro ⟨context, typed⟩
    exact (checkClause_iff _ _ _).mpr (inferred_clause_typed signature context clause typed)

#print axioms inferred_context_agrees
#print axioms inferred_clause_typed
#print axioms inferClause_iff

end Mettapedia.Languages.Datalog.StaticTyping
