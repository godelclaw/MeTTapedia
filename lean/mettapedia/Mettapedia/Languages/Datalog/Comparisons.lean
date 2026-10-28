import Mettapedia.Languages.Datalog.Grounding

/-! Guard evaluation is relative to a declared comparison interpretation.
The operator family supplies its independent relation and an exact checker.
Missing operands are distinct from a refuted guard. Concrete native numeric
profiles require their own correspondence before execution admission. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.Datalog.Comparisons

open Join Grounding

structure Policy where
  Holds : ComparisonOperator → Value → Value → Prop
  check : ComparisonOperator → Value → Value → Bool
  exact : ∀ operator left right, check operator left right = true ↔ Holds operator left right

def Holds (policy : Policy) (model : Assignment) (comparison : Comparison) : Prop :=
  ∃ left right, comparison.left.Matches model left ∧ comparison.right.Matches model right ∧
    policy.Holds comparison.operator left right

def eval? (policy : Policy) (environment : Environment) (comparison : Comparison) : Option Bool := do
  let left ← argumentValue? environment comparison.left
  let right ← argumentValue? environment comparison.right
  pure (policy.check comparison.operator left right)

theorem eval?_sound (policy : Policy) {environment : Environment} {comparison : Comparison}
    (checked : eval? policy environment comparison = some true) :
    Holds policy (assignment environment) comparison := by
  cases leftFound : argumentValue? environment comparison.left with
  | none => simp [eval?, leftFound] at checked
  | some left =>
    cases rightFound : argumentValue? environment comparison.right with
    | none => simp [eval?, leftFound, rightFound] at checked
    | some right =>
      have succeeds : policy.check comparison.operator left right = true := by
        simpa [eval?, leftFound, rightFound] using checked
      exact ⟨left, right, argumentValue?_matches leftFound, argumentValue?_matches rightFound,
        (policy.exact _ _ _).mp succeeds⟩

private theorem argument_complete (environment : Environment) (argument : Argument) (value : Value)
    (notAnonymous : argument ≠ .anonymous) (matched : argument.Matches (assignment environment) value) :
    argumentValue? environment argument = some value := by
  cases argument with
  | literal expected => exact congrArg some matched
  | var _ => exact matched
  | anonymous => exact False.elim (notAnonymous rfl)

theorem eval?_complete (policy : Policy) (environment : Environment) (comparison : Comparison)
    (leftNamed : comparison.left ≠ .anonymous) (rightNamed : comparison.right ≠ .anonymous)
    (holds : Holds policy (assignment environment) comparison) :
    eval? policy environment comparison = some true := by
  obtain ⟨left, right, leftMatches, rightMatches, relation⟩ := holds
  have leftFound := argument_complete environment comparison.left left leftNamed leftMatches
  have rightFound := argument_complete environment comparison.right right rightNamed rightMatches
  simp [eval?, leftFound, rightFound, (policy.exact _ _ _).mpr relation]

theorem eval?_eq_some_true_iff (policy : Policy) (environment : Environment) (comparison : Comparison)
    (leftNamed : comparison.left ≠ .anonymous) (rightNamed : comparison.right ≠ .anonymous) :
    eval? policy environment comparison = some true ↔ Holds policy (assignment environment) comparison :=
  ⟨eval?_sound policy, eval?_complete policy environment comparison leftNamed rightNamed⟩

def guards (clause : Clause) : List Comparison :=
  clause.body.filterMap fun premise => match premise with
    | .comparison comparison => some comparison
    | _ => none

theorem guard_arguments_required {clause : Clause} {comparison : Comparison}
    (member : comparison ∈ guards clause) {argument : Argument} (inside : argument ∈ comparison.arguments) :
    argument ∈ clause.requiredArguments := by
  obtain ⟨premise, present, selected⟩ := List.mem_filterMap.mp member
  cases premise with
  | atom _ => cases selected
  | comparison actual =>
    cases selected
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨.comparison comparison, present, inside⟩

theorem operands_defined_of_join (clause : Clause) (restricted : clause.RangeRestricted)
    (known : List GroundFact) (before : Environment) {row : Row}
    (joined : row ∈ join clause.positiveAtoms known before) {comparison : Comparison}
    (member : comparison ∈ guards clause) :
    ∃ left right, argumentValue? row.environment comparison.left = some left ∧
      argumentValue? row.environment comparison.right = some right := by
  have defined : ∀ argument ∈ comparison.arguments, ∃ value,
      argumentValue? row.environment argument = some value := by
    intro argument inside
    have required := guard_arguments_required member inside
    cases argument with
    | literal value => exact ⟨value, rfl⟩
    | var identifier =>
      exact required_variable_bound clause restricted known before joined
        (List.mem_flatMap.mpr ⟨.var identifier, required, by simp [Argument.vars]⟩)
    | anonymous => exact False.elim (restricted.1 .anonymous required rfl)
  obtain ⟨left, first⟩ := defined comparison.left (by simp [Comparison.arguments])
  obtain ⟨right, second⟩ := defined comparison.right (by simp [Comparison.arguments])
  exact ⟨left, right, first, second⟩

theorem eval?_defined_of_join (policy : Policy) (clause : Clause) (restricted : clause.RangeRestricted)
    (known : List GroundFact) (before : Environment) {row : Row}
    (joined : row ∈ join clause.positiveAtoms known before) {comparison : Comparison}
    (member : comparison ∈ guards clause) :
    ∃ verdict, eval? policy row.environment comparison = some verdict := by
  obtain ⟨left, right, first, second⟩ := operands_defined_of_join clause restricted known before joined member
  exact ⟨policy.check comparison.operator left right, by simp [eval?, first, second]⟩

def all? (policy : Policy) (environment : Environment) : List Comparison → Option Bool
  | [] => some true
  | comparison :: comparisons => do
      let first ← eval? policy environment comparison
      let rest ← all? policy environment comparisons
      pure (first && rest)

theorem all?_eq_some_true_iff (policy : Policy) (environment : Environment) (comparisons : List Comparison)
    (noAnonymous : ∀ comparison ∈ comparisons,
      comparison.left ≠ .anonymous ∧ comparison.right ≠ .anonymous) :
    all? policy environment comparisons = some true ↔
      ∀ comparison ∈ comparisons, Holds policy (assignment environment) comparison := by
  induction comparisons with
  | nil => simp [all?]
  | cons comparison comparisons ih =>
    have first := eval?_eq_some_true_iff policy environment comparison
      (noAnonymous comparison List.mem_cons_self).1 (noAnonymous comparison List.mem_cons_self).2
    have rest := ih (fun other inside => noAnonymous other (List.mem_cons_of_mem _ inside))
    constructor
    · intro checked
      cases found : eval? policy environment comparison with
      | none => simp [all?, found] at checked
      | some verdict =>
        cases later : all? policy environment comparisons with
        | none => simp [all?, found, later] at checked
        | some remaining =>
          have both : verdict = true ∧ remaining = true := by
            simpa [all?, found, later] using checked
          intro other inside
          rcases List.mem_cons.mp inside with rfl | inside
          · exact first.mp (both.1 ▸ found)
          · exact rest.mp (both.2 ▸ later) other inside
    · intro held
      have firstTrue := first.mpr (held comparison List.mem_cons_self)
      have restTrue := rest.mpr (fun other inside => held other (List.mem_cons_of_mem _ inside))
      simp [all?, firstTrue, restTrue]

#print axioms eval?_eq_some_true_iff
#print axioms eval?_defined_of_join
#print axioms all?_eq_some_true_iff

end Mettapedia.Languages.Datalog.Comparisons
