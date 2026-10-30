import Mettapedia.Languages.Datalog.GroundInstances

/-! Ground instruction coverage is stated at logical firing identity.
Validation positions are supplied by the actual finite snapshot join. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.Datalog.GroundInstances

open Join Grounding DerivationIdentity

private theorem argument_back {environment : Environment} {model : Assignment}
    (agrees : Agrees environment model) (argument : Argument) (value : Value)
    (bound : ∀ identifier ∈ argument.vars, ∃ actual, environment.lookup identifier = some actual)
    (matched : argument.Matches model value) : argument.Matches (assignment environment) value := by
  cases argument with
  | literal _ => exact matched
  | anonymous => trivial
  | var identifier =>
    obtain ⟨actual, found⟩ := bound identifier (by simp [Argument.vars])
    have same : actual = value := Option.some.inj ((agrees identifier actual found).symm.trans matched)
    exact same ▸ found

private theorem arguments_back {environment : Environment} {model : Assignment}
    (agrees : Agrees environment model) (arguments : List Argument) (values : List Value)
    (bound : ∀ identifier ∈ arguments.flatMap Argument.vars,
      ∃ actual, environment.lookup identifier = some actual)
    (matched : List.Forall₂ (Argument.Matches model) arguments values) :
    List.Forall₂ (Argument.Matches (assignment environment)) arguments values := by
  induction matched with
  | nil => exact .nil
  | @cons argument value arguments values first _ ih =>
    refine .cons (argument_back agrees argument value ?_ first) (ih ?_)
    · intro identifier inside
      exact bound identifier (List.mem_append_left _ inside)
    · intro identifier inside
      exact bound identifier (List.mem_append_right _ inside)

theorem produce_complete (policy : Comparisons.Policy) (statementIndex : Nat) (clause : Clause)
    (known : List GroundFact) (wanted : Instance)
    (authorized : Authorized policy statementIndex clause known wanted) :
    ∃ emitted ∈ produce policy statementIndex clause known,
      emitted.key = wanted.key ∧ emitted.conclusion = wanted.conclusion := by
  obtain ⟨restricted, ordinal, model, headMatches, bodyMatches, available, guardMeaning, names, values⟩ := authorized
  obtain ⟨row, joined, sameFacts, agrees⟩ := join_complete clause.positiveAtoms known
    wanted.key.positivePremises [] model (by intro identifier value found; cases found)
    available bodyMatches
  have requiredBound : ∀ argument ∈ clause.requiredArguments,
      ∀ identifier ∈ argument.vars, ∃ actual, row.environment.lookup identifier = some actual := by
    intro argument inside identifier used
    exact required_variable_bound clause restricted known [] joined
      (List.mem_flatMap.mpr ⟨argument, inside, used⟩)
  have headRow : clause.head.Matches (assignment row.environment) wanted.conclusion := by
    refine ⟨headMatches.1, arguments_back agrees clause.head.arguments wanted.conclusion.values ?_ headMatches.2⟩
    intro identifier used
    obtain ⟨argument, inside, present⟩ := List.mem_flatMap.mp used
    exact requiredBound argument (List.mem_append_left _ inside) identifier present
  have headFound : head? row.environment clause.head = some wanted.conclusion :=
    head?_complete row.environment clause.head wanted.conclusion
      (fun argument inside => restricted.1 argument (List.mem_append_left _ inside)) headRow
  have projected : readback row.environment (clauseVariables clause) = some wanted.key.grounding := by
    apply readback_complete row.environment (clauseVariables clause) wanted.key.grounding names
    intro pair inside
    apply argument_back agrees (.var pair.1) pair.2 ?_ (values pair inside)
    intro identifier used
    have same : identifier = pair.1 := by simpa [Argument.vars] using used
    subst identifier
    have named : pair.1 ∈ clauseVariables clause := names ▸ List.mem_map.mpr ⟨pair, inside, rfl⟩
    exact provided_variable_bound clause known [] joined (by simpa [clauseVariables] using named)
  have keyFound : key? statementIndex clause row = some wanted.key := by
    simp only [key?, projected, Option.map_some]
    have same : DerivationKey.mk statementIndex wanted.key.grounding row.facts = wanted.key := by
      cases wanted with
      | mk key conclusion positions =>
        cases key
        simp_all
    exact congrArg some same
  have guardRow : ∀ comparison ∈ Comparisons.guards clause,
      Comparisons.Holds policy (assignment row.environment) comparison := by
    intro comparison inside
    obtain ⟨left, right, first, second, holds⟩ := guardMeaning comparison inside
    refine ⟨left, right, argument_back agrees comparison.left left ?_ first,
      argument_back agrees comparison.right right ?_ second, holds⟩
    · exact requiredBound comparison.left
        (Comparisons.guard_arguments_required inside (by simp [Comparison.arguments]))
    · exact requiredBound comparison.right
        (Comparisons.guard_arguments_required inside (by simp [Comparison.arguments]))
  have guards : Comparisons.all? policy row.environment (Comparisons.guards clause) = some true := by
    apply (Comparisons.all?_eq_some_true_iff policy row.environment (Comparisons.guards clause) ?_).mpr guardRow
    intro comparison inside
    exact ⟨restricted.1 comparison.left
        (Comparisons.guard_arguments_required inside (by simp [Comparison.arguments])),
      restricted.1 comparison.right
        (Comparisons.guard_arguments_required inside (by simp [Comparison.arguments]))⟩
  let emitted : Instance := ⟨wanted.key, wanted.conclusion, row.rowPositions⟩
  refine ⟨emitted, ?_, rfl, rfl⟩
  unfold produce
  rw [if_pos ((Clause.checkRangeRestriction_iff clause).mpr restricted)]
  refine List.mem_filterMap.mpr ⟨row, joined, ?_⟩
  simp [fromRow?, guards, headFound, keyFound, emitted]

#print axioms produce_complete

end Mettapedia.Languages.Datalog.GroundInstances
