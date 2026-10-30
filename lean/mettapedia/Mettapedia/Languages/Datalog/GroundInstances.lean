import Mettapedia.Languages.Datalog.Comparisons
import Mettapedia.Languages.Datalog.DerivationIdentity

/-! Clause-authorized ground instructions. A rule identifier alone does not
authorize an arbitrary conclusion: the join, guards, head and canonical
grounding projection must all agree with the source clause. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.Datalog.GroundInstances

open Join Grounding DerivationIdentity

structure Instance where
  key : DerivationKey
  conclusion : GroundFact
  rowPositions : List Nat
  deriving Repr, DecidableEq

def fromRow? (policy : Comparisons.Policy) (statementIndex : Nat) (clause : Clause) (row : Row) :
    Option Instance := do
  if Comparisons.all? policy row.environment (Comparisons.guards clause) != some true then none
  else
    let conclusion ← head? row.environment clause.head
    let key ← key? statementIndex clause row
    pure ⟨key, conclusion, row.rowPositions⟩

def produce (policy : Comparisons.Policy) (statementIndex : Nat) (clause : Clause)
    (known : List GroundFact) : List Instance :=
  if clause.checkRangeRestriction then
    (join clause.positiveAtoms known []).filterMap (fromRow? policy statementIndex clause)
  else []

/-- Source meaning uses matching and the declared primitive relations,
independently of join enumeration and head/key construction. -/
def Authorized (policy : Comparisons.Policy) (statementIndex : Nat) (clause : Clause)
    (known : List GroundFact) (instanceData : Instance) : Prop :=
  clause.RangeRestricted ∧ instanceData.key.statementIndex = statementIndex ∧
    ∃ model : Assignment,
      clause.head.Matches model instanceData.conclusion ∧
      List.Forall₂ (Atom.Matches model) clause.positiveAtoms instanceData.key.positivePremises ∧
      (∀ fact ∈ instanceData.key.positivePremises, fact ∈ known) ∧
      (∀ comparison ∈ Comparisons.guards clause, Comparisons.Holds policy model comparison) ∧
      instanceData.key.grounding.map Prod.fst = clauseVariables clause ∧
      ∀ pair ∈ instanceData.key.grounding, model pair.1 = some pair.2

theorem fromRow?_fields {policy : Comparisons.Policy} {statementIndex : Nat} {clause : Clause}
    {row : Row} {instanceData : Instance}
    (checked : fromRow? policy statementIndex clause row = some instanceData) :
    Comparisons.all? policy row.environment (Comparisons.guards clause) = some true ∧
      head? row.environment clause.head = some instanceData.conclusion ∧
      key? statementIndex clause row = some instanceData.key ∧
      instanceData.rowPositions = row.rowPositions := by
  unfold fromRow? at checked
  split at checked
  · cases checked
  · rename_i guard
    have guards : Comparisons.all? policy row.environment (Comparisons.guards clause) = some true := by
      simpa using guard
    cases headFound : head? row.environment clause.head with
    | none => simp [headFound] at checked
    | some conclusion =>
      cases keyFound : key? statementIndex clause row with
      | none => simp [headFound, keyFound] at checked
      | some key =>
        simp only [headFound, keyFound] at checked
        change some (Instance.mk key conclusion row.rowPositions) = some instanceData at checked
        cases checked
        exact ⟨guards, rfl, rfl, rfl⟩

private theorem fact_member_of_positions {known facts : List GroundFact} {positions : List Nat}
    (related : List.Forall₂ (fun fact position => known[position]? = some fact) facts positions) :
    ∀ fact ∈ facts, fact ∈ known := by
  induction related with
  | nil => simp
  | @cons fact position facts positions first _ ih =>
    intro other member
    rcases List.mem_cons.mp member with rfl | later
    · obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp first
      exact same ▸ List.getElem_mem bound
    · exact ih other later

theorem produce_sound (policy : Comparisons.Policy) (statementIndex : Nat) (clause : Clause)
    (known : List GroundFact) {instanceData : Instance}
    (member : instanceData ∈ produce policy statementIndex clause known) :
    Authorized policy statementIndex clause known instanceData ∧
      List.Forall₂ (fun fact position => known[position]? = some fact)
        instanceData.key.positivePremises instanceData.rowPositions := by
  unfold produce at member
  split at member
  · rename_i checked
    have restricted := (Clause.checkRangeRestriction_iff clause).mp checked
    obtain ⟨row, joined, formed⟩ := List.mem_filterMap.mp member
    obtain ⟨guards, headFound, keyFound, positions⟩ := fromRow?_fields formed
    obtain ⟨_, matched, selected⟩ := join_sound _ _ _ joined
    obtain ⟨ordinal, facts, names, values⟩ := key_fields keyFound
    have guardMeaning : ∀ comparison ∈ Comparisons.guards clause,
        Comparisons.Holds policy (assignment row.environment) comparison := by
      apply (Comparisons.all?_eq_some_true_iff policy row.environment (Comparisons.guards clause) ?_).mp guards
      intro comparison inside
      constructor
      · exact restricted.1 comparison.left
          (Comparisons.guard_arguments_required inside (by simp [Comparison.arguments]))
      · exact restricted.1 comparison.right
          (Comparisons.guard_arguments_required inside (by simp [Comparison.arguments]))
    have positionMeaning : List.Forall₂ (fun fact position => known[position]? = some fact)
        instanceData.key.positivePremises instanceData.rowPositions := by
      simpa only [facts, positions] using selected
    refine ⟨⟨restricted, ordinal, assignment row.environment, head?_sound headFound, ?_,
      fact_member_of_positions positionMeaning, guardMeaning, names, values⟩, positionMeaning⟩
    simpa only [facts] using matched
  · simp at member

theorem invalid_range_refused (policy : Comparisons.Policy) (statementIndex : Nat)
    (clause : Clause) (known : List GroundFact) (invalid : ¬clause.RangeRestricted) :
    produce policy statementIndex clause known = [] := by
  have failed : clause.checkRangeRestriction = false := by
    cases checked : clause.checkRangeRestriction with
    | false => rfl
    | true => exact False.elim (invalid ((Clause.checkRangeRestriction_iff clause).mp checked))
  simp [produce, failed]

#print axioms fromRow?_fields
#print axioms produce_sound
#print axioms invalid_range_refused

end Mettapedia.Languages.Datalog.GroundInstances
