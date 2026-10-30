import Mettapedia.Languages.Datalog.ClosureSemantics
import Mathlib.Data.Finset.Card

/-! A finite fact universe derived from the actual program and input.
Head literals and input values bound the active domain; source head shapes
bound relation names and tuple lengths. The universe is used for a proof
bound, not as the grounding algorithm's enumeration strategy. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Mettapedia.Languages.Datalog.Closure

open GroundInstances

def headLiterals (clause : Clause) : List Value :=
  clause.head.arguments.filterMap fun argument => match argument with
    | .literal value => some value
    | _ => none

def activeDomain (program : Program) (seeds : List GroundFact) : List Value :=
  (seeds.flatMap GroundFact.values ++
    (LPBridge.numberedClauses program).flatMap (fun pair => headLiterals pair.2)).eraseDups

def tuples (domain : List Value) : Nat → List (List Value)
  | 0 => [[]]
  | arity + 1 => domain.flatMap fun value => (tuples domain arity).map (value :: ·)

theorem mem_tuples_iff (domain : List Value) (arity : Nat) (values : List Value) :
    values ∈ tuples domain arity ↔ values.length = arity ∧ ∀ value ∈ values, value ∈ domain := by
  induction arity generalizing values with
  | zero =>
    cases values <;> simp [tuples]
  | succ arity ih =>
    cases values with
    | nil => simp [tuples]
    | cons value values =>
      simp only [tuples, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨first, firstIn, rest, restIn, same⟩
        cases same
        obtain ⟨length, inside⟩ := (ih values).mp restIn
        exact ⟨congrArg Nat.succ length,
          fun other member => (List.mem_cons.mp member).elim (fun same => same ▸ firstIn) (inside other)⟩
      · rintro ⟨length, inside⟩
        refine ⟨value, inside value List.mem_cons_self, values, ?_, rfl⟩
        exact (ih values).mpr ⟨Nat.succ.inj length,
          fun other member => inside other (List.mem_cons_of_mem _ member)⟩

def factUniverse (program : Program) (seeds : List GroundFact) : Finset GroundFact :=
  (seeds ++ (LPBridge.numberedClauses program).flatMap fun pair =>
    (tuples (activeDomain program seeds) pair.2.head.arguments.length).map fun values =>
      (⟨pair.2.head.relation, values⟩ : GroundFact)).toFinset

private theorem forall₂_member {Left Right : Type} {relation : Left → Right → Prop}
    {left : List Left} {right : List Right} (related : List.Forall₂ relation left right)
    {item : Left} (inside : item ∈ left) : ∃ value ∈ right, relation item value := by
  induction related with
  | nil => cases inside
  | @cons first second rest values head _ ih =>
    rcases List.mem_cons.mp inside with rfl | inside
    · exact ⟨second, List.mem_cons_self, head⟩
    · obtain ⟨value, member, relatedValue⟩ := ih inside
      exact ⟨value, List.mem_cons_of_mem _ member, relatedValue⟩

theorem head_literals_in_domain (program : Program) (seeds : List GroundFact)
    {statementIndex : Nat} {clause : Clause}
    (source : ProgramGrounding.ClauseAt program statementIndex clause)
    (value : Value) (literal : Argument.literal value ∈ clause.head.arguments) :
    value ∈ activeDomain program seeds := by
  apply List.mem_eraseDups.mpr
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨(statementIndex, clause), (ProgramGrounding.clauseAt_iff_numbered _ _ _).mp source, ?_⟩
  exact List.mem_filterMap.mpr ⟨.literal value, literal, rfl⟩

theorem derives_values_in_domain (policy : Comparisons.Policy) (program : Program)
    (seeds : List GroundFact) {fact : GroundFact} (derived : Derives policy program seeds fact) :
    ∀ value ∈ fact.values, value ∈ activeDomain program seeds := by
  induction derived with
  | seed member =>
    intro value inside
    exact List.mem_eraseDups.mpr (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨_, member, inside⟩))
  | fire row authorized _ ih =>
    obtain ⟨clause, source, restricted, _, model, head, body, _, _, _, _⟩ := authorized
    exact Clause.head_values_in_active_domain restricted model
      {premise | premise ∈ row.key.positivePremises}
      {value | value ∈ activeDomain program seeds}
      ih (head_literals_in_domain program seeds source)
      (fun atom member => forall₂_member body member) row.conclusion head

theorem derives_in_universe (policy : Comparisons.Policy) (program : Program)
    (seeds : List GroundFact) {fact : GroundFact} (derived : Derives policy program seeds fact) :
    fact ∈ factUniverse program seeds := by
  apply List.mem_toFinset.mpr
  cases derived with
  | seed member => exact List.mem_append_left _ member
  | fire row authorized premises =>
    have domain := derives_values_in_domain policy program seeds (.fire row authorized premises)
    obtain ⟨clause, source, _, _, model, head, _, _, _, _, _⟩ := authorized
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨(row.key.statementIndex, clause),
      (ProgramGrounding.clauseAt_iff_numbered _ _ _).mp source, ?_⟩
    apply List.mem_map.mpr
    refine ⟨row.conclusion.values, (mem_tuples_iff _ _ _).mpr ⟨head.2.length_eq.symm, domain⟩, ?_⟩
    have relationSame := head.1
    generalize row.conclusion = conclusion at relationSame ⊢
    cases conclusion
    simp_all

theorem run_facts_bounded (policy : Comparisons.Policy) (program : Program)
    (seeds : List GroundFact) (ticks : Nat) :
    (run policy program ticks (initial seeds)).facts.toFinset ⊆ factUniverse program seeds := by
  intro fact member
  exact derives_in_universe policy program seeds
    ((run_initial_sound _ _ _ _).1 fact (List.mem_toFinset.mp member))

#print axioms mem_tuples_iff
#print axioms derives_values_in_domain
#print axioms derives_in_universe
#print axioms run_facts_bounded

end Mettapedia.Languages.Datalog.Closure
