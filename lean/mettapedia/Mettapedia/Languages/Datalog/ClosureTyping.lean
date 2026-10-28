import Mettapedia.Languages.Datalog.ClosureSemantics
import Mettapedia.Languages.Datalog.ProgramStatic
import Mettapedia.Languages.Datalog.StaticGrounding

/-! Every round of the source closure retains the actual program signature.
Typing comes from checked source statements and the join's typed bindings,
including source facts extracted as zero-premise clauses. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Datalog.Closure

open StaticTyping GroundInstances

theorem groundClause_typed (signature : Signature) (context : VariableTypes)
    (fact : GroundFact) (typed : FactTyped signature fact) :
    ClauseTyped signature context (LPBridge.groundClause fact) := by
  obtain ⟨types, declared, values⟩ := typed
  refine ⟨?_, ⟨types, declared, ?_⟩, ?_⟩
  · constructor
    · intro argument member
      change argument ∈ fact.values.map Argument.literal ++ [] at member
      simp only [List.append_nil] at member
      obtain ⟨value, _, same⟩ := List.mem_map.mp member
      subst argument
      simp
    · intro name member
      simp [Clause.requiredVariables, Clause.requiredArguments, LPBridge.groundClause,
        Argument.vars] at member
  · exact (List.forall₂_map_left_iff).mpr values
  · intro premise member
    cases member

theorem clauseAt_typed (program : Program) (typed : ProgramStatic.ProgramTyped program)
    {statementIndex : Nat} {clause : Clause}
    (source : ProgramGrounding.ClauseAt program statementIndex clause) :
    ∃ context, ClauseTyped (ProgramStatic.signature program) context clause := by
  rcases source with rule | ⟨fact, source, rfl⟩
  · have member : Statement.rule clause ∈ program.statements :=
      (List.getElem?_eq_some_iff.mp rule).2 ▸ List.getElem_mem (List.getElem?_eq_some_iff.mp rule).1
    exact typed.2 _ member
  · have member : Statement.fact fact ∈ program.statements :=
      (List.getElem?_eq_some_iff.mp source).2 ▸ List.getElem_mem (List.getElem?_eq_some_iff.mp source).1
    exact ⟨fun _ => none, groundClause_typed _ _ fact (typed.2 _ member)⟩

theorem produced_fact_typed (policy : Comparisons.Policy) (program : Program)
    (typed : ProgramStatic.ProgramTyped program) (known : List GroundFact)
    (knownTyped : ∀ fact ∈ known, FactTyped (ProgramStatic.signature program) fact)
    {row : Instance} (produced : row ∈ ProgramGrounding.produce policy program known) :
    FactTyped (ProgramStatic.signature program) row.conclusion := by
  obtain ⟨⟨statementIndex, clause⟩, selected, emitted⟩ := List.mem_flatMap.mp produced
  obtain ⟨context, clauseTyped⟩ := clauseAt_typed program typed
    ((ProgramGrounding.clauseAt_iff_numbered _ _ _).mpr selected)
  exact produced_conclusion_typed _ context policy statementIndex clause clauseTyped known knownTyped emitted

theorem step_facts_typed (policy : Comparisons.Policy) (program : Program)
    (typed : ProgramStatic.ProgramTyped program) (state : State)
    (knownTyped : ∀ fact ∈ state.facts, FactTyped (ProgramStatic.signature program) fact) :
    ∀ fact ∈ (step policy program state).facts, FactTyped (ProgramStatic.signature program) fact := by
  intro fact member
  rcases (mem_step_facts _ _ _ _).mp member with old | ⟨key, member⟩
  · exact knownTyped fact old
  · obtain ⟨row, produced, same⟩ := List.mem_map.mp member
    have sameFact : row.conclusion = fact := congrArg Prod.snd same
    exact sameFact ▸ produced_fact_typed policy program typed state.facts knownTyped produced

theorem run_facts_typed (policy : Comparisons.Policy) (program : Program)
    (typed : ProgramStatic.ProgramTyped program) (ticks : Nat) (state : State)
    (knownTyped : ∀ fact ∈ state.facts, FactTyped (ProgramStatic.signature program) fact) :
    ∀ fact ∈ (run policy program ticks state).facts, FactTyped (ProgramStatic.signature program) fact := by
  induction ticks generalizing state with
  | zero => exact knownTyped
  | succ ticks ih => exact ih _ (step_facts_typed _ _ typed _ knownTyped)

theorem run_initial_facts_typed (policy : Comparisons.Policy) (program : Program)
    (typed : ProgramStatic.ProgramTyped program) (ticks : Nat) (seeds : List GroundFact)
    (seedTyped : ∀ fact ∈ seeds, FactTyped (ProgramStatic.signature program) fact) :
    ∀ fact ∈ (run policy program ticks (initial seeds)).facts,
      FactTyped (ProgramStatic.signature program) fact :=
  run_facts_typed _ _ typed _ _ (fun fact member => seedTyped fact (List.mem_eraseDups.mp member))

#print axioms groundClause_typed
#print axioms produced_fact_typed
#print axioms run_initial_facts_typed

end Mettapedia.Languages.Datalog.Closure
