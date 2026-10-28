import Mettapedia.Languages.Datalog.ClosureFinite

/-! Executable, separately checked completion observations and a source-derived
finite closure bound. A budget prefix never certifies absence by itself. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.Datalog.Closure

def factsComplete? (policy : Comparisons.Policy) (program : Program) (state : State) : Bool :=
  (firings policy program state.facts).all fun firing => decide (firing.2 ∈ state.facts)

def keysComplete? (policy : Comparisons.Policy) (program : Program) (state : State) : Bool :=
  (firings policy program state.facts).all fun firing => decide (firing.1 ∈ state.keys)

theorem factsComplete?_iff (policy : Comparisons.Policy) (program : Program) (state : State) :
    factsComplete? policy program state = true ↔ FactsComplete policy program state := by
  simp only [factsComplete?, List.all_eq_true, decide_eq_true_eq, FactsComplete]
  exact ⟨fun held key conclusion member => held (key, conclusion) member,
    fun held firing member => held firing.1 firing.2 member⟩

theorem keysComplete?_iff (policy : Comparisons.Policy) (program : Program) (state : State) :
    keysComplete? policy program state = true ↔ KeysComplete policy program state := by
  simp only [keysComplete?, List.all_eq_true, decide_eq_true_eq, KeysComplete]
  exact ⟨fun held key conclusion member => held (key, conclusion) member,
    fun held firing member => held firing.1 firing.2 member⟩

inductive Completion where
  | pending
  | factsOnly
  | factsAndKeys
  deriving Repr, DecidableEq

def completion (policy : Comparisons.Policy) (program : Program) (state : State) : Completion :=
  if factsComplete? policy program state then
    if keysComplete? policy program state then .factsAndKeys else .factsOnly
  else .pending

theorem completion_exact (policy : Comparisons.Policy) (program : Program) (state : State) :
    (completion policy program state = .pending ↔ ¬FactsComplete policy program state) ∧
    (completion policy program state = .factsOnly ↔
      FactsComplete policy program state ∧ ¬KeysComplete policy program state) ∧
    (completion policy program state = .factsAndKeys ↔
      FactsComplete policy program state ∧ KeysComplete policy program state) := by
  have facts := factsComplete?_iff policy program state
  have keys := keysComplete?_iff policy program state
  cases factChecked : factsComplete? policy program state <;>
    cases keyChecked : keysComplete? policy program state <;>
    simp_all [completion]

theorem run_succ (policy : Comparisons.Policy) (program : Program) (ticks : Nat) (state : State) :
    run policy program (ticks + 1) state = step policy program (run policy program ticks state) := by
  rw [run_add]
  rfl

theorem factsComplete_run (policy : Comparisons.Policy) (program : Program) (ticks : Nat) (state : State)
    (closed : FactsComplete policy program state) :
    FactsComplete policy program (run policy program ticks state) := by
  induction ticks generalizing state with
  | zero => exact closed
  | succ ticks ih =>
    exact ih _ (keysComplete_after_factClosure policy program state closed).1

theorem fact_card_strict_of_pending (policy : Comparisons.Policy) (program : Program) (state : State)
    (pending : ¬FactsComplete policy program state) :
    state.facts.toFinset.card < (step policy program state).facts.toFinset.card := by
  have subset : state.facts.toFinset ⊆ (step policy program state).facts.toFinset := by
    intro fact member
    exact List.mem_toFinset.mpr (facts_in_step _ _ _ fact (List.mem_toFinset.mp member))
  by_contra noGrowth
  have equal := Finset.eq_of_subset_of_card_le subset (Nat.le_of_not_gt noGrowth)
  apply pending
  apply (factsComplete_iff _ _ _).mpr
  intro fact
  simpa only [List.mem_toFinset] using (Finset.ext_iff.mp equal.symm fact)

/-- The bound is derived from this program's actual head shapes and input
values. It is not an assumed finite candidate model or a timing bound. -/
theorem exists_factClosure_by_bound (policy : Comparisons.Policy) (program : Program)
    (seeds : List GroundFact) :
    ∃ ticks ≤ (factUniverse program seeds).card,
      FactsComplete policy program (run policy program ticks (initial seeds)) := by
  classical
  by_contra missing
  have pending : ∀ ticks ≤ (factUniverse program seeds).card,
      ¬FactsComplete policy program (run policy program ticks (initial seeds)) := by
    intro ticks bound closed
    exact missing ⟨ticks, bound, closed⟩
  have growth : ∀ ticks ≤ (factUniverse program seeds).card + 1,
      ticks ≤ (run policy program ticks (initial seeds)).facts.toFinset.card := by
    intro ticks bound
    induction ticks with
    | zero => omega
    | succ ticks ih =>
      have previous := ih (by omega)
      have strict := fact_card_strict_of_pending policy program _ (pending ticks (by omega))
      rw [← run_succ] at strict
      omega
  have lower := growth ((factUniverse program seeds).card + 1) (by omega)
  have upper := Finset.card_le_card
    (run_facts_bounded policy program seeds ((factUniverse program seeds).card + 1))
  omega

theorem factClosure_by_bound (policy : Comparisons.Policy) (program : Program)
    (seeds : List GroundFact) :
    FactsComplete policy program (run policy program (factUniverse program seeds).card (initial seeds)) := by
  obtain ⟨ticks, bounded, closed⟩ := exists_factClosure_by_bound policy program seeds
  have persisted := factsComplete_run policy program ((factUniverse program seeds).card - ticks) _ closed
  rw [← run_add, Nat.add_sub_of_le bounded] at persisted
  exact persisted

/-- Finite facts and finite logical one-step keys both finish. This theorem
deliberately does not say that cyclic unfolded derivation enumeration finishes. -/
theorem fullClosure_by_bound (policy : Comparisons.Policy) (program : Program)
    (seeds : List GroundFact) :
    completion policy program
      (run policy program ((factUniverse program seeds).card + 1) (initial seeds)) = .factsAndKeys := by
  apply (completion_exact _ _ _).2.2.mpr
  rw [run_succ]
  exact keysComplete_after_factClosure policy program _ (factClosure_by_bound policy program seeds)

#print axioms completion_exact
#print axioms fact_card_strict_of_pending
#print axioms exists_factClosure_by_bound
#print axioms factClosure_by_bound
#print axioms fullClosure_by_bound

end Mettapedia.Languages.Datalog.Closure
