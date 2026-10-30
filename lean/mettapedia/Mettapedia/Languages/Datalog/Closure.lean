import Mettapedia.Languages.Datalog.ProgramGrounding
import Mettapedia.Languages.Datalog.Observation

/-! Positive Datalog closure over the actual whole-program ground producer.
Each round reads one immutable fact snapshot. Logical keys and facts are
published independently: an already known conclusion does not suppress a
new explanation. This is a source reference computation, not another native
runner or an admission of an ordinary-source comparison profile. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.Datalog.Closure

open GroundInstances

deriving instance ReflBEq, LawfulBEq for DerivationKey

abbrev Firing := DerivationKey × GroundFact

def firings (policy : Comparisons.Policy) (program : Program)
    (known : List GroundFact) : List Firing :=
  (ProgramGrounding.produce policy program known).map fun row => (row.key, row.conclusion)

theorem mem_firings_iff (policy : Comparisons.Policy) (program : Program)
    (known : List GroundFact) (key : DerivationKey) (conclusion : GroundFact) :
    (key, conclusion) ∈ firings policy program known ↔
      ProgramGrounding.SourceAuthorized policy program known ⟨key, conclusion, []⟩ := by
  constructor
  · intro member
    obtain ⟨row, produced, same⟩ := List.mem_map.mp member
    obtain ⟨clause, atSource, authorized⟩ := ProgramGrounding.produce_sound policy program known produced
    have keySame : row.key = key := congrArg Prod.fst same
    have conclusionSame : row.conclusion = conclusion := congrArg Prod.snd same
    refine ⟨clause, ?_, ?_⟩
    · simpa only [keySame] using atSource
    · simpa only [Authorized, keySame, conclusionSame] using authorized
  · intro authorized
    obtain ⟨row, produced, keySame, conclusionSame⟩ :=
      ProgramGrounding.produce_complete policy program known ⟨key, conclusion, []⟩ authorized
    exact List.mem_map.mpr ⟨row, produced, Prod.ext keySame conclusionSame⟩

theorem authorized_mono (policy : Comparisons.Policy) (program : Program)
    (before after : List GroundFact) (included : ∀ fact ∈ before, fact ∈ after)
    (row : Instance) (authorized : ProgramGrounding.SourceAuthorized policy program before row) :
    ProgramGrounding.SourceAuthorized policy program after row := by
  obtain ⟨clause, atSource, valid⟩ := authorized
  exact ⟨clause, atSource,
    Observation.authorized_of_known_extension policy row.key.statementIndex clause before after included row valid⟩

theorem firings_mono (policy : Comparisons.Policy) (program : Program)
    (before after : List GroundFact) (included : ∀ fact ∈ before, fact ∈ after) :
    ∀ firing ∈ firings policy program before, firing ∈ firings policy program after := by
  rintro ⟨key, conclusion⟩ member
  exact (mem_firings_iff policy program after key conclusion).mpr
    (authorized_mono policy program before after included _
      ((mem_firings_iff policy program before key conclusion).mp member))

theorem firings_congr (policy : Comparisons.Policy) (program : Program)
    (first second : List GroundFact) (same : ∀ fact, fact ∈ first ↔ fact ∈ second)
    (firing : Firing) :
    firing ∈ firings policy program first ↔ firing ∈ firings policy program second :=
  ⟨firings_mono policy program first second (fun fact => (same fact).mp) firing,
    firings_mono policy program second first (fun fact => (same fact).mpr) firing⟩

structure State where
  facts : List GroundFact
  keys : List DerivationKey
  deriving Repr, DecidableEq

def initial (seeds : List GroundFact) : State := ⟨seeds.eraseDups, []⟩

def step (policy : Comparisons.Policy) (program : Program) (state : State) : State :=
  let batch := firings policy program state.facts
  ⟨(state.facts ++ batch.map Prod.snd).eraseDups,
    (state.keys ++ batch.map Prod.fst).eraseDups⟩

def run (policy : Comparisons.Policy) (program : Program) : Nat → State → State
  | 0, state => state
  | ticks + 1, state => run policy program ticks (step policy program state)

@[simp] theorem mem_step_facts (policy : Comparisons.Policy) (program : Program)
    (state : State) (fact : GroundFact) :
    fact ∈ (step policy program state).facts ↔
      fact ∈ state.facts ∨ ∃ key, (key, fact) ∈ firings policy program state.facts := by
  simp only [step, List.mem_eraseDups, List.mem_append, List.mem_map]
  constructor
  · rintro (known | ⟨⟨key, conclusion⟩, member, same⟩)
    · exact Or.inl known
    · exact Or.inr ⟨key, same ▸ member⟩
  · rintro (known | ⟨key, member⟩)
    · exact Or.inl known
    · exact Or.inr ⟨(key, fact), member, rfl⟩

@[simp] theorem mem_step_keys (policy : Comparisons.Policy) (program : Program)
    (state : State) (key : DerivationKey) :
    key ∈ (step policy program state).keys ↔
      key ∈ state.keys ∨ ∃ conclusion, (key, conclusion) ∈ firings policy program state.facts := by
  simp only [step, List.mem_eraseDups, List.mem_append, List.mem_map]
  constructor
  · rintro (known | ⟨⟨actual, conclusion⟩, member, same⟩)
    · exact Or.inl known
    · exact Or.inr ⟨conclusion, same ▸ member⟩
  · rintro (known | ⟨conclusion, member⟩)
    · exact Or.inl known
    · exact Or.inr ⟨(key, conclusion), member, rfl⟩

theorem facts_in_step (policy : Comparisons.Policy) (program : Program) (state : State) :
    ∀ fact ∈ state.facts, fact ∈ (step policy program state).facts :=
  fun _ member => (mem_step_facts _ _ _ _).mpr (Or.inl member)

theorem keys_in_step (policy : Comparisons.Policy) (program : Program) (state : State) :
    ∀ key ∈ state.keys, key ∈ (step policy program state).keys :=
  fun _ member => (mem_step_keys _ _ _ _).mpr (Or.inl member)

theorem run_add (policy : Comparisons.Policy) (program : Program)
    (first second : Nat) (state : State) :
    run policy program (first + second) state =
      run policy program second (run policy program first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, run]
  | succ first ih =>
    simpa only [Nat.succ_add, run] using ih (step policy program state)

/-- Facts can finish while the key account still has one publication round
outstanding. These predicates therefore have different completion tests. -/
def FactsComplete (policy : Comparisons.Policy) (program : Program) (state : State) : Prop :=
  ∀ key conclusion, (key, conclusion) ∈ firings policy program state.facts → conclusion ∈ state.facts

def KeysComplete (policy : Comparisons.Policy) (program : Program) (state : State) : Prop :=
  ∀ key conclusion, (key, conclusion) ∈ firings policy program state.facts → key ∈ state.keys

theorem factsComplete_iff (policy : Comparisons.Policy) (program : Program) (state : State) :
    FactsComplete policy program state ↔
      ∀ fact, fact ∈ (step policy program state).facts ↔ fact ∈ state.facts := by
  constructor
  · intro closed fact
    rw [mem_step_facts]
    exact ⟨fun member => member.elim id (fun ⟨key, fired⟩ => closed key fact fired), Or.inl⟩
  · intro same key conclusion member
    exact (same conclusion).mp ((mem_step_facts _ _ _ _).mpr (Or.inr ⟨key, member⟩))

theorem keysComplete_iff (policy : Comparisons.Policy) (program : Program) (state : State) :
    KeysComplete policy program state ↔
      ∀ key, key ∈ (step policy program state).keys ↔ key ∈ state.keys := by
  constructor
  · intro closed key
    rw [mem_step_keys]
    exact ⟨fun member => member.elim id (fun ⟨conclusion, fired⟩ => closed key conclusion fired), Or.inl⟩
  · intro same key conclusion member
    exact (same key).mp ((mem_step_keys _ _ _ _).mpr (Or.inr ⟨conclusion, member⟩))

/-- A fact fixed point needs only one further round to finish its finite
one-step key account. This says nothing about unfolded proof-tree completion. -/
theorem keysComplete_after_factClosure (policy : Comparisons.Policy) (program : Program) (state : State)
    (closed : FactsComplete policy program state) :
    FactsComplete policy program (step policy program state) ∧
      KeysComplete policy program (step policy program state) := by
  have same := (factsComplete_iff policy program state).mp closed
  constructor
  · intro key conclusion member
    have old := (firings_congr policy program (step policy program state).facts state.facts same _).mp member
    exact facts_in_step policy program state conclusion (closed key conclusion old)
  · intro key conclusion member
    have old := (firings_congr policy program (step policy program state).facts state.facts same _).mp member
    exact (mem_step_keys _ _ _ _).mpr (Or.inr ⟨conclusion, old⟩)

#print axioms mem_firings_iff
#print axioms firings_congr
#print axioms run_add
#print axioms keysComplete_after_factClosure

end Mettapedia.Languages.Datalog.Closure
