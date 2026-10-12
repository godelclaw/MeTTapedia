import Mettapedia.Machines.ConstraintPropagation
import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Max
import Mathlib.Data.Prod.Lex

/-!
# Finite positive producer support

A ground producer may provide seed answers and copy answers from named
callees. This is the dependency fragment used by cyclic and diamond controls.
Each dependency and possible answer lowers to an actual Horn rule. The
existing worklist executes these rules; graph reachability independently
specifies their meaning. Completion and exact support follow for every
pending-rule selection policy, including cyclic dependency graphs.

These laws concern finite positive support. They do not quotient ordered proof
occurrences into support, establish the native SCC scheduler's correspondence,
or assert a native instruction bound. Term formation, arbitrary clause bodies,
negative tests and effects require separate admission and interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ProducerSupport

open ConstraintPropagation

variable {Key Item : Type*} [DecidableEq Key] [DecidableEq Item]
  [Fintype Key] [Fintype Item]

/-- The source producer reads the target producer's answers. -/
def rules (dependencies : Finset (Key × Key)) :
    (↥dependencies × Item) → HornRule (Key × Item) := fun index =>
  ⟨{(index.1.val.2, index.2)}, {(index.1.val.1, index.2)}⟩

/-- A seed supplies an answer along any finite chain of callee dependencies. -/
def Reachable (dependencies : Finset (Key × Key)) (seeds : Finset (Key × Item))
    (answer : Key × Item) : Prop :=
  ∃ seed, (seed, answer.2) ∈ seeds ∧
    Relation.ReflTransGen (fun source target => (source, target) ∈ dependencies)
      answer.1 seed

omit [DecidableEq Key] [DecidableEq Item] [Fintype Key] [Fintype Item] in
theorem models_iff_closed (dependencies : Finset (Key × Key))
    (answers : Finset (Key × Item)) :
    Models (rules dependencies) answers ↔
      ∀ dependency ∈ dependencies, ∀ item,
        (dependency.2, item) ∈ answers → (dependency.1, item) ∈ answers := by
  constructor
  · intro model dependency member item present
    have accepted := model (⟨dependency, member⟩, item)
      (by simpa [rules] using present)
    exact accepted (by simp [rules])
  · intro closed index enabled answer produced
    have present : (index.1.val.2, index.2) ∈ answers :=
      enabled (by simp [rules])
    have equal : answer = (index.1.val.1, index.2) := by
      simpa [rules] using produced
    rw [equal]
    exact closed index.1.val index.1.property index.2 present

theorem solve_sound (dependencies : Finset (Key × Key))
    (select : Selector (↥dependencies × Item)) (seeds : Finset (Key × Item))
    (answer : Key × Item)
    (produced : answer ∈ solve (rules dependencies) select seeds) :
    Reachable dependencies seeds answer := by
  classical
  let upper := Finset.univ.filter (Reachable dependencies seeds)
  have bound : seeds ⊆ upper := by
    intro seed member
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, seed.1, member, .refl⟩
  have closed : Models (rules dependencies) upper := by
    apply (models_iff_closed dependencies upper).mpr
    intro dependency member item present
    obtain ⟨seed, seeded, path⟩ := (Finset.mem_filter.mp present).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, seed, seeded, Relation.ReflTransGen.head member path⟩
  have least := (solve_least_model (rules dependencies) select seeds).2.2
  exact (Finset.mem_filter.mp (least upper bound closed produced)).2

theorem solve_complete (dependencies : Finset (Key × Key))
    (select : Selector (↥dependencies × Item)) (seeds : Finset (Key × Item))
    (answer : Key × Item) (reachable : Reachable dependencies seeds answer) :
    answer ∈ solve (rules dependencies) select seeds := by
  rcases answer with ⟨key, item⟩
  obtain ⟨extension, model, _⟩ := solve_least_model (rules dependencies) select seeds
  have closed := (models_iff_closed dependencies _).mp model
  obtain ⟨seed, seeded, path⟩ := reachable
  change Relation.ReflTransGen (fun source target =>
    (source, target) ∈ dependencies) key seed at path
  exact Relation.ReflTransGen.head_induction_on
    (motive := fun producer _ =>
      (producer, item) ∈ solve (rules dependencies) select seeds)
    path (extension seeded) (fun member _ ih => closed _ member item ih)

/-- Worklist execution and the independently specified graph semantics agree. -/
theorem solve_exact (dependencies : Finset (Key × Key))
    (select : Selector (↥dependencies × Item)) (seeds : Finset (Key × Item))
    (answer : Key × Item) :
    answer ∈ solve (rules dependencies) select seeds ↔
      Reachable dependencies seeds answer :=
  ⟨solve_sound dependencies select seeds answer,
    solve_complete dependencies select seeds answer⟩

/-- A cycle with no seed cannot manufacture answer support. -/
theorem unseeded_empty (dependencies : Finset (Key × Key))
    (select : Selector (↥dependencies × Item)) :
    solve (rules dependencies) select ∅ = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro answer produced
  obtain ⟨seed, impossible, _⟩ := solve_sound dependencies select ∅ answer produced
  simp at impossible

/-- The bound counts worklist rule applications in the independent model,
not native generator instructions or answer-materialization costs. -/
theorem completes_within (dependencies : Finset (Key × Key))
    (select : Selector (↥dependencies × Item)) (seeds : Finset (Key × Item)) :
    (drain (rules dependencies) select
      ((Fintype.card (Key × Item) - seeds.card) *
          (dependencies.card * Fintype.card Item + 1) +
        dependencies.card * Fintype.card Item)
      (initial seeds)).pending = ∅ := by
  apply drain_pending_empty
  simp [potential, initial, Fintype.card_prod, Fintype.card_coe]

def lowest {Index : Type*} [LinearOrder Index] : Selector Index :=
  fun pending nonempty => ⟨pending.min' nonempty, Finset.min'_mem _ _⟩

namespace Controls

def cycle : Finset (Fin 2 × Fin 2) := {(0, 1), (1, 0)}
def seed : Finset (Fin 2 × Fin 2) := {(0, 0)}

local instance {Left Right : Type*} [LinearOrder Left] [LinearOrder Right] :
    LinearOrder (Left × Right) :=
  inferInstanceAs (LinearOrder (Left ×ₗ Right))

theorem seeded_cycle_completes :
    solve (rules (Item := Fin 2) cycle) lowest seed = {(0, 0), (1, 0)} := by decide

theorem unreachable_answer_not_invented :
    (0, 1) ∉ solve (rules (Item := Fin 2) cycle) lowest seed := by decide

theorem changed_seed_changes_support :
    solve (rules (Item := Fin 2) cycle) lowest seed ≠
      solve (rules (Item := Fin 2) cycle) lowest ({(0, 1)} : Finset (Fin 2 × Fin 2)) := by decide

def diamond : Finset (Fin 4 × Fin 4) := {(0, 1), (0, 2), (1, 3), (2, 3)}
def diamondSeed : Finset (Fin 4 × Fin 2) := {(3, 0)}

theorem diamond_shares_answer_support :
    solve (rules (Item := Fin 2) diamond) lowest diamondSeed =
      {(0, 0), (1, 0), (2, 0), (3, 0)} := by decide

def reference {nodes : Nat} (dependencies : Finset (Fin nodes × Fin nodes))
    (seeds : Finset (Fin nodes × Fin 2)) : Finset (Fin nodes × Fin 2) :=
  solve (rules dependencies) lowest seeds

end Controls

#print axioms solve_exact
#print axioms unseeded_empty
#print axioms completes_within
#print axioms Controls.seeded_cycle_completes

end Mettapedia.Machines.ProducerSupport
