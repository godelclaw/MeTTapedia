import Mettapedia.GSLT.Core.LooseRelationEquipment
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Signed Bellman certificates for compatible boundary histories

Attach a real cost to each witness of the existing loose-relation equipment.
Composition retains the intermediate state and both witnesses, and adds their
signed costs. A local reserve inequality therefore composes with no new initial
allowance at a seam. No discounting, positivity of costs, finite state space,
or existence of an optimizing witness is assumed.

Cost domination is additional to witness transport: a reduction preserving
reachability alone need not preserve a budget. The final example preserves
individual edge costs while forgetting a state distinction needed for the
reserve; its reduced relation admits an unpaid positive loop.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.BoundaryBellman

open Mettapedia.GSLT.LooseRelationEquipment

universe u

/-- A numerical observation of each retained boundary witness. -/
structure CostedRelation (Source Target : Type u) where
  witness : Loose Source Target
  cost : ∀ {source target}, witness source target → ℝ

namespace CostedRelation

variable {A B C D : Type u}

/-- The existing witness composition, with additive signed costs. -/
def comp (first : CostedRelation A B) (second : CostedRelation B C) :
    CostedRelation A C where
  witness := LooseRelationEquipment.comp first.witness second.witness
  cost h := first.cost h.2.1 + second.cost h.2.2

/-- Empty history retains equality of the full boundary state. -/
def identity (A : Type u) : CostedRelation A A where
  witness := LooseRelationEquipment.identity
  cost _ := 0

/-- A Bellman upper bound over every witness, without forming a possibly
infinite supremum. Negative step costs are retained. -/
def Upper (relation : CostedRelation A B) (terminal : B → ℝ)
    (source : A) (budget : ℝ) : Prop :=
  ∀ target (h : relation.witness source target), relation.cost h + terminal target ≤ budget

/-- The source reserve pays the signed cost and the remaining target reserve. -/
def Bounds (relation : CostedRelation A B) (before : A → ℝ) (after : B → ℝ) : Prop :=
  ∀ source, relation.Upper after source (before source)

/-- Exact backward budget composition. The same intermediate state and the
cost of its first witness constrain every possible continuation. -/
theorem upper_comp_iff (first : CostedRelation A B) (second : CostedRelation B C)
    (terminal : C → ℝ) (source : A) (budget : ℝ) :
    (first.comp second).Upper terminal source budget ↔
      ∀ middle (h : first.witness source middle),
        second.Upper terminal middle (budget - first.cost h) := by
  constructor
  · intro bound middle left target right
    have h := bound target ⟨middle, left, right⟩
    change (first.cost left + second.cost right) + terminal target ≤ budget at h
    linarith
  · intro bound target h
    obtain ⟨middle, left, right⟩ := h
    have h := bound middle left target right
    change (first.cost left + second.cost right) + terminal target ≤ budget
    linarith

theorem bounds_identity (reserve : A → ℝ) : (identity A).Bounds reserve reserve := by
  intro source target h
  have same := h.down.down
  subst target
  simp [identity]

/-- Intermediate reserves cancel; the first reserve is used only once. -/
theorem Bounds.comp {first : CostedRelation A B} {second : CostedRelation B C}
    {initial : A → ℝ} {middle : B → ℝ} {final : C → ℝ}
    (left : first.Bounds initial middle) (right : second.Bounds middle final) :
    (first.comp second).Bounds initial final := by
  intro source target h
  obtain ⟨state, firstWitness, secondWitness⟩ := h
  have hfirst := left source state firstWitness
  have hsecond := right state target secondWitness
  change (first.cost firstWitness + second.cost secondWitness) + final target ≤ initial source
  linarith

/-- Any retained finite number of steps, using the same relation. -/
def iterate (relation : CostedRelation A A) : ℕ → CostedRelation A A
  | 0 => identity A
  | n + 1 => relation.comp (relation.iterate n)

theorem Bounds.iterate {relation : CostedRelation A A} {reserve : A → ℝ}
    (bound : relation.Bounds reserve reserve) (n : ℕ) :
    (relation.iterate n).Bounds reserve reserve := by
  induction n with
  | zero => exact bounds_identity reserve
  | succ n ih => exact bound.comp ih

theorem cost_le_initial {relation : CostedRelation A B}
    {before : A → ℝ} {after : B → ℝ}
    (bound : relation.Bounds before after) (nonnegative : ∀ target, 0 ≤ after target)
    {source target} (h : relation.witness source target) :
    relation.cost h ≤ before source :=
  (le_add_of_nonneg_right (nonnegative target)).trans (bound source target h)

/-- Witness transport alone does not earn a cost comparison. The inequality
is oriented so an upper bound on the summary also bounds the original. -/
structure Domination (first second : CostedRelation A B) where
  transport : Cell id id first.witness second.witness
  cost_le : ∀ {source target} (h : first.witness source target),
    first.cost h ≤ second.cost (transport.map h)

theorem Bounds.of_domination {first second : CostedRelation A B}
    {before : A → ℝ} {after : B → ℝ}
    (bound : second.Bounds before after) (reduction : first.Domination second) :
    first.Bounds before after := by
  intro source target h
  have hcost := reduction.cost_le h
  have hbound := bound source target (reduction.transport.map h)
  change first.cost h + after target ≤ before source
  linarith

/-- Cost domination extends through both surrounding components. -/
def Domination.comp {first first' : CostedRelation A B}
    {second second' : CostedRelation B C}
    (left : first.Domination first') (right : second.Domination second') :
    (first.comp second).Domination (first'.comp second') where
  transport := Cell.hcomp left.transport right.transport
  cost_le h := add_le_add (left.cost_le h.2.1) (right.cost_le h.2.2)

/-- In particular, a strictly positive closed cost excludes a finite
state-only reserve on that boundary representation. -/
theorem no_bounds_of_positive_loop {relation : CostedRelation A A} {source : A}
    (h : relation.witness source source) (positive : 0 < relation.cost h) :
    ¬ ∃ reserve : A → ℝ, relation.Bounds reserve reserve := by
  rintro ⟨reserve, bound⟩
  have hbound := bound source source h
  linarith

end CostedRelation

namespace StateErasureExample

open CostedRelation

def reserve : Bool → ℝ := fun spent => if spent then 0 else 2

/-- An exact signed transfer between charged and spent states. -/
def retained : CostedRelation Bool Bool where
  witness _ _ := PUnit
  cost {source target} _ := reserve source - reserve target

theorem retained_bounds : retained.Bounds reserve reserve := by
  intro source target h
  change (reserve source - reserve target) + reserve target ≤ reserve source
  linarith

theorem retained_all_prefixes (n : ℕ) {source target : Bool}
    (h : (retained.iterate n).witness source target) :
    (retained.iterate n).cost h ≤ reserve source := by
  apply cost_le_initial (retained_bounds.iterate n) (fun target => ?_) h
  cases target <;> norm_num [reserve]

/-- Individual events survive, but their hidden endpoints are no longer
required to agree when events are composed. -/
def forgotten : CostedRelation Unit Unit where
  witness _ _ := Bool × Bool
  cost h := reserve h.1 - reserve h.2

def forget : Cell (fun _ : Bool => ()) (fun _ : Bool => ())
    retained.witness forgotten.witness where
  map {source target} _ := (source, target)

theorem forget_preserves_single_cost {source target : Bool}
    (h : retained.witness source target) :
    forgotten.cost (forget.map h) = retained.cost h := rfl

theorem forgotten_no_reserve : ¬ ∃ value : Unit → ℝ, forgotten.Bounds value value := by
  apply no_bounds_of_positive_loop (relation := forgotten) (source := ()) (false, true)
  change (0 : ℝ) < 2 - 0
  norm_num

end StateErasureExample

end Mettapedia.GSLT.Dynamics.BoundaryBellman
