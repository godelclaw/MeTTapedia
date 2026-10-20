import Mettapedia.Logic.MarkovLogicClauseSemantics

/-!
# Finite Boolean tables represented by grounded clause potentials

For each Boolean valuation, a blocking clause is false exactly at that
valuation. Give its false branch the table weight and its true branch weight
one. The product of these independently defined clause potentials recovers the
entire table, including zero weights.

This is an existence and semantic correspondence result. The presentation has
one full-width clause per valuation and makes no compactness or performance
claim. Zero potentials use the general grounded-clause interface; they need
hard constraints rather than finite real log-weights in a classical MLN.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.MarkovLogicFiniteTable

open scoped ENNReal BigOperators
open Mettapedia.Logic.MarkovLogicClauseSemantics

variable {Atom : Type*} [Fintype Atom] [DecidableEq Atom]

/-- A disjunction expressing that the valuation differs from `excluded`. -/
def blockingClause (excluded : AtomValuation Atom) : GroundClause Atom :=
  Finset.univ.image fun atom => if excluded atom then Literal.neg atom else Literal.pos atom

theorem blockingClause_holds (excluded world : AtomValuation Atom) :
    (blockingClause excluded).holds world ↔ world ≠ excluded := by
  classical
  constructor
  · rintro ⟨literal, member, holds⟩ same
    subst world
    obtain ⟨atom, _, rfl⟩ := Finset.mem_image.mp member
    cases value : excluded atom <;> simp [value, Literal.holds] at holds
  · intro different
    have witness : ∃ atom, world atom ≠ excluded atom := by
      by_contra absent
      apply different
      funext atom
      exact Classical.not_not.mp (fun unequal => absent ⟨atom, unequal⟩)
    obtain ⟨atom, unequal⟩ := witness
    refine ⟨_, Finset.mem_image.mpr ⟨atom, Finset.mem_univ _, rfl⟩, ?_⟩
    cases left : excluded atom <;> cases right : world atom <;>
      simp_all [Literal.holds]

/-- A clause potential that contributes the table entry only on its own row. -/
noncomputable def rowClause (weight : AtomValuation Atom → ℝ≥0∞)
    (finite : ∀ world, weight world ≠ ⊤) (excluded : AtomValuation Atom) :
    WeightedGroundClause Atom where
  clause := blockingClause excluded
  satisfiedPotential := 1
  unsatisfiedPotential := weight excluded
  satisfied_ne_top := ENNReal.one_ne_top
  unsatisfied_ne_top := finite excluded

theorem rowClause_eval (weight : AtomValuation Atom → ℝ≥0∞)
    (finite : ∀ world, weight world ≠ ⊤) (excluded world : AtomValuation Atom) :
    (rowClause weight finite excluded).eval world = if world = excluded then weight excluded else 1 := by
  classical
  simp only [WeightedGroundClause.eval, rowClause, blockingClause_holds]
  by_cases same : world = excluded <;> simp [same]

/-- The actual clause presentation of a finite Boolean weight table. -/
noncomputable def tableMLN (weight : AtomValuation Atom → ℝ≥0∞)
    (finite : ∀ world, weight world ≠ ⊤) : GroundMLN Atom (AtomValuation Atom) where
  clauseData := rowClause weight finite

/-- Exactly one row clause contributes its false-branch weight; all others
contribute one. The product therefore agrees with the complete table. -/
theorem tableMLN_worldWeight (weight : AtomValuation Atom → ℝ≥0∞)
    (finite : ∀ world, weight world ≠ ⊤) (world : AtomValuation Atom) :
    (tableMLN weight finite).worldWeight Finset.univ world = weight world := by
  classical
  rw [GroundMLN.worldWeight_eq_prod]
  simp only [tableMLN, rowClause_eval]
  rw [Finset.prod_eq_single world]
  · simp
  · intro other _ different
    simp [Ne.symm different]
  · simp

end Mettapedia.Logic.MarkovLogicFiniteTable
