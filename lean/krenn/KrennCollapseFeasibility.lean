import KrennCollapseReductionReflection
import KrennCollapseSupportCover.Base

/-!
The semantic bridge from reduced binomial equations to the Boolean support
condition used by the global C6 collapse cover.

For an integral-domain-valued assignment, a squarefree monomial is nonzero
exactly when all of its variables are nonzero.  Thus equality of the two
monomials in each reduced relation makes their two Boolean activity tests
equivalent.  This is the algebra-to-support half of the connector.
-/

namespace Krenn.CollapseFeasibility

open Krenn.LatticeCombinationReflection
open Krenn.CollapseReductionReflection
open Krenn.CollapseSupportCover

/-- The Boolean support pattern induced by a concrete valuation. -/
def supportPattern {R : Type*} [Zero R] (values : Fin 26 → R) :
    Fin 26 → Prop := fun coordinate => values coordinate ≠ 0

@[simp] theorem supportPattern_iff {R : Type*} [Zero R]
    (values : Fin 26 → R) (coordinate : Fin 26) :
    supportPattern values coordinate ↔ values coordinate ≠ 0 := Iff.rfl

theorem left_active_iff_monomial_ne_zero {R : Type*}
    [CommMonoidWithZero R] [Nontrivial R] [NoZeroDivisors R]
    (values : Fin 26 → R) (index : Fin 14) :
    relationLeftActive (supportPattern values) index ↔
      monomial values (reducedRelation index).left ≠ 0 := by
  fin_cases index <;>
    simp [relationLeftActive, supportPattern, reducedRelation, monomial_add,
      monomial_single_one]

theorem right_active_iff_monomial_ne_zero {R : Type*}
    [CommMonoidWithZero R] [Nontrivial R] [NoZeroDivisors R]
    (values : Fin 26 → R) (index : Fin 14) :
    relationRightActive (supportPattern values) index ↔
      monomial values (reducedRelation index).right ≠ 0 := by
  fin_cases index <;>
    simp [relationRightActive, supportPattern, reducedRelation, monomial_add,
      monomial_single_one]

/-- Every exact reduced binomial system induces a feasible Boolean support
pattern. -/
theorem feasible_of_reduced_relations {R : Type*}
    [CommMonoidWithZero R] [Nontrivial R] [NoZeroDivisors R]
    (values : Fin 26 → R)
    (relations : ∀ index,
      monomial values (reducedRelation index).left =
        monomial values (reducedRelation index).right) :
    Feasible (supportPattern values) := by
  have activity (index : Fin 14) :
      relationLeftActive (supportPattern values) index ↔
        relationRightActive (supportPattern values) index := by
    rw [left_active_iff_monomial_ne_zero, right_active_iff_monomial_ne_zero,
      relations index]
  exact ⟨activity 0, activity 1, activity 2, activity 3, activity 4,
    activity 5, activity 6, activity 7, activity 8, activity 9, activity 10,
    activity 11, activity 12, activity 13⟩

/-- Native form of the bridge: the eighteen raw determinant equations force
the feasibility condition after the four quotient identifications. -/
theorem feasible_of_raw_collapse {R : Type*}
    [CommRing R] [Nontrivial R] [NoZeroDivisors R]
    (values : Fin 30 → R) (collapse : SatisfiesRawCollapse values) :
    Feasible (supportPattern (reduceRaw values)) :=
  feasible_of_reduced_relations (reduceRaw values)
    (reduced_relations_of_raw_collapse values collapse)

end Krenn.CollapseFeasibility

#print axioms Krenn.CollapseFeasibility.feasible_of_raw_collapse
