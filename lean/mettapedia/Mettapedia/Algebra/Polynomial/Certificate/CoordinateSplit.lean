import Mettapedia.Algebra.Polynomial.Certificate.Sparse

/-!
Logical exhaustivity of the zero/invertible carrier splits used by the finite
polynomial refutation trees.

For every coordinate over a field, either the coordinate is zero or it has an
inverse satisfying `x * x⁻¹ - 1 = 0`.  Choosing this independently for a finite
coordinate family gives exactly the Boolean branch cube used by the external
tree generator.  If every branch contradicts the parent equations, the parent
has no common zero.
-/

namespace Mettapedia.Algebra.Polynomial.Certificate.CoordinateSplit

universe u

/-- Simultaneous vanishing of a finite or infinite indexed equation family. -/
def commonZero {ι R : Type*} [Zero R] (equations : ι → R) : Prop :=
  ∀ index, equations index = 0

/-- The semantic condition represented by one Boolean coordinate branch.
`false` appends the equation `x = 0`; `true` introduces a fresh witness and
appends `x * inverse - 1 = 0`. -/
def coordinateBranch {R : Type*} [Ring R]
    (value : R) (nonzero : Bool) : Prop :=
  if nonzero then ∃ inverse : R, value * inverse - 1 = 0 else value = 0

/-- Conditions for one complete Boolean branch over a coordinate family. -/
def branchConditions {κ R : Type*} [Ring R]
    (coordinates : κ → R) (bits : κ → Bool) : Prop :=
  ∀ index, coordinateBranch (coordinates index) (bits index)

/-- Every point over a field belongs to one zero/invertible branch. -/
theorem exists_branch {κ R : Type*} [Field R]
    (coordinates : κ → R) :
    ∃ bits : κ → Bool, branchConditions coordinates bits := by
  classical
  refine ⟨fun index => if coordinates index = 0 then false else true, ?_⟩
  intro index
  by_cases zero : coordinates index = 0
  · simp [coordinateBranch, zero]
  · simp only [zero, if_false, coordinateBranch, if_true]
    exact ⟨(coordinates index)⁻¹, by simp [zero]⟩

/-- If all Boolean coordinate branches are impossible together with the
parent equations, then the parent equation family has no common zero. -/
theorem noCommonZero_of_allBranches
    {κ ι R : Type*} [Field R]
    (equations : ι → R) (coordinates : κ → R)
    (branchesImpossible : ∀ bits : κ → Bool,
      ¬ (commonZero equations ∧ branchConditions coordinates bits)) :
    ¬ commonZero equations := by
  intro parentZero
  obtain ⟨bits, branch⟩ := exists_branch coordinates
  exact branchesImpossible bits ⟨parentZero, branch⟩

/-- Binary form, useful when replaying a recursive tree one split at a time. -/
theorem noCommonZero_of_zero_invertible_split
    {ι R : Type*} [Field R] (equations : ι → R) (coordinate : R)
    (zeroImpossible : ¬ (commonZero equations ∧ coordinate = 0))
    (invertibleImpossible : ¬ ∃ inverse : R,
      commonZero equations ∧ coordinate * inverse - 1 = 0) :
    ¬ commonZero equations := by
  intro parentZero
  by_cases zero : coordinate = 0
  · exact zeroImpossible ⟨parentZero, zero⟩
  · apply invertibleImpossible
    refine ⟨coordinate⁻¹, parentZero, ?_⟩
    simp [zero]

/-- The exact three-coordinate cube over three coordinates has eight
Boolean branches.  This corollary fixes the arity while retaining the generic
semantic theorem above. -/
theorem noCommonZero_of_threeCoordinateCarrier
    {ι R : Type*} [Field R] (equations : ι → R)
    (coordinates : Fin 3 → R)
    (branchesImpossible : ∀ bits : Fin 3 → Bool,
      ¬ (commonZero equations ∧ branchConditions coordinates bits)) :
    ¬ commonZero equations :=
  noCommonZero_of_allBranches equations coordinates branchesImpossible

/-- A recursive proof object for the nested three-coordinate carrier trees
for three coordinate tests.  A leaf directly refutes its current
chart proposition.  An internal node supplies all eight recursively refuted
zero/invertible children. -/
inductive RefutationTree {R : Type u} [Field R] : Prop → Type (u + 1)
  | leaf {chart : Prop} (impossible : ¬ chart) : RefutationTree (R := R) chart
  | split {chart : Prop} (coordinates : Fin 3 → R)
      (children : ∀ bits : Fin 3 → Bool,
        RefutationTree (R := R) (chart ∧ branchConditions coordinates bits)) :
      RefutationTree (R := R) chart

/-- Structural soundness of an arbitrarily deep carrier tree. -/
theorem RefutationTree.sound {R : Type*} [Field R] {chart : Prop}
    (tree : RefutationTree (R := R) chart) : ¬ chart := by
  induction tree with
  | leaf impossible => exact impossible
  | @split chart coordinates children childSound =>
      intro root
      obtain ⟨bits, branch⟩ := exists_branch coordinates
      exact childSound bits ⟨root, branch⟩

end Mettapedia.Algebra.Polynomial.Certificate.CoordinateSplit
