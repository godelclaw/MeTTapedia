import Mettapedia.Algebra.Polynomial.Certificate.CoordinateSplit

/-!
The semantic parent-to-child connector for coordinate-refinement trees.

Zero/invertible cases exhaust a coordinate family. This file packages that
argument at the equation-
system boundary used by the generated artifacts: a child retains every parent
equation on a prefix of its variables and appends one equation per split
coordinate.  A zero branch appends `c`; a live branch appends
`c * freshInverse - 1`.

Every parent point extends to one Boolean child, and every child point
restricts to a parent point. These are statements about the displayed equation
systems, independent of how a search procedure discovers them.
-/

namespace Mettapedia.Algebra.Polynomial.Certificate.EquationSplit

universe uν uκ uι uR

/-- A family of equations whose coefficients are evaluated at a variable
assignment. -/
abbrev EquationSystem (ν ι R : Type*) := (ν → R) → ι → R

/-- A fixed assignment simultaneously annihilates every equation. -/
def commonZeroAt {ν ι R : Type*} [Zero R]
    (system : EquationSystem ν ι R) (values : ν → R) : Prop :=
  ∀ equation, system values equation = 0

/-- The system has at least one common zero. -/
def hasCommonZero {ν ι R : Type*} [Zero R]
    (system : EquationSystem ν ι R) : Prop :=
  ∃ values, commonZeroAt system values

/-- The uniform child-system schema used by a carrier refinement.

The old variables/equations occupy the left summands.  The right variable at
`coordinate` is the fresh inverse witness for that coordinate; the right
equation is the corresponding zero or invertibility equation. -/
def childSystem {ν κ ι R : Type*} [Ring R]
    (parent : EquationSystem ν ι R) (coordinates : κ → ν)
    (bits : κ → Bool) : EquationSystem (Sum ν κ) (Sum ι κ) R :=
  fun values equation =>
    match equation with
    | .inl parentEquation => parent (fun v => values (.inl v)) parentEquation
    | .inr coordinate =>
        if bits coordinate then
          values (.inl (coordinates coordinate)) * values (.inr coordinate) - 1
        else
          values (.inl (coordinates coordinate))

/-- A child common zero restricts to a common zero of the inherited parent
equations. -/
theorem childCommonZero_restricts_to_parent
    {ν κ ι R : Type*} [Ring R]
    (parent : EquationSystem ν ι R) (coordinates : κ → ν)
    (bits : κ → Bool) (values : Sum ν κ → R)
    (childZero : commonZeroAt (childSystem parent coordinates bits) values) :
    commonZeroAt parent (fun v => values (.inl v)) := by
  intro equation
  exact childZero (.inl equation)

/-- Every parent common zero over a field extends to a common zero of one
Boolean child.  The bits are selected by actual zero tests and live
coordinates receive their field inverses as the fresh values. -/
theorem parentCommonZero_extends_to_child
    {ν κ ι R : Type*} [Field R]
    (parent : EquationSystem ν ι R) (coordinates : κ → ν)
    (parentValues : ν → R) (parentZero : commonZeroAt parent parentValues) :
    ∃ (bits : κ → Bool) (childValues : Sum ν κ → R),
      commonZeroAt (childSystem parent coordinates bits) childValues := by
  classical
  let bits : κ → Bool := fun coordinate =>
    if parentValues (coordinates coordinate) = 0 then false else true
  let childValues : Sum ν κ → R := fun
    | .inl v => parentValues v
    | .inr coordinate => (parentValues (coordinates coordinate))⁻¹
  refine ⟨bits, childValues, ?_⟩
  intro equation
  cases equation with
  | inl parentEquation =>
      simpa [childSystem, childValues] using parentZero parentEquation
  | inr coordinate =>
      by_cases zero : parentValues (coordinates coordinate) = 0
      · simp [childSystem, bits, childValues, zero]
      · simp [childSystem, bits, childValues, zero]

/-- If every Boolean child system is empty, then the parent system is empty.
This is the generic semantic connector for an arbitrary carrier arity. -/
theorem parentEmpty_of_allChildrenEmpty
    {ν κ ι R : Type*} [Field R]
    (parent : EquationSystem ν ι R) (coordinates : κ → ν)
    (childrenEmpty : ∀ bits : κ → Bool,
      ¬ hasCommonZero (childSystem parent coordinates bits)) :
    ¬ hasCommonZero parent := by
  rintro ⟨parentValues, parentZero⟩
  obtain ⟨bits, childValues, childZero⟩ :=
    parentCommonZero_extends_to_child parent coordinates parentValues parentZero
  exact childrenEmpty bits ⟨childValues, childZero⟩

/-- The exact arity used by all three-coordinate refinements. -/
theorem parentEmpty_of_eightChildrenEmpty
    {ν ι R : Type*} [Field R]
    (parent : EquationSystem ν ι R) (coordinates : Fin 3 → ν)
    (childrenEmpty : ∀ bits : Fin 3 → Bool,
      ¬ hasCommonZero (childSystem parent coordinates bits)) :
    ¬ hasCommonZero parent :=
  parentEmpty_of_allChildrenEmpty parent coordinates childrenEmpty

end Mettapedia.Algebra.Polynomial.Certificate.EquationSplit

#print axioms Mettapedia.Algebra.Polynomial.Certificate.EquationSplit.parentEmpty_of_eightChildrenEmpty
