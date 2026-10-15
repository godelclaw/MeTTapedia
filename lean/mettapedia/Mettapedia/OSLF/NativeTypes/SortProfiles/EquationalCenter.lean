import Mettapedia.OSLF.Framework.ModalHypercube
import Mettapedia.UniversalAlgebra.BoundedTerm
import Mettapedia.UniversalAlgebra.EquationalLogic
import Mathlib.Data.Fintype.Sigma

open Mettapedia.OSLF.Framework

/-!
# Finite sort-algebra admission for generated type systems

The equation test enumerates every two-valued valuation of each displayed
equation. Stability is independently specified by all substitution instances
and congruence consequences of the equations. Their equality therefore includes
equation detours, rather than only the displayed examples.

A local input/output profile and an operation's truth table are different data.
`TableSlot` makes the latter explicit: there is one output entry per input
valuation. No uninterpreted equation is silently discarded.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter

open Mettapedia.UniversalAlgebra
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)

variable (S : Signature.{0})

/-- Entries of the finite two-valued operation tables of a signature. -/
abbrev TableSlot := Σ operation : S.Operation, Fin (S.arity operation) → HSort

/-- A complete sort interpretation, with every input case represented. -/
abbrev Vertex := TableSlot S → HSort

/-- The independently specified universal-algebra model read from the tables. -/
def model (vertex : Vertex S) : Model S HSort where
  interpret operation arguments := vertex ⟨operation, arguments⟩

variable {S}

def contextBound (equation : Equation S) : Nat :=
  equation.1.variableBound + equation.2.variableBound

theorem left_bounded (equation : Equation S) :
    equation.1.VariablesBelow (contextBound equation) :=
  equation.1.variablesBelow_variableBound.mono (Nat.le_add_right _ _)

theorem right_bounded (equation : Equation S) :
    equation.2.VariablesBelow (contextBound equation) :=
  equation.2.variablesBelow_variableBound.mono (Nat.le_add_left _ _)

/-- The actual finite computation of one equation's universal valuation test. -/
def checkEquation (vertex : Vertex S) (equation : Equation S) : Bool :=
  decide (∀ valuation : Fin (contextBound equation) → HSort,
    equation.1.evaluateBelow (model S vertex) valuation (left_bounded equation) =
      equation.2.evaluateBelow (model S vertex) valuation (right_bounded equation))

private def extend {bound : Nat} (valuation : Fin bound → HSort) : Nat → HSort :=
  fun index => if below : index < bound then valuation ⟨index, below⟩ else .star

/-- Finite valuation enumeration has exactly the universal equation meaning. -/
theorem checkEquation_iff (vertex : Vertex S) (equation : Equation S) :
    checkEquation vertex equation = true ↔ equation.Holds (model S vertex) := by
  constructor
  · intro checked valuation
    have equality := of_decide_eq_true checked
      (fun index : Fin (contextBound equation) => valuation index.val)
    rw [Term.evaluateBelow_eq_evaluate (agrees := fun _ _ => rfl),
      Term.evaluateBelow_eq_evaluate (agrees := fun _ _ => rfl)] at equality
    exact equality
  · intro holds
    apply decide_eq_true
    intro valuation
    rw [Term.evaluateBelow_eq_evaluate (totalValuation := extend valuation)
        (agrees := fun _ below => by simp only [extend, below, dite_true]),
      Term.evaluateBelow_eq_evaluate (totalValuation := extend valuation)
        (agrees := fun _ below => by simp only [extend, below, dite_true])]
    exact holds _

/-- Checking a finite authored equation system is executable. -/
def check (system : EquationSystem S) (vertex : Vertex S) : Bool :=
  system.equations.all (checkEquation vertex)

/-- An equation-stable sort interpretation must respect every generated
equational consequence, including substitution and operation contexts. -/
def Stable (system : EquationSystem S) (vertex : Vertex S) : Prop :=
  ∀ equation, EquationalConsequence system equation → equation.Holds (model S vertex)

theorem stable_iff_satisfies (system : EquationSystem S) (vertex : Vertex S) :
    Stable system vertex ↔ (model S vertex).Satisfies system := by
  constructor
  · intro stable equation member
    apply stable equation
    have derivation := Mettapedia.Logic.Derives.node [] _
      (EquationalRule.systemInstance member Term.var)
      (by intro premise absent; cases absent)
    change Mettapedia.Logic.Derives (EquationalRule system) equation
    simpa only [Term.subst_variables, Prod.mk.eta] using derivation
  · intro satisfies equation derivation
    exact derivation.holdsInModel (model S vertex) satisfies

/-- No admissibility predicate is a supplied field: it is earned by this test. -/
theorem check_iff_stable (system : EquationSystem S) (vertex : Vertex S) :
    check system vertex = true ↔ Stable system vertex := by
  rw [stable_iff_satisfies]
  constructor
  · intro checked equation member
    exact (checkEquation_iff vertex equation).mp (List.all_eq_true.mp checked equation member)
  · intro satisfies
    exact List.all_eq_true.mpr fun equation member =>
      (checkEquation_iff vertex equation).mpr (satisfies equation member)

variable [Fintype S.Operation] [DecidableEq S.Operation]

/-- The finite solution set computed from the actual equation system. -/
def center (system : EquationSystem S) : Finset (Vertex S) :=
  Finset.univ.filter fun vertex => check system vertex = true

theorem mem_center_iff (system : EquationSystem S) (vertex : Vertex S) :
    vertex ∈ center system ↔ Stable system vertex := by
  simp only [center, Finset.mem_filter, Finset.mem_univ, true_and, check_iff_stable]

/-- With no equations, every operation table is admitted, for every signature. -/
theorem no_equations_center (system : EquationSystem S) (empty : system.equations = []) :
    center system = Finset.univ := by
  simp [center, check, empty]

theorem respects_substitution (system : EquationSystem S) (vertex : Vertex S)
    (member : vertex ∈ center system) {equation : Equation S}
    (derivation : EquationalConsequence system equation) (substitution : Nat → Term S)
    (valuation : Nat → HSort) :
    (equation.1.subst substitution).evaluate (model S vertex) valuation =
      (equation.2.subst substitution).evaluate (model S vertex) valuation := by
  rw [Term.evaluate_subst, Term.evaluate_subst]
  exact (mem_center_iff system vertex).mp member equation derivation _

/-- A variable permutation does not change the center. -/
def rename (permutation : Nat ≃ Nat) (system : EquationSystem S) : EquationSystem S where
  equations := system.equations.map fun equation =>
    (equation.1.subst (fun index => .var (permutation index)),
      equation.2.subst (fun index => .var (permutation index)))

omit [Fintype S.Operation] [DecidableEq S.Operation] in
theorem renamed_equation_iff (permutation : Nat ≃ Nat) (vertex : Vertex S)
    (equation : Equation S) :
    Equation.Holds (model S vertex)
      (equation.1.subst (fun index => .var (permutation index)),
        equation.2.subst (fun index => .var (permutation index))) ↔
        equation.Holds (model S vertex) := by
  constructor
  · intro holds valuation
    have equal := holds (fun index => valuation (permutation.symm index))
    simpa only [Term.evaluate_subst, Term.evaluate, Equiv.symm_apply_apply] using equal
  · intro holds valuation
    simp only [Term.evaluate_subst, Term.evaluate]
    exact holds (fun index => valuation (permutation index))

theorem center_rename (permutation : Nat ≃ Nat) (system : EquationSystem S) :
    center (rename permutation system) = center system := by
  ext vertex
  rw [mem_center_iff, mem_center_iff, stable_iff_satisfies, stable_iff_satisfies]
  constructor
  · intro satisfies equation member
    exact (renamed_equation_iff permutation vertex equation).mp
      (satisfies _ (List.mem_map.mpr ⟨equation, member, rfl⟩))
  · intro satisfies equation member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact (renamed_equation_iff permutation vertex original).mpr
      (satisfies original originalMember)

end Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter
