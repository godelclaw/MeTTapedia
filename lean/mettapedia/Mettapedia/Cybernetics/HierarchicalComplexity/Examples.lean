import Mettapedia.Cybernetics.HierarchicalComplexity.Finite

/-!
# Commons--Pekker chain and coordination examples

Commons and Pekker, *Presenting the Formal Theory of Hierarchical Complexity*
(2008), pp. 376--377: Example A independently computes `(3, 12)`; Example C
observes `14` or `10` according to operation order. Their arithmetic readouts
are defined independently of their finite-action interpretations below.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.HierarchicalComplexity.SourceExamples

open HierarchicalComplexity

/-! ## Example A: two independent arithmetic actions -/

/-- Independent result slots for Example A's addition and multiplication. -/
def exampleAInitial : Nat × Nat := (0, 0)

/-- Execute `1 + 2`, leaving the multiplication component unchanged. -/
def exampleAAddition (state : Nat × Nat) : Nat × Nat :=
  (1 + 2, state.2)

/-- Execute `3 * 4`, leaving the addition component unchanged. -/
def exampleAMultiplication (state : Nat × Nat) : Nat × Nat :=
  (state.1, 3 * 4)

/-- Execute Example A in the supplied binary schedule. -/
def exampleASemantics : ScheduleSemantics (Fin 2) (Nat × Nat) :=
  fun schedule =>
    if schedule 0 = 0 then
      exampleAMultiplication (exampleAAddition exampleAInitial)
    else
      exampleAAddition (exampleAMultiplication exampleAInitial)

theorem exampleASemantics_eq (schedule : Schedule (Fin 2)) :
    exampleASemantics schedule = (3, 12) := by
  simp [exampleASemantics, exampleAInitial, exampleAAddition,
    exampleAMultiplication]

/-- Commons and Pekker's Example A is a chain by permutation invariance. -/
theorem exampleA_isChain : IsChain exampleASemantics := by
  intro first second
  rw [exampleASemantics_eq first, exampleASemantics_eq second]

def exampleAOrganization : Organization (Fin 2) (Nat × Nat) :=
  .chain exampleASemantics exampleA_isChain

/-- Example A as a finite Commons action with two simple children. -/
def exampleAAction : Finite.Action.{0, 0} (Nat × Nat) :=
  Finite.Action.chain LimitCanary.binary_hasAtLeastTwo
    (fun _ => Finite.Action.simple (Nat × Nat))
    exampleASemantics exampleA_isChain

/-- Example A's independent scheduling preserves order zero. -/
theorem exampleA_order : exampleAAction.order = 0 := by
  apply (Finite.Action.order_eq_iff _ _).mpr
  change (⨆ _ : Fin 2, (0 : Ordinal)) = 0
  exact ciSup_const

/-! ## Example C: order-sensitive arithmetic -/

/-- Example C's two execution orders compute `2*(3+4)` and `(2*3)+4`. -/
def exampleCSemantics : ScheduleSemantics (Fin 2) Nat :=
  fun schedule =>
    if schedule 0 = 0 then 2 * (3 + 4) else 2 * 3 + 4

@[simp] theorem exampleC_additionFirst : exampleCSemantics (Equiv.refl (Fin 2)) = 14 := by
  simp [exampleCSemantics]

@[simp] theorem exampleC_multiplicationFirst :
    exampleCSemantics (Equiv.swap (0 : Fin 2) 1) = 10 := by
  simp [exampleCSemantics]

/-- The identity and swap schedules distinguish Example C's outcomes. -/
theorem exampleC_isCoordination : IsCoordination exampleCSemantics := by
  refine ⟨Equiv.refl (Fin 2), Equiv.swap 0 1, ?_⟩
  simp

def exampleCOrganization : Organization (Fin 2) Nat :=
  .coordination exampleCSemantics exampleC_isCoordination

/-- Example C as a finite Commons action with two simple children. -/
def exampleCAction : Finite.Action.{0, 0} Nat :=
  Finite.Action.coordination LimitCanary.binary_hasAtLeastTwo
    (fun _ => Finite.Action.simple Nat)
    exampleCSemantics exampleC_isCoordination
    (fun _ _ => rfl)

theorem exampleC_order : exampleCAction.order = 1 := by
  apply (Finite.Action.order_eq_iff _ _).mpr
  change Order.succ (⨆ _ : Fin 2, (0 : Ordinal)) = ((1 : Nat) : Ordinal)
  simp only [ciSup_const, Order.succ_eq_add_one, zero_add, Nat.cast_one]

end Mettapedia.Cybernetics.HierarchicalComplexity.SourceExamples
