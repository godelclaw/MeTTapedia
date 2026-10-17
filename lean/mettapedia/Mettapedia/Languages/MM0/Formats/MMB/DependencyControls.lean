import Mettapedia.Languages.MM0.Formats.MMB.Machine

/-!
# Dependency controls for the theorem-variable and dummy-injectivity defects

These exercise the actual MMB transition helpers. The bound slot of `isz x`
must contribute `x` during theorem checking, even though definition dependency
analysis can intentionally bind that slot. A generalization axiom with an
independent formula argument cannot then be instantiated with `isz x`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Formats.MMB.DependencyControls

private def x : ExprType := ⟨0, true, {0}⟩
private def y : ExprType := ⟨0, true, {1}⟩
private def wff : ExprType := ⟨1, false, ∅⟩
private def iszX : ExprType := ⟨1, false, appDeps .assertion [x] wff [x]⟩
private def iszY : ExprType := ⟨1, false, appDeps .assertion [x] wff [y]⟩

theorem theorem_bound_argument_counted : iszX.deps = {0} := by decide
theorem definition_can_bind_argument : appDeps .definition [x] wff [x] = ∅ := by decide
theorem invalid_generalization_rejected : thmArgsDisjoint [x, wff] [x, iszX] = false := by decide
theorem independent_generalization_accepted : thmArgsDisjoint [x, wff] [x, iszY] = true := by decide
theorem reverse_formal_order_still_rejected : thmArgsDisjoint [wff, x] [iszX, x] = false := by decide
theorem declared_dependency_is_accepted : thmArgsDisjoint [x, ⟨1, false, {0}⟩] [x, iszX] = true := by decide

/-- Omitting the bound-slot dependency is exactly enough to hide the violation. -/
theorem omitted_dependency_would_accept : thmArgsDisjoint [x, wff] [x, wff] = true := by decide

private def store : List Alloc := [⟨.var 0, x⟩, ⟨.var 1, y⟩, ⟨.app 0 [0, 1], ⟨1, false, {0, 1}⟩⟩]

theorem collapsed_dummy_rejected :
    unifyStep store .definition ⟨[0], [(0, false)], [], []⟩ (.dummy 0) = none := by decide

/-- A saved compound term is not an earlier dummy. Its presence cannot veto
the distinct dummy already occurring inside that saved term. -/
theorem saved_terms_do_not_create_dummy_conflicts :
    (unifyStep store .definition ⟨[1], [(0, false), (2, true)], [], []⟩ (.dummy 0)).isSome = true := by decide

end Mettapedia.Languages.MM0.Formats.MMB.DependencyControls
