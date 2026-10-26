import Mathlib.SetTheory.Cardinal.Arithmetic
import Mettapedia.Cybernetics.HierarchicalComplexity.Finite

/-!
# Infinite branching and the boundary of the finite `phi` law

Finite order `n` has minimum leaf count `2^n`. The countable limit chain
instead has rank `omega` and only `aleph0` leaves, strictly below `2^aleph0`.
This is a boundary control, not a Commons--Pekker transfinite claim.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.HierarchicalComplexity

open LimitCanary

namespace InfiniteCanary

/-- The binary finite-order tower has exactly `2^n` simple leaves before
taking the natural-cardinality readout. -/
theorem simpleLeafCardinal_finiteTower (n : Nat) :
    Action.simpleLeafCardinal (finiteTower n) = (2 : Cardinal) ^ n := by
  let : _root_.Finite (Action.SimpleLeaves (finiteTower n)) :=
    Action.finite_simpleLeaves (finiteTower n)
      (Finite.Phi.finitelyBranching_finiteTower n)
  rw [Action.simpleLeafCardinal]
  rw [← Nat.cast_card]
  simp only [Finite.Phi.natCard_simpleLeaves_finiteTower, Nat.cast_pow,
    Nat.cast_ofNat]

/-- The limit chain is not finitely branching; hence the finite `phi` theorem
cannot be applied to it. -/
theorem limitChain_not_finitelyBranching : ¬ Action.FinitelyBranching limitChain := by
  intro finite
  simpa only [rank_limitChain, lt_self_iff_false] using
    Action.rank_lt_omega0_of_finitelyBranching limitChain finite

/-- The countable family of finite towers has exactly countably many simple
leaves. -/
theorem simpleLeafCardinal_limitChain : Action.simpleLeafCardinal limitChain = Cardinal.aleph0 := by
  rw [limitChain, Action.simpleLeafCardinal_compound]
  simp_rw [simpleLeafCardinal_finiteTower]
  rw [Cardinal.sum_pow_eq_max_aleph0]
  · simp
  · exact two_ne_zero

/-- Naively replacing the finite exponent in `phi n = 2^n` by cardinal
exponentiation at the limit gives the wrong answer for this chain. -/
theorem simpleLeafCardinal_limitChain_lt_two_power_aleph0 : Action.simpleLeafCardinal limitChain <
      (2 : Cardinal) ^ Cardinal.aleph0 := by
  rw [simpleLeafCardinal_limitChain]
  exact Cardinal.cantor Cardinal.aleph0

end InfiniteCanary

end Mettapedia.Cybernetics.HierarchicalComplexity
