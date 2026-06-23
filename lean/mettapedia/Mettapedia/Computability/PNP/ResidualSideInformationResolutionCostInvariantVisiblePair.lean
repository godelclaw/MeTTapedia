import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCostInvariantFullBudget

/-!
# Residual side-information resolution cost: visible-pair invariance

Zero and positive orbit-resolving mass characterized as supportwise visible-pair invariance or its failure.
-/

namespace Mettapedia.Computability.PNP

section

variable {α Base Side : Type*} [Fintype α]

/-- Over an invariant base, zero orbit-resolving mass is exactly the same as
supportwise invariance of the visible `(base, side)` pair. -/
theorem resolvedMass_eq_zero_iff_supportwise_visiblePair_invariant_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x) :
    resolvedMass τ side w = 0 ↔
      ∀ x, 0 < w x → (base (τ x), side (τ x)) = (base x, side x) := by
  constructor
  · intro hzero x hxw
    refine Prod.ext (hbase x) ?_
    by_contra hside
    have hmass : 0 < resolvedMass τ side w :=
      resolvedMass_pos_of_resolving_point τ side w hxw hside
    have hnot : ¬ 0 < resolvedMass τ side w := by
      simp [hzero]
    exact (hnot hmass).elim
  · intro hpair
    refine resolvedMass_eq_zero_of_supportwise_unresolved τ side w ?_
    intro x hxw
    exact congrArg Prod.snd (hpair x hxw)

/-- Over an invariant base, positive orbit-resolving mass is exactly the same
as failure of supportwise visible-pair invariance on positive support. -/
theorem pos_resolvedMass_iff_not_supportwise_visiblePair_invariant_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x) :
    0 < resolvedMass τ side w ↔
      ¬ ∀ x, 0 < w x → (base (τ x), side (τ x)) = (base x, side x) := by
  constructor
  · intro hmass hpair
    have hzero :
        resolvedMass τ side w = 0 :=
      (resolvedMass_eq_zero_iff_supportwise_visiblePair_invariant_invariant_base
        τ base side w hbase).2 hpair
    have hnot : ¬ 0 < resolvedMass τ side w := by
      simp [hzero]
    exact (hnot hmass).elim
  · intro hnot
    by_contra hmass
    have hzero : resolvedMass τ side w = 0 := Nat.eq_zero_of_not_pos hmass
    exact hnot
      ((resolvedMass_eq_zero_iff_supportwise_visiblePair_invariant_invariant_base
        τ base side w hbase).1 hzero)

end

end Mettapedia.Computability.PNP
