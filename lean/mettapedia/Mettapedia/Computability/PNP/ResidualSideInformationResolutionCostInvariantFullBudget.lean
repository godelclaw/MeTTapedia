import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCostInvariantPositiveMass

/-!
# Residual side-information resolution cost: full budget

Full orbit-resolving mass and supportwise-correct classifiers over invariant bases.
-/

namespace Mettapedia.Computability.PNP

section

variable {α Base Side : Type*} [Fintype α]

/-- Over an invariant base, full orbit-resolving mass is exactly the same as
supportwise separation of the visible `(base, side)` pair on positive
support. -/
theorem resolvedMass_eq_weightedTotalMass_iff_supportwise_visiblePair_separated_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side) (w : α → ℕ)
    (hbase : ∀ x, base (τ x) = base x) :
    resolvedMass τ side w = weightedTotalMass w ↔
      ∀ x, 0 < w x → (base (τ x), side (τ x)) ≠ (base x, side x) := by
  constructor
  · intro hmass x hxw hpair
    have hsep :=
      (resolvedMass_eq_weightedTotalMass_iff_supportwise_resolving τ side w).1
        hmass x hxw
    exact hsep (congrArg Prod.snd hpair)
  · intro hsep
    exact
      (resolvedMass_eq_weightedTotalMass_iff_supportwise_resolving τ side w).2
        (fun x hxw hside => hsep x hxw (Prod.ext (hbase x) hside))

omit [Fintype α] in
/-- If a classifier on `(base, side)` is correct on every positive-weight point
and the target flips across every positive-weight involution pair, then the
visible pair must separate every supported involution pair. -/
theorem supportwise_visiblePair_separated_of_supportwise_correct_pair
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hy : ∀ x, 0 < w x → y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hcorrect : ∀ x, 0 < w x →
      Correct (fun x => (base x, side x)) y h x) :
    ∀ x, 0 < w x → (base (τ x), side (τ x)) ≠ (base x, side x) := by
  intro x hxw hpair
  have hxwτ : 0 < w (τ x) := by
    simpa [hw x] using hxw
  have hcorr : h (base x, side x) = y x := hcorrect x hxw
  have hcorrτ : h (base (τ x), side (τ x)) = y (τ x) := hcorrect (τ x) hxwτ
  have hsame : y (τ x) = y x := by
    calc
      y (τ x) = h (base (τ x), side (τ x)) := hcorrτ.symm
      _ = h (base x, side x) := by simp [hpair]
      _ = y x := hcorr
  have hflip : y (τ x) = !(y x) := hy x hxw
  rw [hsame] at hflip
  simp at hflip

/-- Under the same supportwise-correctness hypothesis, an invariant-base
residual repair already uses the full support budget as orbit-resolving
mass. -/
theorem resolvedMass_eq_weightedTotalMass_of_supportwise_correct_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, 0 < w x → y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hcorrect : ∀ x, 0 < w x →
      Correct (fun x => (base x, side x)) y h x) :
    resolvedMass τ side w = weightedTotalMass w := by
  exact
    (resolvedMass_eq_weightedTotalMass_iff_supportwise_visiblePair_separated_invariant_base
      τ base side w hbase).2
      (supportwise_visiblePair_separated_of_supportwise_correct_pair
        τ base side y w h hy hw hcorrect)

/-- Under the same supportwise-correctness hypothesis, the doubled advantage of
the visible-pair classifier is exactly the orbit-resolving mass. -/
theorem doubledAdvantage_eq_resolvedMass_of_supportwise_correct_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, 0 < w x → y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hcorrect : ∀ x, 0 < w x →
      Correct (fun x => (base x, side x)) y h x) :
    doubledAdvantage (fun x => (base x, side x)) y w h =
      resolvedMass τ side w := by
  rw [doubledAdvantage_eq_weightedTotalMass_of_supportwise_correct
    (fun x => (base x, side x)) y w h hcorrect]
  exact
    (resolvedMass_eq_weightedTotalMass_of_supportwise_correct_invariant_base
      τ base side y w h hbase hy hw hcorrect).symm

end

end Mettapedia.Computability.PNP
