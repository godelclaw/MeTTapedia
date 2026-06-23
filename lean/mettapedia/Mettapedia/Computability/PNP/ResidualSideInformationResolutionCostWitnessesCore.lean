import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCostBalancingCollapse

/-!
# Residual side-information resolution cost: proof-relevant witnesses

Classifier and same-base residual-witness extraction for residual repair claims.
-/

namespace Mettapedia.Computability.PNP

section

variable {α Base Side : Type*} [Fintype α]

/-- Any existential positive-advantage residual repair over an invariant base
is already proof-relevant: Lean extracts a witness classifier together with
positive resolved mass and a supported same-base residual change. -/
theorem exists_classifier_and_same_base_residual_witness_of_exists_pos_doubledAdvantage_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsuccess : ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) :
    ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x := by
  rcases hsuccess with ⟨h, hadv⟩
  refine ⟨h, hadv, ?_, ?_⟩
  · exact
      resolvedMass_pos_of_pos_doubledAdvantage_pair
        τ base side y w h hτ hbase hy hw hadv
  · exact
      exists_positive_same_base_ne_side_of_pos_doubledAdvantage_invariant_base
        τ base side y w h hτ hbase hy hw hadv

/-- The same proof-relevant extraction works for an existential strict
half-accuracy residual repair claim. -/
theorem exists_classifier_and_same_base_residual_witness_of_exists_total_lt_two_mul_weightedCorrectMass_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x)
    (hsuccess : ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) :
    ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x := by
  rcases hsuccess with ⟨h, hadv⟩
  refine ⟨h, hadv, ?_, ?_⟩
  · exact
      resolvedMass_pos_of_total_lt_two_mul_weightedCorrectMass_pair
        τ base side y w h hτ hbase hy hw hadv
  · exact
      exists_positive_same_base_ne_side_of_total_lt_two_mul_weightedCorrectMass_invariant_base
        τ base side y w h hτ hbase hy hw hadv

/-- Exact minimal proof-relevant boundary: over an invariant base, claiming
that some classifier on `(base, side)` has positive doubled advantage is
equivalent to claiming that some classifier succeeds and thereby exposes a
positive-support same-base residual witness together with positive resolved
mass. -/
theorem exists_pos_doubledAdvantage_iff_exists_classifier_and_same_base_residual_witness_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    (∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) ↔
    ∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x := by
  constructor
  · exact
      exists_classifier_and_same_base_residual_witness_of_exists_pos_doubledAdvantage_invariant_base
        τ base side y w hτ hbase hy hw
  · intro hwitness
    rcases hwitness with ⟨h, hadv, _⟩
    exact ⟨h, hadv⟩

/-- Exact minimal proof-relevant boundary for the strict half-accuracy
formulation. -/
theorem exists_total_lt_two_mul_weightedCorrectMass_iff_exists_classifier_and_same_base_residual_witness_invariant_base
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    (∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h) ↔
    ∃ h : Base × Side → Bool,
      weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      ∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x := by
  constructor
  · exact
      exists_classifier_and_same_base_residual_witness_of_exists_total_lt_two_mul_weightedCorrectMass_invariant_base
        τ base side y w hτ hbase hy hw
  · intro hwitness
    rcases hwitness with ⟨h, hadv, _⟩
    exact ⟨h, hadv⟩

end

end Mettapedia.Computability.PNP
