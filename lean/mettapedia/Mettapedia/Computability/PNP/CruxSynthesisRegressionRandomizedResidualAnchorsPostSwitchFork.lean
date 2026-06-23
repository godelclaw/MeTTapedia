import Mettapedia.Computability.PNP.CruxRandomizedResidualAnchorsPostSwitchFork

/-!
# Regression checks for randomized-residual post-switch fork anchors

Regression wrappers for post-switch fork b-resolution and nonzero-column witness anchors.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem post_switch_fork_anchor_positive_advantage_b_resolution_witness_regression
    {Z : Type*} [Fintype Z] {k : ℕ}
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv : 0 < doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h) :
    ∃ u : PostSwitchInput Z k, 0 < w u ∧ (tiInputMap u).b ≠ u.b := by
  exact
    postSwitchForkCoverage_anchor_positive_advantage_b_resolution_witness
      y w h hy hw hadv

theorem post_switch_fork_anchor_positive_advantage_nonzero_column_witness_regression
    {Z : Type*} [Fintype Z] {k : ℕ}
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv : 0 < doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h) :
    ∃ u : PostSwitchInput Z k, 0 < w u ∧ nonzeroColumn u.a := by
  exact
    postSwitchForkCoverage_anchor_positive_advantage_nonzeroColumn_witness
      y w h hy hw hadv

end Mettapedia.Computability.PNP.CruxSynthesisRegression
