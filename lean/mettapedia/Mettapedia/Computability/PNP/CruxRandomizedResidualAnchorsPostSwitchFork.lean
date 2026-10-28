import Mettapedia.Computability.PNP.PostSwitchForkObstruction

/-!
# PNP randomized-residual anchors: post-switch fork

Exact post-switch fork anchors exposing retained-b and nonzero-column witnesses from strict half-accuracy advantage.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: positive advantage from the exact post-switch
classifier on `((z, a_i), b)` exposes a positive-weight input where the
`b` side channel changes under the manuscript involution. -/
theorem postSwitchForkCoverage_anchor_positive_advantage_b_resolution_witness
    {Z : Type*} [Fintype Z] {k : ℕ}
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv : 0 < doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h) :
    ∃ u : PostSwitchInput Z k, 0 < w u ∧ (tiInputMap u).b ≠ u.b :=
  exists_b_resolving_input_of_pos_doubledAdvantage_invariantProjection_with_b
    y w h hy hw hadv

/-- Route-coverage anchor: positive advantage from the exact post-switch
classifier on `((z, a_i), b)` exposes a positive-weight nonzero `a_i` column. -/
theorem postSwitchForkCoverage_anchor_positive_advantage_nonzeroColumn_witness
    {Z : Type*} [Fintype Z] {k : ℕ}
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv : 0 < doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h) :
    ∃ u : PostSwitchInput Z k, 0 < w u ∧ nonzeroColumn u.a :=
  exists_nonzeroColumn_of_pos_doubledAdvantage_invariantProjection_with_b
    y w h hy hw hadv

/-- Route-coverage anchor: strict half-accuracy advantage from the exact
post-switch classifier on `((z, a_i), b)` exposes a positive-weight input
where the retained `b` side channel changes under the manuscript involution. -/
theorem postSwitchForkCoverage_anchor_strict_half_advantage_b_resolution_witness
    {Z : Type*} [Fintype Z] {k : ℕ}
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun u => (invariantProjection u, u.b)) y w h) :
    ∃ u : PostSwitchInput Z k, 0 < w u ∧ (tiInputMap u).b ≠ u.b :=
  exists_b_resolving_input_of_total_lt_two_mul_weightedCorrectMass_invariantProjection_with_b
    y w h hy hw hadv

/-- Route-coverage anchor: strict half-accuracy advantage from the exact
post-switch classifier on `((z, a_i), b)` exposes a positive-weight input on
a nonzero `a_i` column. -/
theorem postSwitchForkCoverage_anchor_strict_half_advantage_nonzeroColumn_witness
    {Z : Type*} [Fintype Z] {k : ℕ}
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun u => (invariantProjection u, u.b)) y w h) :
    ∃ u : PostSwitchInput Z k, 0 < w u ∧ nonzeroColumn u.a :=
  exists_nonzeroColumn_of_total_lt_two_mul_weightedCorrectMass_invariantProjection_with_b
    y w h hy hw hadv

/-- Route-coverage anchor: strict half-accuracy advantage from the exact
post-switch classifier on `((z, a_i), b)` already lands on the fork
obstruction surface.  It simultaneously exposes a positive-weight
`b`-resolving input, a positive-weight nonzero `a_i` column, and refutes the
manuscript's exact-input-invariant support premise. -/
theorem postSwitchForkCoverage_anchor_strict_half_advantage_fork_obstruction_package
    {Z : Type*} [Fintype Z] {k : ℕ}
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u)
    (hadv :
      weightedTotalMass w <
        2 * weightedCorrectMass (fun u => (invariantProjection u, u.b)) y w h) :
    (∃ u : PostSwitchInput Z k, 0 < w u ∧ (tiInputMap u).b ≠ u.b) ∧
      (∃ u : PostSwitchInput Z k, 0 < w u ∧ nonzeroColumn u.a) ∧
      ¬ exactInputInvariantWeightedSupport w := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      postSwitchForkCoverage_anchor_strict_half_advantage_b_resolution_witness
        y w h hy hw hadv
  · exact
      postSwitchForkCoverage_anchor_strict_half_advantage_nonzeroColumn_witness
        y w h hy hw hadv
  · exact
      not_exactInputInvariantWeightedSupport_of_total_lt_two_mul_weightedCorrectMass_invariantProjection_with_b
        y w h hy hw hadv

end Mettapedia.Computability.PNP
