import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Fintype.Card

/-!
# Adaptive covers with a uniform cardinality bound

A fixed compact target set has a finite metric net. For each map into that
set, choose one actual source point from every occupied net ball. These
source points give an adaptive cover with cardinality bounded independently
of the map, its oscillation, or a modulus of continuity. The source need not
carry a topology. The target range and tolerance determine the bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.CompactRangeCover

theorem exists_uniform_card_cover {X E : Type*} [PseudoMetricSpace E]
    (K : Set E) (hK : IsCompact K) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ M : ℕ, 0 < M ∧ ∀ A : X → E, (∀ x, A x ∈ K) →
      ∃ centers : Finset X, centers.card ≤ M ∧
        ∀ x, ∃ y ∈ centers, dist (A x) (A y) < epsilon := by
  classical
  obtain ⟨t, _, ht, hcover⟩ := hK.finite_cover_balls (show 0 < epsilon / 2 by positivity)
  let net := ht.toFinset
  refine ⟨net.card + 1, by omega, ?_⟩
  intro A hA
  let occupied := net.filter (fun b ↦ ∃ x, dist (A x) b < epsilon / 2)
  have hex (b : ↑occupied) : ∃ x, dist (A x) b.1 < epsilon / 2 :=
    (Finset.mem_filter.mp b.2).2
  let point : ↑occupied → X := fun b ↦ (hex b).choose
  have hpoint (b : ↑occupied) : dist (A (point b)) b.1 < epsilon / 2 := (hex b).choose_spec
  let centers := occupied.attach.image point
  refine ⟨centers, ?_, ?_⟩
  · calc
      centers.card ≤ occupied.attach.card := Finset.card_image_le
      _ = occupied.card := Finset.card_attach
      _ ≤ net.card := Finset.card_filter_le _ _
      _ ≤ net.card + 1 := Nat.le_succ _
  · intro x
    obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.mp (hcover (hA x))
    have hx : dist (A x) b < epsilon / 2 := hxb
    have hb' : b ∈ occupied := Finset.mem_filter.mpr ⟨ht.mem_toFinset.mpr hb, x, hx⟩
    let j : ↑occupied := ⟨b, hb'⟩
    refine ⟨point j, Finset.mem_image.mpr ⟨j, Finset.mem_attach _ _, rfl⟩, ?_⟩
    calc
      dist (A x) (A (point j)) ≤ dist (A x) b + dist b (A (point j)) := dist_triangle _ _ _
      _ < epsilon / 2 + epsilon / 2 := add_lt_add hx (by simpa only [dist_comm] using hpoint j)
      _ = epsilon := by ring

/-- Properness converts a common norm bound into a common adaptive cover-size bound. -/
theorem exists_uniform_card_norm_cover {X E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (R epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ M : ℕ, 0 < M ∧ ∀ A : X → E, (∀ x, ‖A x‖ ≤ R) →
      ∃ centers : Finset X, centers.card ≤ M ∧
        ∀ x, ∃ y ∈ centers, ‖A x - A y‖ < epsilon := by
  obtain ⟨M, hM, h⟩ := exists_uniform_card_cover (X := X)
    (Metric.closedBall (0 : E) R) (isCompact_closedBall _ _) epsilon hepsilon
  refine ⟨M, hM, ?_⟩
  intro A hA
  have hball : ∀ x, A x ∈ Metric.closedBall (0 : E) R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hA
  simpa only [dist_eq_norm] using h A hball

end Mettapedia.Analysis.CompactRangeCover
