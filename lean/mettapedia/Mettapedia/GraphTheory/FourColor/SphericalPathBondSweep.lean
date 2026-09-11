import Mettapedia.GraphTheory.FourColor.SphericalCanonicalTerminalBonds

/-!
# Full optimal interfaces along an embedded path

Split the vertices of an actual simple path into a nonempty prefix and
suffix. Finite minimization constructs a complete cut extending this split;
every other vertex, including cap material, may change sides. The resulting
cuts are connected planar bonds and strictly nest on the full edge shores.

A complete contour cycle supplies the path by removing its first edge:
`Walk.IsCycle.isPath_tail`. No terminal-connectivity or cut-supply premise
is needed. The actual minimum widths are not asserted uniformly bounded,
and no colour-state repetition or shortening is inferred.
-/

namespace Mettapedia.GraphTheory.FourColor.SphericalPathBondSweep

open SimpleGraph SimpleGraphDartRotation CanonicalTerminalCuts
open SphericalCanonicalTerminalBonds GoertzelV24RotationMultigraphAdapter
open GoertzelV24TwoEdgeCutMinimality GoertzelV24OrbitFaceTwoSided
open GoertzelV24ComplementaryRegionBoundaryOrder GoertzelV24DeletedRegionRotationSplice
open GoertzelV24RetainedRegionBoundaryOrder GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24ConnectedVertexSideEdgeShore

noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G

def prefixSide (p : G.Walk u v) (t : Nat) : Finset V := (p.support.take (t + 1)).toFinset
def suffix (p : G.Walk u v) (t : Nat) : Finset V := (p.support.drop (t + 1)).toFinset

omit [Fintype V] [DecidableRel G.Adj] in
theorem prefix_connected (p : G.Walk u v) (t : Nat) :
    (G.induce (↑(prefixSide p t) : Set V)).Connected := by
  have heq : {x | x ∈ (p.take t).support} = (↑(prefixSide p t) : Set V) := by
    ext x
    simp [prefixSide, Walk.support_take]
  exact heq ▸ (p.take t).connected_induce_support

omit [Fintype V] [DecidableRel G.Adj] in
theorem suffix_connected (p : G.Walk u v) {t : Nat} (ht : t < p.length) :
    (G.induce (↑(suffix p t) : Set V)).Connected := by
  have heq : {x | x ∈ (p.drop (t + 1)).support} = (↑(suffix p t) : Set V) := by
    ext x
    simp [suffix, Walk.drop_support_eq_support_drop_min, Nat.min_eq_left (by omega : t + 1 ≤ p.length)]
  exact heq ▸ (p.drop (t + 1)).connected_induce_support

omit [Fintype V] [DecidableRel G.Adj] in
theorem terminals_disjoint (p : G.Walk u v) (hp : p.IsPath) (t : Nat) :
    Disjoint (prefixSide p t) (suffix p t) := by
  have h := List.disjoint_take_drop hp.support_nodup (Nat.le_refl (t + 1))
  simpa [prefixSide, suffix, Finset.disjoint_left, List.disjoint_left] using h

omit [Fintype V] [DecidableRel G.Adj] in
theorem prefix_mono (p : G.Walk u v) {i j : Nat} (hij : i ≤ j) :
    prefixSide p i ⊆ prefixSide p j := by
  intro x hx
  simp only [prefixSide, List.mem_toFinset] at hx ⊢
  exact List.take_subset_take_left p.support (by omega) hx

omit [Fintype V] [DecidableRel G.Adj] in
theorem suffix_antitone (p : G.Walk u v) {i j : Nat} (hij : i ≤ j) :
    suffix p j ⊆ suffix p i := by
  intro x hx
  simp only [suffix, List.mem_toFinset] at hx ⊢
  exact List.drop_subset_drop_left p.support (by omega) hx

omit [Fintype V] [DecidableRel G.Adj] in
theorem terminal_moves (p : G.Walk u v) {i j : Nat} (hij : i < j) (hj : j < p.length) :
    ∃ x, x ∈ suffix p i ∧ x ∈ prefixSide p j := by
  have hi : i + 1 < p.support.length := by simp only [Walk.length_support]; omega
  refine ⟨p.support[i + 1], ?_, ?_⟩
  · simp only [suffix, List.mem_toFinset, List.mem_drop_iff_getElem]
    exact ⟨0, by omega, by simp⟩
  · simp only [prefixSide, List.mem_toFinset, List.mem_take_iff_getElem]
    exact ⟨i + 1, by omega, rfl⟩

/-- The sweep is constructed, with no off-path cap ownership prescribed. -/
def side (data : Data G) (p : G.Walk u v) (hp : p.IsPath) (t : Fin p.length) : Finset V :=
  canonical (toMultigraph data.toRotationSystem) (prefixSide p t) (suffix p t)
    (terminals_disjoint p hp t)

/-- Complete connected interfaces and their opposite first-return orders. -/
theorem side_spec (data : Data G)
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (p : G.Walk u v) (hp : p.IsPath) (t : Fin p.length) :
    IsCanonical (toMultigraph data.toRotationSystem) (prefixSide p t) (suffix p t) (side data p hp t) ∧
    (G.induce (↑(side data p hp t) : Set V)).Connected ∧
    (G.induce (↑(side data p hp t)ᶜ : Set V)).Connected ∧
    CutFacesHaveUniqueRetainedBoundaryDart data.toRotationSystem (side data p hp t)ᶜ ∧
    retainedRegionBoundarySuccessor data.toRotationSystem (deletedRegionKeep (side data p hp t)ᶜ) =
      (deletedRegionBoundarySuccessor data.toRotationSystem (side data p hp t)ᶜ)⁻¹ := by
  have hc := connected_sides data ambient _ _ (prefix_connected p t)
    (suffix_connected p t.isLt) (terminals_disjoint p hp t)
  have ho := full_boundary_orders data ambient htwo _ _ (prefix_connected p t)
    (suffix_connected p t.isLt) (terminals_disjoint p hp t)
  exact ⟨canonical_spec _ _ _ _, hc.1, hc.2, ho.1, ho.2⟩

/-- Every advancing split strictly grows the full original incident-edge shore. -/
theorem side_strict (data : Data G)
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (p : G.Walk u v) (hp : p.IsPath) {i j : Fin p.length} (hij : i < j) :
    side data p hp i ⊂ side data p hp j ∧
      incidentEdgeShore G (· ∈ side data p hp i) ⊂ incidentEdgeShore G (· ∈ side data p hp j) :=
  full_shores_strict data ambient (prefix_connected p i) (suffix_connected p i.isLt)
    (suffix_connected p j.isLt) (terminals_disjoint p hp i) (terminals_disjoint p hp j)
    (prefix_mono p (Nat.le_of_lt hij)) (suffix_antitone p (Nat.le_of_lt hij))
    (terminal_moves p hij j.isLt)

end
end Mettapedia.GraphTheory.FourColor.SphericalPathBondSweep
