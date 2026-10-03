import MettapediaFourColor.ThreeBlockGeometry
import Mettapedia.GraphTheory.Kempe

/-!
# An exterior complementary path enables physical source reconstruction

The geometric separator is consumed by an actual Kempe component. One
switch on the component containing port 7 changes exactly the required
boundary run; the symbolic core law supplies the matching source colouring.
This is uniform in the exterior graph. It assumes the complementary path
exists, and does not assert that every exterior colouring supplies one.
-/

namespace FourColor.ThreeBlockGeometry

open SimpleGraph Mettapedia.GraphTheory.FourColor
open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open SimpleGraphDartRotation FiveTriangleCollapseObstruction ThreeBlockCore
open Color

noncomputable section

private theorem component_walk {W : Type*} {H : SimpleGraph W}
    (C : H.Coloring Color) (a b : Color)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    {u v : W} (hu : u ∈ C.kempeComponentSet a b K)
    (hv : v ∈ C.kempeComponentSet a b K) :
    ∃ walk : H.Walk u v, ∀ w ∈ walk.support, C w = a ∨ C w = b := by
  obtain ⟨hua, huK⟩ := hu
  obtain ⟨hva, hvK⟩ := hv
  obtain ⟨q⟩ := ConnectedComponent.exact (huK.trans hvK.symm)
  let forget : C.bicoloredSubgraph a b →g H := ⟨Subtype.val, fun h => h⟩
  refine ⟨q.map forget, ?_⟩
  intro w hw
  rw [Walk.support_map, List.mem_map] at hw
  obtain ⟨z, _, rfl⟩ := hw
  exact z.property

variable {V W : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W}
  {data : Data G}

/-- Embedded exterior data contains only vertices, edges and boundary
identifications. It contains no colouring or repair assumptions. -/
structure ExteriorReading (s : Patch data) (H : SimpleGraph W) where
  embedding : H ↪g G
  outside : ∀ w, s.Exterior (embedding w)
  ports : Fin 11 → W
  boundary : ∀ j, embedding (ports j) = s.point (j.castAdd 7)

namespace ExteriorReading

variable {s : Patch data} (e : ExteriorReading s H)

theorem port_adj (i j : Fin 11) (h : upper.graph.Adj (i.castAdd 7) (j.castAdd 7)) :
    H.Adj (e.ports i) (e.ports j) := by
  apply e.embedding.map_adj_iff.mp
  rw [e.boundary, e.boundary]
  exact s.adjacent _ _ h

/-- The useful component separation follows from geometry and complementary
colours; it is not an input to the physical switch. -/
theorem excludes_first_runs
    (rotation : VertexRotationCyclic data.toRotationSystem)
    (dual : (interiorDualGraph (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (connected : G.Connected)
    (euler : (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace data.toRotationSystem) = 2)
    (C : H.Coloring Color)
    (p : H.Walk (e.ports 1) (e.ports 6))
    (active : ∀ x ∈ p.support, C x = c1 ∨ C x = c3)
    (K : (C.bicoloredSubgraph c0 c2).ConnectedComponent)
    (tail : e.ports 7 ∈ C.kempeComponentSet c0 c2 K) :
    e.ports 2 ∉ C.kempeComponentSet c0 c2 K ∧
      e.ports 5 ∉ C.kempeComponentSet c0 c2 K := by
  have exclude (i : Fin 11) (which : i = 2 ∨ i = 5)
      (hi : e.ports i ∈ C.kempeComponentSet c0 c2 K) : False := by
    obtain ⟨q, hq⟩ := component_walk C c0 c2 K hi tail
    let P := (p.map e.embedding.toHom).copy (e.boundary 1) (e.boundary 6)
    let Q := (q.map e.embedding.toHom).copy (e.boundary i) (e.boundary 7)
    have image {u v : W} (r : H.Walk u v) {u' v' : V}
        (hu : e.embedding u = u') (hv : e.embedding v = v') (x : V) :
        x ∈ ((r.map e.embedding.toHom).copy hu hv).support ↔
          ∃ y ∈ r.support, e.embedding y = x := by
      simp [Walk.support_copy, Walk.support_map]
    have outsideP : ∀ x ∈ P.support, s.Exterior x := by
      intro x hx
      obtain ⟨y, _, rfl⟩ := (image p _ _ x).mp hx
      exact e.outside y
    have outsideQ : ∀ x ∈ Q.support, s.Exterior x := by
      intro x hx
      obtain ⟨y, _, rfl⟩ := (image q _ _ x).mp hx
      exact e.outside y
    have disjoint : ∀ x ∈ Q.support, x ∉ P.support := by
      intro x hx hp
      obtain ⟨y, hy, ey⟩ := (image q _ _ x).mp hx
      obtain ⟨z, hz, ez⟩ := (image p _ _ x).mp hp
      have same := e.embedding.injective (ey.trans ez.symm)
      subst z
      rcases hq y hy with h | h <;> rcases active y hz with h' | h' <;>
        cases h.symm.trans h'
    exact s.no_crossing_paths rotation dual connected euler P outsideP
      (i.castAdd 7) (by rcases which with rfl | rfl <;> simp) Q outsideQ disjoint
  exact ⟨exclude 2 (Or.inl rfl), exclude 5 (Or.inr rfl)⟩

/-- One genuine component switch produces an exterior colouring agreeing
with a reconstructed D0092 core on every port. -/
theorem repair_of_path
    (rotation : VertexRotationCyclic data.toRotationSystem)
    (dual : (interiorDualGraph (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (connected : G.Connected)
    (euler : (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace data.toRotationSystem) = 2)
    (C : H.Coloring Color)
    (boundary : ∀ j, C (e.ports j) = word false false false j)
    (p : H.Walk (e.ports 1) (e.ports 6))
    (active : ∀ x ∈ p.support, C x = c1 ∨ C x = c3) :
    ∃ D : H.Coloring Color, H.KempeStep C D ∧
      ∃ k : upper.graph.Coloring Color, ∀ j : Fin 11,
        k (j.castAdd 7) = D (e.ports j) := by
  classical
  have b7 : C (e.ports 7) = c0 := boundary 7
  let K := (C.bicoloredSubgraph c0 c2).connectedComponentMk
    ⟨e.ports 7, Or.inl b7⟩
  have m7 : e.ports 7 ∈ C.kempeComponentSet c0 c2 K := C.mem_kempeComponentSet_self (Or.inl b7)
  obtain ⟨n2, n5⟩ := e.excludes_first_runs rotation dual connected euler C p active K m7
  have m8 := C.mem_kempeComponentSet_of_adj m7
    (e.port_adj 7 8 (by decide +kernel)) (Or.inr (boundary 8))
  have m9 := C.mem_kempeComponentSet_of_adj m8
    (e.port_adj 8 9 (by decide +kernel)) (Or.inl (boundary 9))
  have m10 := C.mem_kempeComponentSet_of_adj m9
    (e.port_adj 9 10 (by decide +kernel)) (Or.inr (boundary 10))
  have inactive (j : Fin 11) (hj : j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 ∨ j = 6) :
      e.ports j ∉ C.kempeComponentSet c0 c2 K := by
    intro mem
    have a := C.mem_bicoloredSet_of_mem_kempeComponentSet mem
    rw [boundary] at a
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> cases a <;> contradiction
  have membership : ∀ j : Fin 11,
      e.ports j ∈ C.kempeComponentSet c0 c2 K ↔ 7 ≤ j.val := by
    intro j
    fin_cases j
    · exact iff_of_false (inactive 0 (by simp)) (by decide)
    · exact iff_of_false (inactive 1 (by simp)) (by decide)
    · exact iff_of_false n2 (by decide)
    · exact iff_of_false (inactive 3 (by simp)) (by decide)
    · exact iff_of_false (inactive 4 (by simp)) (by decide)
    · exact iff_of_false n5 (by decide)
    · exact iff_of_false (inactive 6 (by simp)) (by decide)
    · exact iff_of_true m7 (by decide)
    · exact iff_of_true m8 (by decide)
    · exact iff_of_true m9 (by decide)
    · exact iff_of_true m10 (by decide)
  have table : ∀ j : Fin 11,
      (if 7 ≤ j.val then Equiv.swap c0 c2 (word false false false j)
        else word false false false j) = word false false true j := by decide
  let D := C.swapOnKempeComponent c0 c2 K
  have newBoundary : ∀ j, D (e.ports j) = word false false true j := by
    intro j
    change (if e.ports j ∈ C.kempeComponentSet c0 c2 K then
      Equiv.swap c0 c2 (C (e.ports j)) else C (e.ports j)) = _
    simp only [membership, boundary]
    exact table j
  refine ⟨D, H.kempeStep_swapOnKempeComponent C c0 c2 K,
    colouring false false true rfl (by decide), ?_⟩
  intro j
  exact (colouring_boundary false false true rfl (by decide) j).trans (newBoundary j).symm

end ExteriorReading
end
end FourColor.ThreeBlockGeometry
