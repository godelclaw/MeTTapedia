import MettapediaFourColor.VisiblePortRepair
import Mettapedia.GraphTheory.Kempe.IndependentLift

/-!
# A free boundary port joins the paths needed for reconstruction

In the residual three-run case, a one/three path joins ports three and six.
If port two has no exterior neighbour of colour one, a singleton switch
recolours it from two to one. The two boundary edges through that port join
the path to port one. Spherical separation then permits the final zero/two
switch, and a direct core assignment reconstructs the whole map.

The exterior size and the length of the supplied path are unrestricted.
The local neighbour condition is essential to this supplier and is not
asserted for every residual occurrence.
-/

namespace FourColor.ResidualPortPreparation

open SimpleGraph Color ThreeBlockCore FiveTriangleCollapseObstruction
open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open ThreeBlockGeometry

noncomputable section

def preparedWord (j : Fin 11) : Color :=
  if j = 2 then c1 else word false false false j

def assignment : Fin 18 → Color :=
  ![c1,c3,c1,c3,c1,c0,c3,c2,c0,c2,c0,c1,c2,c1,c3,c0,c3,c2]

theorem assignment_proper : ∀ u v, upper.graph.Adj u v → assignment u ≠ assignment v := by
  decide +kernel

def sourceColouring : upper.graph.Coloring Color :=
  .mk assignment (fun h => assignment_proper _ _ h)

theorem boundary_assignment : ∀ j : Fin 11, sourceColouring (j.castAdd 7) =
    if 7 ≤ j.val then Equiv.swap c0 c2 (preparedWord j) else preparedWord j := by
  decide +kernel

variable {W : Type*} {H : SimpleGraph W}

/-- A singleton switch creates the complementary path, while preserving
every vertex of its old three-to-six portion. -/
theorem prepare (C : H.Coloring Color) (ports : Fin 11 → W)
    (injective : Function.Injective ports)
    (edge12 : H.Adj (ports 1) (ports 2)) (edge23 : H.Adj (ports 2) (ports 3))
    (boundary : ∀ j, C (ports j) = word false false false j)
    (free : ∀ x, H.Adj (ports 2) x → C x ≠ c1)
    (p : H.Walk (ports 3) (ports 6))
    (active : ∀ x ∈ p.support, C x = c1 ∨ C x = c3) :
    ∃ D : H.Coloring Color, H.KempeStep C D ∧
      (∀ j, D (ports j) = preparedWord j) ∧
      ∃ q : H.Walk (ports 1) (ports 6),
        ∀ x ∈ q.support, D x = c1 ∨ D x = c3 := by
  classical
  let D : H.Coloring Color := .mk (fun x => if x = ports 2 then c1 else C x) (by
    intro x y edge
    by_cases hx : x = ports 2 <;> by_cases hy : y = ports 2
    · exact (edge.ne (hx.trans hy.symm)).elim
    · subst x
      simpa [hy] using (free y edge).symm
    · subst y
      simpa [hx] using free x edge.symm
    · simpa [hx, hy] using C.valid edge)
  have value (x : W) : D x = if x = ports 2 then c1 else C x := rfl
  have dboundary : ∀ j, D (ports j) = preparedWord j := by
    intro j
    simp only [value, injective.eq_iff, boundary, preparedWord]
  have step : H.KempeStep C D :=
    (KempeIndependentLift.single_vertex (ports 2)
      (fun x hx => by simp [value, hx]) ∅ (by simp)).kempeStep
  let q : H.Walk (ports 1) (ports 6) :=
    .cons edge12
      (.cons edge23 p)
  refine ⟨D, step, dboundary, q, ?_⟩
  intro x hx
  simp only [q, Walk.support_cons, List.mem_cons] at hx
  rcases hx with rfl | rfl | hx
  · exact Or.inr (dboundary 1)
  · exact Or.inl (dboundary 2)
  · have outside : x ≠ ports 2 := by
      intro same
      have col := active x hx
      rw [same, boundary] at col
      cases col <;> contradiction
    simpa only [value, ite_eq_right outside] using active x hx

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {data : Data G} {s : ThreeBlockGeometry.Patch data} (e : ExteriorReading s H)

private theorem ports_injective : Function.Injective e.ports := by
  intro i j eq
  have same : s.point (i.castAdd 7) = s.point (j.castAdd 7) := by
    rw [← e.boundary, ← e.boundary, eq]
  exact Fin.ext (congrArg (fun x : Fin 18 => x.val) (s.injective same))

/-- The new path supplies separation; the final component is not assumed
to have the desired boundary observation. -/
theorem finish
    (rotation : VertexRotationCyclic data.toRotationSystem)
    (dual : (interiorDualGraph (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (connected : G.Connected)
    (euler : (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace data.toRotationSystem) = 2)
    (D : H.Coloring Color) (boundary : ∀ j, D (e.ports j) = preparedWord j)
    (p : H.Walk (e.ports 1) (e.ports 6))
    (active : ∀ x ∈ p.support, D x = c1 ∨ D x = c3) :
    ∃ E : H.Coloring Color, H.KempeStep D E ∧
      ∀ j : Fin 11, sourceColouring (j.castAdd 7) = E (e.ports j) := by
  classical
  have a7 : D (e.ports 7) = c0 ∨ D (e.ports 7) = c2 := Or.inl (boundary 7)
  let K := (D.bicoloredSubgraph c0 c2).connectedComponentMk ⟨e.ports 7, a7⟩
  have m7 : e.ports 7 ∈ D.kempeComponentSet c0 c2 K := D.mem_kempeComponentSet_self a7
  obtain ⟨n2, n5⟩ := e.excludes_first_runs rotation dual connected euler D p active K m7
  have m8 := D.mem_kempeComponentSet_of_adj m7
    (e.port_adj 7 8 (by decide +kernel)) (Or.inr (boundary 8))
  have m9 := D.mem_kempeComponentSet_of_adj m8
    (e.port_adj 8 9 (by decide +kernel)) (Or.inl (boundary 9))
  have m10 := D.mem_kempeComponentSet_of_adj m9
    (e.port_adj 9 10 (by decide +kernel)) (Or.inr (boundary 10))
  have inactive (j : Fin 11) (which : j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 ∨ j = 6) :
      e.ports j ∉ D.kempeComponentSet c0 c2 K := by
    intro member
    have colours := D.mem_bicoloredSet_of_mem_kempeComponentSet member
    rw [boundary] at colours
    rcases which with rfl | rfl | rfl | rfl | rfl <;> cases colours <;> contradiction
  have membership : ∀ j : Fin 11,
      e.ports j ∈ D.kempeComponentSet c0 c2 K ↔ 7 ≤ j.val := by
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
  refine ⟨D.swapOnKempeComponent c0 c2 K,
    H.kempeStep_swapOnKempeComponent D c0 c2 K, ?_⟩
  intro j
  change _ = if e.ports j ∈ D.kempeComponentSet c0 c2 K then
    Equiv.swap c0 c2 (D (e.ports j)) else D (e.ports j)
  simp only [membership, boundary]
  exact boundary_assignment j

/-- Two physical steps and literal whole-map reconstruction, uniformly in
the exterior size. The first step supplies the second one's separator. -/
theorem whole_repair_of_free_port
    (rotation : VertexRotationCyclic data.toRotationSystem)
    (dual : (interiorDualGraph (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (connected : G.Connected)
    (euler : (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace data.toRotationSystem) = 2)
    (covers : ∀ v, s.Exterior v → ∃ w, e.embedding w = v)
    (stars : ∀ i : Fin 18, 11 ≤ i.val → ∀ v, G.Adj (s.point i) v →
      ∃ j, s.point j = v ∧ upper.graph.Adj i j)
    (C : H.Coloring Color) (boundary : ∀ j, C (e.ports j) = word false false false j)
    (free : ∀ x, H.Adj (e.ports 2) x → C x ≠ c1)
    (K : (C.bicoloredSubgraph c1 c3).ConnectedComponent)
    (m3 : e.ports 3 ∈ C.kempeComponentSet c1 c3 K)
    (m6 : e.ports 6 ∈ C.kempeComponentSet c1 c3 K) :
    ∃ D E : H.Coloring Color, H.KempeStep C D ∧ H.KempeStep D E ∧
      ∃ k : G.Coloring Color, ∀ w, k (e.embedding w) = E w := by
  obtain ⟨a3, k3⟩ := m3
  obtain ⟨a6, k6⟩ := m6
  obtain ⟨p⟩ := ConnectedComponent.exact (k3.trans k6.symm)
  let forget : C.bicoloredSubgraph c1 c3 →g H := ⟨Subtype.val, fun h => h⟩
  have active : ∀ x ∈ (p.map forget).support, C x = c1 ∨ C x = c3 := by
    intro x hx
    rw [Walk.support_map, List.mem_map] at hx
    obtain ⟨z, _, rfl⟩ := hx
    exact z.property
  obtain ⟨D, first, bd, q, aq⟩ := prepare C e.ports (ports_injective e)
    (e.port_adj 1 2 (by decide +kernel)) (e.port_adj 2 3 (by decide +kernel))
    boundary free (p.map forget) active
  obtain ⟨E, second, agree⟩ := finish e rotation dual connected euler D bd q aq
  obtain ⟨k, reads, _⟩ := e.reconstruct covers stars E sourceColouring agree
  exact ⟨D,E,first,second,k,reads⟩

/-- Failure of the proved repairs now forces a specific colour-one neighbour
at port two, in addition to the previous residual connectivity. -/
theorem whole_repair_or_neighbor
    (rotation : VertexRotationCyclic data.toRotationSystem)
    (dual : (interiorDualGraph (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (connected : G.Connected)
    (euler : (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace data.toRotationSystem) = 2)
    (covers : ∀ v, s.Exterior v → ∃ w, e.embedding w = v)
    (stars : ∀ i : Fin 18, 11 ≤ i.val → ∀ v, G.Adj (s.point i) v →
      ∃ j, s.point j = v ∧ upper.graph.Adj i j)
    (C : H.Coloring Color) (boundary : ∀ j, C (e.ports j) = word false false false j) :
    (∃ E : H.Coloring Color, E ∈ H.KempeClosure C ∧
      ∃ k : G.Coloring Color, ∀ w, k (e.embedding w) = E w) ∨
    (∃ K : (C.bicoloredSubgraph c1 c3).ConnectedComponent,
      e.ports 6 ∈ C.kempeComponentSet c1 c3 K ∧
      e.ports 3 ∈ C.kempeComponentSet c1 c3 K ∧
      e.ports 1 ∉ C.kempeComponentSet c1 c3 K) ∧
      ∃ x, H.Adj (e.ports 2) x ∧ C x = c1 := by
  classical
  rcases VisiblePortRepair.whole_repair_or_residual e rotation dual connected euler
    covers stars C boundary with repaired | residual
  · obtain ⟨E, step, k, agree⟩ := repaired
    exact Or.inl ⟨E, Relation.ReflTransGen.single step, k, agree⟩
  · by_cases free : ∀ x, H.Adj (e.ports 2) x → C x ≠ c1
    · obtain ⟨K,m6,m3,_⟩ := residual
      obtain ⟨D,E,first,second,k,agree⟩ := whole_repair_of_free_port e rotation dual
        connected euler covers stars C boundary free K m3 m6
      exact Or.inl ⟨E, (Relation.ReflTransGen.single first).trans
        (Relation.ReflTransGen.single second), k, agree⟩
    · exact Or.inr ⟨residual, by simpa using free⟩

end
end FourColor.ResidualPortPreparation
