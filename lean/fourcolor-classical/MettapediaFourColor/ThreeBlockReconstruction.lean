import MettapediaFourColor.ThreeBlockPathRepair

/-!
# Reconstruct the whole map after the complementary-path repair

The exterior covers exactly the vertices outside the seven source-core
vertices. Completeness of each core star prevents unrecorded incident edges.
These geometric conditions turn source/exterior agreement into a colouring
of the entire ambient graph and give a strictly smaller exterior.
-/

namespace FourColor.ThreeBlockGeometry.ExteriorReading

open SimpleGraph Mettapedia.GraphTheory.FourColor
open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open SimpleGraphDartRotation FiveTriangleCollapseObstruction ThreeBlockCore
open Color

variable {V W : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W}
  {data : Data G} {s : Patch data} (e : ExteriorReading s H)

noncomputable section

/-- Exact source stars and exterior coverage suffice for witness gluing. -/
theorem reconstruct {α : Type*}
    (covers : ∀ v, s.Exterior v → ∃ w, e.embedding w = v)
    (stars : ∀ i : Fin 18, 11 ≤ i.val → ∀ v, G.Adj (s.point i) v →
      ∃ j, s.point j = v ∧ upper.graph.Adj i j)
    (D : H.Coloring α) (k : upper.graph.Coloring α)
    (agree : ∀ j : Fin 11, k (j.castAdd 7) = D (e.ports j)) :
    ∃ K : G.Coloring α,
      (∀ w, K (e.embedding w) = D w) ∧ (∀ i, K (s.point i) = k i) := by
  classical
  have core {v : V} (h : ¬s.Exterior v) :
      ∃ i : Fin 18, 11 ≤ i.val ∧ s.point i = v := by
    simp only [Patch.Exterior, not_forall, not_not] at h
    obtain ⟨i, hi, eq⟩ := h
    exact ⟨i, hi, eq.symm⟩
  let f (v : V) : α := if h : s.Exterior v then D (covers v h).choose else k (core h).choose
  have exterior_read (w : W) : f (e.embedding w) = D w := by
    have h := e.outside w
    dsimp only [f]
    rw [dite_eq_left h]
    exact congrArg D (e.embedding.injective (covers _ h).choose_spec)
  have source_read (i : Fin 18) : f (s.point i) = k i := by
    by_cases hi : 11 ≤ i.val
    · have h : ¬s.Exterior (s.point i) := fun hx => hx i hi rfl
      dsimp only [f]
      rw [dite_eq_right h]
      exact congrArg k (s.injective (core h).choose_spec.2)
    · let j : Fin 11 := ⟨i.val, by omega⟩
      have ij : j.castAdd 7 = i := Fin.ext rfl
      calc
        f (s.point i) = f (e.embedding (e.ports j)) := by rw [e.boundary, ij]
        _ = D (e.ports j) := exterior_read _
        _ = k (j.castAdd 7) := (agree j).symm
        _ = k i := by rw [ij]
  have proper : ∀ u v, G.Adj u v → f u ≠ f v := by
    intro u v edge
    by_cases hu : s.Exterior u
    · by_cases hv : s.Exterior v
      · obtain ⟨x, rfl⟩ := covers u hu
        obtain ⟨y, rfl⟩ := covers v hv
        rw [exterior_read, exterior_read]
        exact D.valid (e.embedding.map_adj_iff.mp edge)
      · obtain ⟨i, hi, rfl⟩ := core hv
        obtain ⟨j, rfl, hji⟩ := stars i hi u edge.symm
        rw [source_read, source_read]
        exact (k.valid hji).symm
    · obtain ⟨i, hi, rfl⟩ := core hu
      obtain ⟨j, rfl, hij⟩ := stars i hi v edge
      rw [source_read, source_read]
      exact k.valid hij
  exact ⟨.mk f (fun h => proper _ _ h), exterior_read, source_read⟩

include e in
/-- At least one actual source-core vertex is absent from the exterior. -/
theorem strict_decrease [Fintype W] : Fintype.card W < Fintype.card V := by
  apply Fintype.card_lt_of_injective_of_notMem e.embedding e.embedding.injective
    (b := s.point 11)
  rintro ⟨w, hw⟩
  exact e.outside w 11 (by decide) hw

/-- With complete exterior coverage, exactly the seven source-core vertices
have been removed. No auxiliary vertices are introduced. -/
theorem exact_decrease [Fintype W]
    (covers : ∀ v, s.Exterior v → ∃ w, e.embedding w = v) :
    Fintype.card V = Fintype.card W + 7 := by
  classical
  let assemble : W ⊕ Fin 7 → V := Sum.elim e.embedding (fun i => s.point (i.natAdd 11))
  have injective : Function.Injective assemble := by
    intro x y h
    cases x with
    | inl w =>
      cases y with
      | inl z => exact congrArg Sum.inl (e.embedding.injective h)
      | inr j => exact (e.outside w (j.natAdd 11) (by change 11 ≤ 11 + j.val; omega) h).elim
    | inr i =>
      cases y with
      | inl w => exact (e.outside w (i.natAdd 11) (by change 11 ≤ 11 + i.val; omega) h.symm).elim
      | inr j =>
        have same := s.injective h
        have values := congrArg Fin.val same
        have ij : i = j := Fin.ext (by simpa using values)
        exact congrArg Sum.inr ij
  have surjective : Function.Surjective assemble := by
    intro v
    by_cases h : s.Exterior v
    · obtain ⟨w, hw⟩ := covers v h
      exact ⟨.inl w, hw⟩
    · simp only [Patch.Exterior, not_forall, not_not] at h
      obtain ⟨i, hi, hv⟩ := h
      let j : Fin 7 := ⟨i.val - 11, by omega⟩
      have ji : j.natAdd 11 = i := Fin.ext (by dsimp [j]; omega)
      refine ⟨.inr j, ?_⟩
      change s.point (j.natAdd 11) = v
      rw [ji, hv]
  have cardinal := Fintype.card_congr (Equiv.ofBijective assemble ⟨injective, surjective⟩)
  simpa only [Fintype.card_sum, Fintype.card_fin] using cardinal.symm

/-- A complementary path in the stated boundary class gives an actual
smaller-to-larger colouring repair. The exterior may be arbitrarily large. -/
theorem whole_repair_of_path
    (rotation : VertexRotationCyclic data.toRotationSystem)
    (dual : (interiorDualGraph (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (connected : G.Connected)
    (euler : (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace data.toRotationSystem) = 2)
    (covers : ∀ v, s.Exterior v → ∃ w, e.embedding w = v)
    (stars : ∀ i : Fin 18, 11 ≤ i.val → ∀ v, G.Adj (s.point i) v →
      ∃ j, s.point j = v ∧ upper.graph.Adj i j)
    (C : H.Coloring Color)
    (boundary : ∀ j, C (e.ports j) = word false false false j)
    (p : H.Walk (e.ports 1) (e.ports 6))
    (active : ∀ x ∈ p.support, C x = c1 ∨ C x = c3) :
    ∃ D : H.Coloring Color, H.KempeStep C D ∧
      ∃ K : G.Coloring Color, ∀ w, K (e.embedding w) = D w := by
  obtain ⟨D, step, k, agree⟩ := e.repair_of_path rotation dual connected euler C boundary p active
  obtain ⟨K, read, _⟩ := e.reconstruct covers stars D k agree
  exact ⟨D, step, K, read⟩

end
end FourColor.ThreeBlockGeometry.ExteriorReading
