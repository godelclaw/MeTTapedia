import Mettapedia.GraphTheory.FourColor.ElevenLobeNormalizedGeometry

/-!
# Actual darts of the eleven-cycle and its inner pentagon

These coordinates retain all sixteen vertices, all forty-eight incident
darts and the six exposed half-edges. Cubicity excludes extra internal
attachments. Exterior endpoints need not be distinct.
-/

namespace Mettapedia.GraphTheory.FourColor.ElevenLobeSpokeOrder

open SimpleGraph SimpleGraphDartRotation CubicCycleIncidence CycleBoundaryOrientation
open GoertzelV24RotationCutDartDecomposition GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24ComplementaryShoreBoundaryOrder GoertzelV24DeletedRegionRotationSplice

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Coordinate
abbrev Vertex := Fin 11 ⊕ Fin 5
abbrev Dart := (Fin 11 × Fin 3) ⊕ (Fin 5 × Fin 3)

def vertex : Dart → Vertex := Sum.map Prod.fst Prod.fst

def boundary : Dart → Prop
  | .inl (i, s) => reverseAt i = true ∧ s = 0
  | .inr _ => False

instance : DecidablePred boundary := fun d => by cases d <;> unfold boundary <;> infer_instance

def turn : Dart → Dart
  | .inl d => .inl (CycleBoundaryOrientation.turn 11 reverseAt d)
  | .inr (i, s) => .inr (i, s - 1)

/-- Exposed darts stay fixed; all other darts cross their actual edge. -/
def flip : Dart → Dart
  | .inl (i, 0) => if h : i.val % 2 = 0 then .inl (i, 0)
      else .inr (⟨i.val / 2, by omega⟩, 0)
  | .inl (i, 1) => .inl (i - 1, 2)
  | .inl (i, 2) => .inl (i + 1, 1)
  | .inr (i, 0) => .inl (inward i, 0)
  | .inr (i, 1) => .inr (i - 1, 2)
  | .inr (i, 2) => .inr (i + 1, 1)

theorem even_position {i : Fin 11} (h : reverseAt i = true) :
    ∃ j : Fin 6, i = Incidence.outward j := by
  refine ⟨⟨i.val / 2, by omega⟩, ?_⟩
  apply Fin.ext
  simp only [reverseAt, decide_eq_true_eq] at h
  simp only [Incidence.outward, Function.Embedding.coeFn_mk]
  omega

theorem odd_position {i : Fin 11} (h : reverseAt i = false) :
    ∃ j : Fin 5, i = inward j := by
  have hodd : i.val % 2 ≠ 0 := by simpa [reverseAt] using h
  refine ⟨⟨i.val / 2, by omega⟩, ?_⟩
  apply Fin.ext
  simp only [inward, Function.Embedding.coeFn_mk]
  omega
end Coordinate

namespace Incidence
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V]
  [DecidableRel G.Adj] [G.LocallyFinite]
  (L : Incidence G) (b : Bool)
  (hm : ∀ i, L.matching (if b then i + 1 else i - 1) = L.matching i + 1)

local instance lobeDartsEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance lobeDartsEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

def patchVertices : Finset V := by
  classical
  exact Finset.univ.filter fun v => L.outer.keep v ∨ L.inner.keep v
abbrev patchKeep := deletedSideKeep L.patchVertices

omit [DecidableRel G.Adj] [G.LocallyFinite] in
@[simp] theorem patchKeep_iff (v : V) : L.patchKeep v ↔ L.outer.keep v ∨ L.inner.keep v := by
  classical
  simp only [patchKeep, deletedSideKeep, deletedRegionKeep, patchVertices,
    Finset.mem_filter, Finset.mem_univ, true_and, not_not]

def coordinateVertex : Coordinate.Vertex → V
  | .inl i => L.outer.vertex i
  | .inr j => (L.innerBySpoke b hm).vertex j

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [G.LocallyFinite] in
@[simp] theorem coordinateVertex_outer (i : Fin 11) :
    L.coordinateVertex b hm (.inl i) = L.outer.vertex i := rfl
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [G.LocallyFinite] in
@[simp] theorem coordinateVertex_inner (j : Fin 5) :
    L.coordinateVertex b hm (.inr j) = L.inner.vertex (L.matching.symm j) := rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [G.LocallyFinite] in
theorem coordinateVertex_injective : Function.Injective (L.coordinateVertex b hm) := by
  intro v w h
  cases v with
  | inl i =>
      cases w with
      | inl j => exact congrArg Sum.inl (L.outer.vertex.injective h)
      | inr j => exact (L.disjoint _ _ h).elim
  | inr i =>
      cases w with
      | inl j => exact (L.disjoint _ _ h.symm).elim
      | inr j => exact congrArg Sum.inr ((L.innerBySpoke b hm).vertex.injective h)

omit [DecidableRel G.Adj] [G.LocallyFinite] in
theorem coordinateVertex_keep (v : Coordinate.Vertex) : L.patchKeep (L.coordinateVertex b hm v) := by
  cases v with
  | inl i => exact (L.patchKeep_iff _).2 (.inl (L.outer.vertex_keep i))
  | inr j => exact (L.patchKeep_iff _).2 (.inr (L.inner.vertex_keep _))

def patchVertexEquiv : Coordinate.Vertex ≃ {v // L.patchKeep v} :=
  Equiv.ofBijective (fun v => ⟨L.coordinateVertex b hm v, L.coordinateVertex_keep b hm v⟩) ⟨by
    intro v w h
    exact L.coordinateVertex_injective b hm (congrArg Subtype.val h), by
    intro v
    rcases (L.patchKeep_iff _).1 v.2 with hv | hv
    · obtain ⟨i, hi⟩ := (L.outer.keep_iff _).1 hv
      exact ⟨.inl i, Subtype.ext hi.symm⟩
    · obtain ⟨j, hj⟩ := (L.inner.keep_iff _).1 hv
      refine ⟨.inr (L.matching j), Subtype.ext ?_⟩
      simpa using hj.symm⟩

def coordinateDart : Coordinate.Dart → G.Dart
  | .inl (i, s) => L.outer.star i s
  | .inr (j, s) => (L.innerBySpoke b hm).star j s

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [G.LocallyFinite] in
@[simp] theorem coordinateDart_fst (d : Coordinate.Dart) :
    (L.coordinateDart b hm d).fst = L.coordinateVertex b hm (Coordinate.vertex d) := by
  cases d <;> simp [coordinateDart, Coordinate.vertex, coordinateVertex]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [G.LocallyFinite] in
theorem coordinateDart_injective : Function.Injective (L.coordinateDart b hm) := by
  intro d e h
  cases d with
  | inl d =>
      cases e with
      | inl e => exact congrArg Sum.inl (L.outer.star_injective (by decide) h)
      | inr e => exact (L.disjoint d.1 (L.matching.symm e.1) (by
          simpa [coordinateDart] using congrArg (fun d : G.Dart => d.fst) h)).elim
  | inr d =>
      cases e with
      | inl e => exact (L.disjoint e.1 (L.matching.symm d.1) (by
          simpa [coordinateDart] using congrArg (fun d : G.Dart => d.fst) h.symm)).elim
      | inr e => exact congrArg Sum.inr ((L.innerBySpoke b hm).star_injective (by decide) h)

variable (rotation : Data G)

def retainedCoordinate (d : Coordinate.Dart) : RetainedDart rotation.toRotationSystem L.patchKeep :=
  ⟨L.coordinateDart b hm d, by
    change L.patchKeep (L.coordinateDart b hm d).fst
    rw [L.coordinateDart_fst]
    exact L.coordinateVertex_keep b hm _⟩

def patchDartEquiv (hcubic : G.IsRegularOfDegree 3) :
    Coordinate.Dart ≃ RetainedDart rotation.toRotationSystem L.patchKeep :=
  Equiv.ofBijective (L.retainedCoordinate b hm rotation) ⟨by
    intro d e h
    exact L.coordinateDart_injective b hm (congrArg Subtype.val h), by
    intro d
    rcases (L.patchKeep_iff _).1 d.2 with hd | hd
    · obtain ⟨i, hi⟩ := (L.outer.keep_iff _).1 hd
      obtain ⟨s, hs⟩ := L.outer.star_surjective_at (by decide) hcubic i d.1 hi
      exact ⟨.inl (i, s), Subtype.ext hs⟩
    · obtain ⟨j, hj⟩ := (L.inner.keep_iff _).1 hd
      have hv : d.1.fst = (L.innerBySpoke b hm).vertex (L.matching j) := by simpa using hj
      obtain ⟨s, hs⟩ := (L.innerBySpoke b hm).star_surjective_at
        (by decide) hcubic (L.matching j) d.1 hv
      exact ⟨.inr (L.matching j, s), Subtype.ext hs⟩⟩

omit rotation [DecidableRel G.Adj] in
theorem outward_spoke_not_patch (hcubic : G.IsRegularOfDegree 3) (j : Fin 6) :
    ¬ L.patchKeep (L.outer.spoke (outward j)) := by
  rw [L.patchKeep_iff]
  rintro (h | h)
  · exact L.outer.spoke_not_keep _ h
  · obtain ⟨i, hi⟩ := (L.inner.keep_iff _).1 h
    exact L.outward_spoke_not_inner hcubic j i hi

omit rotation [DecidableRel G.Adj] in
theorem coordinateDart_boundary (hcubic : G.IsRegularOfDegree 3) (d : Coordinate.Dart) :
    (¬ L.patchKeep (L.coordinateDart b hm d).snd) ↔ Coordinate.boundary d := by
  rcases d with ⟨i, s⟩ | ⟨j, s⟩
  · fin_cases s
    · cases h : reverseAt i
      · obtain ⟨j, rfl⟩ := Coordinate.odd_position h
        erw [show (L.coordinateDart b hm (.inl (inward j, 0))).snd =
          L.inner.vertex (L.matching.symm j) from L.outer_spoke hcubic j]
        simp [Coordinate.boundary, h]
      · obtain ⟨j, rfl⟩ := Coordinate.even_position h
        exact iff_of_true (L.outward_spoke_not_patch hcubic j) ⟨h, rfl⟩
    · simp [coordinateDart, Frame.star, Coordinate.boundary]
    · simp [coordinateDart, Frame.star, Coordinate.boundary]
  · fin_cases s
    · simp [coordinateDart, Frame.star, Coordinate.boundary]
    · simp [coordinateDart, Frame.star, Coordinate.boundary]
    · simp [coordinateDart, Frame.star, Coordinate.boundary]

omit [Fintype V] [DecidableRel G.Adj] in
/-- Every internal coordinate crosses the genuine ambient edge. -/
theorem coordinateDart_flip (hcubic : G.IsRegularOfDegree 3)
    (d : Coordinate.Dart) (hd : ¬ Coordinate.boundary d) :
    L.coordinateDart b hm (Coordinate.flip d) = (L.coordinateDart b hm d).symm := by
  rcases d with ⟨i, s⟩ | ⟨j, s⟩
  · fin_cases s
    · have ho : reverseAt i = false := by
        cases h : reverseAt i
        · rfl
        · exact (hd ⟨h, rfl⟩).elim
      obtain ⟨j, rfl⟩ := Coordinate.odd_position ho
      have hf : Coordinate.flip (.inl (inward j, 0)) = .inr (j, 0) := by
        fin_cases j <;> rfl
      erw [hf]
      apply SimpleGraph.Dart.ext
      simp [coordinateDart, Frame.star, L.outer_spoke hcubic, SimpleGraph.Dart.symm]
    · apply SimpleGraph.Dart.ext
      simp [Coordinate.flip, coordinateDart, Frame.star, SimpleGraph.Dart.symm]
    · apply SimpleGraph.Dart.ext
      simp [Coordinate.flip, coordinateDart, Frame.star, SimpleGraph.Dart.symm]
  · fin_cases s
    · apply SimpleGraph.Dart.ext
      simp [Coordinate.flip, coordinateDart, Frame.star, L.outer_spoke hcubic,
        SimpleGraph.Dart.symm]
    · apply SimpleGraph.Dart.ext
      simp [Coordinate.flip, coordinateDart, Frame.star, SimpleGraph.Dart.symm]
    · apply SimpleGraph.Dart.ext
      simp [Coordinate.flip, coordinateDart, Frame.star, SimpleGraph.Dart.symm]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [G.LocallyFinite] in
/-- The actual vertex permutation commutes with the whole coordinate map. -/
theorem coordinateDart_turn
    (houter : ∀ d : CycleBoundaryOrientation.Dart 11,
      rotation.vertexRotation (L.outer.star d.1 d.2) =
        L.outer.star (CycleBoundaryOrientation.turn 11 reverseAt d).1
          (CycleBoundaryOrientation.turn 11 reverseAt d).2)
    (hinner : ∀ d : CycleBoundaryOrientation.Dart 5,
      rotation.vertexRotation (L.inner.star d.1 d.2) =
        L.inner.star (CycleBoundaryOrientation.turn 5 (fun _ => b) d).1
          (CycleBoundaryOrientation.turn 5 (fun _ => b) d).2)
    (d : Coordinate.Dart) :
    L.coordinateDart b hm (Coordinate.turn d) =
      rotation.vertexRotation (L.coordinateDart b hm d) := by
  rcases d with ⟨i, s⟩ | ⟨j, s⟩
  · exact (houter (i, s)).symm
  · exact (L.innerBySpoke_rotation b hm rotation hinner j s).symm

end Incidence
end
end Mettapedia.GraphTheory.FourColor.ElevenLobeSpokeOrder
