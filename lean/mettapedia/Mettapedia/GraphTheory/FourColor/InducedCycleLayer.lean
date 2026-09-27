import Mettapedia.GraphTheory.FourColor.CycleFrame

/-!
# Ring layers from induced cycles in cubic graphs

Chordlessness makes the cyclic frame's third edges leave the entire row.
Alternating attachments then construct a slab with exact colouring witnesses.
-/

namespace Mettapedia.GraphTheory.FourColor.InducedCycleLayer

open ZigzagRing SimpleGraphDartRotation TubeSlab

variable {V : Type*} {G : SimpleGraph V} {k : ℕ} [NeZero k]

/-- A cyclic frame with no ambient chords. -/
structure Cycle (G : SimpleGraph V) (k : ℕ) [NeZero k] extends Frame G k where
  induced : ∀ u v, G.Adj (vertex u) (vertex v) → v = next k u ∨ v = prev k u

instance : Coe (Cycle G k) (Frame G k) := ⟨Cycle.toFrame⟩

namespace Cycle

variable (C : Cycle G k) [DecidableEq V] [G.LocallyFinite]
variable (hk : 2 ≤ k) (hG : G.IsRegularOfDegree 3)

include hk hG

omit [DecidableEq V] [G.LocallyFinite] hk hG in
theorem adjacent_prev (v : Vtx k) : G.Adj (C.vertex v) (C.vertex (prev k v)) :=
  C.toFrame.adjacent_prev v

theorem existsUnique_port (v : Vtx k) :
    ∃! p, G.Adj (C.vertex v) p ∧ p ≠ C.vertex (next k v) ∧ p ≠ C.vertex (prev k v) :=
  C.toFrame.existsUnique_port hk hG v

noncomputable abbrev port := C.toFrame.port hk hG

theorem port_spec (v : Vtx k) :
    G.Adj (C.vertex v) (C.port hk hG v) ∧
      C.port hk hG v ≠ C.vertex (next k v) ∧ C.port hk hG v ≠ C.vertex (prev k v) :=
  C.toFrame.port_spec hk hG v

theorem neighborFinset_eq (v : Vtx k) :
    G.neighborFinset (C.vertex v) =
      {C.port hk hG v, C.vertex (next k v), C.vertex (prev k v)} :=
  C.toFrame.neighborFinset_eq hk hG v

theorem adjacent_iff (v : Vtx k) (w : V) :
    G.Adj (C.vertex v) w ↔
      w = C.port hk hG v ∨ w = C.vertex (next k v) ∨ w = C.vertex (prev k v) :=
  C.toFrame.adjacent_iff hk hG v w

noncomputable abbrev star := C.toFrame.star hk hG

theorem star_fst (v : Vtx k) (j : Fin 3) :
    (C.star hk hG v j).fst = C.vertex v :=
  C.toFrame.star_fst hk hG v j

theorem star_injective : Function.Injective (fun p : Vtx k × Fin 3 => C.star hk hG p.1 p.2) :=
  C.toFrame.star_injective hk hG

theorem star_surjective_at (v : Vtx k) (d : G.Dart) (hd : d.fst = C.vertex v) :
    ∃ j, C.star hk hG v j = d :=
  C.toFrame.star_surjective_at hk hG v d hd

noncomputable abbrev embedding := C.toFrame.embedding hk hG

theorem embedding_injective : Function.Injective (C.embedding hk hG) :=
  C.toFrame.embedding_injective hk hG

theorem embedding_fst (d : AllDart k) :
    (C.embedding hk hG d).fst = C.vertex ((ring k).vertOf d) :=
  C.toFrame.embedding_fst hk hG d

theorem embedding_flip (d : ZigzagRing.Dart k) :
    (C.embedding hk hG (.inl d)).symm = C.embedding hk hG (.inl (flip k d)) :=
  C.toFrame.embedding_flip hk hG d

theorem embedding_covers (d : G.Dart) (hd : ∃ v, d.fst = C.vertex v) :
    ∃ x, C.embedding hk hG x = d :=
  C.toFrame.embedding_covers hk hG d hd

/-- The unused edge actually leaves the entire row, by chordlessness. -/
theorem port_not_cycle (v w : Vtx k) : C.port hk hG v ≠ C.vertex w := by
  intro he
  have ha := (C.port_spec hk hG v).1
  rw [he] at ha
  rcases C.induced v w ha with rfl | rfl
  · exact (C.port_spec hk hG v).2.1 he
  · exact (C.port_spec hk hG v).2.2 he

/-- How the row meets a vertex region. The inner cut is completely incident
with the first vertex class; the second class has no inner neighbour. -/
structure Attachment (inner : V → Prop) : Prop where
  disjoint : ∀ v, ¬ inner (C.vertex v)
  enters : ∀ i, ∃ w, inner w ∧ G.Adj (C.vertex (.inl i)) w
  exits : ∀ i w, G.Adj (C.vertex (.inr i)) w → ¬ inner w
  covers : ∀ u w, inner u → ¬ inner w → G.Adj u w → ∃ i, w = C.vertex (.inl i)

variable {inner : V → Prop}

theorem eq_port_of_inner (h : C.Attachment inner) {v : Vtx k} {w : V}
    (hw : inner w) (ha : G.Adj (C.vertex v) w) : w = C.port hk hG v := by
  rcases (C.adjacent_iff hk hG v w).mp ha with he | he | he
  · exact he
  · exact (h.disjoint (next k v) (he ▸ hw)).elim
  · exact (h.disjoint (prev k v) (he ▸ hw)).elim

theorem port_enters (h : C.Attachment inner) (i : Fin k) :
    inner (C.port hk hG (.inl i)) := by
  obtain ⟨w, hw, ha⟩ := h.enters i
  exact C.eq_port_of_inner hk hG h hw ha ▸ hw

theorem port_exits (h : C.Attachment inner) (i : Fin k) :
    ¬ inner (C.port hk hG (.inr i)) :=
  h.exits i _ (C.port_spec hk hG (.inr i)).1

variable [Fintype V] [DecidableRel G.Adj]

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- The graph conditions construct every field of the physical slab. No
colouring, port bijection or dart embedding is requested from the caller. -/
noncomputable def toSlab (data : Data G) (h : C.Attachment inner) :
    ZigzagSlab data.toRotationSystem k inner where
  ι := C.embedding hk hG
  vtx := C.vertex
  ι_inj := C.embedding_injective hk hG
  vtx_inj := C.injective
  vtx_not_inner := h.disjoint
  vert_ι := C.embedding_fst hk hG
  alpha_interior := C.embedding_flip hk hG
  in_inner := by
    intro i
    exact C.port_enters hk hG h i
  out_not_inner := by
    intro i
    exact C.port_exits hk hG h i
  out_not_slab := by
    intro i v
    exact C.port_not_cycle hk hG (.inr i) v
  cubic_slab := C.embedding_covers hk hG
  boundary_inner := by
    intro b
    obtain ⟨i, hi⟩ := h.covers b.1.1.fst b.1.1.snd b.1.2 b.2 b.1.1.adj
    have hu : b.1.1.fst = C.port hk hG (.inl i) :=
      C.eq_port_of_inner hk hG h b.1.2 (by simpa only [hi] using b.1.1.adj.symm)
    refine ⟨i, ?_⟩
    apply SimpleGraph.Dart.ext
    exact Prod.ext hu hi

/-- The actual enlarged region accepts exactly the ring images of the old
region's support, in the port order constructed from the cycle. -/
theorem support_after_cycle (data : Data G) (h : C.Attachment inner) (y : Fin k → Color) :
    let S := C.toSlab hk hG data h
    (fun b => y (S.outEquiv.symm b)) ∈ sideSupport data.toRotationSystem S.inner' ↔
      ∃ x : Fin k → Color,
        (fun b => x (S.inEquiv.symm b)) ∈ sideSupport data.toRotationSystem inner ∧
          (ring k).AcceptsBoundaryWords x y :=
  (C.toSlab hk hG data h).mem_sideSupport_inner'_iff y

/-- The recognized row gives exact witness composition on the original
ambient darts, not merely agreement of accepted boundary words. -/
noncomputable def colouringEquiv (data : Data G) (h : C.Attachment inner) :
    SideColoring data.toRotationSystem (C.toSlab hk hG data h).inner' ≃
      (C.toSlab hk hG data h).CompatibleColorings :=
  (C.toSlab hk hG data h).colouringEquiv

open GoertzelV24RotationCutDartDecomposition

variable (data : Data G) (h : C.Attachment inner)
  (old : SideColoring data.toRotationSystem inner) (rc : AllDart k → Color)
  (hrc : (ring k).IsTaitColoring rc)
  (seam : ∀ i, old.color ((C.toSlab hk hG data h).inPartner i).1 = rc (.inr (.inl i)))

/-- Construct the new proper colouring from the two compatible actual
witnesses, using the cycle-derived dart and port maps. -/
noncomputable def extend : SideColoring data.toRotationSystem (C.toSlab hk hG data h).inner' :=
  (C.toSlab hk hG data h).glueSideColoring old rc (fun i => rc (.inr (.inl i)))
    seam hrc (fun _ => rfl)

theorem extend_inner (d : RetainedDart data.toRotationSystem inner) :
    (C.extend hk hG data h old rc hrc seam).color ⟨d.val, Or.inl d.property⟩ = old.color d :=
  (C.toSlab hk hG data h).glueSideColoring_inner old rc _ seam hrc (fun _ => rfl) d

theorem extend_row (d : AllDart k) :
    (C.extend hk hG data h old rc hrc seam).color
      ((C.toSlab hk hG data h).slabDart d) = rc d :=
  (C.toSlab hk hG data h).glueSideColoring_slab old rc _ seam hrc (fun _ => rfl) d

end Cycle
end Mettapedia.GraphTheory.FourColor.InducedCycleLayer
