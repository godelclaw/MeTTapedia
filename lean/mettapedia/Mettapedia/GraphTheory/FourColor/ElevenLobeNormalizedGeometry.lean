import Mettapedia.GraphTheory.FourColor.ElevenLobeSpokeOrder

/-!
# One coherent coordinate system for the pentagonal lobe

Label inner vertices by their actual outer attachments. The orientation
forced by spherical geometry makes both the cycle adjacency and every
inner rotation agree in these coordinates. The two descriptions use the
same matching witness.
-/

namespace Mettapedia.GraphTheory.FourColor.ElevenLobeSpokeOrder

open SimpleGraph SimpleGraphDartRotation CubicCycleIncidence CycleBoundaryOrientation

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Incidence
variable {V : Type*} {G : SimpleGraph V} (L : Incidence G)
  (b : Bool)
  (hm : ∀ i, L.matching (if b then i + 1 else i - 1) = L.matching i + 1)

include hm in
theorem matching_symm_next (j : Fin 5) :
    L.matching.symm (j + 1) = if b then L.matching.symm j + 1 else L.matching.symm j - 1 := by
  apply L.matching.injective
  rw [Equiv.apply_symm_apply, hm, Equiv.apply_symm_apply]

include hm in
theorem matching_symm_prev (j : Fin 5) :
    L.matching.symm (j - 1) = if b then L.matching.symm j - 1 else L.matching.symm j + 1 := by
  have h := L.matching_symm_next b hm (j - 1)
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, sub_add_cancel] at h ⊢
  · exact (sub_eq_iff_eq_add.mp h.symm)
  · exact (eq_sub_iff_add_eq.mpr h.symm)

/-- The new index is the outer spoke position, not an independently
chosen orientation of the inner cycle. -/
def innerBySpoke : Frame G 5 where
  vertex := L.matching.symm.toEmbedding.trans L.inner.vertex
  adjacent j := by
    change G.Adj (L.inner.vertex (L.matching.symm j))
      (L.inner.vertex (L.matching.symm (j + 1)))
    rw [L.matching_symm_next b hm]
    cases b
    · exact L.inner.adjacent_prev _
    · exact L.inner.adjacent _
  spoke j := L.outer.vertex (inward j)
  spoke_adjacent j := by
    change G.Adj (L.inner.vertex (L.matching.symm j)) (L.outer.vertex (inward j))
    have h := L.inner.spoke_adjacent (L.matching.symm j)
    simpa only [L.spoke, Equiv.apply_symm_apply] using h
  spoke_outside j i := L.disjoint _ _

@[simp] theorem innerBySpoke_vertex (j : Fin 5) :
    (L.innerBySpoke b hm).vertex j = L.inner.vertex (L.matching.symm j) := rfl

@[simp] theorem innerBySpoke_spoke (j : Fin 5) :
    (L.innerBySpoke b hm).spoke j = L.outer.vertex (inward j) := rfl

theorem innerBySpoke_star (j : Fin 5) (s : Fin 3) :
    (L.innerBySpoke b hm).star j s =
      L.inner.star (L.matching.symm j) (if b then s else -s) := by
  have hn := L.matching_symm_next b hm j
  have hp := L.matching_symm_prev b hm j
  cases b <;> fin_cases s <;> apply SimpleGraph.Dart.ext <;>
    norm_num [Frame.star, innerBySpoke, L.spoke, Fin.neg_def] <;> simp_all

variable (rotation : Data G)

/-- Reindexing preserves the coupled direction: the canonical inner turn
is now the predecessor in the three-dart star at every vertex. -/
theorem innerBySpoke_rotation
    (hinner : ∀ d : CycleBoundaryOrientation.Dart 5,
      rotation.vertexRotation (L.inner.star d.1 d.2) =
        L.inner.star (turn 5 (fun _ => b) d).1 (turn 5 (fun _ => b) d).2)
    (j : Fin 5) (s : Fin 3) :
    rotation.vertexRotation ((L.innerBySpoke b hm).star j s) =
      (L.innerBySpoke b hm).star j (s - 1) := by
  rw [L.innerBySpoke_star, L.innerBySpoke_star,
    hinner (L.matching.symm j, if b then s else -s)]
  cases b <;> fin_cases s <;> rfl

/-- Six outward attachments, including both sides of the closing gap. -/
def outward : Fin 6 ↪ Fin 11 where
  toFun i := ⟨2 * i.val, by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

variable [DecidableEq V] [G.LocallyFinite]

/-- No outward spoke can secretly end on the inner cycle: its three
neighbours are already exhausted by the inner cycle and its matched spoke. -/
theorem outward_spoke_not_inner (hcubic : G.IsRegularOfDegree 3) (j : Fin 6) (i : Fin 5) :
    L.outer.spoke (outward j) ≠ L.inner.vertex i := by
  intro he
  have ha := (L.outer.spoke_adjacent (outward j)).symm
  rw [he] at ha
  rcases (L.inner.adjacent_iff (by decide) hcubic i _).mp ha with h | h | h
  · rw [L.spoke] at h
    have hh := congrArg Fin.val (L.outer.vertex.injective h)
    simp only [outward, inward, Function.Embedding.coeFn_mk] at hh
    omega
  · exact L.disjoint _ _ h
  · exact L.disjoint _ _ h

end Incidence
end
end Mettapedia.GraphTheory.FourColor.ElevenLobeSpokeOrder
