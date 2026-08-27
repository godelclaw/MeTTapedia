import Mathlib.Combinatorics.Pigeonhole

/-!
# Material forced between nested finite edge shores

This file isolates the incidence count needed by the sphere-cut descent.
If `A ⊆ B` are nested edge shores, a vertex is on the middle of a shore
when it sees an edge on both sides.  If every vertex meets at most `d` edges
and `B \ A` has more edges than can be supported on the two middle sets,
then some vertex is incident only with edges of `B \ A`.  In a cubic graph
with both middle sets of size at most `w`, the sufficient bound is `6 * w`.

The result is purely finite incidence counting; no planar separation theorem
is used.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SphereCutMaterial

open scoped Classical

/-- Equal phases at two distinct indices force their distance
to be at least one full period. -/
theorem period_le_sub_of_mod_eq {period i j : ℕ}
    (hij : i < j) (hmod : i % period = j % period) :
    period ≤ j - i := by
  have hcong : i ≡ j [MOD period] := hmod
  have hdvd : period ∣ j - i :=
    (Nat.modEq_iff_dvd' (Nat.le_of_lt hij)).mp hcong
  exact Nat.le_of_dvd (Nat.sub_pos_of_lt hij) hdvd

section Incidence

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- Vertices incident with an edge in the shore and an edge outside it. -/
noncomputable def middleVertices (incident : V → E → Prop)
    (shore : Finset E) : Finset V :=
  Finset.univ.filter fun vertex =>
    (∃ edge ∈ shore, incident vertex edge) ∧
      ∃ edge ∉ shore, incident vertex edge

omit [DecidableEq V] in theorem mem_middleVertices_iff (incident : V → E → Prop)
    (shore : Finset E) (vertex : V) :
    vertex ∈ middleVertices incident shore ↔
      (∃ edge ∈ shore, incident vertex edge) ∧
        ∃ edge ∉ shore, incident vertex edge := by
  simp [middleVertices]

/-- If a nested slab has more edges than the union of its two middle sets
can support, it contains a vertex all of whose incident edges lie in the
slab. -/
theorem exists_strict_slab_vertex
    (incident : V → E → Prop)
    (A B : Finset E) (degreeBound : ℕ)
    (hedge : ∀ edge : E, ∃ vertex : V, incident vertex edge)
    (hdegree : ∀ vertex : V,
      (Finset.univ.filter fun edge => incident vertex edge).card ≤ degreeBound)
    (hlarge :
      degreeBound *
          ((middleVertices incident A ∪ middleVertices incident B).card) <
        (B \ A).card) :
    ∃ vertex : V,
      (∃ edge ∈ B \ A, incident vertex edge) ∧
        ∀ edge, incident vertex edge → edge ∈ B \ A := by
  classical
  let endpoint : E → V := fun edge => Classical.choose (hedge edge)
  have endpoint_incident (edge : E) : incident (endpoint edge) edge :=
    Classical.choose_spec (hedge edge)
  have hexterior :
      ∃ edge ∈ B \ A,
        endpoint edge ∉ middleVertices incident A ∪ middleVertices incident B := by
    by_contra hnone
    push Not at hnone
    have hmaps : ∀ edge ∈ B \ A,
        endpoint edge ∈ middleVertices incident A ∪ middleVertices incident B :=
      hnone
    obtain ⟨vertex, _hvertex, hfiber⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        (f := endpoint) hmaps (by simpa [Nat.mul_comm] using hlarge)
    have hfiberSubset :
        ((B \ A).filter fun edge => endpoint edge = vertex) ⊆
          Finset.univ.filter fun edge => incident vertex edge := by
      intro edge hedgeMem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hedgeMem ⊢
      rw [← hedgeMem.2]
      exact endpoint_incident edge
    exact (not_lt_of_ge
      (le_trans (Finset.card_le_card hfiberSubset) (hdegree vertex))) hfiber
  obtain ⟨edge, hedgeSlab, hedgeMiddle⟩ := hexterior
  let vertex := endpoint edge
  refine ⟨vertex, ⟨edge, hedgeSlab, endpoint_incident edge⟩, ?_⟩
  intro other hother
  have hedgeB : edge ∈ B := (Finset.mem_sdiff.1 hedgeSlab).1
  have hedgeA : edge ∉ A := (Finset.mem_sdiff.1 hedgeSlab).2
  have hvertexA : vertex ∉ middleVertices incident A := by
    intro hmem
    exact hedgeMiddle (Finset.mem_union_left _ hmem)
  have hvertexB : vertex ∉ middleVertices incident B := by
    intro hmem
    exact hedgeMiddle (Finset.mem_union_right _ hmem)
  have hotherA : other ∉ A := by
    intro hmem
    apply hvertexA
    rw [mem_middleVertices_iff]
    exact ⟨⟨other, hmem, hother⟩, ⟨edge, hedgeA, endpoint_incident edge⟩⟩
  have hotherB : other ∈ B := by
    by_contra hnot
    apply hvertexB
    rw [mem_middleVertices_iff]
    exact ⟨⟨edge, hedgeB, endpoint_incident edge⟩, ⟨other, hnot, hother⟩⟩
  exact Finset.mem_sdiff.2 ⟨hotherB, hotherA⟩

/-- Width form of `exists_strict_slab_vertex`.  When both middle sets have
at most `w` vertices, more than `2 * degreeBound * w` slab edges force a
strictly interior slab vertex. -/
theorem exists_strict_slab_vertex_of_middle_card_le
    (incident : V → E → Prop)
    (A B : Finset E) (degreeBound w : ℕ)
    (hedge : ∀ edge : E, ∃ vertex : V, incident vertex edge)
    (hdegree : ∀ vertex : V,
      (Finset.univ.filter fun edge => incident vertex edge).card ≤ degreeBound)
    (hmiddleA : (middleVertices incident A).card ≤ w)
    (hmiddleB : (middleVertices incident B).card ≤ w)
    (hlarge : degreeBound * (2 * w) < (B \ A).card) :
    ∃ vertex : V,
      (∃ edge ∈ B \ A, incident vertex edge) ∧
        ∀ edge, incident vertex edge → edge ∈ B \ A := by
  apply exists_strict_slab_vertex incident A B degreeBound hedge hdegree
  have hunion :
      (middleVertices incident A ∪ middleVertices incident B).card ≤ 2 * w := by
    calc
      (middleVertices incident A ∪ middleVertices incident B).card ≤
          (middleVertices incident A).card +
            (middleVertices incident B).card := Finset.card_union_le _ _
      _ ≤ w + w := Nat.add_le_add hmiddleA hmiddleB
      _ = 2 * w := by omega
  exact lt_of_le_of_lt (Nat.mul_le_mul_left degreeBound hunion) hlarge

/-- Cubic specialization: two width-`w` middle sets can support at most
`6 * w` slab edges unless a vertex lies strictly in the slab. -/
theorem exists_strict_slab_vertex_of_cubic
    (incident : V → E → Prop)
    (A B : Finset E) (w : ℕ)
    (hedge : ∀ edge : E, ∃ vertex : V, incident vertex edge)
    (hcubic : ∀ vertex : V,
      (Finset.univ.filter fun edge => incident vertex edge).card ≤ 3)
    (hmiddleA : (middleVertices incident A).card ≤ w)
    (hmiddleB : (middleVertices incident B).card ≤ w)
    (hlarge : 6 * w < (B \ A).card) :
    ∃ vertex : V,
      (∃ edge ∈ B \ A, incident vertex edge) ∧
        ∀ edge, incident vertex edge → edge ∈ B \ A := by
  apply exists_strict_slab_vertex_of_middle_card_le
    incident A B 3 w hedge hcubic hmiddleA hmiddleB
  omega

end Incidence

end GoertzelV24SphereCutMaterial

end Mettapedia.GraphTheory.FourColor
