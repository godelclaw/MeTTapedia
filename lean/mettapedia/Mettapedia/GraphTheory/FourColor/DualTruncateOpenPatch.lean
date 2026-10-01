import Mettapedia.GraphTheory.FourColor.DualTruncateCornerSemantics
import Mettapedia.GraphTheory.FourColor.DualTruncateConstructionGSLT

/-!
# Exact reconstruction of open dual-and-truncate patches

A selected target region is closed under source edge reversal. All boundary
edges are then polygon edges. Their corner colours, together with the whole
fixed exterior, specify an exact extension fibre. The interior summary keeps
the joint corner choices and endpoint balance. Reconstruction restores every
cross edge and preserves every exterior dart colour, including the cut edges.

There is no assertion that the summary admits every supplied exterior, nor
that eliminating colour variables is a smaller embedded graph operation.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateOpenPatch

open DualTruncateColoring DualTruncateCornerSemantics

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem.{u,u,u} V E)

/-- Every actual edge incident to an exterior vertex is fixed. -/
def Extends (keep : RS.D → Prop) (base c : Edge RS → Color) : Prop :=
  ∀ d, ¬keep d → ∀ i : Fin 3,
    c ((rotation RS).edgeOf (d,i)) = base ((rotation RS).edgeOf (d,i))

/-- A polygon edge is visible when at least one endpoint is outside. -/
def Visible (keep : RS.D → Prop) (d : RS.D) : Prop :=
  ¬keep d ∨ ¬keep (RS.phi.symm d)

/-- Visibility is actual incidence with an exterior target vertex. -/
def VisibleEdge (keep : RS.D → Prop) (e : Edge RS) : Prop :=
  ∃ x : (rotation RS).D, (rotation RS).edgeOf x = e ∧ ¬keep ((rotation RS).vertOf x)

theorem polygon_visible_iff (keep : RS.D → Prop) (d : RS.D) :
    VisibleEdge RS keep (.inr (RS.phi.symm d)) ↔ Visible RS keep d := by
  constructor
  · rintro ⟨x,hx,hn⟩
    have hs := (rotation RS).edge_fiber_two_cases
      (d := (d,2)) (y := x) (show (rotation RS).edgeOf (d,2) = .inr (RS.phi.symm d) from rfl) hx
    rcases hs with rfl | rfl
    · exact Or.inl hn
    · exact Or.inr hn
  · rintro (hd | hp)
    · exact ⟨(d,2),rfl,hd⟩
    · exact ⟨(RS.phi.symm d,1),rfl,hp⟩

theorem extends_iff_visible_edges (keep : RS.D → Prop) (base c : Edge RS → Color) :
    Extends RS keep base c ↔ ∀ e, VisibleEdge RS keep e → c e = base e := by
  constructor
  · rintro h e ⟨⟨d,i⟩,he,hd⟩
    rw [← he]
    exact h d hd i
  · intro h d hd i
    exact h _ ⟨(d,i),rfl,hd⟩

/-- Actual local constraints and retained visible corner values. -/
def Summary (keep : RS.D → Prop) (base : Edge RS → Color) (q : RS.D → Color) : Prop :=
  (∀ d, keep d → q d ≠ 0 ∧ q (RS.phi d) ≠ 0 ∧
    q d ≠ q (RS.phi d) ∧ Balanced RS q d) ∧
  ∀ d, Visible RS keep d → q d = corner RS base d

variable {keep : RS.D → Prop} {base : Edge RS → Color}
  (hclosed : ∀ d, keep (RS.alpha d) ↔ keep d)
  (hout : ∀ d, ¬keep d → Star RS base d)

include hclosed in
theorem cross_visible_iff (d : RS.D) :
    VisibleEdge RS keep (.inl (RS.edgeOf d)) ↔ ¬keep d := by
  constructor
  · rintro ⟨x,hx,hn⟩
    have hs := (rotation RS).edge_fiber_two_cases
      (d := (d,0)) (y := x) (show (rotation RS).edgeOf (d,0) = .inl (RS.edgeOf d) from rfl) hx
    rcases hs with rfl | rfl
    · exact hn
    · exact fun hd => hn ((hclosed d).mpr hd)
  · intro hd
    exact ⟨(d,0),rfl,hd⟩

theorem outside_corners {q : RS.D → Color} (h : Summary RS keep base q)
    {d : RS.D} (hd : ¬keep d) :
    q d = corner RS base d ∧ q (RS.phi d) = corner RS base (RS.phi d) :=
  ⟨h.2 d (Or.inl hd), h.2 (RS.phi d)
    (Or.inr (by simpa only [Equiv.symm_apply_apply] using hd))⟩

include hclosed hout in
theorem summary_valid {q : RS.D → Color} (h : Summary RS keep base q) : Valid RS q := by
  have localGood (d) : q d ≠ 0 ∧ q (RS.phi d) ≠ 0 ∧
      q d ≠ q (RS.phi d) ∧ Balanced RS q d := by
    by_cases hd : keep d
    · exact h.1 d hd
    · have ha : ¬keep (RS.alpha d) := fun ha => hd ((hclosed d).mp ha)
      have eqd := outside_corners RS h hd
      have eqa := outside_corners RS h ha
      rw [eqd.1, eqd.2]
      have hs := hout d hd
      refine ⟨hs.1 2, ?_, ?_, ?_⟩
      · rw [corner_phi]
        exact hs.1 1
      · intro he
        have he' : base ((rotation RS).edgeOf (d,2)) =
            base ((rotation RS).edgeOf (d,1)) := by
          rw [corner_star_two RS base d]
          change corner RS base d = base (.inr d)
          rw [← corner_phi RS base d]
          exact he
        exact (by decide : (2 : Fin 3) ≠ 1) (hs.2 he')
      · unfold DualTruncateCornerSemantics.Balanced
        rw [eqd.1, eqd.2, eqa.1, eqa.2]
        exact corners_balanced_of_stars RS hs (hout (RS.alpha d) ha)
  exact ⟨fun d => (localGood d).1,
    fun d => (localGood d).2.2.1, fun d => (localGood d).2.2.2⟩

include hclosed hout in
theorem reconstructed_extends {q : RS.D → Color} (h : Summary RS keep base q) :
    Extends RS keep base (edgeColours RS q) := by
  intro d hd i
  have eqd := outside_corners RS h hd
  have hcross := cross_of_star RS (hout d hd)
  have hb := (summary_valid RS hclosed hout h).2.2 d
  fin_cases i
  · change edgeColours RS q ((rotation RS).edgeOf (d,0)) = base (.inl (RS.edgeOf d))
    rw [edge_star_zero RS q d hb, eqd.1, eqd.2]
    exact hcross.symm
  · change q (RS.phi d) = base (.inr d)
    exact eqd.2.trans (corner_phi RS base d)
  · change edgeColours RS q ((rotation RS).edgeOf (d,2)) = base ((rotation RS).edgeOf (d,2))
    rw [edge_star_two RS q d, corner_star_two RS base d]
    exact eqd.1

theorem summary_of_extension (c : (rotation RS).EdgeColoring Color)
    (hc : (rotation RS).IsTaitEdgeColoring c) (he : Extends RS keep base c) :
    Summary RS keep base (corner RS c) := by
  have hq := corners_valid RS c hc
  refine ⟨fun d _ => ⟨hq.1 d, hq.1 (RS.phi d), hq.2.1 d, hq.2.2 d⟩, ?_⟩
  intro d hd
  rcases hd with hd | hd
  · exact he d hd 2
  · exact he (RS.phi.symm d) hd 1

/-- Genuine interior witnesses and the exact joint summary are inverse
representations, relative to the same fixed exterior. -/
def extensionEquiv :
    {c : (rotation RS).EdgeColoring Color //
      (rotation RS).IsTaitEdgeColoring c ∧ Extends RS keep base c} ≃
    {q : RS.D → Color // Summary RS keep base q} where
  toFun c := ⟨corner RS c.val, summary_of_extension RS c.val c.property.1 c.property.2⟩
  invFun q := ⟨colouring RS q.val (summary_valid RS hclosed hout q.property),
    colouring_tait RS q.val (summary_valid RS hclosed hout q.property),
    reconstructed_extends RS hclosed hout q.property⟩
  left_inv c := by
    apply Subtype.ext
    apply DFunLike.ext
    intro e
    exact congrFun (edgeColours_corners RS c.val c.property.1) e
  right_inv q := by
    apply Subtype.ext
    exact corner_edgeColours RS q.val

include hclosed hout in
theorem extension_count :
    Nat.card {c : (rotation RS).EdgeColoring Color //
      (rotation RS).IsTaitEdgeColoring c ∧ Extends RS keep base c} =
    Nat.card {q : RS.D → Color // Summary RS keep base q} :=
  Nat.card_congr (extensionEquiv RS hclosed hout)

/-- The actual target vertices incident to a selected source vertex set. -/
def vertexRegion (selected : V → Prop) (d : RS.D) : Prop :=
  selected (RS.vertOf d) ∨ selected (RS.vertOf (RS.alpha d))

theorem vertexRegion_closed (selected : V → Prop) (d : RS.D) :
    vertexRegion RS selected (RS.alpha d) ↔ vertexRegion RS selected d := by
  simp only [vertexRegion, RS.alpha_involutive, or_comm]

open TubeSlab.VertexTransfer VertexCodeSourceGeometry SourceVertexCodeTrace
open VertexConstructionGSLT

include hclosed hout in
/-- Reconstruction supplies genuine compatible witnesses throughout every
complete faithful construction route, using no source vertex-colouring input. -/
theorem every_complete_sweep {q : RS.D → Color} (h : Summary RS keep base q)
    (order : List RS.D) (hn : order.Nodup) (he : order ≠ [])
    (hcover : ∀ d, visited order d) :
    VertexConstructionGSLT.colouring.Supports
      (route (encodeClosed (cubic RS) (DualTruncateConstructionGSLT.rotationCyclic RS)
        order hn he hcover).trace) Fin.elim0 Fin.elim0 := by
  have hv := summary_valid RS hclosed hout h
  exact (SourceConstructionGSLT.encoded_support_iff (cubic RS)
    (DualTruncateConstructionGSLT.rotationCyclic RS) order hn he hcover).mpr
    ⟨colouring RS q hv, colouring_tait RS q hv⟩

end
end Mettapedia.GraphTheory.FourColor.DualTruncateOpenPatch
