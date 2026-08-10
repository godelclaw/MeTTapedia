import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionTaitInheritance
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationDartColoring

/-!
# Gluing two literal open-region Tait colorings

The compositional proof cuts a planar map into open pieces and later glues
matching boundary states.  This module supplies the elementary color-level
gluing theorem for that operation.  Given literal open rotation systems on
the two complementary vertex sides, Tait colorings of those pieces, and
agreement on every exposed half-edge, their colors descend to a Tait coloring
of the original rotation system.

Nothing here selects a finite configuration or invokes a covering reduction:
it is generic combinatorial-map plumbing.  Source-specific crosscut modules
will supply the two sides and prove their boundary words agree through the
finite profile semantics.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenRegionColorGluing

open GoertzelV24OpenRegionRotation
open GoertzelV24RotationDartColoring
open SimpleGraph

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Read an open-region edge coloring at an old ambient dart retained by that
region.  This leaves the boundary stub implicit: the next lemma identifies
the two readings along an exposed edge. -/
def openOldDartColor
    (RS : RotationSystem V E) (keep : V → Prop)
    (root : Dart RS keep)
    (coloring : (rotationSystem RS keep root).EdgeColoring Color)
    (dart : RS.D) (hdart : keep (RS.vertOf dart)) : Color :=
  coloring ((rotationSystem RS keep root).edgeOf (Sum.inl ⟨dart, hdart⟩))

/-- On an edge wholly inside one literal open region, its two ambient dart
readings agree. -/
theorem openOldDartColor_alpha_of_internal
    (RS : RotationSystem V E) (keep : V → Prop)
    (root : Dart RS keep)
    (coloring : (rotationSystem RS keep root).EdgeColoring Color)
    (dart : RS.D) (hdart : keep (RS.vertOf dart))
    (halpha : keep (RS.vertOf (RS.alpha dart))) :
    openOldDartColor RS keep root coloring (RS.alpha dart) halpha =
      openOldDartColor RS keep root coloring dart hdart := by
  unfold openOldDartColor
  rw [← rotationSystem_alpha_old_of_internal RS keep root ⟨dart, hdart⟩ halpha]
  exact congrArg coloring
    ((rotationSystem RS keep root).edge_alpha (Sum.inl ⟨dart, hdart⟩))

/-- At an exposed half-edge, the old-dart reading of an open-region coloring
equals its literal fresh-stub reading. -/
theorem openOldDartColor_eq_boundaryStubColor
    (RS : RotationSystem V E) (keep : V → Prop)
    (root : Dart RS keep)
    (coloring : (rotationSystem RS keep root).EdgeColoring Color)
    (dart : RS.D) (hdart : keep (RS.vertOf dart))
    (halpha : ¬ keep (RS.vertOf (RS.alpha dart))) :
    openOldDartColor RS keep root coloring dart hdart =
      coloring ((rotationSystem RS keep root).edgeOf
        (Sum.inr ⟨⟨dart, hdart⟩, halpha⟩)) := by
  unfold openOldDartColor
  calc
    coloring ((rotationSystem RS keep root).edgeOf (Sum.inl ⟨dart, hdart⟩)) =
        coloring ((rotationSystem RS keep root).edgeOf
          ((rotationSystem RS keep root).alpha (Sum.inl ⟨dart, hdart⟩))) :=
      congrArg coloring
        ((rotationSystem RS keep root).edge_alpha (Sum.inl ⟨dart, hdart⟩)).symm
    _ = coloring ((rotationSystem RS keep root).edgeOf
          (Sum.inr ⟨⟨dart, hdart⟩, halpha⟩)) := by
      rw [rotationSystem_alpha_old_of_boundary RS keep root ⟨dart, hdart⟩ halpha]

/-- Distinct ambient darts at one retained old vertex still receive distinct
colors from any proper coloring of the literal open region. -/
theorem openOldDartColor_proper
    (RS : RotationSystem V E) (keep : V → Prop)
    (root : Dart RS keep)
    (coloring : (rotationSystem RS keep root).EdgeColoring Color)
    {left right : RS.D}
    (hleft : keep (RS.vertOf left)) (hright : keep (RS.vertOf right))
    (hvertex : RS.vertOf left = RS.vertOf right) (hne : left ≠ right) :
    openOldDartColor RS keep root coloring left hleft ≠
      openOldDartColor RS keep root coloring right hright := by
  have hopenVertex :
      (rotationSystem RS keep root).vertOf (Sum.inl ⟨left, hleft⟩) =
        (rotationSystem RS keep root).vertOf (Sum.inl ⟨right, hright⟩) := by
    rw [rotationSystem_vertOf_old, rotationSystem_vertOf_old]
    apply congrArg Sum.inl
    apply Subtype.ext
    exact hvertex
  have hopenDartNe :
      (Sum.inl ⟨left, hleft⟩ : Dart RS keep) ≠ Sum.inl ⟨right, hright⟩ := by
    intro heq
    apply hne
    exact congrArg Subtype.val (Sum.inl.inj heq)
  have hopenEdgeNe :
      (rotationSystem RS keep root).edgeOf (Sum.inl ⟨left, hleft⟩) ≠
        (rotationSystem RS keep root).edgeOf (Sum.inl ⟨right, hright⟩) := by
    intro hedge
    apply hopenDartNe
    apply (rotationSystem RS keep root).edgeOf_injOn_dartsAt
      ((rotationSystem RS keep root).vertOf (Sum.inl ⟨left, hleft⟩))
    · simp [RotationSystem.dartsAt]
    · simp [RotationSystem.dartsAt, hopenVertex]
    · exact hedge
  unfold openOldDartColor
  apply coloring.valid
  apply ((rotationSystem RS keep root).edgeAdjacencyGraph_adj_iff).2
  refine ⟨hopenEdgeNe,
    (rotationSystem RS keep root).vertOf (Sum.inl ⟨left, hleft⟩), ?_, ?_⟩
  · exact ((rotationSystem RS keep root).mem_endpoints_iff).2
      ⟨Sum.inl ⟨left, hleft⟩, by simp, rfl⟩
  · exact ((rotationSystem RS keep root).mem_endpoints_iff).2
      ⟨Sum.inl ⟨right, hright⟩, by simp, hopenVertex.symm⟩

/-- The old-dart reading of a literal open Tait coloring is nonzero. -/
theorem openOldDartColor_ne_zero
    (RS : RotationSystem V E) (keep : V → Prop)
    (root : Dart RS keep)
    (coloring : (rotationSystem RS keep root).EdgeColoring Color)
    (hcoloring : (rotationSystem RS keep root).IsTaitEdgeColoring coloring)
    (dart : RS.D) (hdart : keep (RS.vertOf dart)) :
    openOldDartColor RS keep root coloring dart hdart ≠ 0 :=
  hcoloring _

/-- The exact data needed to glue two complementary literal open regions:
their readings agree across every exposed ambient edge.  The equality is
written on old darts; the preceding stub lemma identifies it with agreement
of the two genuine open-tangle boundary colors. -/
def BoundaryAgreement
    (RS : RotationSystem V E) (keep : V → Prop)
    (insideRoot : Dart RS keep)
    (outsideRoot : Dart RS (fun vertex => ¬ keep vertex))
    (inside : (rotationSystem RS keep insideRoot).EdgeColoring Color)
    (outside : (rotationSystem RS (fun vertex => ¬ keep vertex) outsideRoot).EdgeColoring
      Color) : Prop :=
  ∀ (dart : RS.D) (hinside : keep (RS.vertOf dart))
      (houtside : ¬ keep (RS.vertOf (RS.alpha dart))),
    openOldDartColor RS keep insideRoot inside dart hinside =
      openOldDartColor RS (fun vertex => ¬ keep vertex) outsideRoot outside
        (RS.alpha dart) houtside

/-- Glue the two open-region colorings by reading from the side containing
each ambient dart. -/
noncomputable def gluedDartColor
    (RS : RotationSystem V E) (keep : V → Prop)
    (insideRoot : Dart RS keep)
    (outsideRoot : Dart RS (fun vertex => ¬ keep vertex))
    (inside : (rotationSystem RS keep insideRoot).EdgeColoring Color)
    (outside : (rotationSystem RS (fun vertex => ¬ keep vertex) outsideRoot).EdgeColoring
      Color) : RS.D → Color := by
  classical
  exact fun dart =>
    if hinside : keep (RS.vertOf dart) then
      openOldDartColor RS keep insideRoot inside dart hinside
    else
      openOldDartColor RS (fun vertex => ¬ keep vertex) outsideRoot outside dart hinside

/-- The piecewise dart coloring is invariant across every original edge:
inside edges use one piece, outside edges use the other, and crossing edges
use the explicit boundary agreement. -/
theorem gluedDartColor_alpha
    (RS : RotationSystem V E) (keep : V → Prop)
    (insideRoot : Dart RS keep)
    (outsideRoot : Dart RS (fun vertex => ¬ keep vertex))
    (inside : (rotationSystem RS keep insideRoot).EdgeColoring Color)
    (outside : (rotationSystem RS (fun vertex => ¬ keep vertex) outsideRoot).EdgeColoring
      Color)
    (hagreement : BoundaryAgreement RS keep insideRoot outsideRoot inside outside)
    (dart : RS.D) :
    gluedDartColor RS keep insideRoot outsideRoot inside outside (RS.alpha dart) =
      gluedDartColor RS keep insideRoot outsideRoot inside outside dart := by
  classical
  unfold gluedDartColor
  by_cases hinside : keep (RS.vertOf dart)
  · by_cases halphaInside : keep (RS.vertOf (RS.alpha dart))
    · rw [dif_pos halphaInside, dif_pos hinside]
      exact openOldDartColor_alpha_of_internal RS keep insideRoot inside dart
        hinside halphaInside
    · rw [dif_neg halphaInside, dif_pos hinside]
      exact (hagreement dart hinside halphaInside).symm
  · by_cases halphaInside : keep (RS.vertOf (RS.alpha dart))
    · rw [dif_pos halphaInside, dif_neg hinside]
      have houtside : ¬ keep (RS.vertOf (RS.alpha (RS.alpha dart))) := by
        simpa only [RS.alpha_involutive] using hinside
      have hagreed := hagreement (RS.alpha dart) halphaInside houtside
      simpa only [RS.alpha_involutive] using hagreed
    · rw [dif_neg halphaInside, dif_neg hinside]
      exact openOldDartColor_alpha_of_internal RS
        (fun vertex => ¬ keep vertex) outsideRoot outside dart hinside halphaInside

/-- The piecewise dart coloring is locally proper because every ambient
vertex belongs to exactly one of the two old regions. -/
theorem gluedDartColor_proper
    (RS : RotationSystem V E) (keep : V → Prop)
    (insideRoot : Dart RS keep)
    (outsideRoot : Dart RS (fun vertex => ¬ keep vertex))
    (inside : (rotationSystem RS keep insideRoot).EdgeColoring Color)
    (outside : (rotationSystem RS (fun vertex => ¬ keep vertex) outsideRoot).EdgeColoring
      Color)
    {left right : RS.D}
    (hvertex : RS.vertOf left = RS.vertOf right) (hne : left ≠ right) :
    gluedDartColor RS keep insideRoot outsideRoot inside outside left ≠
      gluedDartColor RS keep insideRoot outsideRoot inside outside right := by
  classical
  unfold gluedDartColor
  by_cases hleft : keep (RS.vertOf left)
  · have hright : keep (RS.vertOf right) := by
      rw [← hvertex]
      exact hleft
    rw [dif_pos hleft, dif_pos hright]
    exact openOldDartColor_proper RS keep insideRoot inside hleft hright hvertex hne
  · have hright : ¬ keep (RS.vertOf right) := by
      intro hright
      apply hleft
      rwa [hvertex]
    rw [dif_neg hleft, dif_neg hright]
    exact openOldDartColor_proper RS (fun vertex => ¬ keep vertex)
      outsideRoot outside hleft hright hvertex hne

/-- Nonzero colors also glue sidewise. -/
theorem gluedDartColor_ne_zero
    (RS : RotationSystem V E) (keep : V → Prop)
    (insideRoot : Dart RS keep)
    (outsideRoot : Dart RS (fun vertex => ¬ keep vertex))
    (inside : (rotationSystem RS keep insideRoot).EdgeColoring Color)
    (outside : (rotationSystem RS (fun vertex => ¬ keep vertex) outsideRoot).EdgeColoring
      Color)
    (hinside : (rotationSystem RS keep insideRoot).IsTaitEdgeColoring inside)
    (houtside : (rotationSystem RS (fun vertex => ¬ keep vertex) outsideRoot).IsTaitEdgeColoring
      outside)
    (dart : RS.D) :
    gluedDartColor RS keep insideRoot outsideRoot inside outside dart ≠ 0 := by
  classical
  unfold gluedDartColor
  by_cases hkeep : keep (RS.vertOf dart)
  · rw [dif_pos hkeep]
    exact openOldDartColor_ne_zero RS keep insideRoot inside hinside dart hkeep
  · rw [dif_neg hkeep]
    exact openOldDartColor_ne_zero RS (fun vertex => ¬ keep vertex)
      outsideRoot outside houtside dart hkeep

/-- The closed edge coloring obtained by gluing two literal open pieces. -/
noncomputable def gluedColoring
    (RS : RotationSystem V E) (keep : V → Prop)
    (insideRoot : Dart RS keep)
    (outsideRoot : Dart RS (fun vertex => ¬ keep vertex))
    (inside : (rotationSystem RS keep insideRoot).EdgeColoring Color)
    (outside : (rotationSystem RS (fun vertex => ¬ keep vertex) outsideRoot).EdgeColoring
      Color)
    (hagreement : BoundaryAgreement RS keep insideRoot outsideRoot inside outside) :
    RS.EdgeColoring Color :=
  edgeColoringOfDartColor RS
    (gluedDartColor RS keep insideRoot outsideRoot inside outside)
    (gluedDartColor_alpha RS keep insideRoot outsideRoot inside outside hagreement)
    (gluedDartColor_proper RS keep insideRoot outsideRoot inside outside)

/-- The glued coloring is Tait when both literal open pieces are Tait and
their exposed boundary readings agree. -/
theorem gluedColoring_isTait
    (RS : RotationSystem V E) (keep : V → Prop)
    (insideRoot : Dart RS keep)
    (outsideRoot : Dart RS (fun vertex => ¬ keep vertex))
    (inside : (rotationSystem RS keep insideRoot).EdgeColoring Color)
    (outside : (rotationSystem RS (fun vertex => ¬ keep vertex) outsideRoot).EdgeColoring
      Color)
    (hinside : (rotationSystem RS keep insideRoot).IsTaitEdgeColoring inside)
    (houtside : (rotationSystem RS (fun vertex => ¬ keep vertex) outsideRoot).IsTaitEdgeColoring
      outside)
    (hagreement : BoundaryAgreement RS keep insideRoot outsideRoot inside outside) :
    RS.IsTaitEdgeColoring
      (gluedColoring RS keep insideRoot outsideRoot inside outside hagreement) :=
  edgeColoringOfDartColor_isTait RS
    (gluedDartColor RS keep insideRoot outsideRoot inside outside)
    (gluedDartColor_alpha RS keep insideRoot outsideRoot inside outside hagreement)
    (gluedDartColor_proper RS keep insideRoot outsideRoot inside outside)
    (gluedDartColor_ne_zero RS keep insideRoot outsideRoot inside outside
      hinside houtside)

/-- Existential form of literal open-region gluing. -/
theorem exists_taitColoring_of_openRegionColorings_of_boundaryAgreement
    (RS : RotationSystem V E) (keep : V → Prop)
    (insideRoot : Dart RS keep)
    (outsideRoot : Dart RS (fun vertex => ¬ keep vertex))
    (inside : (rotationSystem RS keep insideRoot).EdgeColoring Color)
    (outside : (rotationSystem RS (fun vertex => ¬ keep vertex) outsideRoot).EdgeColoring
      Color)
    (hinside : (rotationSystem RS keep insideRoot).IsTaitEdgeColoring inside)
    (houtside : (rotationSystem RS (fun vertex => ¬ keep vertex) outsideRoot).IsTaitEdgeColoring
      outside)
    (hagreement : BoundaryAgreement RS keep insideRoot outsideRoot inside outside) :
    ∃ closed : RS.EdgeColoring Color, RS.IsTaitEdgeColoring closed :=
  ⟨gluedColoring RS keep insideRoot outsideRoot inside outside hagreement,
    gluedColoring_isTait RS keep insideRoot outsideRoot inside outside
      hinside houtside hagreement⟩

end

end GoertzelV24OpenRegionColorGluing

end Mettapedia.GraphTheory.FourColor
