import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionRotation
import Mettapedia.GraphTheory.FourColor.GoertzelV24RewiredTaitColoring

/-!
# Tait-color restriction to a literal open region

An ambient Tait coloring restricts to the literal open region constructed in
`GoertzelV24OpenRegionRotation`: every retained old dart and every fresh
boundary stub receives the color of its originating ambient edge.  This is the
forward validation map from a closed map into the source route's open-piece
semantics.  It does not claim that arbitrary boundary colors glue back.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenRegionTaitInheritance

open GoertzelV24OpenRegionRotation
open GoertzelV24RotationSpliceConstructor
open SimpleGraph

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Color an open-region dart by the ambient edge from which it came. -/
def inheritedDartColor (RS : RotationSystem V E) (keep : V → Prop)
    (coloring : RS.EdgeColoring Color) : Dart RS keep → Color
  | Sum.inl dart => coloring (RS.edgeOf dart.1)
  | Sum.inr boundary => coloring (RS.edgeOf boundary.1.1)

/-- Read any literal open-region edge coloring at one of its oriented darts.
This applies to arbitrary open colorings, not only ones inherited from an
ambient closed map. -/
def dartColor (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep)
    (coloring : (rotationSystem RS keep outer).EdgeColoring Color)
    (dart : Dart RS keep) : Color :=
  coloring ((rotationSystem RS keep outer).edgeOf dart)

/-- A Tait coloring of a literal open region is nonzero at every old dart and
every newly created boundary stub. -/
theorem dartColor_ne_zero
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep)
    (coloring : (rotationSystem RS keep outer).EdgeColoring Color)
    (hcoloring : (rotationSystem RS keep outer).IsTaitEdgeColoring coloring)
    (dart : Dart RS keep) :
    dartColor RS keep outer coloring dart ≠ 0 :=
  hcoloring _

/-- The inherited colors are constant on every new open-region edge. -/
theorem inheritedDartColor_alpha
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep) (coloring : RS.EdgeColoring Color) :
    ∀ dart : Dart RS keep,
      inheritedDartColor RS keep coloring
          ((rewiredDartSystem RS keep outer).alpha dart) =
        inheritedDartColor RS keep coloring dart := by
  classical
  intro dart
  rcases dart with dart | boundary
  · by_cases hinternal : keep (RS.vertOf (RS.alpha dart.1))
    · simp [inheritedDartColor, rewiredDartSystem, alpha, alphaFun,
        hinternal, RS.edge_alpha]
    · simp [inheritedDartColor, rewiredDartSystem, alpha, alphaFun,
        hinternal]
  · simp [inheritedDartColor, rewiredDartSystem, alpha, alphaFun]

/-- Properness of the ambient edge coloring survives at old retained vertices;
at a fresh boundary vertex there is only one incident dart. -/
theorem inheritedDartColor_proper
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep) (coloring : RS.EdgeColoring Color) :
    ∀ {left right : Dart RS keep},
      (rewiredDartSystem RS keep outer).vertOf left =
          (rewiredDartSystem RS keep outer).vertOf right →
        left ≠ right →
          inheritedDartColor RS keep coloring left ≠
            inheritedDartColor RS keep coloring right := by
  intro left right hvertex hne
  rcases left with left | left <;> rcases right with right | right
  · have hvertex' : RS.vertOf left.1 = RS.vertOf right.1 :=
      congrArg Subtype.val (Sum.inl.inj hvertex)
    have hedges : RS.edgeOf left.1 ≠ RS.edgeOf right.1 := by
      intro hedge
      apply hne
      apply congrArg Sum.inl
      apply Subtype.ext
      exact RS.edgeOf_injOn_dartsAt (RS.vertOf left.1)
        (by simp [RotationSystem.dartsAt])
        (by simp [RotationSystem.dartsAt, hvertex']) hedge
    unfold inheritedDartColor
    apply coloring.valid
    apply (RS.edgeAdjacencyGraph_adj_iff).2
    refine ⟨hedges, RS.vertOf left.1, ?_, ?_⟩
    · exact (RS.mem_endpoints_iff).2 ⟨left.1, by simp, rfl⟩
    · exact (RS.mem_endpoints_iff).2
        ⟨right.1, by simp, hvertex'.symm⟩
  · cases hvertex
  · cases hvertex
  · have hboundary : left = right := Sum.inr.inj hvertex
    subst right
    exact (hne rfl).elim

/-- Every inherited open-region dart is nonzero when the ambient coloring is
Tait. -/
theorem inheritedDartColor_nonzero
    (RS : RotationSystem V E) (keep : V → Prop)
    (coloring : RS.EdgeColoring Color) (hcoloring : RS.IsTaitEdgeColoring coloring) :
    ∀ dart : Dart RS keep, inheritedDartColor RS keep coloring dart ≠ 0 := by
  intro dart
  rcases dart with dart | boundary
  · exact hcoloring _
  · exact hcoloring _

/-- Restrict an ambient edge coloring to the actual open-region rotation
system. -/
noncomputable def inheritedColoring
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep) (coloring : RS.EdgeColoring Color) :
    (rotationSystem RS keep outer).EdgeColoring Color :=
  (rewiredDartSystem RS keep outer).descendedColoring
    (inheritedDartColor RS keep coloring)
    (inheritedDartColor_alpha RS keep outer coloring)
    (inheritedDartColor_proper RS keep outer coloring)

/-- The inherited edge coloring reads back the ambient edge color assigned to
either source dart of an open-region edge. -/
theorem inheritedColoring_edgeOf
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep) (coloring : RS.EdgeColoring Color)
    (dart : Dart RS keep) :
    inheritedColoring RS keep outer coloring
        ((rotationSystem RS keep outer).edgeOf dart) =
      inheritedDartColor RS keep coloring dart := by
  change (rewiredDartSystem RS keep outer).descendedEdgeColor
      (inheritedDartColor RS keep coloring)
      ((rewiredDartSystem RS keep outer).edgeOf dart) = _
  exact (rewiredDartSystem RS keep outer).descendedEdgeColor_edgeOf
    (inheritedDartColor RS keep coloring)
    (inheritedDartColor_alpha RS keep outer coloring) dart

/-- The restricted coloring is Tait whenever its ambient parent is Tait. -/
theorem inheritedColoring_isTait
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep) (coloring : RS.EdgeColoring Color)
    (hcoloring : RS.IsTaitEdgeColoring coloring) :
    (rotationSystem RS keep outer).IsTaitEdgeColoring
      (inheritedColoring RS keep outer coloring) := by
  exact (rewiredDartSystem RS keep outer).descendedColoring_isTait
    (inheritedDartColor RS keep coloring)
    (inheritedDartColor_alpha RS keep outer coloring)
    (inheritedDartColor_proper RS keep outer coloring)
    (inheritedDartColor_nonzero RS keep coloring hcoloring)

/-- A closed Tait coloring gives a concrete Tait coloring of every literal
open region with a chosen root dart. -/
theorem exists_taitColoring_of_ambientTaitColoring
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep) (coloring : RS.EdgeColoring Color)
    (hcoloring : RS.IsTaitEdgeColoring coloring) :
    ∃ openColoring : (rotationSystem RS keep outer).EdgeColoring Color,
      (rotationSystem RS keep outer).IsTaitEdgeColoring openColoring :=
  ⟨inheritedColoring RS keep outer coloring,
    inheritedColoring_isTait RS keep outer coloring hcoloring⟩

end

end GoertzelV24OpenRegionTaitInheritance

end Mettapedia.GraphTheory.FourColor
