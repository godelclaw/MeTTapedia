import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutOpenTaitColoring
import Mettapedia.GraphTheory.FourColor.GoertzelV24RewiredTaitColoring

/-!
# Restricting closed Tait colorings to a cut-open annular interface

The open coloring semantics is not a new hypothesis: every Tait coloring of
the original closed rotation system restricts to one of its simultaneous
slit.  On each opened primal edge both new boundary stubs inherit the old edge
color.  This is the validation direction from the existing closed-map
formalization into the source's open-piece semantics.

The converse is deliberately not asserted: an arbitrary open coloring may
assign independent boundary data and need not glue to a coloring of the old
closed map.  Those independent states are exactly what the transfer count
must retain.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24AnnularCrosscutSlitRotation
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RotationSpliceConstructor
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance openTaitInheritanceGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace AlignedSimpleDualCrosscuts

/-- Color each slit dart by the color of the original primal edge from which
it came.  In particular, the old dart and its newly exposed stub agree. -/
def inheritedSlitDartColor
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (coloring : RS.EdgeColoring Color) :
    SlitDart RS pair.crossingSupport → Color
  | .inl dart => coloring (RS.edgeOf dart)
  | .inr port => coloring (RS.edgeOf port.1)

/-- The inherited dart colors are constant on every newly rewired slit edge. -/
theorem inheritedSlitDartColor_alpha
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (coloring : RS.EdgeColoring Color) :
    ∀ dart : SlitDart RS pair.crossingSupport,
      pair.inheritedSlitDartColor coloring
          ((slitRewiredDartSystem RS pair.crossingSupport).alpha dart) =
        pair.inheritedSlitDartColor coloring dart := by
  intro dart
  rcases dart with dart | port
  · by_cases hcut : RS.edgeOf dart ∈ pair.crossingSupport
    · simp [inheritedSlitDartColor, slitRewiredDartSystem, slitAlpha,
        slitAlphaFun, hcut]
    · simp [inheritedSlitDartColor, slitRewiredDartSystem, slitAlpha,
        slitAlphaFun, hcut, RS.edge_alpha]
  · simp [inheritedSlitDartColor, slitRewiredDartSystem, slitAlpha,
      slitAlphaFun]

/-- Properness of a closed coloring remains proper at every old vertex of the
slit.  A fresh stub has one dart, so its case is vacuous. -/
theorem inheritedSlitDartColor_proper
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (coloring : RS.EdgeColoring Color) :
    ∀ {left right : SlitDart RS pair.crossingSupport},
      (slitRewiredDartSystem RS pair.crossingSupport).vertOf left =
        (slitRewiredDartSystem RS pair.crossingSupport).vertOf right →
      left ≠ right →
      pair.inheritedSlitDartColor coloring left ≠
        pair.inheritedSlitDartColor coloring right := by
  intro left right hvertex hne
  rcases left with left | left <;> rcases right with right | right
  · have hvertex' : RS.vertOf left = RS.vertOf right :=
      Sum.inl.inj hvertex
    have hedges : RS.edgeOf left ≠ RS.edgeOf right := by
      intro hedge
      apply hne
      exact congrArg Sum.inl
        (RS.edgeOf_injOn_dartsAt (RS.vertOf left)
          (by simp [RotationSystem.dartsAt])
          (by simp [RotationSystem.dartsAt, hvertex']) hedge)
    apply coloring.valid
    apply (RS.edgeAdjacencyGraph_adj_iff).2
    refine ⟨hedges, RS.vertOf left, ?_, ?_⟩
    · exact (RS.mem_endpoints_iff).2 ⟨left, by simp, rfl⟩
    · exact (RS.mem_endpoints_iff).2 ⟨right, by simp, hvertex'.symm⟩
  · cases hvertex
  · cases hvertex
  · have hports : left = right := Sum.inr.inj hvertex
    subst right
    exact (hne rfl).elim

/-- Every inherited slit dart has a nonzero color when the original coloring
is Tait. -/
theorem inheritedSlitDartColor_nonzero
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (coloring : RS.EdgeColoring Color) (hcoloring : RS.IsTaitEdgeColoring coloring) :
    ∀ dart : SlitDart RS pair.crossingSupport,
      pair.inheritedSlitDartColor coloring dart ≠ 0 := by
  intro dart
  rcases dart with dart | port
  · exact hcoloring _
  · exact hcoloring _

/-- A closed Tait coloring restricted through the simultaneous slit. -/
noncomputable def inheritedOpenTaitColoring
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (coloring : RS.EdgeColoring Color) : pair.OpenTaitColoring :=
  (slitRewiredDartSystem RS pair.crossingSupport).descendedColoring
    (pair.inheritedSlitDartColor coloring)
    (pair.inheritedSlitDartColor_alpha coloring)
    (pair.inheritedSlitDartColor_proper coloring)

/-- Restriction preserves the nonzero Tait condition, so a closed coloring
gives an actual point of the open coloring fiber. -/
theorem inheritedOpenTaitColoring_isOpenTaitColoring
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (coloring : RS.EdgeColoring Color) (hcoloring : RS.IsTaitEdgeColoring coloring) :
    pair.IsOpenTaitColoring (pair.inheritedOpenTaitColoring coloring) := by
  exact (slitRewiredDartSystem RS pair.crossingSupport).descendedColoring_isTait
    (pair.inheritedSlitDartColor coloring)
    (pair.inheritedSlitDartColor_alpha coloring)
    (pair.inheritedSlitDartColor_proper coloring)
    (pair.inheritedSlitDartColor_nonzero coloring hcoloring)

/-- At a left stub, the restricted open coloring reads the original primal
edge color exactly. -/
theorem inheritedOpenTaitColoring_leftBoundaryColor
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (coloring : RS.EdgeColoring Color) (endpoint : pair.LeftInterfaceEnd) :
    pair.leftBoundaryColor (pair.inheritedOpenTaitColoring coloring) endpoint =
      coloring (RS.edgeOf endpoint.2.1) := by
  change (slitRewiredDartSystem RS pair.crossingSupport).descendedEdgeColor
      (pair.inheritedSlitDartColor coloring)
      ((slitRewiredDartSystem RS pair.crossingSupport).edgeOf
        (pair.leftInterfaceStub endpoint)) = _
  rw [(slitRewiredDartSystem RS pair.crossingSupport).descendedEdgeColor_edgeOf
    (pair.inheritedSlitDartColor coloring)
    (pair.inheritedSlitDartColor_alpha coloring)]
  rfl

/-- At a right stub, the restricted open coloring reads the original primal
edge color exactly. -/
theorem inheritedOpenTaitColoring_rightBoundaryColor
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (coloring : RS.EdgeColoring Color) (endpoint : pair.RightInterfaceEnd) :
    pair.rightBoundaryColor (pair.inheritedOpenTaitColoring coloring) endpoint =
      coloring (RS.edgeOf endpoint.2.1) := by
  change (slitRewiredDartSystem RS pair.crossingSupport).descendedEdgeColor
      (pair.inheritedSlitDartColor coloring)
      ((slitRewiredDartSystem RS pair.crossingSupport).edgeOf
        (pair.rightInterfaceStub endpoint)) = _
  rw [(slitRewiredDartSystem RS pair.crossingSupport).descendedEdgeColor_edgeOf
    (pair.inheritedSlitDartColor coloring)
    (pair.inheritedSlitDartColor_alpha coloring)]
  rfl

/-- The boundary-color count contains the restriction of every closed Tait
coloring, at its two induced open boundary words. -/
theorem openTaitBoundaryColorCount_pos_of_closedTaitColoring
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (coloring : RS.EdgeColoring Color) (hcoloring : RS.IsTaitEdgeColoring coloring) :
    0 < pair.openTaitBoundaryColorCount
      (pair.leftBoundaryWord (pair.inheritedOpenTaitColoring coloring))
      (pair.rightBoundaryWord (pair.inheritedOpenTaitColoring coloring)) := by
  rw [openTaitBoundaryColorCount_apply]
  apply Finset.card_pos.mpr
  refine ⟨pair.inheritedOpenTaitColoring coloring, ?_⟩
  apply (pair.mem_openTaitColoringFiber_iff _ _ _).2
  exact ⟨pair.inheritedOpenTaitColoring_isOpenTaitColoring coloring hcoloring,
    rfl, rfl⟩

end AlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
