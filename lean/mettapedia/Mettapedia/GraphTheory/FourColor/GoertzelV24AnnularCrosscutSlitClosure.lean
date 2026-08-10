import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutSlitRotation
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationDartColoring

/-!
# Closing a cut-open rotation system

An open tangle becomes an original closed map precisely when the colors on
the two boundary stubs created from each cut edge agree.  This file proves
that elementary gluing operation for arbitrary finite rotation systems.  It
is the local color-level construction used by the compositional splice; no
configuration catalogue or covering-style reduction is involved.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscutSlitClosure

open GoertzelV24AnnularCrosscutSlitRotation
open GoertzelV24RotationDartColoring
open GoertzelV24RotationSpliceConstructor
open SimpleGraph

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Read a slit edge coloring at one of its darts. -/
def slitDartColor
    (RS : RotationSystem V E) (cut : Finset E)
    (coloring : (slitRotationSystem RS cut).EdgeColoring Color)
    (dart : SlitDart RS cut) : Color :=
  coloring ((slitRotationSystem RS cut).edgeOf dart)

/-- Read a slit coloring on the old oriented end of an original edge. -/
def oldSlitDartColor
    (RS : RotationSystem V E) (cut : Finset E)
    (coloring : (slitRotationSystem RS cut).EdgeColoring Color)
    (dart : RS.D) : Color :=
  slitDartColor RS cut coloring (Sum.inl dart)

/-- Read a slit coloring on one newly created boundary stub. -/
def slitStubColor
    (RS : RotationSystem V E) (cut : Finset E)
    (coloring : (slitRotationSystem RS cut).EdgeColoring Color)
    (port : CutDart RS cut) : Color :=
  slitDartColor RS cut coloring (Sum.inr port)

/-- A slit edge coloring is constant across its own edge involution. -/
theorem slitDartColor_alpha
    (RS : RotationSystem V E) (cut : Finset E)
    (coloring : (slitRotationSystem RS cut).EdgeColoring Color)
    (dart : SlitDart RS cut) :
    slitDartColor RS cut coloring ((slitRotationSystem RS cut).alpha dart) =
      slitDartColor RS cut coloring dart := by
  unfold slitDartColor
  rw [(slitRotationSystem RS cut).edge_alpha]

/-- On a cut edge, the old slit dart and its fresh boundary stub have the
same color. -/
theorem oldSlitDartColor_eq_stub
    (RS : RotationSystem V E) (cut : Finset E)
    (coloring : (slitRotationSystem RS cut).EdgeColoring Color)
    (dart : RS.D) (hcut : RS.edgeOf dart ∈ cut) :
    oldSlitDartColor RS cut coloring dart =
      slitStubColor RS cut coloring ⟨dart, hcut⟩ := by
  have halpha := slitDartColor_alpha RS cut coloring (Sum.inl dart)
  simpa [oldSlitDartColor, slitStubColor,
    slitRotationSystem_alpha_old_of_mem RS cut hcut] using halpha.symm

/-- On an uncut edge, the two old slit darts still form one edge. -/
theorem oldSlitDartColor_alpha_of_not_mem
    (RS : RotationSystem V E) (cut : Finset E)
    (coloring : (slitRotationSystem RS cut).EdgeColoring Color)
    (dart : RS.D) (hcut : RS.edgeOf dart ∉ cut) :
    oldSlitDartColor RS cut coloring (RS.alpha dart) =
      oldSlitDartColor RS cut coloring dart := by
  have halpha := slitDartColor_alpha RS cut coloring (Sum.inl dart)
  simpa [oldSlitDartColor,
    slitRotationSystem_alpha_old_of_not_mem RS cut hcut] using halpha

/-- Agreement of the two boundary stubs for each cut edge is exactly the
missing alpha-invariance needed to close the slit. -/
theorem oldSlitDartColor_alpha_of_stubAgreement
    (RS : RotationSystem V E) (cut : Finset E)
    (coloring : (slitRotationSystem RS cut).EdgeColoring Color)
    (hstub : ∀ (dart : RS.D) (hcut : RS.edgeOf dart ∈ cut),
      slitStubColor RS cut coloring
          ⟨RS.alpha dart, by simpa only [RS.edge_alpha dart] using hcut⟩ =
        slitStubColor RS cut coloring ⟨dart, hcut⟩)
    (dart : RS.D) :
    oldSlitDartColor RS cut coloring (RS.alpha dart) =
      oldSlitDartColor RS cut coloring dart := by
  by_cases hcut : RS.edgeOf dart ∈ cut
  · have hcutAlpha : RS.edgeOf (RS.alpha dart) ∈ cut := by
      simpa only [RS.edge_alpha dart] using hcut
    calc
      oldSlitDartColor RS cut coloring (RS.alpha dart) =
          slitStubColor RS cut coloring ⟨RS.alpha dart, hcutAlpha⟩ :=
        oldSlitDartColor_eq_stub RS cut coloring (RS.alpha dart) hcutAlpha
      _ = slitStubColor RS cut coloring ⟨dart, hcut⟩ := by
        simpa only using hstub dart hcut
      _ = oldSlitDartColor RS cut coloring dart :=
        (oldSlitDartColor_eq_stub RS cut coloring dart hcut).symm
  · exact oldSlitDartColor_alpha_of_not_mem RS cut coloring dart hcut

/-- Two distinct old darts at a common original vertex still name distinct
slit edges.  Cutting can split an edge, but it cannot identify two distinct
incident edges. -/
theorem slitOldEdge_ne_of_distinct_at_vertex
    (RS : RotationSystem V E) (cut : Finset E)
    {left right : RS.D}
    (hvertex : RS.vertOf left = RS.vertOf right) (hne : left ≠ right) :
    (slitRotationSystem RS cut).edgeOf (Sum.inl left) ≠
      (slitRotationSystem RS cut).edgeOf (Sum.inl right) := by
  intro hedge
  rcases ((slitRewiredDartSystem RS cut).edgeOf_eq_edgeOf_iff
      (Sum.inl left) (Sum.inl right)).1 hedge with hsame | hopposite
  · exact hne (Sum.inl.inj hsame)
  · by_cases hcut : RS.edgeOf right ∈ cut
    · change Sum.inl left = slitAlpha RS cut (Sum.inl right) at hopposite
      rw [slitAlpha_old_of_mem RS cut hcut] at hopposite
      cases hopposite
    · change Sum.inl left = slitAlpha RS cut (Sum.inl right) at hopposite
      rw [slitAlpha_old_of_not_mem RS cut hcut] at hopposite
      have halpha : left = RS.alpha right := Sum.inl.inj hopposite
      apply RS.no_self_loops right
      rw [← halpha]
      exact hvertex.symm

/-- Properness of a slit edge coloring restricts to the old dart carrier. -/
theorem oldSlitDartColor_proper
    (RS : RotationSystem V E) (cut : Finset E)
    (coloring : (slitRotationSystem RS cut).EdgeColoring Color)
    {left right : RS.D}
    (hvertex : RS.vertOf left = RS.vertOf right) (hne : left ≠ right) :
    oldSlitDartColor RS cut coloring left ≠
      oldSlitDartColor RS cut coloring right := by
  unfold oldSlitDartColor slitDartColor
  apply coloring.valid
  apply ((slitRotationSystem RS cut).edgeAdjacencyGraph_adj_iff).2
  refine ⟨slitOldEdge_ne_of_distinct_at_vertex RS cut hvertex hne,
    Sum.inl (RS.vertOf left), ?_, ?_⟩
  · exact ((slitRotationSystem RS cut).mem_endpoints_iff).2
      ⟨Sum.inl left, ((slitRotationSystem RS cut).mem_dartsOn).2 rfl, rfl⟩
  · exact ((slitRotationSystem RS cut).mem_endpoints_iff).2
      ⟨Sum.inl right, ((slitRotationSystem RS cut).mem_dartsOn).2 rfl,
        by
          exact congrArg
            (fun vertex : V => (Sum.inl vertex : SlitVertex RS cut)) hvertex.symm⟩

/-- A Tait coloring of the slit is nonzero on every old dart. -/
theorem oldSlitDartColor_ne_zero
    (RS : RotationSystem V E) (cut : Finset E)
    (coloring : (slitRotationSystem RS cut).EdgeColoring Color)
    (hcoloring : (slitRotationSystem RS cut).IsTaitEdgeColoring coloring)
    (dart : RS.D) :
    oldSlitDartColor RS cut coloring dart ≠ 0 :=
  hcoloring _

/-- Close a slit coloring when its paired boundary stubs agree. -/
noncomputable def closedSlitColoring
    (RS : RotationSystem V E) (cut : Finset E)
    (coloring : (slitRotationSystem RS cut).EdgeColoring Color)
    (hstub : ∀ (dart : RS.D) (hcut : RS.edgeOf dart ∈ cut),
      slitStubColor RS cut coloring
          ⟨RS.alpha dart, by simpa only [RS.edge_alpha dart] using hcut⟩ =
        slitStubColor RS cut coloring ⟨dart, hcut⟩) :
    RS.EdgeColoring Color :=
  edgeColoringOfDartColor RS (oldSlitDartColor RS cut coloring)
    (oldSlitDartColor_alpha_of_stubAgreement RS cut coloring hstub)
    (fun hvertex hne => oldSlitDartColor_proper RS cut coloring hvertex hne)

/-- The closed coloring reads the same value as the open coloring on either
old dart of an original edge. -/
theorem closedSlitColoring_edgeOf
    (RS : RotationSystem V E) (cut : Finset E)
    (coloring : (slitRotationSystem RS cut).EdgeColoring Color)
    (hstub : ∀ (dart : RS.D) (hcut : RS.edgeOf dart ∈ cut),
      slitStubColor RS cut coloring
          ⟨RS.alpha dart, by simpa only [RS.edge_alpha dart] using hcut⟩ =
        slitStubColor RS cut coloring ⟨dart, hcut⟩)
    (dart : RS.D) :
    closedSlitColoring RS cut coloring hstub (RS.edgeOf dart) =
      oldSlitDartColor RS cut coloring dart :=
  edgeColoringOfDartColor_edgeOf RS (oldSlitDartColor RS cut coloring)
    (oldSlitDartColor_alpha_of_stubAgreement RS cut coloring hstub)
    (fun hvertex hne => oldSlitDartColor_proper RS cut coloring hvertex hne) dart

/-- Closing an open Tait coloring with agreed stubs produces a Tait coloring
of the original rotation system. -/
theorem closedSlitColoring_isTait
    (RS : RotationSystem V E) (cut : Finset E)
    (coloring : (slitRotationSystem RS cut).EdgeColoring Color)
    (hcoloring : (slitRotationSystem RS cut).IsTaitEdgeColoring coloring)
    (hstub : ∀ (dart : RS.D) (hcut : RS.edgeOf dart ∈ cut),
      slitStubColor RS cut coloring
          ⟨RS.alpha dart, by simpa only [RS.edge_alpha dart] using hcut⟩ =
        slitStubColor RS cut coloring ⟨dart, hcut⟩) :
    RS.IsTaitEdgeColoring (closedSlitColoring RS cut coloring hstub) :=
  edgeColoringOfDartColor_isTait RS (oldSlitDartColor RS cut coloring)
    (oldSlitDartColor_alpha_of_stubAgreement RS cut coloring hstub)
    (fun hvertex hne => oldSlitDartColor_proper RS cut coloring hvertex hne)
    (oldSlitDartColor_ne_zero RS cut coloring hcoloring)

/-- A literal cut-open Tait coloring whose paired stubs agree closes to a
Tait coloring of the original map. -/
theorem exists_taitColoring_of_slitTaitColoring_of_stubAgreement
    (RS : RotationSystem V E) (cut : Finset E)
    (coloring : (slitRotationSystem RS cut).EdgeColoring Color)
    (hcoloring : (slitRotationSystem RS cut).IsTaitEdgeColoring coloring)
    (hstub : ∀ (dart : RS.D) (hcut : RS.edgeOf dart ∈ cut),
      slitStubColor RS cut coloring
          ⟨RS.alpha dart, by simpa only [RS.edge_alpha dart] using hcut⟩ =
        slitStubColor RS cut coloring ⟨dart, hcut⟩) :
    ∃ closed : RS.EdgeColoring Color, RS.IsTaitEdgeColoring closed :=
  ⟨closedSlitColoring RS cut coloring hstub,
    closedSlitColoring_isTait RS cut coloring hcoloring hstub⟩

end

end GoertzelV24AnnularCrosscutSlitClosure

end Mettapedia.GraphTheory.FourColor
