import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnNestedCuts
import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedVertexSideEdgeShore

/-!
# Strict material between nested residual-return cuts

Four returns in strict nesting order contain more information than the
three-return side-containment theorem uses.  The innermost return orients the
deep separator.  The shallower return path then lies on the opposite side of
that separator, while it remains part of the shallower separator itself.

This file proves that the shallower physical path also remains outside rooted
saturation of the deep side.  It is the material witness needed to upgrade a
nested pair of connected cut shores from inclusion to strict inclusion.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace ResidualReturnStrictNesting

open AlternatingSiteGeometry
open CyclePushOffCut
open GoertzelV24CyclicThreeCutConnectedSides
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24ConnectedVertexSideEdgeShore
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24ResidualReturnShore
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open Mettapedia.GraphTheory.Embedding
open ResidualReturnComplementaryCycle
open ResidualReturnNestedFamily
open ResidualReturnSeparatorNesting
open RootedCutSaturation
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance finiteGraphLocallyFinite : G.LocallyFinite := fun vertex =>
  @Subtype.fintype V (Membership.mem (G.neighborSet vertex))
    (inferInstance : DecidablePred (Membership.mem (G.neighborSet vertex)))
    inferInstance

/-- A carrier position before the left endpoint of a chord lies on its
complementary carrier interval. -/
theorem cycleVertexOrder_mem_complementaryCycleInterval_support_of_lt_left
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingComponentWitness G sigma first second)
    {pairing : Pairing (CyclePosition sigma site)}
    (chord : OrderedReturnChord pairing)
    (position : CyclePosition sigma site)
    (hposition : position < chord.left) :
    (cycleVertexOrder sigma site position).1 ∈
      (complementaryCycleInterval sigma site chord).support := by
  have hmem : (cycleVertexOrder sigma site position).1 ∈
      site.cycle.tail.support := by
    rw [cycleVertexOrder_apply_val]
    exact List.get_mem _ _
  have hidx : site.cycle.tail.support.idxOf
      (cycleVertexOrder sigma site position).1 = position.val := by
    rw [cycleVertexOrder_apply_val,
      List.get_idxOf site.cycle_isCycle.isPath_tail.support_nodup position]
  rw [complementaryCycleInterval_support]
  apply List.mem_append.mpr
  right
  exact (List.mem_take_iff_idxOf_lt hmem).2 (by
    rw [hidx]
    exact Nat.lt_succ_of_lt (Fin.mk_lt_mk.mp hposition))

/-- A carrier position before the left endpoint also lies on the full
complementary return cycle. -/
theorem cycleVertexOrder_mem_complementaryReturnCycle_support_of_lt_left
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingComponentWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (position : CyclePosition sigma site)
    (hposition : position < chord.left) :
    (cycleVertexOrder sigma site position).1 ∈
      (complementaryReturnCycle hG sigma hSigma site chord).support := by
  let interval := complementaryCycleInterval sigma site chord
  have hinterval : (cycleVertexOrder sigma site position).1 ∈
      interval.support := by
    simpa only [interval] using
      cycleVertexOrder_mem_complementaryCycleInterval_support_of_lt_left
        sigma site chord position hposition
  have hintervalNotNil : ¬interval.Nil := by
    apply SimpleGraph.Walk.not_nil_of_ne
    intro heq
    have hpositions : chord.right = chord.left := by
      apply (cycleVertexOrder sigma site).injective
      exact Subtype.ext heq
    exact (ne_of_gt chord.left_lt_right) hpositions
  have htail : (cycleVertexOrder sigma site position).1 ∈
      interval.support.tail := by
    rw [← interval.cons_support_tail hintervalNotNil] at hinterval
    rcases List.mem_cons.mp hinterval with hstart | htail
    · have hpositions : position = chord.right := by
        apply (cycleVertexOrder sigma site).injective
        exact Subtype.ext hstart
      subst position
      exfalso
      exact (not_lt_of_ge chord.left_lt_right.le) hposition
    · simpa only [interval.support_tail_of_not_nil hintervalNotNil] using htail
  unfold complementaryReturnCycle
  rw [SimpleGraph.Walk.support_append]
  exact List.mem_append_right _ htail

/-- In a four-return nest, the complementary cycle of the shallow middle
return lies wholly outside the selected side of the deep middle separator.
The innermost guard determines the selected label; the shallow and inner
third darts read opposite labels across the deep separator. -/
theorem shallow_complementaryReturnCycle_outside_deep_filledCycleSide
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (outer shallow deep inner : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma bond.site))
    (houterShallowLeft : outer.left < shallow.left)
    (hshallowDeepLeft : shallow.left < deep.left)
    (hdeepInnerLeft : deep.left < inner.left)
    (hinnerDeepRight : inner.right < deep.right)
    (hdeepShallowRight : deep.right < shallow.right)
    (hshallowOuterRight : shallow.right < outer.right)
    (hshoreOuterShallow :
      orderedReturnShore rotation hG sigma hSigma bond outer.left =
        orderedReturnShore rotation hG sigma hSigma bond shallow.left)
    (hshoreShallowDeep :
      orderedReturnShore rotation hG sigma hSigma bond shallow.left =
        orderedReturnShore rotation hG sigma hSigma bond deep.left)
    (hshoreDeepInner :
      orderedReturnShore rotation hG sigma hSigma bond deep.left =
        orderedReturnShore rotation hG sigma hSigma bond inner.left)
    (cut : ExactFaceCut rotation.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈
        (orderedReturnSeparator hG sigma hSigma bond.site deep).edges) F2)
    (selected : F2)
    (houtside : ∀ vertex,
      vertex ∈
          (complementaryReturnCycle hG sigma hSigma bond.site outer).support →
        ¬cut.filledCycleSide rotation
          (orderedReturnSeparator hG sigma hSigma bond.site deep)
          selected vertex) :
    ∀ vertex,
      vertex ∈
          (complementaryReturnCycle hG sigma hSigma bond.site shallow).support →
        ¬cut.filledCycleSide rotation
          (orderedReturnSeparator hG sigma hSigma bond.site deep)
          selected vertex := by
  let separator := orderedReturnSeparator hG sigma hSigma bond.site deep
  let shallowCycle :=
    complementaryReturnCycle hG sigma hSigma bond.site shallow
  have houterDeepLeft : outer.left < deep.left :=
    houterShallowLeft.trans hshallowDeepLeft
  have hdeepOuterRight : deep.right < outer.right :=
    hdeepShallowRight.trans hshallowOuterRight
  have hshoreOuterDeep :
      orderedReturnShore rotation hG sigma hSigma bond outer.left =
        orderedReturnShore rotation hG sigma hSigma bond deep.left :=
    hshoreOuterShallow.trans hshoreShallowDeep
  have hinnerLabel :=
    label_inner_thirdDart_eq_selected_of_outer_complement_outside
      rotation minimal hG sigma hSigma bond outer deep inner
        houterDeepLeft hdeepInnerLeft hinnerDeepRight hdeepOuterRight
        hshoreOuterDeep hshoreDeepInner cut selected houtside
  have hlabelsNe := label_ne_outer_inner_thirdDarts_of_triple_nested
    rotation minimal hG sigma hSigma bond shallow deep inner
      hshallowDeepLeft hdeepInnerLeft hinnerDeepRight hdeepShallowRight
      hshoreShallowDeep hshoreDeepInner cut
  let shallowDart := siteThirdDart hG sigma hSigma bond.site
    (cycleVertexOrder sigma bond.site shallow.left)
  have hshallowLabelNe :
      cut.label (dartOrbitFace rotation.toRotationSystem shallowDart) ≠
        selected := by
    intro hshallow
    apply hlabelsNe
    exact hshallow.trans hinnerLabel.symm
  have hdisjoint : shallowCycle.support.Disjoint separator.support := by
    simpa only [shallowCycle, separator] using
      complementaryReturnCycle_support_disjoint_orderedReturnSeparator
        hG sigma hSigma bond.site shallow deep
          hshallowDeepLeft hdeepShallowRight
  have hbaseMem : (cycleVertexOrder sigma bond.site shallow.left).1 ∈
      shallowCycle.support := by
    simp [shallowCycle, complementaryReturnCycle]
  have hbaseOff : (cycleVertexOrder sigma bond.site shallow.left).1 ∉
      separator.support := by
    intro hseparator
    exact (List.disjoint_left.mp hdisjoint) hbaseMem hseparator
  have hread := cut.filledCycleSide_iff_label_of_not_mem_support
    rotation minimal.vertexRotationCyclic separator selected shallowDart
      (by simpa [shallowDart, siteThirdDart] using hbaseOff)
  have hbaseOutside : ¬cut.filledCycleSide rotation separator selected
      (cycleVertexOrder sigma bond.site shallow.left).1 := by
    intro hside
    apply hshallowLabelNe
    exact hread.mp (by simpa [shallowDart, siteThirdDart] using hside)
  intro vertex hvertex hvertexSide
  have havoid : ∀ point ∈
      (shallowCycle.takeUntil vertex hvertex).support,
      point ∉ separator.support := by
    intro point hpoint hseparator
    apply (List.disjoint_left.mp hdisjoint)
      (shallowCycle.support_takeUntil_subset_support hvertex hpoint)
      hseparator
  exact hbaseOutside
    ((filledCycleSide_iff_of_walk_avoids_support rotation
      minimal.vertexRotationCyclic separator cut selected
      (shallowCycle.takeUntil vertex hvertex) havoid).2 hvertexSide)

/-- The shallow return path remains in the exterior component selected by
the common outer root.  Rooted saturation of the deep side therefore cannot
swallow this physical path. -/
theorem shallow_ambientPath_outside_deep_closureSide
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (outer shallow deep inner : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma bond.site))
    (houterShallowLeft : outer.left < shallow.left)
    (hshallowDeepLeft : shallow.left < deep.left)
    (hdeepInnerLeft : deep.left < inner.left)
    (hinnerDeepRight : inner.right < deep.right)
    (hdeepShallowRight : deep.right < shallow.right)
    (hshallowOuterRight : shallow.right < outer.right)
    (hshoreOuterShallow :
      orderedReturnShore rotation hG sigma hSigma bond outer.left =
        orderedReturnShore rotation hG sigma hSigma bond shallow.left)
    (hshoreShallowDeep :
      orderedReturnShore rotation hG sigma hSigma bond shallow.left =
        orderedReturnShore rotation hG sigma hSigma bond deep.left)
    (hshoreDeepInner :
      orderedReturnShore rotation hG sigma hSigma bond deep.left =
        orderedReturnShore rotation hG sigma hSigma bond inner.left)
    (cut : ExactFaceCut rotation.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈
        (orderedReturnSeparator hG sigma hSigma bond.site deep).edges) F2)
    (selected : F2)
    (houtside : ∀ vertex,
      vertex ∈
          (complementaryReturnCycle hG sigma hSigma bond.site outer).support →
        ¬cut.filledCycleSide rotation
          (orderedReturnSeparator hG sigma hSigma bond.site deep)
          selected vertex)
    (hroot : ¬cut.filledCycleSide rotation
      (orderedReturnSeparator hG sigma hSigma bond.site deep) selected
      (cycleVertexOrder sigma bond.site outer.left).1) :
    ∀ vertex,
      vertex ∈
          (orderedChordAmbientPath hG sigma hSigma bond.site shallow).support →
        ¬closureSide (G := G)
          (cut.filledCycleSide rotation
            (orderedReturnSeparator hG sigma hSigma bond.site deep) selected)
          (cycleVertexOrder sigma bond.site outer.left).1 hroot vertex := by
  let separator := orderedReturnSeparator hG sigma hSigma bond.site deep
  let shallowCycle :=
    complementaryReturnCycle hG sigma hSigma bond.site shallow
  let shallowPath := orderedChordAmbientPath hG sigma hSigma bond.site shallow
  have hcycleOutside :=
    shallow_complementaryReturnCycle_outside_deep_filledCycleSide
      rotation minimal hG sigma hSigma bond outer shallow deep inner
        houterShallowLeft hshallowDeepLeft hdeepInnerLeft hinnerDeepRight
        hdeepShallowRight hshallowOuterRight hshoreOuterShallow
        hshoreShallowDeep hshoreDeepInner cut selected houtside
  have hrootMem : (cycleVertexOrder sigma bond.site outer.left).1 ∈
      shallowCycle.support := by
    simpa only [shallowCycle] using
      cycleVertexOrder_mem_complementaryReturnCycle_support_of_lt_left
        hG sigma hSigma bond.site shallow outer.left houterShallowLeft
  intro vertex hvertex hclosure
  have hvertexMem : vertex ∈ shallowCycle.support := by
    unfold shallowCycle complementaryReturnCycle
    rw [SimpleGraph.Walk.support_append]
    exact List.mem_append_left _ (by simpa only [shallowPath] using hvertex)
  have hsupportSubset : ∀ point,
      point ∈ shallowCycle.support →
        ¬cut.filledCycleSide rotation separator selected point := by
    simpa only [shallowCycle, separator] using hcycleOutside
  have hreachSupport := shallowCycle.connected_induce_support.preconnected
    ⟨(cycleVertexOrder sigma bond.site outer.left).1, hrootMem⟩
    ⟨vertex, hvertexMem⟩
  let inclusion := G.induceHomOfLE hsupportSubset
  have hreachComplement := hreachSupport.map inclusion.toHom
  apply hclosure
  refine ⟨hsupportSubset vertex hvertexMem, ?_⟩
  convert hreachComplement using 1 <;> apply Subtype.ext <;> rfl

/-- A nonempty path contained in a larger vertex side and disjoint from a
smaller one witnesses strict inclusion of their incident-edge shores. -/
theorem incidentEdgeShore_ssubset_of_path_material
    (smaller larger : V → Prop)
    (hsubset : ∀ vertex, smaller vertex → larger vertex)
    {start finish : V} (path : G.Walk start finish)
    (hnil : ¬path.Nil)
    (hlarger : ∀ vertex, vertex ∈ path.support → larger vertex)
    (hsmaller : ∀ vertex, vertex ∈ path.support → ¬smaller vertex) :
    incidentEdgeShore G smaller ⊂ incidentEdgeShore G larger := by
  have hmono : incidentEdgeShore G smaller ⊆ incidentEdgeShore G larger :=
    incidentEdgeShore_mono hsubset
  apply (Finset.ssubset_iff_of_subset hmono).2
  let dart := path.firstDart hnil
  let edge : G.edgeSet := ⟨dart.edge, dart.edge_mem⟩
  refine ⟨edge, ?_, ?_⟩
  · apply (mem_incidentEdgeShore_iff larger edge).2
    refine ⟨start, ?_, hlarger start (by simp)⟩
    simp [edge, dart, SimpleGraph.Dart.edge]
  · intro hedge
    rcases (mem_incidentEdgeShore_iff smaller edge).1 hedge with
      ⟨vertex, hvertexEdge, hvertexSmaller⟩
    have hcases : vertex = start ∨ vertex = path.snd := by
      simpa [edge, dart, SimpleGraph.Dart.edge] using hvertexEdge
    rcases hcases with hstart | hsnd
    · exact hsmaller vertex (by simpa [hstart]) hvertexSmaller
    · exact hsmaller vertex (by
        rw [hsnd]
        exact List.mem_of_mem_tail (path.snd_mem_tail_support hnil))
          hvertexSmaller

/-- The shallow physical return path is a strict edge-shore witness after
both nested separator sides have been saturated at the common outer root. -/
theorem incidentEdgeShore_deepClosure_ssubset_shallowClosure
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (outer shallow deep inner : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma bond.site))
    (houterShallowLeft : outer.left < shallow.left)
    (hshallowDeepLeft : shallow.left < deep.left)
    (hdeepInnerLeft : deep.left < inner.left)
    (hinnerDeepRight : inner.right < deep.right)
    (hdeepShallowRight : deep.right < shallow.right)
    (hshallowOuterRight : shallow.right < outer.right)
    (hshoreOuterShallow :
      orderedReturnShore rotation hG sigma hSigma bond outer.left =
        orderedReturnShore rotation hG sigma hSigma bond shallow.left)
    (hshoreShallowDeep :
      orderedReturnShore rotation hG sigma hSigma bond shallow.left =
        orderedReturnShore rotation hG sigma hSigma bond deep.left)
    (hshoreDeepInner :
      orderedReturnShore rotation hG sigma hSigma bond deep.left =
        orderedReturnShore rotation hG sigma hSigma bond inner.left)
    (shallowCut : ExactFaceCut rotation.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈
        (orderedReturnSeparator hG sigma hSigma bond.site shallow).edges) F2)
    (shallowSelected : F2)
    (deepCut : ExactFaceCut rotation.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈
        (orderedReturnSeparator hG sigma hSigma bond.site deep).edges) F2)
    (deepSelected : F2)
    (houtsideDeep : ∀ vertex,
      vertex ∈
          (complementaryReturnCycle hG sigma hSigma bond.site outer).support →
        ¬deepCut.filledCycleSide rotation
          (orderedReturnSeparator hG sigma hSigma bond.site deep)
          deepSelected vertex)
    (hrootShallow : ¬shallowCut.filledCycleSide rotation
      (orderedReturnSeparator hG sigma hSigma bond.site shallow)
      shallowSelected (cycleVertexOrder sigma bond.site outer.left).1)
    (hrootDeep : ¬deepCut.filledCycleSide rotation
      (orderedReturnSeparator hG sigma hSigma bond.site deep)
      deepSelected (cycleVertexOrder sigma bond.site outer.left).1)
    (hnested : ∀ vertex,
      closureSide (G := G)
          (deepCut.filledCycleSide rotation
            (orderedReturnSeparator hG sigma hSigma bond.site deep)
            deepSelected)
          (cycleVertexOrder sigma bond.site outer.left).1 hrootDeep vertex →
        closureSide (G := G)
          (shallowCut.filledCycleSide rotation
            (orderedReturnSeparator hG sigma hSigma bond.site shallow)
            shallowSelected)
          (cycleVertexOrder sigma bond.site outer.left).1 hrootShallow vertex) :
    incidentEdgeShore G
        (closureSide (G := G)
          (deepCut.filledCycleSide rotation
            (orderedReturnSeparator hG sigma hSigma bond.site deep)
            deepSelected)
          (cycleVertexOrder sigma bond.site outer.left).1 hrootDeep) ⊂
      incidentEdgeShore G
        (closureSide (G := G)
          (shallowCut.filledCycleSide rotation
            (orderedReturnSeparator hG sigma hSigma bond.site shallow)
            shallowSelected)
          (cycleVertexOrder sigma bond.site outer.left).1 hrootShallow) := by
  let path := orderedChordAmbientPath hG sigma hSigma bond.site shallow
  apply incidentEdgeShore_ssubset_of_path_material
    _ _ hnested path
      (by simpa only [path] using
        orderedChordAmbientPath_not_nil hG sigma hSigma bond.site shallow)
  · intro vertex hvertex
    apply side_subset_closureSide
      (shallowCut.filledCycleSide rotation
        (orderedReturnSeparator hG sigma hSigma bond.site shallow)
        shallowSelected)
      (cycleVertexOrder sigma bond.site outer.left).1 hrootShallow
    apply shallowCut.mem_filledCycleSide_of_mem_support rotation
      (orderedReturnSeparator hG sigma hSigma bond.site shallow)
      shallowSelected
    unfold orderedReturnSeparator
    rw [SimpleGraph.Walk.support_append]
    exact List.mem_append_left _ (by simpa only [path] using hvertex)
  · intro vertex hvertex
    exact shallow_ambientPath_outside_deep_closureSide
      rotation minimal hG sigma hSigma bond outer shallow deep inner
        houterShallowLeft hshallowDeepLeft hdeepInnerLeft hinnerDeepRight
        hdeepShallowRight hshallowOuterRight hshoreOuterShallow
        hshoreShallowDeep hshoreDeepInner deepCut deepSelected houtsideDeep
        hrootDeep vertex (by simpa only [path] using hvertex)

end

end ResidualReturnStrictNesting

end Mettapedia.GraphTheory.FourColor.Compositional
