import Mettapedia.GraphTheory.FourColor.Compositional.CyclePushOffNesting
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnRootedCut

/-!
# Nested sides of residual-return separators

Strictly nested residual returns on one facial shore bound genuinely nested
primal regions.  This file proves the geometric bridge in two stages.  First,
the same-shore bit determines which exact-cut label is seen by a deeper
return.  Second, exact-cut transport carries that label along the deeper
return path, while its carrier interval already lies on the shallower
separator.

The result supplies the literal support containment consumed by rooted cut
saturation.  It does not assume a nested family of vertex predicates.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace ResidualReturnSeparatorNesting

open AlternatingSiteGeometry
open CyclePushOffCut
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnArc
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24ResidualReturnShore
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open Mettapedia.GraphTheory.Embedding
open ResidualReturnComplementaryCycle
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

/-- Taking a nontrivial prefix of a walk preserves its first oriented dart. -/
private theorem firstDart_takeUntil_eq
    {start finish point : V} (walk : G.Walk start finish)
    (hpoint : point ∈ walk.support) (hne : start ≠ point)
    (hwalk : ¬walk.Nil) :
    (walk.takeUntil point hpoint).firstDart
        ((SimpleGraph.Walk.nil_takeUntil walk hpoint).not.mpr hne) =
      walk.firstDart hwalk := by
  cases walk with
  | nil => exact (hwalk SimpleGraph.Walk.nil_nil).elim
  | @cons _ next _ hadj tail =>
      have htail : point ∈ tail.support := by
        simpa [SimpleGraph.Walk.support, hne, hne.symm] using hpoint
      simp only [SimpleGraph.Walk.takeUntil, dif_neg hne]
      apply SimpleGraph.Dart.ext
      rw [SimpleGraph.Walk.firstDart_toProd,
        SimpleGraph.Walk.firstDart_toProd]
      simp [SimpleGraph.Walk.snd]

/-- Retyping the endpoints of a nontrivial walk does not change its first
oriented dart. -/
private theorem firstDart_copy_eq
    {start finish start' finish' : V} (walk : G.Walk start finish)
    (hstart : start = start') (hfinish : finish = finish')
    (hcopy : ¬(walk.copy hstart hfinish).Nil) (hwalk : ¬walk.Nil) :
    (walk.copy hstart hfinish).firstDart hcopy = walk.firstDart hwalk := by
  subst start'
  subst finish'
  rfl

/-- An internal vertex of one residual return is not on the separator of a
distinct residual return.  The two return paths are disjoint, and a return
can meet the common carrier only at its own endpoints. -/
theorem orderedChordAmbientPath_vertex_not_mem_orderedReturnSeparator
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (separatorChord otherChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (hne : separatorChord ≠ otherChord)
    {vertex : V}
    (hpath : vertex ∈
      (orderedChordAmbientPath hG sigma hSigma site otherChord).support)
    (hneLeft : vertex ≠
      (cycleVertexOrder sigma site otherChord.left).1)
    (hneRight : vertex ≠
      (cycleVertexOrder sigma site otherChord.right).1) :
    vertex ∉
      (orderedReturnSeparator hG sigma hSigma site separatorChord).support := by
  intro hseparator
  unfold orderedReturnSeparator at hseparator
  rw [SimpleGraph.Walk.support_append] at hseparator
  rcases List.mem_append.mp hseparator with hseparatorPath | hseparatorInterval
  · have hdisjoint := orderedChordAmbientPath_support_disjoint_of_ne
      hG sigma hSigma site separatorChord otherChord hne
    exact (List.disjoint_left.mp hdisjoint) hseparatorPath hpath
  · have hinterval : vertex ∈
        (residualCycleInterval sigma site separatorChord).support := by
      have : vertex ∈
          (residualCycleInterval sigma site separatorChord).reverse.support :=
        List.mem_of_mem_tail hseparatorInterval
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using this
    have hcarrier : vertex ∈ site.carrier :=
      mem_carrier_of_mem_residualCycleInterval_support
        sigma site separatorChord hinterval
    rcases
        eq_left_or_eq_right_of_mem_orderedChordAmbientPath_support_of_mem_carrier
          hG sigma hSigma site otherChord hpath hcarrier with hleft | hright
    · exact hneLeft hleft
    · exact hneRight hright

/-- The carrier interval used to close a residual return is contained in the
support of the resulting separator.  The only vertex omitted by the tail of
the reversed interval is its right endpoint, which already belongs to the
return path. -/
theorem residualCycleInterval_support_subset_orderedReturnSeparator_support
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site)) :
    ∀ vertex,
      vertex ∈ (residualCycleInterval sigma site chord).support →
        vertex ∈
          (orderedReturnSeparator hG sigma hSigma site chord).support := by
  intro vertex hvertex
  unfold orderedReturnSeparator
  rw [SimpleGraph.Walk.support_append]
  by_cases hright :
      vertex = (cycleVertexOrder sigma site chord.right).1
  · apply List.mem_append.mpr
    left
    simpa [hright]
  · apply List.mem_append.mpr
    right
    have hreverse : vertex ∈
        (residualCycleInterval sigma site chord).reverse.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hvertex
    rw [← (residualCycleInterval sigma site chord).reverse.cons_tail_support]
      at hreverse
    rcases List.mem_cons.mp hreverse with hstart | htail
    · exact (hright (by simpa using hstart)).elim
    · exact htail

/-- Strict containment of chord endpoints gives literal containment of the
corresponding displayed carrier intervals. -/
theorem residualCycleInterval_support_subset_of_strictly_nested
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    {pairing : Pairing (CyclePosition sigma site)}
    (outer inner : OrderedReturnChord pairing)
    (hleft : outer.left < inner.left)
    (hright : inner.right < outer.right) :
    ∀ vertex,
      vertex ∈ (residualCycleInterval sigma site inner).support →
        vertex ∈ (residualCycleInterval sigma site outer).support := by
  intro vertex hvertex
  rcases (mem_residualCycleInterval_support_iff
      sigma site inner vertex).1 hvertex with
    ⟨position, hinnerLeft, hinnerRight, hposition⟩
  apply (mem_residualCycleInterval_support_iff
    sigma site outer vertex).2
  exact ⟨position, hleft.le.trans hinnerLeft,
    hinnerRight.trans hright.le, hposition⟩

/-- Across the left endpoint of the middle return, the exact separator label
flips between a surrounding return and a deeper return on the same facial
shore. -/
theorem label_ne_outer_inner_thirdDarts_of_triple_nested
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (outer middle inner : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma bond.site))
    (houterMiddleLeft : outer.left < middle.left)
    (hmiddleInnerLeft : middle.left < inner.left)
    (hinnerMiddleRight : inner.right < middle.right)
    (hmiddleOuterRight : middle.right < outer.right)
    (hshoreOuterMiddle :
      orderedReturnShore rotation hG sigma hSigma bond outer.left =
        orderedReturnShore rotation hG sigma hSigma bond middle.left)
    (hshoreMiddleInner :
      orderedReturnShore rotation hG sigma hSigma bond middle.left =
        orderedReturnShore rotation hG sigma hSigma bond inner.left)
    (cut : ExactFaceCut rotation.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈
        (orderedReturnSeparator hG sigma hSigma bond.site middle).edges) F2) :
    cut.label (dartOrbitFace rotation.toRotationSystem
        (siteThirdDart hG sigma hSigma bond.site
          (cycleVertexOrder sigma bond.site outer.left))) ≠
      cut.label (dartOrbitFace rotation.toRotationSystem
        (siteThirdDart hG sigma hSigma bond.site
          (cycleVertexOrder sigma bond.site inner.left))) := by
  apply GoertzelV24ResidualReturnCycleOrder.ExactFaceCut.label_ne_thirdDarts_of_single_selected_cyclePosition
    rotation minimal.spherical.cubic minimal.vertexRotationCyclic hG sigma
      hSigma bond.site cut outer.left middle.left inner.left
  · exact houterMiddleLeft
  · exact hmiddleInnerLeft
  · intro position houterPosition hpositionInner
    constructor
    · intro hselected
      by_contra hpositionMiddle
      have hpositionRight : position ≠ middle.right := by
        intro heq
        subst position
        have hinnerOrder := inner.left_lt_right
        omega
      exact (siteThirdDart_edge_not_orderedReturnSeparator_of_ne_endpoints
        hG sigma hSigma bond.site middle position hpositionMiddle
          hpositionRight) hselected
    · intro hposition
      subst position
      exact siteThirdDart_left_edge_mem_orderedReturnSeparator
        hG sigma hSigma bond.site middle
  · exact cycleRotationSector_iff_of_orderedReturnShore_eq
      rotation minimal.spherical.cubic minimal.vertexRotationCyclic hG sigma
        hSigma bond outer.left middle.left hshoreOuterMiddle
  · exact cycleRotationSector_iff_of_orderedReturnShore_eq
      rotation minimal.spherical.cubic minimal.vertexRotationCyclic hG sigma
        hSigma bond inner.left middle.left hshoreMiddleInner.symm

/-- If the outer complementary cycle is declared outside the selected side
of the middle separator, the inner return's first third dart reads exactly
the selected label.  This is the binary face-side choice that nesting needs. -/
theorem label_inner_thirdDart_eq_selected_of_outer_complement_outside
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (outer middle inner : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma bond.site))
    (houterMiddleLeft : outer.left < middle.left)
    (hmiddleInnerLeft : middle.left < inner.left)
    (hinnerMiddleRight : inner.right < middle.right)
    (hmiddleOuterRight : middle.right < outer.right)
    (hshoreOuterMiddle :
      orderedReturnShore rotation hG sigma hSigma bond outer.left =
        orderedReturnShore rotation hG sigma hSigma bond middle.left)
    (hshoreMiddleInner :
      orderedReturnShore rotation hG sigma hSigma bond middle.left =
        orderedReturnShore rotation hG sigma hSigma bond inner.left)
    (cut : ExactFaceCut rotation.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈
        (orderedReturnSeparator hG sigma hSigma bond.site middle).edges) F2)
    (selected : F2)
    (houtside : ∀ vertex,
      vertex ∈
          (complementaryReturnCycle hG sigma hSigma bond.site outer).support →
        ¬cut.filledCycleSide rotation
          (orderedReturnSeparator hG sigma hSigma bond.site middle)
          selected vertex) :
    cut.label (dartOrbitFace rotation.toRotationSystem
        (siteThirdDart hG sigma hSigma bond.site
          (cycleVertexOrder sigma bond.site inner.left))) = selected := by
  let outerVertex := (cycleVertexOrder sigma bond.site outer.left).1
  let outerDart := siteThirdDart hG sigma hSigma bond.site
    (cycleVertexOrder sigma bond.site outer.left)
  have houterComplement : outerVertex ∈
      (complementaryReturnCycle hG sigma hSigma bond.site outer).support := by
    simp [outerVertex, complementaryReturnCycle]
  have hdisjoint :=
    complementaryReturnCycle_support_disjoint_orderedReturnSeparator
      hG sigma hSigma bond.site outer middle houterMiddleLeft hmiddleOuterRight
  have houterOff : outerVertex ∉
      (orderedReturnSeparator hG sigma hSigma bond.site middle).support := by
    intro hseparator
    exact (List.disjoint_left.mp hdisjoint) houterComplement hseparator
  have houterLabelNe :
      cut.label (dartOrbitFace rotation.toRotationSystem outerDart) ≠
        selected := by
    intro hlabel
    have hread := cut.filledCycleSide_iff_label_of_not_mem_support
      rotation minimal.vertexRotationCyclic
        (orderedReturnSeparator hG sigma hSigma bond.site middle)
        selected outerDart (by simpa [outerVertex, outerDart, siteThirdDart]
          using houterOff)
    have hside : cut.filledCycleSide rotation
        (orderedReturnSeparator hG sigma hSigma bond.site middle)
        selected outerVertex := by
      simpa [outerVertex, outerDart, siteThirdDart] using hread.mpr hlabel
    exact houtside outerVertex houterComplement hside
  have hlabelsNe := label_ne_outer_inner_thirdDarts_of_triple_nested
    rotation minimal hG sigma hSigma bond outer middle inner
      houterMiddleLeft hmiddleInnerLeft hinnerMiddleRight hmiddleOuterRight
      hshoreOuterMiddle hshoreMiddleInner cut
  change cut.label (dartOrbitFace rotation.toRotationSystem outerDart) ≠
      cut.label (dartOrbitFace rotation.toRotationSystem
        (siteThirdDart hG sigma hSigma bond.site
          (cycleVertexOrder sigma bond.site inner.left))) at hlabelsNe
  generalize cut.label (dartOrbitFace rotation.toRotationSystem outerDart) =
    outerLabel at houterLabelNe hlabelsNe
  generalize cut.label (dartOrbitFace rotation.toRotationSystem
    (siteThirdDart hG sigma hSigma bond.site
      (cycleVertexOrder sigma bond.site inner.left))) = innerLabel at hlabelsNe ⊢
  fin_cases outerLabel <;> fin_cases innerLabel <;> fin_cases selected <;>
    simp_all

/-- Three strictly nested returns on one facial shore have genuinely nested
separator sides.  Once the outer complementary cycle chooses the outside of
the middle separator, both the inner carrier interval and the entire inner
return path lie in the selected filled side. -/
theorem orderedReturnSeparator_support_subset_filledCycleSide_of_triple_nested
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (outer middle inner : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma bond.site))
    (houterMiddleLeft : outer.left < middle.left)
    (hmiddleInnerLeft : middle.left < inner.left)
    (hinnerMiddleRight : inner.right < middle.right)
    (hmiddleOuterRight : middle.right < outer.right)
    (hshoreOuterMiddle :
      orderedReturnShore rotation hG sigma hSigma bond outer.left =
        orderedReturnShore rotation hG sigma hSigma bond middle.left)
    (hshoreMiddleInner :
      orderedReturnShore rotation hG sigma hSigma bond middle.left =
        orderedReturnShore rotation hG sigma hSigma bond inner.left)
    (cut : ExactFaceCut rotation.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈
        (orderedReturnSeparator hG sigma hSigma bond.site middle).edges) F2)
    (selected : F2)
    (houtside : ∀ vertex,
      vertex ∈
          (complementaryReturnCycle hG sigma hSigma bond.site outer).support →
        ¬cut.filledCycleSide rotation
          (orderedReturnSeparator hG sigma hSigma bond.site middle)
          selected vertex) :
    ∀ vertex,
      vertex ∈
          (orderedReturnSeparator hG sigma hSigma bond.site inner).support →
        cut.filledCycleSide rotation
          (orderedReturnSeparator hG sigma hSigma bond.site middle)
          selected vertex := by
  have hinnerLabel :=
    label_inner_thirdDart_eq_selected_of_outer_complement_outside
      rotation minimal hG sigma hSigma bond outer middle inner
        houterMiddleLeft hmiddleInnerLeft hinnerMiddleRight hmiddleOuterRight
        hshoreOuterMiddle hshoreMiddleInner cut selected houtside
  have hchordNe : middle ≠ inner := by
    intro heq
    subst inner
    exact (lt_irrefl middle.left) hmiddleInnerLeft
  intro vertex hvertex
  unfold orderedReturnSeparator at hvertex
  rw [SimpleGraph.Walk.support_append] at hvertex
  rcases List.mem_append.mp hvertex with hpathVertex | hintervalVertex
  · let path := orderedChordAmbientPath hG sigma hSigma bond.site inner
    change vertex ∈ path.support at hpathVertex
    by_cases hmiddleSupport : vertex ∈
        (orderedReturnSeparator hG sigma hSigma bond.site middle).support
    · exact cut.mem_filledCycleSide_of_mem_support rotation
        (orderedReturnSeparator hG sigma hSigma bond.site middle)
        selected hmiddleSupport
    · have hinnerLeftInterval :
          (cycleVertexOrder sigma bond.site inner.left).1 ∈
            (residualCycleInterval sigma bond.site inner).support := by
        apply (mem_residualCycleInterval_support_iff
          sigma bond.site inner _).2
        exact ⟨inner.left, le_rfl, inner.left_lt_right.le, rfl⟩
      have hinnerLeftMiddleInterval :
          (cycleVertexOrder sigma bond.site inner.left).1 ∈
            (residualCycleInterval sigma bond.site middle).support :=
        residualCycleInterval_support_subset_of_strictly_nested
          sigma bond.site middle inner hmiddleInnerLeft hinnerMiddleRight _
            hinnerLeftInterval
      have hinnerLeftMiddleSupport :
          (cycleVertexOrder sigma bond.site inner.left).1 ∈
            (orderedReturnSeparator hG sigma hSigma bond.site middle).support :=
        residualCycleInterval_support_subset_orderedReturnSeparator_support
          hG sigma hSigma bond.site middle _ hinnerLeftMiddleInterval
      have hneStart :
          (cycleVertexOrder sigma bond.site inner.left).1 ≠ vertex := by
        intro heq
        apply hmiddleSupport
        simpa [heq] using hinnerLeftMiddleSupport
      let initialPath := path.takeUntil vertex hpathVertex
      have hpathNil : ¬path.Nil := by
        simpa [path] using orderedChordAmbientPath_not_nil
          hG sigma hSigma bond.site inner
      have hprefixNil : ¬initialPath.Nil := by
        exact (SimpleGraph.Walk.nil_takeUntil path hpathVertex).not.mpr hneStart
      have htransport :=
        rotation.trail_labels_eq_firstDart_alpha_lastDart_of_walk_edges_not_cut
          minimal.spherical.cubic minimal.vertexRotationCyclic cut.label
          (fun edge : G.edgeSet => edge.1 ∈
            (orderedReturnSeparator hG sigma hSigma bond.site middle).edges)
          cut.separates initialPath hprefixNil
          ((orderedChordAmbientPath_isPath hG sigma hSigma bond.site inner).isTrail
            |>.takeUntil hpathVertex)
          (by
            intro edge hedge
            apply orderedChordAmbientPath_edge_not_orderedReturnSeparator_of_ne
              hG sigma hSigma bond.site middle inner hchordNe
            exact path.edges_takeUntil_subset_edges hpathVertex hedge)
      have hfirst : initialPath.firstDart hprefixNil =
          siteThirdDart hG sigma hSigma bond.site
            (cycleVertexOrder sigma bond.site inner.left) := by
        calc
          initialPath.firstDart hprefixNil = path.firstDart hpathNil :=
            firstDart_takeUntil_eq path hpathVertex hneStart hpathNil
          _ = siteThirdDart hG sigma hSigma bond.site
                (cycleVertexOrder sigma bond.site inner.left) := by
            calc
              path.firstDart hpathNil =
                  (orderedAmbientReturnPath hG sigma hSigma bond.site
                    inner.left).firstDart
                      (orderedAmbientReturnPath_not_nil
                        hG sigma hSigma bond.site inner.left) := by
                exact firstDart_copy_eq
                  (orderedAmbientReturnPath hG sigma hSigma bond.site inner.left)
                  rfl (by rw [inner.partner_left]) hpathNil
                  (orderedAmbientReturnPath_not_nil
                    hG sigma hSigma bond.site inner.left)
              _ = siteThirdDart hG sigma hSigma bond.site
                    (cycleVertexOrder sigma bond.site inner.left) :=
                orderedAmbientReturnPath_firstDart
                  hG sigma hSigma bond.site inner.left
      rw [hfirst] at htransport
      have hlastLabel :
          cut.label (dartOrbitFace rotation.toRotationSystem
            (rotation.toRotationSystem.alpha
              (initialPath.lastDart hprefixNil))) = selected :=
        htransport.symm.trans hinnerLabel
      have hend : rotation.toRotationSystem.vertOf
          (rotation.toRotationSystem.alpha (initialPath.lastDart hprefixNil)) =
            vertex := by
        rfl
      have hoff : rotation.toRotationSystem.vertOf
          (rotation.toRotationSystem.alpha (initialPath.lastDart hprefixNil)) ∉
            (orderedReturnSeparator hG sigma hSigma bond.site middle).support := by
        simpa only [hend] using hmiddleSupport
      have hread := cut.filledCycleSide_iff_label_of_not_mem_support
        rotation minimal.vertexRotationCyclic
          (orderedReturnSeparator hG sigma hSigma bond.site middle)
          selected
          (rotation.toRotationSystem.alpha (initialPath.lastDart hprefixNil)) hoff
      simpa only [hend] using hread.mpr hlastLabel
  · have hinnerInterval : vertex ∈
        (residualCycleInterval sigma bond.site inner).support := by
      have : vertex ∈
          (residualCycleInterval sigma bond.site inner).reverse.support :=
        List.mem_of_mem_tail hintervalVertex
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using this
    have hmiddleInterval : vertex ∈
        (residualCycleInterval sigma bond.site middle).support :=
      residualCycleInterval_support_subset_of_strictly_nested
        sigma bond.site middle inner hmiddleInnerLeft hinnerMiddleRight
          vertex hinnerInterval
    have hmiddleSupport : vertex ∈
        (orderedReturnSeparator hG sigma hSigma bond.site middle).support :=
      residualCycleInterval_support_subset_orderedReturnSeparator_support
        hG sigma hSigma bond.site middle vertex hmiddleInterval
    exact cut.mem_filledCycleSide_of_mem_support rotation
      (orderedReturnSeparator hG sigma hSigma bond.site middle)
      selected hmiddleSupport

/-- Rooted saturation preserves the preceding physical nesting.  Thus an
inner exact-cut side may be connected without escaping the middle filled
side, provided both use the same exterior root. -/
theorem closureSide_inner_subset_middle_filledSide_of_triple_nested
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (outer middle inner : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma bond.site))
    (houterMiddleLeft : outer.left < middle.left)
    (hmiddleInnerLeft : middle.left < inner.left)
    (hinnerMiddleRight : inner.right < middle.right)
    (hmiddleOuterRight : middle.right < outer.right)
    (hshoreOuterMiddle :
      orderedReturnShore rotation hG sigma hSigma bond outer.left =
        orderedReturnShore rotation hG sigma hSigma bond middle.left)
    (hshoreMiddleInner :
      orderedReturnShore rotation hG sigma hSigma bond middle.left =
        orderedReturnShore rotation hG sigma hSigma bond inner.left)
    (middleCut : ExactFaceCut rotation.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈
        (orderedReturnSeparator hG sigma hSigma bond.site middle).edges) F2)
    (middleSelected : F2)
    (houtsideMiddle : ∀ vertex,
      vertex ∈
          (complementaryReturnCycle hG sigma hSigma bond.site outer).support →
        ¬middleCut.filledCycleSide rotation
          (orderedReturnSeparator hG sigma hSigma bond.site middle)
          middleSelected vertex)
    (innerCut : ExactFaceCut rotation.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈
        (orderedReturnSeparator hG sigma hSigma bond.site inner).edges) F2)
    (innerSelected : F2)
    (outsideRoot : V)
    (hrootInner : ¬innerCut.filledCycleSide rotation
      (orderedReturnSeparator hG sigma hSigma bond.site inner)
      innerSelected outsideRoot)
    (hrootMiddle : ¬middleCut.filledCycleSide rotation
      (orderedReturnSeparator hG sigma hSigma bond.site middle)
      middleSelected outsideRoot)
    (hmiddleComplementConnected :
      (G.induce (fun vertex =>
        ¬middleCut.filledCycleSide rotation
          (orderedReturnSeparator hG sigma hSigma bond.site middle)
          middleSelected vertex)).Connected) :
    ∀ vertex,
      RootedCutSaturation.closureSide (G := G)
          (innerCut.filledCycleSide rotation
            (orderedReturnSeparator hG sigma hSigma bond.site inner)
            innerSelected)
          outsideRoot hrootInner vertex →
        middleCut.filledCycleSide rotation
          (orderedReturnSeparator hG sigma hSigma bond.site middle)
          middleSelected vertex := by
  apply closureSide_filledCycleSide_subset_of_cycle_support_subset
    rotation minimal.vertexRotationCyclic
      (orderedReturnSeparator hG sigma hSigma bond.site inner)
      innerCut innerSelected
      (middleCut.filledCycleSide rotation
        (orderedReturnSeparator hG sigma hSigma bond.site middle)
        middleSelected)
      hmiddleComplementConnected outsideRoot hrootInner hrootMiddle
  exact orderedReturnSeparator_support_subset_filledCycleSide_of_triple_nested
    rotation minimal hG sigma hSigma bond outer middle inner
      houterMiddleLeft hmiddleInnerLeft hinnerMiddleRight hmiddleOuterRight
      hshoreOuterMiddle hshoreMiddleInner middleCut middleSelected
      houtsideMiddle

end

end ResidualReturnSeparatorNesting

end Mettapedia.GraphTheory.FourColor.Compositional
