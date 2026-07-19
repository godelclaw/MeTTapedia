import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitConstantFaceCellBoundaryProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicFaceBoundaryCycleRigidity

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24OrbitFaceWalk
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

namespace CrossCentralExactFaceCertifiedRebaseInvolutionCell

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem list_all_left_or_all_right_of_xor_of_no_switch
    {A : Type*} (relation : A → A → Prop)
    (left right : A → Prop) (items : List A)
    (hchain : items.IsChain relation)
    (hx : ∀ item ∈ items, Xor (left item) (right item))
    (hleftRight : ∀ first second, relation first second →
      left first → right second → False)
    (hrightLeft : ∀ first second, relation first second →
      right first → left second → False) :
    (∀ item ∈ items, left item) ∨
      (∀ item ∈ items, right item) := by
  induction items with
  | nil =>
      exact Or.inl (by simp)
  | cons first tail inductionHypothesis =>
      cases tail with
      | nil =>
          have hfirst := hx first (by simp)
          rw [xor_def] at hfirst
          rcases hfirst with hleft | hright
          · exact Or.inl (by simpa using hleft.1)
          · exact Or.inr (by simpa using hright.1)
      | cons second rest =>
          have hrel : relation first second :=
            List.rel_of_isChain_cons_cons hchain
          have htail := inductionHypothesis hchain.tail (by
            intro item hitem
            exact hx item (List.mem_cons_of_mem first hitem))
          have hfirst := hx first (by simp)
          rw [xor_def] at hfirst
          rcases htail with hallLeft | hallRight
          · left
            intro item hitem
            rcases List.mem_cons.mp hitem with rfl | hitem
            · rcases hfirst with hleft | hright
              · exact hleft.1
              · exact False.elim
                  (hrightLeft item second hrel hright.1
                    (hallLeft second (by simp)))
            · exact hallLeft item hitem
          · right
            intro item hitem
            rcases List.mem_cons.mp hitem with rfl | hitem
            · rcases hfirst with hleft | hright
              · exact False.elim
                  (hleftRight item second hrel hleft.1
                    (hallRight second (by simp)))
              · exact hright.1
            · exact hallRight item hitem

/-- The source cross of a cell, embedded in the ambient cubic graph. -/
abbrev sourceAmbientCross
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) : G.edgeSet :=
  retainedEdgeToAmbientEdge
    (baseData.rotationOrderedData graphData minimal.spherical.cubic
      minimal.vertexRotationCyclic) cell.source.1

/-- The target cross of a cell, embedded in the ambient cubic graph. -/
abbrev targetAmbientCross
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) : G.edgeSet :=
  retainedEdgeToAmbientEdge
    (baseData.rotationOrderedData graphData minimal.spherical.cubic
      minimal.vertexRotationCyclic) cell.target.1

/-- The selected face rooted at the source cross and split, in facial order,
at the target cross.  The two remaining walks are the two complementary
source-to-target boundary arcs. -/
structure BoundaryArcSplit
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) where
  root : graphData.toRotationSystem.D
  root_face :
    dartOrbitFace graphData.toRotationSystem root = cell.face
  root_edge : graphData.toRotationSystem.edgeOf root =
    cell.sourceAmbientCross
  left : V
  right : V
  targetAdj : G.Adj left right
  before : G.Walk root.snd left
  after : G.Walk right root.fst
  target_edge : cell.targetAmbientCross.1 = s(left, right)
  traversal_isPath :
    (before.append
      (SimpleGraph.Walk.cons targetAdj after)).IsPath
  traversal_darts :
    (before.append
        (SimpleGraph.Walk.cons targetAdj after)).darts =
      (faceOrbitDarts graphData root).tail
  traversal_edges_iff : ∀ edge : G.edgeSet,
    edge.1 ∈
          (before.append
            (SimpleGraph.Walk.cons targetAdj after)).edges ↔
      edge ∈ orbitFaceBoundary graphData.toRotationSystem
          (dartOrbitFace graphData.toRotationSystem root) ∧
        edge.1 ≠ root.edge

namespace BoundaryArcSplit

/-- The open facial traversal obtained by deleting the source cross. -/
abbrev traversal
    {cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData}
    (split : BoundaryArcSplit cell) :
    G.Walk split.root.snd split.root.fst :=
  split.before.append
    (SimpleGraph.Walk.cons split.targetAdj split.after)

/-- The first facial arc is a simple path. -/
theorem before_isPath
    {cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData}
    (split : BoundaryArcSplit cell) :
    split.before.IsPath :=
  split.traversal_isPath.of_append_left

/-- The second facial arc is also a simple path. -/
theorem after_isPath
    {cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData}
    (split : BoundaryArcSplit cell) :
    split.after.IsPath :=
  (split.traversal_isPath.of_append_right).of_cons

/-- The ordered source-to-target traversal is in particular edge-simple. -/
theorem traversal_isTrail
    {cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData}
    (split : BoundaryArcSplit cell) :
    (split.before.append
      (SimpleGraph.Walk.cons split.targetAdj split.after)).IsTrail :=
  split.traversal_isPath.isTrail

/-- The root dart really carries the embedded source cross as an underlying
edge value. -/
theorem root_edge_value
    {cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData}
    (split : BoundaryArcSplit cell) :
    split.root.edge = cell.sourceAmbientCross.1 := by
  change (graphData.toRotationSystem.edgeOf split.root).1 =
    cell.sourceAmbientCross.1
  exact congrArg Subtype.val split.root_edge

/-- No dart of the open facial traversal returns to its initial vertex. -/
theorem dart_snd_ne_start
    {cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData}
    (split : BoundaryArcSplit cell)
    (dart : G.Dart) (hdart : dart ∈ split.traversal.darts) :
    dart.snd ≠ split.root.snd := by
  have hsnd : dart.snd ∈ split.traversal.support.tail := by
    rw [← split.traversal.map_snd_darts]
    exact List.mem_map.mpr ⟨dart, hdart, rfl⟩
  have hstartNe :=
    split.traversal_isPath.support_nodup.rel_head_tail hsnd
  have hstartNe' : split.root.snd ≠ dart.snd := by
    simpa using hstartNe
  exact hstartNe'.symm

/-- No dart of the open facial traversal starts at its terminal vertex. -/
theorem dart_fst_ne_end
    {cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData}
    (split : BoundaryArcSplit cell)
    (dart : G.Dart) (hdart : dart ∈ split.traversal.darts) :
    dart.fst ≠ split.root.fst := by
  have hfst : dart.fst ∈ split.traversal.support.dropLast := by
    rw [← split.traversal.map_fst_darts]
    exact List.mem_map.mpr ⟨dart, hdart, rfl⟩
  have hendNe :=
    split.traversal_isPath.support_nodup.rel_dropLast_getLast hfst
  simpa using hendNe

/-- Every dart of the open traversal has the selected cell face on its
oriented side. -/
theorem dartOrbitFace_eq_face
    {cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData}
    (split : BoundaryArcSplit cell)
    (dart : G.Dart) (hdart : dart ∈ split.traversal.darts) :
    dartOrbitFace graphData.toRotationSystem dart = cell.face := by
  have hdartTail : dart ∈ (faceOrbitDarts graphData split.root).tail := by
    rw [← split.traversal_darts]
    exact hdart
  exact
    (dartOrbitFace_eq_of_mem_faceOrbitDarts graphData split.root dart
      (List.mem_of_mem_tail hdartTail)).trans split.root_face

/-- The target cross occurs only in the middle one-edge factor, not on the
first boundary arc. -/
theorem targetCross_not_mem_before
    {cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData}
    (split : BoundaryArcSplit cell) :
    cell.targetAmbientCross.1 ∉ split.before.edges := by
  have hparts :=
    (SimpleGraph.Walk.isTrail_append split.before
      (SimpleGraph.Walk.cons split.targetAdj split.after)).1
        split.traversal_isTrail
  intro htarget
  apply hparts.2.2 htarget
  rw [split.target_edge]
  simp

/-- The target cross likewise does not occur on the second boundary arc. -/
theorem targetCross_not_mem_after
    {cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData}
    (split : BoundaryArcSplit cell) :
    cell.targetAmbientCross.1 ∉ split.after.edges := by
  have hparts :=
    (SimpleGraph.Walk.isTrail_append split.before
      (SimpleGraph.Walk.cons split.targetAdj split.after)).1
        split.traversal_isTrail
  have hcons := hparts.2.1
  rw [SimpleGraph.Walk.isTrail_def, SimpleGraph.Walk.edges_cons,
    List.nodup_cons] at hcons
  rw [split.target_edge]
  exact hcons.1

/-- The deleted root edge, hence the source cross, is absent from the open
facial traversal. -/
theorem sourceCross_not_mem_traversal
    {cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData}
    (split : BoundaryArcSplit cell) :
    cell.sourceAmbientCross.1 ∉ split.traversal.edges := by
  intro hsource
  have hprofile :=
    (split.traversal_edges_iff cell.sourceAmbientCross).1 hsource
  exact hprofile.2 split.root_edge_value.symm

/-- Every edge of the first arc belongs to exactly one source closure. -/
theorem sourceClosures_xor_of_mem_before
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (split : BoundaryArcSplit cell)
    (edge : G.edgeSet) (hedge : edge.1 ∈ split.before.edges) :
    Xor (edge.1 ∈ cell.sourcePrefixClosure.edges)
      (edge.1 ∈ cell.sourceSuffixClosure.edges) := by
  have htraversal : edge.1 ∈ split.traversal.edges := by
    rw [SimpleGraph.Walk.edges_append]
    exact List.mem_append_left _ hedge
  have hprofile := (split.traversal_edges_iff edge).1 htraversal
  have hface : edge ∈
      orbitFaceBoundary graphData.toRotationSystem cell.face := by
    simpa only [split.root_face] using hprofile.1
  apply (cell.sourceClosures_xor_iff_ne_crosses edge hface).2
  constructor
  · intro hsource
    apply split.sourceCross_not_mem_traversal
    exact congrArg Subtype.val hsource ▸ htraversal
  · intro htarget
    apply split.targetCross_not_mem_before
    exact congrArg Subtype.val htarget ▸ hedge

/-- Every edge of the second arc also belongs to exactly one source
closure. -/
theorem sourceClosures_xor_of_mem_after
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (split : BoundaryArcSplit cell)
    (edge : G.edgeSet) (hedge : edge.1 ∈ split.after.edges) :
    Xor (edge.1 ∈ cell.sourcePrefixClosure.edges)
      (edge.1 ∈ cell.sourceSuffixClosure.edges) := by
  have htraversal : edge.1 ∈ split.traversal.edges := by
    rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hedge)
  have hprofile := (split.traversal_edges_iff edge).1 htraversal
  have hface : edge ∈
      orbitFaceBoundary graphData.toRotationSystem cell.face := by
    simpa only [split.root_face] using hprofile.1
  apply (cell.sourceClosures_xor_iff_ne_crosses edge hface).2
  constructor
  · intro hsource
    apply split.sourceCross_not_mem_traversal
    exact congrArg Subtype.val hsource ▸ htraversal
  · intro htarget
    apply split.targetCross_not_mem_after
    exact congrArg Subtype.val htarget ▸ hedge

/-- In facial order, every dart of the first arc lies in one common source
closure channel. -/
theorem before_darts_all_prefix_or_all_suffix
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (split : BoundaryArcSplit cell) :
    (∀ dart ∈ split.before.darts,
        (graphData.toRotationSystem.edgeOf dart).1 ∈
          cell.sourcePrefixClosure.edges) ∨
      (∀ dart ∈ split.before.darts,
        (graphData.toRotationSystem.edgeOf dart).1 ∈
          cell.sourceSuffixClosure.edges) := by
  let RS := graphData.toRotationSystem
  let phiEdgeStep : G.Dart → G.Dart → Prop := fun first second =>
    RS.edgeOf second = RS.edgeOf (RS.phi first)
  have hphiTraversal : split.traversal.darts.IsChain phiEdgeStep := by
    rw [split.traversal_darts]
    exact (faceOrbitDarts_isPhiEdgeChain graphData split.root).tail
  have hphiBefore : split.before.darts.IsChain phiEdgeStep := by
    rw [SimpleGraph.Walk.darts_append,
      SimpleGraph.Walk.darts_cons] at hphiTraversal
    exact hphiTraversal.left_of_append
  let step : G.Dart → G.Dart → Prop := fun first second =>
    G.DartAdj first second ∧ phiEdgeStep first second
  have hstep : split.before.darts.IsChain step := by
    apply List.isChain_iff_forall_rel_of_append_cons_cons.2
    intro first second initial final hdecomp
    exact ⟨
      List.isChain_iff_forall_rel_of_append_cons_cons.1
        split.before.isChain_dartAdj_darts hdecomp,
      List.isChain_iff_forall_rel_of_append_cons_cons.1
        hphiBefore hdecomp⟩
  let locatedStep : G.Dart → G.Dart → Prop := fun first second =>
    first ∈ split.before.darts ∧ second ∈ split.before.darts ∧
      step first second
  have hlocated : split.before.darts.IsChain locatedStep := by
    exact List.IsChain.iff_mem.mp hstep
  let inPrefix : G.Dart → Prop := fun dart =>
    (RS.edgeOf dart).1 ∈ cell.sourcePrefixClosure.edges
  let inSuffix : G.Dart → Prop := fun dart =>
    (RS.edgeOf dart).1 ∈ cell.sourceSuffixClosure.edges
  apply list_all_left_or_all_right_of_xor_of_no_switch locatedStep
    inPrefix inSuffix split.before.darts hlocated
  · intro dart hdart
    apply sourceClosures_xor_of_mem_before cell split (RS.edgeOf dart)
    change dart.edge ∈ split.before.edges
    rw [SimpleGraph.Walk.edges]
    exact List.mem_map.mpr ⟨dart, hdart, rfl⟩
  · intro first second hrel hprefix hsuffix
    rcases hrel with ⟨hfirst, hsecond, hadj, hphi⟩
    have hfirstTraversal : first ∈ split.traversal.darts := by
      rw [SimpleGraph.Walk.darts_append]
      exact List.mem_append_left _ hfirst
    have hsecondTraversal : second ∈ split.traversal.darts := by
      rw [SimpleGraph.Walk.darts_append]
      exact List.mem_append_left _ hsecond
    have hsuffixPhi :
        (RS.edgeOf (RS.phi first)).1 ∈
          cell.sourceSuffixClosure.edges := by
      rw [← hphi]
      exact hsuffix
    have hsource := cell.sourcePrefix_then_suffix_vertex_mem_sourceCross
      first (split.dartOrbitFace_eq_face first hfirstTraversal)
      hprefix hsuffixPhi
    have hroot : first.snd ∈ split.root.edge := by
      rw [split.root_edge_value]
      exact hsource
    simp only [SimpleGraph.Dart.edge, Sym2.mem_iff] at hroot
    change first.snd = second.fst at hadj
    rcases hroot with hend | hstart
    · exact split.dart_fst_ne_end second hsecondTraversal
        (hadj.symm.trans hend)
    · exact split.dart_snd_ne_start first hfirstTraversal hstart
  · intro first second hrel hsuffix hprefix
    rcases hrel with ⟨hfirst, hsecond, hadj, hphi⟩
    have hfirstTraversal : first ∈ split.traversal.darts := by
      rw [SimpleGraph.Walk.darts_append]
      exact List.mem_append_left _ hfirst
    have hsecondTraversal : second ∈ split.traversal.darts := by
      rw [SimpleGraph.Walk.darts_append]
      exact List.mem_append_left _ hsecond
    have hprefixPhi :
        (RS.edgeOf (RS.phi first)).1 ∈
          cell.sourcePrefixClosure.edges := by
      rw [← hphi]
      exact hprefix
    have hsource := cell.sourceSuffix_then_prefix_vertex_mem_sourceCross
      first (split.dartOrbitFace_eq_face first hfirstTraversal)
      hsuffix hprefixPhi
    have hroot : first.snd ∈ split.root.edge := by
      rw [split.root_edge_value]
      exact hsource
    simp only [SimpleGraph.Dart.edge, Sym2.mem_iff] at hroot
    change first.snd = second.fst at hadj
    rcases hroot with hend | hstart
    · exact split.dart_fst_ne_end second hsecondTraversal
        (hadj.symm.trans hend)
    · exact split.dart_snd_ne_start first hfirstTraversal hstart

/-- In facial order, every dart of the second arc likewise lies in one
common source closure channel. -/
theorem after_darts_all_prefix_or_all_suffix
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (split : BoundaryArcSplit cell) :
    (∀ dart ∈ split.after.darts,
        (graphData.toRotationSystem.edgeOf dart).1 ∈
          cell.sourcePrefixClosure.edges) ∨
      (∀ dart ∈ split.after.darts,
        (graphData.toRotationSystem.edgeOf dart).1 ∈
          cell.sourceSuffixClosure.edges) := by
  let RS := graphData.toRotationSystem
  let phiEdgeStep : G.Dart → G.Dart → Prop := fun first second =>
    RS.edgeOf second = RS.edgeOf (RS.phi first)
  have hphiTraversal : split.traversal.darts.IsChain phiEdgeStep := by
    rw [split.traversal_darts]
    exact (faceOrbitDarts_isPhiEdgeChain graphData split.root).tail
  have hphiAfter : split.after.darts.IsChain phiEdgeStep := by
    rw [SimpleGraph.Walk.darts_append,
      SimpleGraph.Walk.darts_cons] at hphiTraversal
    exact hphiTraversal.right_of_append.tail
  let step : G.Dart → G.Dart → Prop := fun first second =>
    G.DartAdj first second ∧ phiEdgeStep first second
  have hstep : split.after.darts.IsChain step := by
    apply List.isChain_iff_forall_rel_of_append_cons_cons.2
    intro first second initial final hdecomp
    exact ⟨
      List.isChain_iff_forall_rel_of_append_cons_cons.1
        split.after.isChain_dartAdj_darts hdecomp,
      List.isChain_iff_forall_rel_of_append_cons_cons.1
        hphiAfter hdecomp⟩
  let locatedStep : G.Dart → G.Dart → Prop := fun first second =>
    first ∈ split.after.darts ∧ second ∈ split.after.darts ∧
      step first second
  have hlocated : split.after.darts.IsChain locatedStep := by
    exact List.IsChain.iff_mem.mp hstep
  let inPrefix : G.Dart → Prop := fun dart =>
    (RS.edgeOf dart).1 ∈ cell.sourcePrefixClosure.edges
  let inSuffix : G.Dart → Prop := fun dart =>
    (RS.edgeOf dart).1 ∈ cell.sourceSuffixClosure.edges
  apply list_all_left_or_all_right_of_xor_of_no_switch locatedStep
    inPrefix inSuffix split.after.darts hlocated
  · intro dart hdart
    apply sourceClosures_xor_of_mem_after cell split (RS.edgeOf dart)
    change dart.edge ∈ split.after.edges
    rw [SimpleGraph.Walk.edges]
    exact List.mem_map.mpr ⟨dart, hdart, rfl⟩
  · intro first second hrel hprefix hsuffix
    rcases hrel with ⟨hfirst, hsecond, hadj, hphi⟩
    have hfirstTraversal : first ∈ split.traversal.darts := by
      rw [SimpleGraph.Walk.darts_append,
        SimpleGraph.Walk.darts_cons]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hfirst)
    have hsecondTraversal : second ∈ split.traversal.darts := by
      rw [SimpleGraph.Walk.darts_append,
        SimpleGraph.Walk.darts_cons]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hsecond)
    have hsuffixPhi :
        (RS.edgeOf (RS.phi first)).1 ∈
          cell.sourceSuffixClosure.edges := by
      rw [← hphi]
      exact hsuffix
    have hsource := cell.sourcePrefix_then_suffix_vertex_mem_sourceCross
      first (split.dartOrbitFace_eq_face first hfirstTraversal)
      hprefix hsuffixPhi
    have hroot : first.snd ∈ split.root.edge := by
      rw [split.root_edge_value]
      exact hsource
    simp only [SimpleGraph.Dart.edge, Sym2.mem_iff] at hroot
    change first.snd = second.fst at hadj
    rcases hroot with hend | hstart
    · exact split.dart_fst_ne_end second hsecondTraversal
        (hadj.symm.trans hend)
    · exact split.dart_snd_ne_start first hfirstTraversal hstart
  · intro first second hrel hsuffix hprefix
    rcases hrel with ⟨hfirst, hsecond, hadj, hphi⟩
    have hfirstTraversal : first ∈ split.traversal.darts := by
      rw [SimpleGraph.Walk.darts_append,
        SimpleGraph.Walk.darts_cons]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hfirst)
    have hsecondTraversal : second ∈ split.traversal.darts := by
      rw [SimpleGraph.Walk.darts_append,
        SimpleGraph.Walk.darts_cons]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hsecond)
    have hprefixPhi :
        (RS.edgeOf (RS.phi first)).1 ∈
          cell.sourcePrefixClosure.edges := by
      rw [← hphi]
      exact hprefix
    have hsource := cell.sourceSuffix_then_prefix_vertex_mem_sourceCross
      first (split.dartOrbitFace_eq_face first hfirstTraversal)
      hsuffix hprefixPhi
    have hroot : first.snd ∈ split.root.edge := by
      rw [split.root_edge_value]
      exact hsource
    simp only [SimpleGraph.Dart.edge, Sym2.mem_iff] at hroot
    change first.snd = second.fst at hadj
    rcases hroot with hend | hstart
    · exact split.dart_fst_ne_end second hsecondTraversal
        (hadj.symm.trans hend)
    · exact split.dart_snd_ne_start first hfirstTraversal hstart

/-- The first geometric arc is wholly contained in one source closure. -/
theorem before_edges_all_prefix_or_all_suffix
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (split : BoundaryArcSplit cell) :
    (∀ edge : G.edgeSet, edge.1 ∈ split.before.edges →
        edge.1 ∈ cell.sourcePrefixClosure.edges) ∨
      (∀ edge : G.edgeSet, edge.1 ∈ split.before.edges →
        edge.1 ∈ cell.sourceSuffixClosure.edges) := by
  rcases before_darts_all_prefix_or_all_suffix cell split with
    hallPrefix | hallSuffix
  · left
    intro edge hedge
    rw [SimpleGraph.Walk.edges] at hedge
    rcases List.mem_map.mp hedge with ⟨dart, hdart, hvalue⟩
    have hmem := hallPrefix dart hdart
    change dart.edge ∈ cell.sourcePrefixClosure.edges at hmem
    exact hvalue ▸ hmem
  · right
    intro edge hedge
    rw [SimpleGraph.Walk.edges] at hedge
    rcases List.mem_map.mp hedge with ⟨dart, hdart, hvalue⟩
    have hmem := hallSuffix dart hdart
    change dart.edge ∈ cell.sourceSuffixClosure.edges at hmem
    exact hvalue ▸ hmem

/-- The second geometric arc is wholly contained in one source closure. -/
theorem after_edges_all_prefix_or_all_suffix
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData)
    (split : BoundaryArcSplit cell) :
    (∀ edge : G.edgeSet, edge.1 ∈ split.after.edges →
        edge.1 ∈ cell.sourcePrefixClosure.edges) ∨
      (∀ edge : G.edgeSet, edge.1 ∈ split.after.edges →
        edge.1 ∈ cell.sourceSuffixClosure.edges) := by
  rcases after_darts_all_prefix_or_all_suffix cell split with
    hallPrefix | hallSuffix
  · left
    intro edge hedge
    rw [SimpleGraph.Walk.edges] at hedge
    rcases List.mem_map.mp hedge with ⟨dart, hdart, hvalue⟩
    have hmem := hallPrefix dart hdart
    change dart.edge ∈ cell.sourcePrefixClosure.edges at hmem
    exact hvalue ▸ hmem
  · right
    intro edge hedge
    rw [SimpleGraph.Walk.edges] at hedge
    rcases List.mem_map.mp hedge with ⟨dart, hdart, hvalue⟩
    have hmem := hallSuffix dart hdart
    change dart.edge ∈ cell.sourceSuffixClosure.edges at hmem
    exact hvalue ▸ hmem

end BoundaryArcSplit

/-- Every involution cell has the canonical ordered two-arc split of its
selected facial boundary. -/
theorem exists_boundaryArcSplit
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) :
    Nonempty (BoundaryArcSplit cell) := by
  let RS := graphData.toRotationSystem
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  have hcrosses := cell.crosses_mem_face
  rcases (mem_orbitFaceBoundary_iff RS cell.face
      cell.sourceAmbientCross).1 hcrosses.1 with
    ⟨root, hrootMem, hrootEdge⟩
  have hrootFace : dartOrbitFace RS root = cell.face :=
    (mem_orbitFaceDarts_iff RS cell.face root).1 hrootMem
  have hrootValue : root.edge = cell.sourceAmbientCross.1 := by
    change (RS.edgeOf root).1 = cell.sourceAmbientCross.1
    exact congrArg Subtype.val hrootEdge
  have htargetRoot : cell.targetAmbientCross.1 ≠ root.edge := by
    intro htarget
    apply cell.cross_ne
    apply data.retainedEdgeToAmbientEdge_injective
    apply Subtype.ext
    exact htarget.trans hrootValue
  have htargetFace : cell.targetAmbientCross ∈
      orbitFaceBoundary RS (dartOrbitFace RS root) := by
    simpa only [hrootFace] using hcrosses.2
  rcases exists_rootedFacePath_splitAtEdge graphData
      minimal.spherical.cubic minimal.facesTwoSided root
      cell.targetAmbientCross htargetFace htargetRoot with
    ⟨left, right, targetAdj, before, after, htargetEdge,
      hpath, hdarts, hedges⟩
  exact ⟨{
    root := root
    root_face := hrootFace
    root_edge := hrootEdge
    left := left
    right := right
    targetAdj := targetAdj
    before := before
    after := after
    target_edge := htargetEdge
    traversal_isPath := hpath
    traversal_darts := hdarts
    traversal_edges_iff := hedges }⟩

end CrossCentralExactFaceCertifiedRebaseInvolutionCell

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
