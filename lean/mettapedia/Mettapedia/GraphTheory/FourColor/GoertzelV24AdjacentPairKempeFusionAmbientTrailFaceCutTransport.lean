import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelFaceCutTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionTerminalFaceCutTransport

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open SimpleGraph
open SimpleGraphDartRotation

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- A nonempty walk in the retained induced graph remains nonempty after
inclusion into the ambient graph. -/
theorem retainedWalkToAmbient_not_nil
    (data : AdjacentPairData G)
    {left right : retainedVertexSet data.firstVertex data.secondVertex}
    (walk : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk left right)
    (hnil : ¬walk.Nil) :
    ¬(data.retainedWalkToAmbient walk).Nil := by
  simpa only [GoertzelV24AdjacentPairBoundary.AdjacentPairData.retainedWalkToAmbient,
    SimpleGraph.Walk.nil_map_iff] using hnil

/-- Inclusion of the retained induced graph preserves edge-simple trails. -/
theorem retainedWalkToAmbient_isTrail
    (data : AdjacentPairData G)
    {left right : retainedVertexSet data.firstVertex data.secondVertex}
    {walk : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk left right}
    (htrail : walk.IsTrail) :
    (data.retainedWalkToAmbient walk).IsTrail := by
  exact SimpleGraph.Walk.map_isTrail_of_injective
    Subtype.val_injective htrail

/-- The first dart of an included retained walk is the included first dart. -/
theorem retainedWalkToAmbient_firstDart
    (data : AdjacentPairData G)
    {left right : retainedVertexSet data.firstVertex data.secondVertex}
    (walk : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk left right)
    (hnil : ¬walk.Nil)
    (hambientNil : ¬(data.retainedWalkToAmbient walk).Nil) :
    (data.retainedWalkToAmbient walk).firstDart hambientNil =
      retainedDartToAmbientDart data (walk.firstDart hnil) := by
  apply SimpleGraph.Dart.ext
  simp [SimpleGraph.Walk.firstDart_toProd,
    GoertzelV24AdjacentPairBoundary.AdjacentPairData.retainedWalkToAmbient,
    GoertzelV24AdjacentPairBoundary.AdjacentPairData.retainedGraphHom,
    retainedDartToAmbientDart, retainedGraphEmbedding,
    SimpleGraph.Embedding.induce]
  constructor <;> rfl

/-- The last dart of an included retained walk is the included last dart. -/
theorem retainedWalkToAmbient_lastDart
    (data : AdjacentPairData G)
    {left right : retainedVertexSet data.firstVertex data.secondVertex}
    (walk : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk left right)
    (hnil : ¬walk.Nil)
    (hambientNil : ¬(data.retainedWalkToAmbient walk).Nil) :
    (data.retainedWalkToAmbient walk).lastDart hambientNil =
      retainedDartToAmbientDart data (walk.lastDart hnil) := by
  apply SimpleGraph.Dart.ext
  simp [SimpleGraph.Walk.lastDart_toProd,
    GoertzelV24AdjacentPairBoundary.AdjacentPairData.retainedWalkToAmbient,
    GoertzelV24AdjacentPairBoundary.AdjacentPairData.retainedGraphHom,
    retainedDartToAmbientDart, retainedGraphEmbedding,
    SimpleGraph.Embedding.induce]
  constructor <;> rfl

/-- A retained edge-support certificate transports a non-cut hypothesis to
every edge of the included ambient walk. -/
theorem retainedWalkToAmbient_edges_not_cut_of_support
    (data : AdjacentPairData G)
    {left right : retainedVertexSet data.firstVertex data.secondVertex}
    (walk : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk left right)
    (support : List (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (cut : G.edgeSet → Prop)
    (hsupport : walk.edges ⊆ support.map Subtype.val)
    (hnot : ∀ edge ∈ support,
      ¬cut (retainedEdgeToAmbientEdge data edge)) :
    ∀ edge : G.edgeSet,
      edge.1 ∈ (data.retainedWalkToAmbient walk).edges → ¬cut edge := by
  intro edge hedge
  rw [GoertzelV24AdjacentPairBoundary.AdjacentPairData.retainedWalkToAmbient,
    SimpleGraph.Walk.edges_map] at hedge
  rcases List.mem_map.mp hedge with
    ⟨retainedValue, hretainedValue, hvalue⟩
  rcases List.mem_map.mp (hsupport hretainedValue) with
    ⟨retainedEdge, hretainedEdge, hedgeValue⟩
  have heq : retainedEdgeToAmbientEdge data retainedEdge = edge := by
    apply Subtype.ext
    calc
      (retainedEdgeToAmbientEdge data retainedEdge).1 =
          retainedEdge.1.map Subtype.val := rfl
      _ = retainedValue.map Subtype.val :=
        congrArg (Sym2.map Subtype.val) hedgeValue
      _ = edge.1 := hvalue
  rw [← heq]
  exact hnot retainedEdge hretainedEdge

/-- An edge-simple retained trail supported away from an ambient exact cut
transports the ambient face label between its included terminal darts. -/
theorem retainedTrail_labels_eq_terminalDarts_of_support_not_cut
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {A : Type*}
    (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    {left right : retainedVertexSet data.firstVertex data.secondVertex}
    (walk : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk left right)
    (hnil : ¬walk.Nil) (htrail : walk.IsTrail)
    (support : List (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (hsupport : walk.edges ⊆ support.map Subtype.val)
    (hnot : ∀ edge ∈ support,
      ¬cut (retainedEdgeToAmbientEdge data edge)) :
    labels (dartOrbitFace graphData.toRotationSystem
        (retainedDartToAmbientDart data (walk.firstDart hnil))) =
      labels (dartOrbitFace graphData.toRotationSystem
        (retainedDartToAmbientDart data (walk.lastDart hnil).symm)) := by
  have hambientNil := retainedWalkToAmbient_not_nil data walk hnil
  have hlabels :=
    graphData.trail_labels_eq_firstDart_alpha_lastDart_of_walk_edges_not_cut
      hcubic hrotation labels cut hexact
        (data.retainedWalkToAmbient walk) hambientNil
        (retainedWalkToAmbient_isTrail data htrail)
        (retainedWalkToAmbient_edges_not_cut_of_support
          data walk support cut hsupport hnot)
  rw [retainedWalkToAmbient_firstDart data walk hnil hambientNil,
    SimpleGraphDartRotation.Data.toRotationSystem_alpha,
    retainedWalkToAmbient_lastDart data walk hnil hambientNil,
    ← retainedDartToAmbientDart_symm] at hlabels
  exact hlabels

/-- A `bc` fusion cross channel whose retained route support avoids an
ambient exact cut equates the corresponding ambient left-terminal faces. -/
theorem EvenKempeFusionLens.bcAmbientTerminalFaceLabels_eq_of_crossChannel_not_cut
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hnonempty : lens01.bcCrossSites lens23 ≠ [])
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {A : Type*}
    (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    (hnot : ∀ edge ∈
      lens01.bRoute.ambientPath.support ++
        lens23.cRoute.ambientPath.support,
      ¬cut (retainedEdgeToAmbientEdge data edge)) :
    labels (dartOrbitFace graphData.toRotationSystem
        (ambientBLeftTerminalDart data lens01)) =
      labels (dartOrbitFace graphData.toRotationSystem
        (ambientCLeftTerminalDart data lens23)) := by
  rcases lens01.exists_bcPrimalTrail_with_routeSupport lens23
      hdata hab hac hbc hbDisjoint hcDisjoint hnonempty with
    ⟨trail, htrail, hpositive, hsupport⟩
  let hnil : ¬trail.Nil :=
    SimpleGraph.Walk.not_nil_iff_lt_length.mpr hpositive
  have hlabels := retainedTrail_labels_eq_terminalDarts_of_support_not_cut
    graphData hcubic hrotation data labels cut hexact trail hnil htrail
      (lens01.bRoute.ambientPath.support ++
        lens23.cRoute.ambientPath.support) hsupport hnot
  have hterminals := lens01.bcPrimalTrail_terminalDarts lens23
    hdata hab hac hbDisjoint hcDisjoint trail hnil hsupport
  rw [hterminals.1, hterminals.2] at hlabels
  exact hlabels

/-- The complementary `cb` fusion cross channel gives the corresponding
ambient terminal-face equality with the two route families exchanged. -/
theorem EvenKempeFusionLens.cbAmbientTerminalFaceLabels_eq_of_crossChannel_not_cut
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hnonempty : lens01.cbCrossSites lens23 ≠ [])
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {A : Type*}
    (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    (hnot : ∀ edge ∈
      lens01.cRoute.ambientPath.support ++
        lens23.bRoute.ambientPath.support,
      ¬cut (retainedEdgeToAmbientEdge data edge)) :
    labels (dartOrbitFace graphData.toRotationSystem
        (ambientCLeftTerminalDart data lens01)) =
      labels (dartOrbitFace graphData.toRotationSystem
        (ambientBLeftTerminalDart data lens23)) := by
  rcases lens01.exists_cbPrimalTrail_with_routeSupport lens23
      hdata hab hac hbc hbDisjoint hcDisjoint hnonempty with
    ⟨trail, htrail, hpositive, hsupport⟩
  let hnil : ¬trail.Nil :=
    SimpleGraph.Walk.not_nil_iff_lt_length.mpr hpositive
  have hlabels := retainedTrail_labels_eq_terminalDarts_of_support_not_cut
    graphData hcubic hrotation data labels cut hexact trail hnil htrail
      (lens01.cRoute.ambientPath.support ++
        lens23.bRoute.ambientPath.support) hsupport hnot
  have hterminals := lens01.cbPrimalTrail_terminalDarts lens23
    hdata hab hac hbDisjoint hcDisjoint trail hnil hsupport
  rw [hterminals.1, hterminals.2] at hlabels
  exact hlabels

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
