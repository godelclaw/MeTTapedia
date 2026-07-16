import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeTerminalPaths
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

namespace SimpleGraph.Coloring

variable {V α : Type*} {G : SimpleGraph V}

/-- The underlying graph vertices used by a walk in a bicolored induced
subgraph. -/
def bicoloredWalkUnderlyingSupport
    (C : G.Coloring α) (a b : α)
    {left right : C.bicoloredSet a b}
    (path : (C.bicoloredSubgraph a b).Walk left right) : Set V :=
  {vertex | ∃ hvertex : vertex ∈ C.bicoloredSet a b,
    (⟨vertex, hvertex⟩ : C.bicoloredSet a b) ∈ path.support}

theorem bicoloredWalk_left_mem_underlyingSupport
    (C : G.Coloring α) (a b : α)
    {left right : C.bicoloredSet a b}
    (path : (C.bicoloredSubgraph a b).Walk left right) :
    left.1 ∈ C.bicoloredWalkUnderlyingSupport a b path := by
  exact ⟨left.2, path.start_mem_support⟩

theorem bicoloredWalk_right_mem_underlyingSupport
    (C : G.Coloring α) (a b : α)
    {left right : C.bicoloredSet a b}
    (path : (C.bicoloredSubgraph a b).Walk left right) :
    right.1 ∈ C.bicoloredWalkUnderlyingSupport a b path := by
  exact ⟨right.2, path.end_mem_support⟩

/-- Two bicolored sets with just their first color in common intersect in
that first color class. -/
theorem color_eq_of_mem_two_bicoloredSets
    (C : G.Coloring α) {a b c : α} (hbc : b ≠ c) {vertex : V}
    (hab : vertex ∈ C.bicoloredSet a b)
    (hac : vertex ∈ C.bicoloredSet a c) :
    C vertex = a := by
  rcases hab with ha | hb
  · exact ha
  · rcases hac with ha | hc
    · exact ha
    · exact False.elim (hbc (hb.symm.trans hc))

/-- Therefore every common vertex of an `(a,b)` walk and an `(a,c)` walk
is `a`-colored when `b` and `c` differ. -/
theorem color_eq_of_mem_bicoloredWalkUnderlyingSupports
    (C : G.Coloring α) {a b c : α} (hbc : b ≠ c)
    {bLeft bRight : C.bicoloredSet a b}
    {cLeft cRight : C.bicoloredSet a c}
    (bPath : (C.bicoloredSubgraph a b).Walk bLeft bRight)
    (cPath : (C.bicoloredSubgraph a c).Walk cLeft cRight)
    {vertex : V}
    (hb : vertex ∈ C.bicoloredWalkUnderlyingSupport a b bPath)
    (hc : vertex ∈ C.bicoloredWalkUnderlyingSupport a c cPath) :
    C vertex = a := by
  rcases hb with ⟨hb, _⟩
  rcases hc with ⟨hc, _⟩
  exact C.color_eq_of_mem_two_bicoloredSets hbc hb hc

end SimpleGraph.Coloring

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24AdjacentPairBoundary
open GoertzelV24TwoEdgeCutMinimality

/-- Two distinct graph edges containing the same vertex are adjacent in
the line graph. -/
theorem lineGraph_adj_of_common_vertex_of_ne
    {V : Type*} {G : SimpleGraph V}
    {vertex : V} {first second : G.edgeSet}
    (hfirst : vertex ∈ (first.1 : Sym2 V))
    (hsecond : vertex ∈ (second.1 : Sym2 V))
    (hne : first ≠ second) :
    G.lineGraph.Adj first second := by
  exact (SimpleGraph.lineGraph_adj_iff_exists).2
    ⟨hne, vertex, hfirst, hsecond⟩

/-- Edges carrying provably distinct colors are distinct. -/
theorem edge_ne_of_color_eq_of_color_eq_of_ne
    {V α : Type*} {G : SimpleGraph V} (C : G.Coloring α)
    {first second : V} {b c : α}
    (hfirst : C first = b) (hsecond : C second = c) (hbc : b ≠ c) :
    first ≠ second := by
  intro hedge
  apply hbc
  exact hfirst.symm.trans ((congrArg C hedge).trans hsecond)

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance fusionLensGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- A simple even route in one selected two-color line graph, with its
terminal graph edges attached to two boundary ports. -/
structure EvenKempePortPath {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (C : G.EdgeColoring Color) (a b : Color)
    (left right : Fin portCount) where
  leftEdge : C.bicoloredSet a b
  rightEdge : C.bicoloredSet a b
  leftIncident : leftEdge.1 ∈
    incidentEdgeFinset G (data.defectVertex left)
  rightIncident : rightEdge.1 ∈
    incidentEdgeFinset G (data.defectVertex right)
  leftColor : C leftEdge.1 = b
  rightColor : C rightEdge.1 = b
  path : (C.bicoloredSubgraph a b).Walk leftEdge rightEdge
  isPath : path.IsPath
  evenLength : Even path.length

/-- Forget the induced-subgraph subtype and view an even Kempe port route
as a path in the ambient line graph. -/
def EvenKempePortPath.ambientPath {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b : Color}
    {left right : Fin portCount}
    (route : data.EvenKempePortPath C a b left right) :
    G.lineGraph.Walk route.leftEdge.1 route.rightEdge.1 :=
  route.path.map
    (SimpleGraph.Embedding.induce
      (G := G.lineGraph) (C.bicoloredSet a b)).toHom

@[simp] theorem EvenKempePortPath.ambientPath_length {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b : Color}
    {left right : Fin portCount}
    (route : data.EvenKempePortPath C a b left right) :
    route.ambientPath.length = route.path.length := by
  change (route.path.map _).length = route.path.length
  exact route.path.length_map _

theorem EvenKempePortPath.ambientPath_isPath {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b : Color}
    {left right : Fin portCount}
    (route : data.EvenKempePortPath C a b left right) :
    route.ambientPath.IsPath := by
  apply SimpleGraph.Walk.map_isPath_of_injective
    Subtype.val_injective route.isPath

/-- Two even terminal routes using the two pairs `(a,b)` and `(a,c)`,
joined at their boundary endpoints. Their common route vertices are exactly
eligible fusion sites and must carry the shared color `a`. -/
structure EvenKempeFusionLens {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (C : G.EdgeColoring Color) (a b c : Color)
    (left right : Fin portCount) where
  bRoute : data.EvenKempePortPath C a b left right
  cRoute : data.EvenKempePortPath C a c left right
  leftConnector : G.lineGraph.Adj bRoute.leftEdge.1 cRoute.leftEdge.1
  rightConnector : G.lineGraph.Adj bRoute.rightEdge.1 cRoute.rightEdge.1
  sharedColor : ∀ edge : G.edgeSet,
    edge ∈ C.bicoloredWalkUnderlyingSupport a b bRoute.path →
    edge ∈ C.bicoloredWalkUnderlyingSupport a c cRoute.path →
    C edge = a

/-- Two routes with distinct second colors canonically form a fusion lens. -/
def evenKempeFusionLensOfRoutes {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (C : G.EdgeColoring Color) {a b c : Color} (hbc : b ≠ c)
    {left right : Fin portCount}
    (bRoute : data.EvenKempePortPath C a b left right)
    (cRoute : data.EvenKempePortPath C a c left right) :
    data.EvenKempeFusionLens C a b c left right where
  bRoute := bRoute
  cRoute := cRoute
  leftConnector := lineGraph_adj_of_common_vertex_of_ne
    (G := G) (vertex := data.defectVertex left)
    (by simpa [incidentEdgeFinset] using bRoute.leftIncident)
    (by simpa [incidentEdgeFinset] using cRoute.leftIncident)
      (edge_ne_of_color_eq_of_color_eq_of_ne C
        bRoute.leftColor cRoute.leftColor hbc)
  rightConnector := lineGraph_adj_of_common_vertex_of_ne
    (G := G) (vertex := data.defectVertex right)
    (by simpa [incidentEdgeFinset] using bRoute.rightIncident)
    (by simpa [incidentEdgeFinset] using cRoute.rightIncident)
      (edge_ne_of_color_eq_of_color_eq_of_ne C
        bRoute.rightColor cRoute.rightColor hbc)
  sharedColor := fun edge hb hc ↦
    C.color_eq_of_mem_bicoloredWalkUnderlyingSupports hbc
      bRoute.path cRoute.path hb hc

/-- The four terminal edges of a fusion lens are not fusion sites: all
intersections occur internally along the shared color. -/
theorem EvenKempeFusionLens.endpoints_not_shared {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) :
    lens.bRoute.leftEdge.1 ∉
        C.bicoloredWalkUnderlyingSupport a c lens.cRoute.path ∧
      lens.bRoute.rightEdge.1 ∉
        C.bicoloredWalkUnderlyingSupport a c lens.cRoute.path ∧
      lens.cRoute.leftEdge.1 ∉
        C.bicoloredWalkUnderlyingSupport a b lens.bRoute.path ∧
      lens.cRoute.rightEdge.1 ∉
        C.bicoloredWalkUnderlyingSupport a b lens.bRoute.path := by
  constructor
  · intro hmem
    apply hab
    exact (lens.sharedColor lens.bRoute.leftEdge.1
      (C.bicoloredWalk_left_mem_underlyingSupport
        a b lens.bRoute.path) hmem).symm.trans lens.bRoute.leftColor
  constructor
  · intro hmem
    apply hab
    exact (lens.sharedColor lens.bRoute.rightEdge.1
      (C.bicoloredWalk_right_mem_underlyingSupport
        a b lens.bRoute.path) hmem).symm.trans lens.bRoute.rightColor
  constructor
  · intro hmem
    apply hac
    exact (lens.sharedColor lens.cRoute.leftEdge.1 hmem
      (C.bicoloredWalk_left_mem_underlyingSupport
        a c lens.cRoute.path)).symm.trans lens.cRoute.leftColor
  · intro hmem
    apply hac
    exact (lens.sharedColor lens.cRoute.rightEdge.1 hmem
      (C.bicoloredWalk_right_mem_underlyingSupport
        a c lens.cRoute.path)).symm.trans lens.cRoute.rightColor

/-- Traverse the first route, cross at the right port, return along the
second route, and cross back at the left port. -/
def EvenKempeFusionLens.closedWalk {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    G.lineGraph.Walk lens.bRoute.leftEdge.1 lens.bRoute.leftEdge.1 :=
  lens.bRoute.ambientPath.append
    (SimpleGraph.Walk.cons lens.rightConnector
      (lens.cRoute.ambientPath.reverse.append
        (SimpleGraph.Walk.cons lens.leftConnector.symm
          SimpleGraph.Walk.nil)))

theorem EvenKempeFusionLens.closedWalk_length {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    lens.closedWalk.length =
      lens.bRoute.path.length + lens.cRoute.path.length + 2 := by
  simp [EvenKempeFusionLens.closedWalk]
  omega

theorem EvenKempeFusionLens.closedWalk_even {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    Even lens.closedWalk.length := by
  rw [lens.closedWalk_length]
  exact (lens.bRoute.evenLength.add lens.cRoute.evenLength).add
    (by decide)

theorem EvenKempeFusionLens.closedWalk_two_le_length {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    2 ≤ lens.closedWalk.length := by
  rw [lens.closedWalk_length]
  omega

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance adjacentFusionLensGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet := Subtype.instDecidableEq

local instance adjacentFusionLensRetainedVertexSetFintype
    (first second : V) : Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

local instance adjacentFusionLensRetainedVertexSetDecidableEq
    (first second : V) : DecidableEq (retainedVertexSet first second) :=
  Subtype.instDecidableEq

/-- At a constant boundary state, each same-side pair of ports carries an
even fusion lens for the two complementary Kempe pairs `(a,b)` and
`(a,a+b)`. -/
theorem exists_two_evenKempeFusionLenses_of_constant_colorWord
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    {a b : Color} (hab : ValidColorPair a b)
    (hconstant : ∀ port : Fin 4,
      data.degreeTwoBoundaryData.colorWord C port = a) :
    Nonempty (data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b (a + b) 0 1) ∧
    Nonempty (data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b (a + b) 2 3) := by
  let boundary := data.degreeTwoBoundaryData
  have hthird := third_color_properties hab.1 hab.2.1 hab.2.2
  have hac : ValidColorPair a (a + b) :=
    ⟨hab.1, hthird.1, hthird.2.1.symm⟩
  have hbc : b ≠ a + b := hthird.2.2.symm
  rcases data.exists_two_even_simpleKempePortPaths_of_constant_colorWord
    hcubic hnotColorable C hC hab hconstant with ⟨hb01, hb23⟩
  rcases data.exists_two_even_simpleKempePortPaths_of_constant_colorWord
    hcubic hnotColorable C hC hac hconstant with ⟨hc01, hc23⟩
  rcases hb01 with
    ⟨bLeft, bRight, hbLeftIncident, hbRightIncident,
      hbLeftColor, hbRightColor, bPath, hbIsPath, hbEven⟩
  rcases hc01 with
    ⟨cLeft, cRight, hcLeftIncident, hcRightIncident,
      hcLeftColor, hcRightColor, cPath, hcIsPath, hcEven⟩
  rcases hb23 with
    ⟨bLeft', bRight', hbLeftIncident', hbRightIncident',
      hbLeftColor', hbRightColor', bPath', hbIsPath', hbEven'⟩
  rcases hc23 with
    ⟨cLeft', cRight', hcLeftIncident', hcRightIncident',
      hcLeftColor', hcRightColor', cPath', hcIsPath', hcEven'⟩
  let bRoute01 : boundary.EvenKempePortPath C a b 0 1 :=
    ⟨bLeft, bRight, hbLeftIncident, hbRightIncident,
      hbLeftColor, hbRightColor, bPath, hbIsPath, hbEven⟩
  let cRoute01 : boundary.EvenKempePortPath C a (a + b) 0 1 :=
    ⟨cLeft, cRight, hcLeftIncident, hcRightIncident,
      hcLeftColor, hcRightColor, cPath, hcIsPath, hcEven⟩
  let bRoute23 : boundary.EvenKempePortPath C a b 2 3 :=
    ⟨bLeft', bRight', hbLeftIncident', hbRightIncident',
      hbLeftColor', hbRightColor', bPath', hbIsPath', hbEven'⟩
  let cRoute23 : boundary.EvenKempePortPath C a (a + b) 2 3 :=
    ⟨cLeft', cRight', hcLeftIncident', hcRightIncident',
      hcLeftColor', hcRightColor', cPath', hcIsPath', hcEven'⟩
  exact ⟨
    ⟨boundary.evenKempeFusionLensOfRoutes C hbc bRoute01 cRoute01⟩,
    ⟨boundary.evenKempeFusionLensOfRoutes C hbc bRoute23 cRoute23⟩⟩

/-- In a graph-backed minimal counterexample, every cyclic adjacent-pair
profile reaches a constant state carrying the two even fusion lenses. -/
theorem CyclicKempeProfile.exists_two_evenKempeFusionLenses_of_minimal
    {graphData : SimpleGraphDartRotation.Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    (profile : CyclicKempeProfile graphData data)
    {a b : Color} (hab : ValidColorPair a b) :
    ∃ C' : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).EdgeColoring Color,
      C' ∈ (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).lineGraph.KempeClosure profile.coloring ∧
      IsTaitEdgeColoring
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C' ∧
      (∀ port : Fin 4,
        data.degreeTwoBoundaryData.colorWord C' port = a) ∧
      Nonempty (data.degreeTwoBoundaryData.EvenKempeFusionLens
        C' a b (a + b) 0 1) ∧
      Nonempty (data.degreeTwoBoundaryData.EvenKempeFusionLens
        C' a b (a + b) 2 3) := by
  rcases profile.exists_kempeClosure_coloring_with_constant_colorWord_of_minimal
    minimal a hab.1 with ⟨C', hclosure, hC', hconstant⟩
  have hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring :=
    graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      graphData minimal
  rcases data.exists_two_evenKempeFusionLenses_of_constant_colorWord
    hcubic hnotColorable C' hC' hab hconstant with ⟨hlens01, hlens23⟩
  exact ⟨C', hclosure, hC', hconstant, hlens01, hlens23⟩

end

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
