import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionTransferMonodromy

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceDualConnectedness
open GoertzelV24FourDefectBoundary
open GoertzelV24InducedHexCorridorTypes

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance fusionTerminalGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Orient the left terminal edge of an even Kempe route away from its
boundary port. -/
def EvenKempePortPath.leftTerminalDart {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b : Color}
    {left right : Fin portCount}
    (route : data.EvenKempePortPath C a b left right) : G.Dart :=
  SimpleGraph.edgeDartAt route.leftEdge.1 (by
    simpa [incidentEdgeFinset] using route.leftIncident)

/-- Orient the right terminal edge away from its boundary port. -/
def EvenKempePortPath.rightTerminalDart {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b : Color}
    {left right : Fin portCount}
    (route : data.EvenKempePortPath C a b left right) : G.Dart :=
  SimpleGraph.edgeDartAt route.rightEdge.1 (by
    simpa [incidentEdgeFinset] using route.rightIncident)

@[simp] theorem EvenKempePortPath.leftTerminalDart_fst
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b : Color}
    {left right : Fin portCount}
    (route : data.EvenKempePortPath C a b left right) :
    route.leftTerminalDart.fst = data.defectVertex left :=
  rfl

@[simp] theorem EvenKempePortPath.rightTerminalDart_fst
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b : Color}
    {left right : Fin portCount}
    (route : data.EvenKempePortPath C a b left right) :
    route.rightTerminalDart.fst = data.defectVertex right :=
  rfl

@[simp] theorem EvenKempePortPath.leftTerminalDart_edge
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b : Color}
    {left right : Fin portCount}
    (route : data.EvenKempePortPath C a b left right) :
    route.leftTerminalDart.edge = route.leftEdge.1.1 :=
  SimpleGraph.edgeDartAt_edge _ _

@[simp] theorem EvenKempePortPath.rightTerminalDart_edge
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b : Color}
    {left right : Fin portCount}
    (route : data.EvenKempePortPath C a b left right) :
    route.rightTerminalDart.edge = route.rightEdge.1.1 :=
  SimpleGraph.edgeDartAt_edge _ _

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance ambientFusionTerminalGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance ambientFusionTerminalRetainedVertexFintype
    (first second : V) : Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

local instance ambientFusionTerminalRetainedVertexDecidableEq
    (first second : V) : DecidableEq (retainedVertexSet first second) :=
  Subtype.instDecidableEq

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem retainedDartToAmbientDart_edge
    (data : AdjacentPairData G)
    (dart : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Dart) :
    (retainedDartToAmbientDart data dart).edge =
      dart.edge.map Subtype.val :=
  rfl

/-- The restored boundary edge oriented from its retained port toward the
deleted adjacent pair. -/
def boundaryPortDart (data : AdjacentPairData G) (port : Fin 4) : G.Dart :=
  SimpleGraph.edgeDartAt (boundaryEdge data port)
    (data.portVertex_mem_boundaryEdgeValue port)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem boundaryPortDart_fst
    (data : AdjacentPairData G) (port : Fin 4) :
    (boundaryPortDart data port).fst = data.portVertex port :=
  rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem boundaryPortDart_edge
    (data : AdjacentPairData G) (port : Fin 4) :
    (boundaryPortDart data port).edge = (boundaryEdge data port).1 :=
  SimpleGraph.edgeDartAt_edge _ _

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A retained edge lifted to the ambient graph cannot be one of the four
restored boundary edges. -/
theorem retainedEdgeToAmbientEdge_ne_boundaryEdge
    (data : AdjacentPairData G)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (port : Fin 4) :
    retainedEdgeToAmbientEdge data edge ≠ boundaryEdge data port := by
  intro heq
  have hdeletedMem : data.boundaryDeletedVertex port ∈
      ((retainedEdgeToAmbientEdge data edge).1 : Sym2 V) := by
    rw [heq]
    change data.boundaryDeletedVertex port ∈
      (data.boundaryEdgeValue port : Sym2 V)
    rw [data.boundaryEdgeValue_eq]
    simp
  rw [retainedEdgeToAmbientEdge_val] at hdeletedMem
  rcases Sym2.mem_map.mp hdeletedMem with
    ⟨retained, _hretainedMem, hvalue⟩
  fin_cases port
  · exact retained.2.1 (by simpa [boundaryDeletedVertex] using hvalue)
  · exact retained.2.1 (by simpa [boundaryDeletedVertex] using hvalue)
  · exact retained.2.2 (by simpa [boundaryDeletedVertex] using hvalue)
  · exact retained.2.2 (by simpa [boundaryDeletedVertex] using hvalue)

/-- The `(a,b)` left terminal dart lifted to the ambient graph. -/
def ambientBLeftTerminalDart (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right) : G.Dart :=
  retainedDartToAmbientDart data lens.bRoute.leftTerminalDart

/-- The `(a,c)` left terminal dart lifted to the ambient graph. -/
def ambientCLeftTerminalDart (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right) : G.Dart :=
  retainedDartToAmbientDart data lens.cRoute.leftTerminalDart

/-- The `(a,b)` right terminal dart lifted to the ambient graph. -/
def ambientBRightTerminalDart (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right) : G.Dart :=
  retainedDartToAmbientDart data lens.bRoute.rightTerminalDart

/-- The `(a,c)` right terminal dart lifted to the ambient graph. -/
def ambientCRightTerminalDart (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right) : G.Dart :=
  retainedDartToAmbientDart data lens.cRoute.rightTerminalDart

@[simp] theorem ambientBLeftTerminalDart_fst
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right) :
    (ambientBLeftTerminalDart data lens).fst = data.portVertex left :=
  rfl

@[simp] theorem ambientCLeftTerminalDart_fst
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right) :
    (ambientCLeftTerminalDart data lens).fst = data.portVertex left :=
  rfl

@[simp] theorem ambientBRightTerminalDart_fst
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right) :
    (ambientBRightTerminalDart data lens).fst = data.portVertex right :=
  rfl

@[simp] theorem ambientCRightTerminalDart_fst
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right) :
    (ambientCRightTerminalDart data lens).fst = data.portVertex right :=
  rfl

@[simp] theorem ambientBLeftTerminalDart_edge
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right) :
    (ambientBLeftTerminalDart data lens).edge =
      (retainedEdgeToAmbientEdge data lens.bRoute.leftEdge.1).1 := by
  simp [ambientBLeftTerminalDart]

@[simp] theorem ambientCLeftTerminalDart_edge
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right) :
    (ambientCLeftTerminalDart data lens).edge =
      (retainedEdgeToAmbientEdge data lens.cRoute.leftEdge.1).1 := by
  simp [ambientCLeftTerminalDart]

@[simp] theorem ambientBRightTerminalDart_edge
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right) :
    (ambientBRightTerminalDart data lens).edge =
      (retainedEdgeToAmbientEdge data lens.bRoute.rightEdge.1).1 := by
  simp [ambientBRightTerminalDart]

@[simp] theorem ambientCRightTerminalDart_edge
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right) :
    (ambientCRightTerminalDart data lens).edge =
      (retainedEdgeToAmbientEdge data lens.cRoute.rightEdge.1).1 := by
  simp [ambientCRightTerminalDart]

/-- At the left port, the restored boundary dart and the two route
terminal darts are pairwise distinct. -/
theorem ambientLeftTerminalDarts_pairwise_ne
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hbc : b ≠ c) :
    boundaryPortDart data left ≠ ambientBLeftTerminalDart data lens ∧
      boundaryPortDart data left ≠ ambientCLeftTerminalDart data lens ∧
      ambientBLeftTerminalDart data lens ≠
        ambientCLeftTerminalDart data lens := by
  have hbcDart : lens.bRoute.leftTerminalDart ≠
      lens.cRoute.leftTerminalDart := by
    apply dart_ne_of_edge_colors_ne C
      lens.bRoute.leftTerminalDart_edge
      lens.cRoute.leftTerminalDart_edge
    rw [lens.bRoute.leftColor, lens.cRoute.leftColor]
    exact hbc
  constructor
  · intro hdarts
    apply retainedEdgeToAmbientEdge_ne_boundaryEdge
      data lens.bRoute.leftEdge.1 left
    apply Subtype.ext
    simpa using (congrArg SimpleGraph.Dart.edge hdarts).symm
  constructor
  · intro hdarts
    apply retainedEdgeToAmbientEdge_ne_boundaryEdge
      data lens.cRoute.leftEdge.1 left
    apply Subtype.ext
    simpa using (congrArg SimpleGraph.Dart.edge hdarts).symm
  · intro hdarts
    apply hbcDart
    apply retainedDartToAmbientDart_injective data
    simpa [ambientBLeftTerminalDart,
      ambientCLeftTerminalDart] using hdarts

/-- The analogous three darts at the right port are pairwise distinct. -/
theorem ambientRightTerminalDarts_pairwise_ne
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hbc : b ≠ c) :
    boundaryPortDart data right ≠ ambientBRightTerminalDart data lens ∧
      boundaryPortDart data right ≠ ambientCRightTerminalDart data lens ∧
      ambientBRightTerminalDart data lens ≠
        ambientCRightTerminalDart data lens := by
  have hbcDart : lens.bRoute.rightTerminalDart ≠
      lens.cRoute.rightTerminalDart := by
    apply dart_ne_of_edge_colors_ne C
      lens.bRoute.rightTerminalDart_edge
      lens.cRoute.rightTerminalDart_edge
    rw [lens.bRoute.rightColor, lens.cRoute.rightColor]
    exact hbc
  constructor
  · intro hdarts
    apply retainedEdgeToAmbientEdge_ne_boundaryEdge
      data lens.bRoute.rightEdge.1 right
    apply Subtype.ext
    simpa using (congrArg SimpleGraph.Dart.edge hdarts).symm
  constructor
  · intro hdarts
    apply retainedEdgeToAmbientEdge_ne_boundaryEdge
      data lens.cRoute.rightEdge.1 right
    apply Subtype.ext
    simpa using (congrArg SimpleGraph.Dart.edge hdarts).symm
  · intro hdarts
    apply hbcDart
    apply retainedDartToAmbientDart_injective data
    simpa [ambientBRightTerminalDart,
      ambientCRightTerminalDart] using hdarts

/-- At the left port, cubicity forces the boundary rotation to choose
exactly one of the two route terminals. -/
theorem rho_boundaryPortDart_eq_leftB_or_leftC
    (graphData : SimpleGraphDartRotation.Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hbc : b ≠ c) :
    graphData.toRotationSystem.rho (boundaryPortDart data left) =
        ambientBLeftTerminalDart data lens ∨
      graphData.toRotationSystem.rho (boundaryPortDart data left) =
        ambientCLeftTerminalDart data lens := by
  have hpairs := ambientLeftTerminalDarts_pairwise_ne data lens hbc
  apply RotationSystem.rho_eq_second_or_third_of_cubic
    graphData.toRotationSystem hcubic hrotation
  · rfl
  · rfl
  · exact hpairs.1
  · exact hpairs.2.1
  · exact hpairs.2.2

/-- The same exhaustive turn law holds at the right port. -/
theorem rho_boundaryPortDart_eq_rightB_or_rightC
    (graphData : SimpleGraphDartRotation.Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hbc : b ≠ c) :
    graphData.toRotationSystem.rho (boundaryPortDart data right) =
        ambientBRightTerminalDart data lens ∨
      graphData.toRotationSystem.rho (boundaryPortDart data right) =
        ambientCRightTerminalDart data lens := by
  have hpairs := ambientRightTerminalDarts_pairwise_ne data lens hbc
  apply RotationSystem.rho_eq_second_or_third_of_cubic
    graphData.toRotationSystem hcubic hrotation
  · rfl
  · rfl
  · exact hpairs.1
  · exact hpairs.2.1
  · exact hpairs.2.2

/-- Boolean encoding of the left boundary turn: `true` selects the
`b` route and `false` selects the `c` route. -/
def fusionLeftTerminalTurn
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right) : Bool :=
  decide (graphData.toRotationSystem.rho (boundaryPortDart data left) =
    ambientBLeftTerminalDart data lens)

/-- Boolean encoding of the right boundary turn. -/
def fusionRightTerminalTurn
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right) : Bool :=
  decide (graphData.toRotationSystem.rho (boundaryPortDart data right) =
    ambientBRightTerminalDart data lens)

@[simp] theorem fusionLeftTerminalTurn_eq_true_iff
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right) :
    fusionLeftTerminalTurn graphData data lens = true ↔
      graphData.toRotationSystem.rho (boundaryPortDart data left) =
        ambientBLeftTerminalDart data lens := by
  simp [fusionLeftTerminalTurn]

@[simp] theorem fusionRightTerminalTurn_eq_true_iff
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right) :
    fusionRightTerminalTurn graphData data lens = true ↔
      graphData.toRotationSystem.rho (boundaryPortDart data right) =
        ambientBRightTerminalDart data lens := by
  simp [fusionRightTerminalTurn]

theorem fusionLeftTerminalTurn_eq_false_iff
    (graphData : SimpleGraphDartRotation.Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hbc : b ≠ c) :
    fusionLeftTerminalTurn graphData data lens = false ↔
      graphData.toRotationSystem.rho (boundaryPortDart data left) =
        ambientCLeftTerminalDart data lens := by
  have hdichotomy := rho_boundaryPortDart_eq_leftB_or_leftC
    graphData hcubic hrotation data lens hbc
  have hterminals :=
    (ambientLeftTerminalDarts_pairwise_ne data lens hbc).2.2
  rw [Bool.eq_false_iff]
  constructor
  · intro hnotB
    rcases hdichotomy with hB | hC
    · exact False.elim (hnotB
        ((fusionLeftTerminalTurn_eq_true_iff
          graphData data lens).2 hB))
    · exact hC
  · intro hC hturnTrue
    apply hterminals
    exact ((fusionLeftTerminalTurn_eq_true_iff
      graphData data lens).1 hturnTrue).symm.trans hC

theorem fusionRightTerminalTurn_eq_false_iff
    (graphData : SimpleGraphDartRotation.Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hbc : b ≠ c) :
    fusionRightTerminalTurn graphData data lens = false ↔
      graphData.toRotationSystem.rho (boundaryPortDart data right) =
        ambientCRightTerminalDart data lens := by
  have hdichotomy := rho_boundaryPortDart_eq_rightB_or_rightC
    graphData hcubic hrotation data lens hbc
  have hterminals :=
    (ambientRightTerminalDarts_pairwise_ne data lens hbc).2.2
  rw [Bool.eq_false_iff]
  constructor
  · intro hnotB
    rcases hdichotomy with hB | hC
    · exact False.elim (hnotB
        ((fusionRightTerminalTurn_eq_true_iff
          graphData data lens).2 hB))
    · exact hC
  · intro hC hturnTrue
    apply hterminals
    exact ((fusionRightTerminalTurn_eq_true_iff
      graphData data lens).1 hturnTrue).symm.trans hC

/-- The route terminal selected by the left boundary rotation. -/
def fusionLeftTerminalTurnDart
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right) : G.Dart :=
  if fusionLeftTerminalTurn graphData data lens = true then
    ambientBLeftTerminalDart data lens
  else
    ambientCLeftTerminalDart data lens

/-- The nonselected route terminal at the left boundary port. -/
def fusionLeftTerminalOtherDart
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right) : G.Dart :=
  if fusionLeftTerminalTurn graphData data lens = true then
    ambientCLeftTerminalDart data lens
  else
    ambientBLeftTerminalDart data lens

/-- The route terminal selected by the right boundary rotation. -/
def fusionRightTerminalTurnDart
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right) : G.Dart :=
  if fusionRightTerminalTurn graphData data lens = true then
    ambientBRightTerminalDart data lens
  else
    ambientCRightTerminalDart data lens

/-- The nonselected route terminal at the right boundary port. -/
def fusionRightTerminalOtherDart
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right) : G.Dart :=
  if fusionRightTerminalTurn graphData data lens = true then
    ambientCRightTerminalDart data lens
  else
    ambientBRightTerminalDart data lens

/-- The boundary, selected terminal, and nonselected terminal form the
complete cyclic dart fiber at the left port. -/
theorem ambientFusionLeftTerminal_rotationCycle
    (graphData : SimpleGraphDartRotation.Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hbc : b ≠ c) :
    graphData.toRotationSystem.rho (boundaryPortDart data left) =
        fusionLeftTerminalTurnDart graphData data lens ∧
      graphData.toRotationSystem.rho
          (fusionLeftTerminalTurnDart graphData data lens) =
        fusionLeftTerminalOtherDart graphData data lens ∧
      graphData.toRotationSystem.rho
          (fusionLeftTerminalOtherDart graphData data lens) =
        boundaryPortDart data left := by
  let RS := graphData.toRotationSystem
  have hpairs := ambientLeftTerminalDarts_pairwise_ne data lens hbc
  by_cases hturn : fusionLeftTerminalTurn graphData data lens = true
  · have hfirst := (fusionLeftTerminalTurn_eq_true_iff
      graphData data lens).1 hturn
    have hcycle := RotationSystem.rho_three_cycle_of_eq_second
      RS hcubic hrotation
      (first := boundaryPortDart data left)
      (second := ambientBLeftTerminalDart data lens)
      (third := ambientCLeftTerminalDart data lens)
      (hsecondBase := rfl) (hthirdBase := rfl)
      hpairs.1 hpairs.2.1 hpairs.2.2 hfirst
    rw [fusionLeftTerminalTurnDart, fusionLeftTerminalOtherDart,
      if_pos hturn, if_pos hturn]
    exact ⟨hfirst, hcycle⟩
  · have hfalse : fusionLeftTerminalTurn graphData data lens = false :=
      Bool.eq_false_of_not_eq_true hturn
    have hfirst := (fusionLeftTerminalTurn_eq_false_iff
      graphData hcubic hrotation data lens hbc).1 hfalse
    have hcycle := RotationSystem.rho_three_cycle_of_eq_second
      RS hcubic hrotation
      (first := boundaryPortDart data left)
      (second := ambientCLeftTerminalDart data lens)
      (third := ambientBLeftTerminalDart data lens)
      (hsecondBase := rfl) (hthirdBase := rfl)
      hpairs.2.1 hpairs.1 hpairs.2.2.symm hfirst
    rw [fusionLeftTerminalTurnDart, fusionLeftTerminalOtherDart,
      if_neg hturn, if_neg hturn]
    exact ⟨hfirst, hcycle⟩

/-- The analogous complete cyclic dart fiber at the right port. -/
theorem ambientFusionRightTerminal_rotationCycle
    (graphData : SimpleGraphDartRotation.Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hbc : b ≠ c) :
    graphData.toRotationSystem.rho (boundaryPortDart data right) =
        fusionRightTerminalTurnDart graphData data lens ∧
      graphData.toRotationSystem.rho
          (fusionRightTerminalTurnDart graphData data lens) =
        fusionRightTerminalOtherDart graphData data lens ∧
      graphData.toRotationSystem.rho
          (fusionRightTerminalOtherDart graphData data lens) =
        boundaryPortDart data right := by
  let RS := graphData.toRotationSystem
  have hpairs := ambientRightTerminalDarts_pairwise_ne data lens hbc
  by_cases hturn : fusionRightTerminalTurn graphData data lens = true
  · have hfirst := (fusionRightTerminalTurn_eq_true_iff
      graphData data lens).1 hturn
    have hcycle := RotationSystem.rho_three_cycle_of_eq_second
      RS hcubic hrotation
      (first := boundaryPortDart data right)
      (second := ambientBRightTerminalDart data lens)
      (third := ambientCRightTerminalDart data lens)
      (hsecondBase := rfl) (hthirdBase := rfl)
      hpairs.1 hpairs.2.1 hpairs.2.2 hfirst
    rw [fusionRightTerminalTurnDart, fusionRightTerminalOtherDart,
      if_pos hturn, if_pos hturn]
    exact ⟨hfirst, hcycle⟩
  · have hfalse : fusionRightTerminalTurn graphData data lens = false :=
      Bool.eq_false_of_not_eq_true hturn
    have hfirst := (fusionRightTerminalTurn_eq_false_iff
      graphData hcubic hrotation data lens hbc).1 hfalse
    have hcycle := RotationSystem.rho_three_cycle_of_eq_second
      RS hcubic hrotation
      (first := boundaryPortDart data right)
      (second := ambientCRightTerminalDart data lens)
      (third := ambientBRightTerminalDart data lens)
      (hsecondBase := rfl) (hthirdBase := rfl)
      hpairs.2.1 hpairs.1 hpairs.2.2.symm hfirst
    rw [fusionRightTerminalTurnDart, fusionRightTerminalOtherDart,
      if_neg hturn, if_neg hturn]
    exact ⟨hfirst, hcycle⟩

/-- Across the left boundary edge, the face successor enters the route
terminal selected by the boundary rotation. -/
theorem phi_alpha_boundaryPortDart_eq_leftTerminalTurnDart
    (graphData : SimpleGraphDartRotation.Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hbc : b ≠ c) :
    graphData.toRotationSystem.phi
        (graphData.toRotationSystem.alpha (boundaryPortDart data left)) =
      fusionLeftTerminalTurnDart graphData data lens := by
  rw [RotationSystem.phi_apply,
    graphData.toRotationSystem.alpha_involutive]
  exact (ambientFusionLeftTerminal_rotationCycle
    graphData hcubic hrotation data lens hbc).1

/-- The selected left terminal and the other route terminal are paired
by one face step after crossing the selected edge. -/
theorem phi_alpha_leftTerminalTurnDart_eq_otherDart
    (graphData : SimpleGraphDartRotation.Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hbc : b ≠ c) :
    graphData.toRotationSystem.phi
        (graphData.toRotationSystem.alpha
          (fusionLeftTerminalTurnDart graphData data lens)) =
      fusionLeftTerminalOtherDart graphData data lens := by
  rw [RotationSystem.phi_apply,
    graphData.toRotationSystem.alpha_involutive]
  exact (ambientFusionLeftTerminal_rotationCycle
    graphData hcubic hrotation data lens hbc).2.1

/-- The nonselected left terminal closes the local face corner back to
the restored boundary dart. -/
theorem phi_alpha_leftTerminalOtherDart_eq_boundaryPortDart
    (graphData : SimpleGraphDartRotation.Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hbc : b ≠ c) :
    graphData.toRotationSystem.phi
        (graphData.toRotationSystem.alpha
          (fusionLeftTerminalOtherDart graphData data lens)) =
      boundaryPortDart data left := by
  rw [RotationSystem.phi_apply,
    graphData.toRotationSystem.alpha_involutive]
  exact (ambientFusionLeftTerminal_rotationCycle
    graphData hcubic hrotation data lens hbc).2.2

/-- Across the right boundary edge, the face successor enters the route
terminal selected by the boundary rotation. -/
theorem phi_alpha_boundaryPortDart_eq_rightTerminalTurnDart
    (graphData : SimpleGraphDartRotation.Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hbc : b ≠ c) :
    graphData.toRotationSystem.phi
        (graphData.toRotationSystem.alpha (boundaryPortDart data right)) =
      fusionRightTerminalTurnDart graphData data lens := by
  rw [RotationSystem.phi_apply,
    graphData.toRotationSystem.alpha_involutive]
  exact (ambientFusionRightTerminal_rotationCycle
    graphData hcubic hrotation data lens hbc).1

/-- The selected right terminal is similarly paired with the other
route terminal. -/
theorem phi_alpha_rightTerminalTurnDart_eq_otherDart
    (graphData : SimpleGraphDartRotation.Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hbc : b ≠ c) :
    graphData.toRotationSystem.phi
        (graphData.toRotationSystem.alpha
          (fusionRightTerminalTurnDart graphData data lens)) =
      fusionRightTerminalOtherDart graphData data lens := by
  rw [RotationSystem.phi_apply,
    graphData.toRotationSystem.alpha_involutive]
  exact (ambientFusionRightTerminal_rotationCycle
    graphData hcubic hrotation data lens hbc).2.1

/-- The nonselected right terminal closes the local face corner back to
the restored boundary dart. -/
theorem phi_alpha_rightTerminalOtherDart_eq_boundaryPortDart
    (graphData : SimpleGraphDartRotation.Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hbc : b ≠ c) :
    graphData.toRotationSystem.phi
        (graphData.toRotationSystem.alpha
          (fusionRightTerminalOtherDart graphData data lens)) =
      boundaryPortDart data right := by
  rw [RotationSystem.phi_apply,
    graphData.toRotationSystem.alpha_involutive]
  exact (ambientFusionRightTerminal_rotationCycle
    graphData hcubic hrotation data lens hbc).2.2

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
