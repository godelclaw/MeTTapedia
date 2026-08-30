import Mettapedia.GraphTheory.FourColor.GoertzelV24BetweenRegionDefectPaths
import Mettapedia.GraphTheory.FourColor.GoertzelV24KempeLiftConfinement

/-!
# Degree-two boundary classification for confined Kempe lifts

In a Tait-coloured graph which is cubic away from finitely many degree-two
ports, every selected two-colour component is either circuit-shaped or meets
a port.  Combining this local classification with the exact common-core lift
records the shape of every lifted switch: a common-core sequence either
reaches the second deleted adjacent pair, or lifts to switches which are
circuit-shaped or meet one of the first deletion's four exposed ports.

This is a structural refinement of support confinement.  It does not assert
that a circuit in the deletion graph is already a boundary-free physical
cycle in the ambient map, and it does not assert wall exclusion.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DegreeTwoBoundaryKempeLiftClassification

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairCommonCoreKempeBoundary
open GoertzelV24AdjacentPairColoringAtlas
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24FourDefectBoundary
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData
open GoertzelV24FramedTrail
open GoertzelV24KempeComponentEmbeddingBoundary
open GoertzelV24KempeLiftConfinement
open GoertzelV24LocalSwapKempeGeneration
open SimpleGraph

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

/-- In a Tait-coloured graph which is cubic away from degree-two ports, a
selected bicoloured component is either a circuit or meets a port. -/
theorem circuit_or_exists_kempeComponentMeetsPort
    {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {a b : Color} (hab : ValidColorPair a b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    IsCircuitKempeComponent C a b K ∨
      ∃ port, data.KempeComponentMeetsPort C a b K port := by
  by_cases hcircuit : IsCircuitKempeComponent C a b K
  · exact Or.inl hcircuit
  · right
    rw [IsCircuitKempeComponent] at hcircuit
    push Not at hcircuit
    rcases hcircuit with ⟨componentEdge, hdegree⟩
    by_contra hnoPort
    push Not at hnoPort
    let edge : G.edgeSet := componentEdge.1.1
    have hedgeComponent : edge ∈ C.kempeComponentSet a b K :=
      ⟨componentEdge.1.2, componentEdge.2⟩
    have hendpointCubic : ∀ vertex ∈ (edge : Sym2 V),
        (incidentEdgeFinset G vertex).card = 3 := by
      intro vertex hvertex
      apply hdata.2.2 vertex
      intro port heq
      apply hnoPort port
      refine ⟨edge, ?_, hedgeComponent⟩
      simpa [edge, incidentEdgeFinset, heq] using hvertex
    apply hdegree
    rw [connectedComponent_neighborSet_ncard_eq_parent K componentEdge]
    simpa [edge] using
      bicoloredSubgraph_neighborSet_ncard_eq_two_of_endpoint_cubic
        C hC hab edge componentEdge.1.2 hendpointCubic

/-- A Tait Kempe step annotated with the exhaustive degree-two-boundary
shape of its selected component. -/
def PortOrCircuitTaitKempeStep {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (source target : G.EdgeColoring Color) : Prop :=
  ∃ first second : Color, ValidColorPair first second ∧
    ∃ component : (source.bicoloredSubgraph first second).ConnectedComponent,
      (IsCircuitKempeComponent source first second component ∨
        ∃ port, data.KempeComponentMeetsPort
          source first second component port) ∧
      target = source.swapOnKempeComponent first second component

/-- Finite Tait Kempe reachability with the component shape of every step
retained in the relation. -/
def PortOrCircuitTaitKempeReachable {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (source target : G.EdgeColoring Color) : Prop :=
  Relation.ReflTransGen (PortOrCircuitTaitKempeStep data) source target

/-- Forgetting the shape annotation gives an ordinary Tait Kempe step. -/
theorem taitKempeStep_of_portOrCircuitTaitKempeStep
    {portCount : Nat} (data : DegreeTwoBoundaryData G portCount)
    {source target : G.EdgeColoring Color}
    (hstep : PortOrCircuitTaitKempeStep data source target) :
    TaitKempeStep source target := by
  rcases hstep with
    ⟨first, second, hpair, component, _hshape, rfl⟩
  exact ⟨first, second, hpair, component, rfl⟩

/-- Forgetting all shape annotations gives ordinary Tait Kempe
reachability. -/
theorem taitKempeReachable_of_portOrCircuitTaitKempeReachable
    {portCount : Nat} (data : DegreeTwoBoundaryData G portCount)
    {source target : G.EdgeColoring Color}
    (hreachable : PortOrCircuitTaitKempeReachable data source target) :
    TaitKempeReachable source target := by
  induction hreachable with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprefix hstep ih =>
      exact ih.tail
        (taitKempeStep_of_portOrCircuitTaitKempeStep data hstep)

variable {SmallVertex : Type u} {LargeVertex : Type v}
  [Fintype LargeVertex] [DecidableEq LargeVertex]
  {smallGraph : SimpleGraph SmallVertex}
  {largeGraph : SimpleGraph LargeVertex}
  [DecidableRel largeGraph.Adj]

/-- A confined lift through a degree-two-boundary graph records an exhaustive
shape annotation at every lifted step. -/
theorem taitBoundaryAlongLiftOrbit_or_exists_portOrCircuitConfinedLift
    {portCount : Nat}
    (data : DegreeTwoBoundaryData largeGraph portCount)
    (hdata : data.WellFormed)
    (base : largeGraph.EdgeColoring Color)
    (hbase : IsTaitEdgeColoring largeGraph base)
    (embedding : smallGraph ↪g largeGraph)
    (target : smallGraph.EdgeColoring Color)
    (hreachable : TaitKempeReachable
      (base.pullbackEmbedding embedding) target) :
    HasTaitBoundaryStepInLiftOrbit base embedding ∨
      ∃ lifted : largeGraph.EdgeColoring Color,
        PortOrCircuitTaitKempeReachable data base lifted ∧
        IsTaitEdgeColoring largeGraph lifted ∧
        lifted.pullbackEmbedding embedding = target ∧
        AgreesOutsideEmbedding base lifted embedding := by
  induction hreachable with
  | refl =>
      right
      exact ⟨base, Relation.ReflTransGen.refl, hbase, rfl,
        fun _edge _houtside => rfl⟩
  | tail hprefix hstep ih =>
      rcases ih with
        hboundary | ⟨current, hcurrent, hcurrentTait, hrestrict, houtside⟩
      · exact Or.inl hboundary
      · rcases hstep with ⟨first, second, hpair, component, rfl⟩
        subst hrestrict
        rcases touchesBoundary_or_exists_liftedComponentSwitch_confined
            current embedding first second component with
          htouches | ⟨targetComponent, hlift, hstepOutside⟩
        · left
          exact ⟨current,
            taitKempeReachable_of_portOrCircuitTaitKempeReachable
              data hcurrent,
            first, second, hpair, component, htouches⟩
        · right
          let lifted := current.swapOnKempeComponent
            first second targetComponent
          have hshape :
              IsCircuitKempeComponent current first second targetComponent ∨
                ∃ port, data.KempeComponentMeetsPort
                  current first second targetComponent port :=
            circuit_or_exists_kempeComponentMeetsPort
              data hdata current hcurrentTait hpair targetComponent
          have hlargeStep : PortOrCircuitTaitKempeStep data current lifted :=
            ⟨first, second, hpair, targetComponent, hshape, rfl⟩
          have hliftedReachable :
              PortOrCircuitTaitKempeReachable data base lifted :=
            hcurrent.tail hlargeStep
          have hliftedTait : IsTaitEdgeColoring largeGraph lifted :=
            isTaitEdgeColoring_of_taitKempeStep hcurrentTait
              (taitKempeStep_of_portOrCircuitTaitKempeStep data hlargeStep)
          refine ⟨lifted, hliftedReachable, hliftedTait, hlift, ?_⟩
          intro edge hedge
          exact (hstepOutside edge hedge).trans (houtside edge hedge)

/-- **Adjacent-pair specialization.**  A common-core sequence either reaches
the second deleted pair, or lifts into the first deletion with every switch
circuit-shaped or incident with one of its four exposed ports. -/
theorem firstTaitOrbitReachesSecondPair_or_exists_portOrCircuitConfinedLift
    (source target : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (base : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (hbase : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex)
      base)
    (targetCommon :
      (DeletedTwoPairsGraph G source.firstVertex source.secondVertex
        target.firstVertex target.secondVertex).EdgeColoring Color)
    (hreachable : TaitKempeReachable
      (firstDeletionCommonCoreColoring
        (third := target.firstVertex) (fourth := target.secondVertex)
        base)
      targetCommon) :
    FirstTaitOrbitReachesSecondPair source target base ∨
      ∃ lifted,
        PortOrCircuitTaitKempeReachable
          source.degreeTwoBoundaryData base lifted ∧
        IsTaitEdgeColoring
          (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex)
          lifted ∧
        firstDeletionCommonCoreColoring
          (third := target.firstVertex) (fourth := target.secondVertex)
          lifted = targetCommon ∧
        AgreesOutsideEmbedding base lifted
          (deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex
            source.secondVertex target.firstVertex target.secondVertex) := by
  rcases taitBoundaryAlongLiftOrbit_or_exists_portOrCircuitConfinedLift
      source.degreeTwoBoundaryData
      (source.degreeTwoBoundaryData_wellFormed hcubic)
      base hbase
      (deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex
        source.secondVertex target.firstVertex target.secondVertex)
      targetCommon hreachable with
    hboundary | hlifted
  · left
    rcases hboundary with
      ⟨current, hcurrent, first, second, hpair, component, htouches⟩
    exact ⟨current, hcurrent, first, second, hpair, component,
      firstComponentReachesSecondPair_of_touchesEmbeddingBoundary
        source target current first second component htouches⟩
  · exact Or.inr hlifted

end

end GoertzelV24DegreeTwoBoundaryKempeLiftClassification

end Mettapedia.GraphTheory.FourColor
