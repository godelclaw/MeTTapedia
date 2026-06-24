import Mettapedia.GraphTheory.FourColor.CAP5Reducibility
import Mettapedia.GraphTheory.FourColor.Theorem49ColoringGeneratorCoordinateKernelProducer

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Edge predicate emitted by the exceptional CAP5 finite generator when the proposed
size-at-most-four separator is forced into the counterexample bin.  Such an edge lies outside the
candidate CAP5 support, crosses the chosen side, and is carried by the one-edge walk avoiding all
listed separator portals. -/
def CAP5TransportedEdgeComponentCoverCore.ExceptionalAnnulusOneEdgeCounterexampleEdge
    {G : SimpleGraph V}
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (p0Inside p4Inside : Bool) (side : V → Prop) (e : G.edgeSet) : Prop :=
  ∃ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
    data.RealizesExceptionalBoundarySupportOrientation
        edgeCandidate.portalCandidate.orientation ∧
      edgeCandidate.portalCandidate.sideCase =
        CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside ∧
      ∃ u v : V, ∃ p : G.Walk u v,
        e ∉ edgeCandidate.edgeSupport ∧
          side u ∧ ¬ side v ∧
            p.edges = [(e : Sym2 V)] ∧
              ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
                ((boundaryEdge i : G.edgeSet) : Sym2 V) ∉ p.edges

/-- The cyclic-five-edge-connected exceptional CAP5 branch emits at least one algebraically
addressable one-edge counterexample edge.  This is the generator-facing edge predicate consumed by
the non-geometric pairing lane. -/
theorem CAP5TransportedEdgeComponentCoverCore.exists_exceptionalAnnulusOneEdgeCounterexampleEdge_of_isExceptional_of_portalSides
    {G : SimpleGraph V}
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (side : V → Prop)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide G side (boundaryEdge i))
    (hinside_cycle : HasCycleOnSide G side)
    (houtside_cycle : HasCycleOnSide G (fun v => ¬ side v)) :
    ∃ e : G.edgeSet,
      data.ExceptionalAnnulusOneEdgeCounterexampleEdge p0Inside p4Inside side e := by
  rcases data.exists_exceptionalAnnulusBoundaryEdgeSupportCandidate_oneEdgeCounterexample_of_isExceptional_of_portalSides
      p0Inside p4Inside h side hcyclic hportal_crosses hinside_cycle houtside_cycle with
    ⟨edgeCandidate, horientation, hsideCase, u, v, e, p, heOutside, hu, hv, hpEdges,
      havoid⟩
  exact ⟨e, edgeCandidate, horientation, hsideCase, u, v, p, heOutside, hu, hv, hpEdges,
    havoid⟩

/-- Algebraic consumption of the exceptional CAP5 counterexample bin.  Once the finite generator
emits a forced outside edge, any selected chain that is nonzero on every such emitted edge is
detected by a projected generator family containing the red and blue single-coordinate chains on
those edges.  The nonzero-coordinate hypothesis is intentionally explicit: this theorem connects
the separator refutation to the algebraic lane without claiming that the lane is already closed. -/
theorem exists_familyPairing_ne_zero_of_exceptionalAnnulusOneEdgeCounterexampleEdge
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (side : V → Prop)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide G side (boundaryEdge i))
    (hinside_cycle : HasCycleOnSide G side)
    (houtside_cycle : HasCycleOnSide G (fun v => ¬ side v))
    {z : G.edgeSet → Color}
    (hzNonzero :
      ∀ e : G.edgeSet,
        data.ExceptionalAnnulusOneEdgeCounterexampleEdge p0Inside p4Inside side e →
          z e ≠ 0)
    (hwitnessRed :
      ∀ e : G.edgeSet,
        data.ExceptionalAnnulusOneEdgeCounterexampleEdge p0Inside p4Inside side e →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e red)
    (hwitnessBlue :
      ∀ e : G.edgeSet,
        data.ExceptionalAnnulusOneEdgeCounterexampleEdge p0Inside p4Inside side e →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e blue) :
    ∃ i : κ,
      chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z ≠ 0 := by
  apply exists_familyPairing_ne_zero_of_edgePredicateWitness family
    (data.ExceptionalAnnulusOneEdgeCounterexampleEdge p0Inside p4Inside side)
  · rcases data.exists_exceptionalAnnulusOneEdgeCounterexampleEdge_of_isExceptional_of_portalSides
      p0Inside p4Inside h side hcyclic hportal_crosses hinside_cycle houtside_cycle with
      ⟨e, hedge⟩
    exact ⟨e, hedge, hzNonzero e hedge⟩
  · exact hwitnessRed
  · exact hwitnessBlue

end Mettapedia.GraphTheory.FourColor
