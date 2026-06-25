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

/-- Normal-form edge predicate for the exceptional CAP5 counterexample bin.  It forgets the
canonical one-edge walk payload and keeps exactly the checker-facing data: a realized exceptional
boundary-support candidate plus an edge outside that support crossing the selected side. -/
def CAP5TransportedEdgeComponentCoverCore.ExceptionalAnnulusCrossingOutsideEdge
    {G : SimpleGraph V}
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (p0Inside p4Inside : Bool) (side : V → Prop) (e : G.edgeSet) : Prop :=
  ∃ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
    data.RealizesExceptionalBoundarySupportOrientation
        edgeCandidate.portalCandidate.orientation ∧
      edgeCandidate.portalCandidate.sideCase =
        CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside ∧
        e ∉ edgeCandidate.edgeSupport ∧
          EdgeCrossesVertexSide G side e

/-- The exceptional CAP5 one-edge counterexample predicate always emits a genuine
side-crossing edge.  This keeps the algebraic lane connected to the raw cyclic-cut checker
instead of treating the emitted edge as an opaque witness. -/
theorem CAP5TransportedEdgeComponentCoverCore.exceptionalAnnulusOneEdgeCounterexampleEdge_crosses
    {G : SimpleGraph V}
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {p0Inside p4Inside : Bool} {side : V → Prop} {e : G.edgeSet}
    (h : data.ExceptionalAnnulusOneEdgeCounterexampleEdge p0Inside p4Inside side e) :
    EdgeCrossesVertexSide G side e := by
  rcases h with
    ⟨_edgeCandidate, _horientation, _hsideCase, u, v, p, _heOutside, hu, hv, hpEdges,
      _havoid⟩
  rcases exists_edgeCrossesVertexSide_of_walk_endpoint_sides side p hu hv with
    ⟨e', heEdges, hcross⟩
  have hsym : (e' : Sym2 V) = (e : Sym2 V) := by
    simpa [hpEdges] using heEdges
  have heq : e' = e := Subtype.ext hsym
  simpa [heq] using hcross

/-- Normal form for the exceptional CAP5 one-edge counterexample predicate: the one-edge walk
payload is canonical, so the predicate is equivalent to a realized exceptional candidate plus a
concrete edge outside that candidate support crossing the selected side. -/
theorem CAP5TransportedEdgeComponentCoverCore.exceptionalAnnulusOneEdgeCounterexampleEdge_iff_exists_candidate_crossing_outside
    {G : SimpleGraph V}
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {p0Inside p4Inside : Bool} {side : V → Prop} {e : G.edgeSet} :
    data.ExceptionalAnnulusOneEdgeCounterexampleEdge p0Inside p4Inside side e ↔
      ∃ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation ∧
          edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside ∧
            e ∉ edgeCandidate.edgeSupport ∧
              EdgeCrossesVertexSide G side e := by
  constructor
  · intro h
    rcases h with
      ⟨edgeCandidate, horientation, hsideCase, u, v, p, heOutside, hu, hv, hpEdges,
        havoid⟩
    have hcross :
        EdgeCrossesVertexSide G side e :=
      data.exceptionalAnnulusOneEdgeCounterexampleEdge_crosses
        ⟨edgeCandidate, horientation, hsideCase, u, v, p, heOutside, hu, hv, hpEdges,
          havoid⟩
    exact ⟨edgeCandidate, horientation, hsideCase, heOutside, hcross⟩
  · rintro ⟨edgeCandidate, horientation, hsideCase, heOutside, hcross⟩
    rcases hcross with ⟨u, v, hu, hv, hsu, hsv⟩
    rcases exists_walk_edges_eq_singleton_of_edge_endpoint_sides
        (G := G) (side := side) (e := e) hu hv hsu hsv with
      ⟨p, hpEdges⟩
    refine ⟨edgeCandidate, horientation, hsideCase, u, v, p,
      heOutside, hsu, hsv, hpEdges, ?_⟩
    intro i hi hiEdges
    have hboundary_eq : boundaryEdge i = e := by
      apply Subtype.ext
      simpa [hpEdges] using hiEdges
    exact heOutside ((edgeCandidate.mem_edgeSupport_iff_exists_portal e).2
      ⟨i, hi, hboundary_eq⟩)

/-- Named normal-form equivalence for the exceptional CAP5 one-edge counterexample edge
predicate.  Algebraic follow-up work can use `ExceptionalAnnulusCrossingOutsideEdge` when the
one-edge walk payload is irrelevant. -/
theorem CAP5TransportedEdgeComponentCoverCore.exceptionalAnnulusOneEdgeCounterexampleEdge_iff_crossingOutsideEdge
    {G : SimpleGraph V}
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {p0Inside p4Inside : Bool} {side : V → Prop} {e : G.edgeSet} :
    data.ExceptionalAnnulusOneEdgeCounterexampleEdge p0Inside p4Inside side e ↔
      data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side e :=
  data.exceptionalAnnulusOneEdgeCounterexampleEdge_iff_exists_candidate_crossing_outside

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

/-- Stronger raw-checker output form: the exceptional CAP5 branch emits a one-edge
counterexample and that emitted edge is a genuine side-crossing edge. -/
theorem CAP5TransportedEdgeComponentCoverCore.exists_crossing_exceptionalAnnulusOneEdgeCounterexampleEdge_of_isExceptional_of_portalSides
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
      data.ExceptionalAnnulusOneEdgeCounterexampleEdge p0Inside p4Inside side e ∧
        EdgeCrossesVertexSide G side e := by
  rcases data.exists_exceptionalAnnulusOneEdgeCounterexampleEdge_of_isExceptional_of_portalSides
      p0Inside p4Inside h side hcyclic hportal_crosses hinside_cycle houtside_cycle with
    ⟨e, hedge⟩
  exact ⟨e, hedge, data.exceptionalAnnulusOneEdgeCounterexampleEdge_crosses hedge⟩

/-- Normal-form raw-checker output: the exceptional CAP5 branch emits an edge outside a realized
boundary-support candidate that crosses the selected side. -/
theorem CAP5TransportedEdgeComponentCoverCore.exists_exceptionalAnnulusCrossingOutsideEdge_of_isExceptional_of_portalSides
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
      data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side e := by
  rcases data.exists_exceptionalAnnulusOneEdgeCounterexampleEdge_of_isExceptional_of_portalSides
      p0Inside p4Inside h side hcyclic hportal_crosses hinside_cycle houtside_cycle with
    ⟨e, hedge⟩
  exact ⟨e, (data.exceptionalAnnulusOneEdgeCounterexampleEdge_iff_crossingOutsideEdge).1 hedge⟩

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

/-- Predicate-level algebraic target for the exceptional CAP5 counterexample bin.  If the edges
emitted by the one-edge counterexample generator control all selected-boundary-zero chains, then
red/blue single-coordinate witnesses on those emitted edges separate family pairings on the whole
selected-boundary-zero subspace. -/
theorem familyPairing_separates_of_exceptionalAnnulusOneEdgeCounterexampleEdges
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e : G.edgeSet,
          data.ExceptionalAnnulusOneEdgeCounterexampleEdge p0Inside p4Inside side e →
            z e = 0) →
          z = 0)
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
    ∀ z : planarBoundaryZeroSubmodule emb,
      (∀ i,
        chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color)
          (z : G.edgeSet → Color) = 0) →
        z = 0 :=
  familyPairing_separates_of_edgePredicateWitnesses family
    (data.ExceptionalAnnulusOneEdgeCounterexampleEdge p0Inside p4Inside side)
    hcontrol hwitnessRed hwitnessBlue

/-- Full Theorem 4.9 synthesis route from the exceptional CAP5 emitted-edge predicate.  The
remaining finite-generator obligation is exactly the control hypothesis: every selected-
boundary-zero chain is determined by its coordinates on the emitted counterexample edges. -/
theorem theorem49BoundaryRootSynthesis_of_exceptionalAnnulusCounterexampleEdgeControl
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e : G.edgeSet,
          data.ExceptionalAnnulusOneEdgeCounterexampleEdge p0Inside p4Inside side e →
            z e = 0) →
          z = 0)
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
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_edgePredicateFamilyPairingSeparation
    emb C₀ colorings hsubset family
    (data.ExceptionalAnnulusOneEdgeCounterexampleEdge p0Inside p4Inside side)
    hcontrol hwitnessRed hwitnessBlue

/-- Witness-form equivalent of the CAP5 emitted-edge control obligation.  The algebraic finite
checker can target the right-hand side: every nonzero selected-boundary-zero chain exposes a
nonzero coordinate on some edge emitted by the exceptional-annulus counterexample generator. -/
theorem exceptionalAnnulusCounterexampleEdgeControl_iff_forall_nonzero_exists
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G}
    (p0Inside p4Inside : Bool) (side : V → Prop) :
    (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ e : G.edgeSet,
        data.ExceptionalAnnulusOneEdgeCounterexampleEdge p0Inside p4Inside side e →
          z e = 0) →
        z = 0) ↔
    (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      z ≠ 0 →
        ∃ e : G.edgeSet,
          data.ExceptionalAnnulusOneEdgeCounterexampleEdge p0Inside p4Inside side e ∧
            z e ≠ 0) :=
  edgePredicateControls_iff_forall_nonzero_exists_edgePredicateWitness
    (data.ExceptionalAnnulusOneEdgeCounterexampleEdge p0Inside p4Inside side)

/-- Witness-form equivalent of the normal-form CAP5 outside-crossing control obligation.  This is
the algebraic target naturally emitted by the finite checker: every nonzero selected-boundary-zero
chain must be visible on some crossing edge outside a realized exceptional boundary-support
candidate. -/
theorem exceptionalAnnulusCrossingOutsideEdgeControl_iff_forall_nonzero_exists
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G}
    (p0Inside p4Inside : Bool) (side : V → Prop) :
    (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ e : G.edgeSet,
        data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side e →
          z e = 0) →
        z = 0) ↔
    (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      z ≠ 0 →
        ∃ e : G.edgeSet,
          data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side e ∧
            z e ≠ 0) :=
  edgePredicateControls_iff_forall_nonzero_exists_edgePredicateWitness
    (data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side)

/-- The one-edge payload and the normal-form outside-crossing predicate give the same algebraic
control obligation. -/
theorem exceptionalAnnulusCounterexampleEdgeControl_iff_crossingOutsideEdgeControl
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G}
    (p0Inside p4Inside : Bool) (side : V → Prop) :
    (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ e : G.edgeSet,
        data.ExceptionalAnnulusOneEdgeCounterexampleEdge p0Inside p4Inside side e →
          z e = 0) →
        z = 0) ↔
    (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ e : G.edgeSet,
        data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side e →
          z e = 0) →
        z = 0) := by
  constructor
  · intro h z hz hvanish
    exact h hz (by
      intro e hedge
      exact hvanish e
        ((data.exceptionalAnnulusOneEdgeCounterexampleEdge_iff_crossingOutsideEdge).1 hedge))
  · intro h z hz hvanish
    exact h hz (by
      intro e hedge
      exact hvanish e
        ((data.exceptionalAnnulusOneEdgeCounterexampleEdge_iff_crossingOutsideEdge).2 hedge))

/-- Predicate-level CAP5 algebraic route in witness form.  This avoids making the finite
generator prove a global control statement directly: it may instead emit a counterexample edge
where each nonzero selected-boundary-zero chain is nonzero. -/
theorem familyPairing_separates_of_exceptionalAnnulusOneEdgeCounterexampleNonzeroWitnesses
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (hnonzero :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.ExceptionalAnnulusOneEdgeCounterexampleEdge p0Inside p4Inside side e ∧
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
    ∀ z : planarBoundaryZeroSubmodule emb,
      (∀ i,
        chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color)
          (z : G.edgeSet → Color) = 0) →
        z = 0 :=
  familyPairing_separates_of_edgePredicateNonzeroWitnesses family
    (data.ExceptionalAnnulusOneEdgeCounterexampleEdge p0Inside p4Inside side)
    hnonzero hwitnessRed hwitnessBlue

/-- Theorem 4.9 synthesis route from CAP5 witness-form edge control.  The named remaining
obligation is now local and checker-facing: every nonzero selected-boundary-zero chain must have
a nonzero coordinate on an emitted exceptional-annulus counterexample edge. -/
theorem theorem49BoundaryRootSynthesis_of_exceptionalAnnulusCounterexampleNonzeroWitnesses
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (hnonzero :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.ExceptionalAnnulusOneEdgeCounterexampleEdge p0Inside p4Inside side e ∧
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
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_edgePredicateNonzeroWitnesses
    emb C₀ colorings hsubset family
    (data.ExceptionalAnnulusOneEdgeCounterexampleEdge p0Inside p4Inside side)
    hnonzero hwitnessRed hwitnessBlue

/-- Theorem 4.9 synthesis route from the normal-form outside-crossing predicate.  This is the
generator-facing algebraic target after the CAP5 separator candidate has been binned as a
counterexample: find a crossing edge outside the realized support where every nonzero
selected-boundary-zero chain is detected. -/
theorem theorem49BoundaryRootSynthesis_of_exceptionalAnnulusCrossingOutsideNonzeroWitnesses
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (hnonzero :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side e ∧
              z e ≠ 0)
    (hwitnessRed :
      ∀ e : G.edgeSet,
        data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side e →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e red)
    (hwitnessBlue :
      ∀ e : G.edgeSet,
        data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side e →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e blue) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_edgePredicateNonzeroWitnesses
    emb C₀ colorings hsubset family
    (data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side)
    hnonzero hwitnessRed hwitnessBlue

end Mettapedia.GraphTheory.FourColor
