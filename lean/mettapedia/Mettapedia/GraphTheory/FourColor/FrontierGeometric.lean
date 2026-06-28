import Mettapedia.GraphTheory.FourColor.ShellsCore
import Mettapedia.GraphTheory.FourColor.CAP5AlgebraBridge
import Mettapedia.GraphTheory.FourColor.Theorem49ClosedWalkShellSynthesis
import Mettapedia.GraphTheory.FourColor.Theorem49DetectorStrength
import Mettapedia.GraphTheory.FourColor.Theorem49AtMostOneNonemptyCarrierImpossibility

/-!
# Geometric frontier routes for Theorem 4.9

This module contains the geometric sufficiency wrappers and structural
necessity facts for the v23 frontier.  Algebraic cancellation shells live in
`FrontierPositive`.
-/

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} {G : SimpleGraph V}

/--
Any proposed side-cut support containing an odd closed walk fails before any planar/Jordan
repair data is considered: one vertex-side predicate cannot make every edge in that support
cross the cut.  This packages the two-band triangle obstruction as an arbitrary odd-cycle
separator obstruction, not as a benchmark-specific packet refutation.
-/
theorem not_exists_sideCut_crosses_closed_odd_walk_subset
    {u : V} (p : G.Walk u u) (hodd : Odd p.length) {edgeCut : Finset G.edgeSet}
    (hsubset : ∀ e : G.edgeSet, (e : Sym2 V) ∈ p.edges → e ∈ edgeCut) :
    ¬ ∃ side : V → Prop,
      ∀ e : G.edgeSet, e ∈ edgeCut → EdgeCrossesVertexSide G side e := by
  rintro ⟨side, hcross⟩
  exact not_forall_edgeCrossesVertexSide_of_closed_walk_odd_length_subset
    (G := G) (side := side) p hodd hsubset hcross

variable [DecidableEq V]

/-! ## Geometric lane: what suffices for the synthesis endpoint -/

/-- Repaired previous-boundary witness geometry on the shell's embedding closes
the route: full Theorem 4.9 synthesis for the shell's Tait coloring. -/
theorem boundaryRootSynthesis_of_closedWalkExactShell_and_previousBoundaryWitnessGeometry
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb)
    (geometry : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) :
    Theorem49BoundaryRootSynthesis emb shell.tait.coloring :=
  theorem49LiveBoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint
    shell.source geometry shell.endpoint shell.tait.coloring shell.tait.isTait

/-- Explicit well-founded face-peel witness data also closes the route. -/
theorem boundaryRootSynthesis_of_closedWalkExactShell_and_wellFoundedPeelWitnessData
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb) :
    Theorem49BoundaryRootSynthesis emb shell.tait.coloring :=
  theorem49LiveBoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    shell.source data shell.endpoint shell.tait.coloring shell.tait.isTait

/-- Generic interior-dual boundary-root distance-peel data closes the route:
it constructs the well-founded witness cover on the shell's own embedding. -/
theorem boundaryRootSynthesis_of_closedWalkExactShell_and_interiorDualPeelData
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb)
    (peel : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    Theorem49BoundaryRootSynthesis emb shell.tait.coloring :=
  boundaryRootSynthesis_of_closedWalkExactShell_and_wellFoundedPeelWitnessData shell
    (closedWalkShellWellFoundedFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
      shell.source peel)

/-- Successor-cycle form of the interior-dual sufficiency. -/
theorem boundaryRootSynthesis_of_successorCycleExactShell_and_interiorDualPeelData
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : SuccessorCycleExactShell emb)
    (peel : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    Theorem49BoundaryRootSynthesis emb shell.tait.coloring :=
  boundaryRootSynthesis_of_closedWalkExactShell_and_interiorDualPeelData
    shell.toClosedWalkExactShell peel

/-! ## Structural necessity: why the cardinal repairs are dead -/

/-- On every closed-walk exact shell, the theorem-4.9 target `W₀(H)` is a
proper subspace of the full selected-boundary-zero chain space.  This is the
route-facing form of the detector-strength gap: the new cancellation oracle is
strictly stronger than the manuscript target on every shell-bearing
embedding. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_lt_planarBoundaryZeroSubmodule_of_closedWalkExactShell
    [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb) :
    theorem49BoundaryZeroKirchhoffSubspace emb
        (selectedBoundaryInteriorEdgeEndpointVertices emb) <
      planarBoundaryZeroSubmodule emb :=
  theorem49BoundaryZeroKirchhoffSubspace_lt_planarBoundaryZeroSubmodule_of_hasUnblockedInteriorEndpoint
    shell.endpoint

/-- Every closed-walk shell (the endpoint witness suffices) forces two distinct
interior edges onto some face boundary.  This is the structural fact that kills
the facewise at-most-one, canonical witness choice, and source-preserving
one-collar repair lanes: they all imply the opposite. -/
theorem exists_two_distinct_interiorEdges_of_closedWalkExactShell
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb) :
    ∃ f : AmbientFace emb.faces,
      ∃ e₁ : G.edgeSet,
        e₁ ∈ emb.faceBoundary f.1 ∧
          e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
            ∃ e₂ : G.edgeSet,
              e₂ ∈ emb.faceBoundary f.1 ∧
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧ e₁ ≠ e₂ :=
  exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint
    shell.source shell.endpoint

/--
Closed-walk exact shells structurally block the source-bound canonical one-collar witness
choice.  This is not a benchmark packet: the endpoint witness in the shell already forces a
face with two distinct interior-support edges, while a canonical one-collar witness choice can
own at most one such edge on that face.
-/
theorem not_nonempty_planarBoundaryCanonicalWitnessChoice_of_closedWalkExactShell
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb) :
    ¬ Nonempty
      (PlanarBoundaryCanonicalWitnessChoice
        shell.source.toPlanarBoundaryAnnulusBoundaryData) := by
  rcases exists_two_distinct_interiorEdges_of_closedWalkExactShell shell with
    ⟨f, e₁, he₁Face, he₁Interior, e₂, he₂Face, he₂Interior, hne⟩
  exact
    not_nonempty_planarBoundaryCanonicalWitnessChoice_of_exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkAnnulusBoundarySource
      shell.source
      ⟨f, e₁, he₁Face, e₂, he₂Face, hne, he₁Interior, he₂Interior⟩

/--
The same obstruction blocks every one-collar annulus collar-geometry repair on the shell's
embedding, independently of which one-collar decomposition is proposed.
-/
theorem not_exists_oneCollarAnnulusCollarGeometry_of_closedWalkExactShell
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb) :
    ¬ ∃ data : PlanarBoundaryAnnulusCollarGeometry emb, data.numCollars = 1 := by
  rcases exists_two_distinct_interiorEdges_of_closedWalkExactShell shell with
    ⟨f, e₁, he₁Face, he₁Interior, e₂, he₂Face, he₂Interior, hne⟩
  exact
    not_exists_planarBoundaryAnnulusCollarGeometry_of_numCollars_eq_one_and_exists_two_distinct_interior_edges_on_faceBoundary
      ⟨f, e₁, he₁Face, e₂, he₂Face, hne, he₁Interior, he₂Interior⟩

/--
Consequently, the previous-boundary witness repair cannot be salvaged by asking for a
one-collar positive-collar geometry: that surface extends the same one-collar collar geometry
already ruled out above.
-/
theorem not_exists_oneCollarAnnulusPreviousBoundaryWitnessGeometry_of_closedWalkExactShell
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb) :
    ¬ ∃ data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb,
      data.numCollars = 1 := by
  rintro ⟨data, hnum⟩
  exact
    not_exists_oneCollarAnnulusCollarGeometry_of_closedWalkExactShell shell
      ⟨data.toPlanarBoundaryAnnulusCollarGeometry, hnum⟩

/--
Route-facing CAP5 normal form of the odd side-cut obstruction.  If a finite support contains an
odd closed walk, it cannot be wholly accepted by the exceptional annulus outside-crossing
predicate for any selected side.
-/
theorem not_exists_exceptionalAnnulusCrossingOutsideEdge_of_closed_odd_walk_subset
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (p0Inside p4Inside : Bool)
    {u : V} (p : G.Walk u u) (hodd : Odd p.length) {edgeCut : Finset G.edgeSet}
    (hsubset : ∀ e : G.edgeSet, (e : Sym2 V) ∈ p.edges → e ∈ edgeCut) :
    ¬ ∃ side : V → Prop,
      ∀ e : G.edgeSet, e ∈ edgeCut →
        data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side e := by
  rintro ⟨side, houtside⟩
  exact data.not_forall_exceptionalAnnulusCrossingOutsideEdge_of_closed_walk_odd_length_subset
    (p0Inside := p0Inside) (p4Inside := p4Inside) (side := side) p hodd hsubset
    houtside

/--
The CAP5/Jordan repair-removal surface for the exceptional annulus branch: at least one
compatible transported CAP5 boundary-edge candidate has been realized as actual cyclic-cut data
in the ambient graph.  This is the topological endpoint the geometric repair must supply before
the algebraic CAP5 lane can consume the exceptional branch.
-/
def CAP5ExceptionalCyclicSeparatorRepairRealization
    [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (p0Inside p4Inside : Bool) : Prop :=
  data.HasSomeExceptionalAnnulusCyclicCutRealizationData (G := G) p0Inside p4Inside

omit [DecidableEq V] in
/--
Fundamental obstruction to the realized exceptional-annulus repair surface.  Once the CAP5/Jordan
repair-removal step realizes even one compatible exceptional candidate as cyclic-cut data, it has
produced a cyclic edge cut of size at most four.  In a cyclically five-edge-connected graph this is
impossible, independently of which CAP5 orientation or side case was selected.
-/
theorem not_CAP5ExceptionalCyclicSeparatorRepairRealization_of_cyclicallyFiveEdgeConnected
    [DecidableEq G.edgeSet]
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (p0Inside p4Inside : Bool)
    (hcyclic : CyclicallyFiveEdgeConnected G) :
    ¬ CAP5ExceptionalCyclicSeparatorRepairRealization (G := G)
      data p0Inside p4Inside := by
  intro hrealization
  exact hcyclic.noCyclicEdgeCutOfSizeAtMostFour
    (data.hasCyclicEdgeCutOfSizeAtMostFour_of_someExceptionalAnnulusCyclicCutRealizationData
      p0Inside p4Inside hrealization)

/--
Consolidated geometric fork obstruction for the currently live repair class.  A closed-walk
exact shell rules out the source-bound canonical/one-collar repairs by the shared two-interior
edge face obstruction; if the proposed side-cut support also contains an odd closed walk, the
same repair packet cannot realize a cyclic separator either.
-/
theorem closedWalkExactShell_oneCollar_and_oddSideCut_obstruction
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb)
    {u : V} (p : G.Walk u u) (hodd : Odd p.length) {edgeCut : Finset G.edgeSet}
    (hsubset : ∀ e : G.edgeSet, (e : Sym2 V) ∈ p.edges → e ∈ edgeCut) :
    (¬ Nonempty
      (PlanarBoundaryCanonicalWitnessChoice
        shell.source.toPlanarBoundaryAnnulusBoundaryData)) ∧
      (¬ ∃ data : PlanarBoundaryAnnulusCollarGeometry emb, data.numCollars = 1) ∧
        (¬ ∃ data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb,
          data.numCollars = 1) ∧
          (¬ ∃ side : V → Prop,
            ∀ e : G.edgeSet, e ∈ edgeCut → EdgeCrossesVertexSide G side e) := by
  exact
    ⟨not_nonempty_planarBoundaryCanonicalWitnessChoice_of_closedWalkExactShell shell,
      not_exists_oneCollarAnnulusCollarGeometry_of_closedWalkExactShell shell,
      not_exists_oneCollarAnnulusPreviousBoundaryWitnessGeometry_of_closedWalkExactShell shell,
      not_exists_sideCut_crosses_closed_odd_walk_subset p hodd hsubset⟩

/--
CAP5-specific consolidated form: the source-bound one-collar repair is impossible on a
closed-walk exact shell, and an odd-walk side-cut support cannot be repaired by the exceptional
annulus outside-crossing normal form.
-/
theorem closedWalkExactShell_oneCollar_and_CAP5OddSideCut_obstruction
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb)
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (p0Inside p4Inside : Bool)
    {u : V} (p : G.Walk u u) (hodd : Odd p.length) {edgeCut : Finset G.edgeSet}
    (hsubset : ∀ e : G.edgeSet, (e : Sym2 V) ∈ p.edges → e ∈ edgeCut) :
    (¬ Nonempty
      (PlanarBoundaryCanonicalWitnessChoice
        shell.source.toPlanarBoundaryAnnulusBoundaryData)) ∧
      (¬ ∃ collar : PlanarBoundaryAnnulusCollarGeometry emb, collar.numCollars = 1) ∧
        (¬ ∃ previous : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb,
          previous.numCollars = 1) ∧
          (¬ ∃ side : V → Prop,
            ∀ e : G.edgeSet, e ∈ edgeCut →
              data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side e) := by
  exact
    ⟨not_nonempty_planarBoundaryCanonicalWitnessChoice_of_closedWalkExactShell shell,
      not_exists_oneCollarAnnulusCollarGeometry_of_closedWalkExactShell shell,
      not_exists_oneCollarAnnulusPreviousBoundaryWitnessGeometry_of_closedWalkExactShell shell,
      not_exists_exceptionalAnnulusCrossingOutsideEdge_of_closed_odd_walk_subset data
        p0Inside p4Inside p hodd hsubset⟩

/--
Repair-removal form of the consolidated geometric obstruction.  A closed-walk exact shell blocks
the source-bound one-collar/canonical repairs by the two-interior-edge face obstruction, while
cyclic five-edge-connectivity blocks the CAP5/Jordan exceptional cyclic-separator realization
itself: any compatible realized candidate would be a forbidden cyclic edge cut of size at most
four.  This moves the side-cut lane from packet refutations to the structural small-cut
obstruction consumed by the CAP5 repair-removal interface.
-/
theorem closedWalkExactShell_oneCollar_and_CAP5CyclicSeparatorRepair_obstruction
    [DecidableEq G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb)
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (p0Inside p4Inside : Bool)
    (hcyclic : CyclicallyFiveEdgeConnected G) :
    (¬ Nonempty
      (PlanarBoundaryCanonicalWitnessChoice
        shell.source.toPlanarBoundaryAnnulusBoundaryData)) ∧
      (¬ ∃ collar : PlanarBoundaryAnnulusCollarGeometry emb, collar.numCollars = 1) ∧
        (¬ ∃ previous : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb,
          previous.numCollars = 1) ∧
          (¬ CAP5ExceptionalCyclicSeparatorRepairRealization (G := G)
            data p0Inside p4Inside) := by
  exact
    ⟨not_nonempty_planarBoundaryCanonicalWitnessChoice_of_closedWalkExactShell shell,
      not_exists_oneCollarAnnulusCollarGeometry_of_closedWalkExactShell shell,
      not_exists_oneCollarAnnulusPreviousBoundaryWitnessGeometry_of_closedWalkExactShell shell,
      not_CAP5ExceptionalCyclicSeparatorRepairRealization_of_cyclicallyFiveEdgeConnected
        data p0Inside p4Inside hcyclic⟩

end Mettapedia.GraphTheory.FourColor
