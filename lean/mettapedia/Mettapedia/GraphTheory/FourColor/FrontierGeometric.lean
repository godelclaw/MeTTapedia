import Mettapedia.GraphTheory.FourColor.ShellsCore
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

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

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

end Mettapedia.GraphTheory.FourColor
