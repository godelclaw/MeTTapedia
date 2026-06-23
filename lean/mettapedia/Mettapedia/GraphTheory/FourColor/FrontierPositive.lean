import Mettapedia.GraphTheory.FourColor.FrontierGeometric
import Mettapedia.GraphTheory.FourColor.Shells
import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceReplacementRoute

/-!
# Positive frontier routes for Theorem 4.9

This module contains the algebraic cancellation theorem surfaces known to
suffice for the current synthesis endpoint.  It also imports
`FrontierGeometric`, so importing this module keeps the full positive frontier
surface available.
-/

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-! ## Algebraic lane: what suffices for the synthesis endpoint -/

/-- The finite-lab algebraic cancellation certificate also closes the route:
once the shell's Tait coloring satisfies the projected-generator detector
property, no additional theorem-4.9 algebra remains. -/
theorem boundaryRootSynthesis_of_closedWalkExactShell_and_boundaryZeroProjectedGeneratorDetector
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb)
    (detector : BoundaryZeroProjectedGeneratorDetector emb shell.tait.coloring) :
    Theorem49BoundaryRootSynthesis emb shell.tait.coloring :=
  theorem49BoundaryRootSynthesis_of_boundaryZeroProjectedGeneratorDetector
    emb shell.tait.coloring detector

/-- Bundled closed-walk form of the algebraic cancellation route. -/
theorem boundaryRootSynthesis_of_closedWalkCancellationShell
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkCancellationShell emb) :
    Theorem49BoundaryRootSynthesis emb shell.exactShell.tait.coloring :=
  boundaryRootSynthesis_of_closedWalkExactShell_and_boundaryZeroProjectedGeneratorDetector
    shell.exactShell shell.detector

/-- Smaller explicit projected-generator certificates inside the shell Tait coloring's Kempe
closure also close the route.  This is the live surface form that matches the finite-lab
certificate shape directly. -/
theorem boundaryRootSynthesis_of_closedWalkExactShell_and_boundaryZeroProjectedColoringGeneratorDetector
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure shell.tait.coloring)
    (detector : BoundaryZeroProjectedColoringGeneratorDetector emb colorings) :
    Theorem49BoundaryRootSynthesis emb shell.tait.coloring :=
  theorem49BoundaryRootSynthesis_of_boundaryZeroProjectedColoringGeneratorDetector
    emb shell.tait.coloring colorings hsubset detector

/-- Bundled closed-walk form of the smaller-family algebraic cancellation route. -/
theorem boundaryRootSynthesis_of_closedWalkNeighborhoodCancellationShell
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkNeighborhoodCancellationShell emb) :
    Theorem49BoundaryRootSynthesis emb shell.exactShell.tait.coloring :=
  boundaryRootSynthesis_of_closedWalkExactShell_and_boundaryZeroProjectedColoringGeneratorDetector
    shell.exactShell shell.colorings shell.subset_closure shell.detector

/-- Direct family-pairing kernel certificates on an explicit Kempe neighborhood also close the
route.  This is the exact shell-facing form of the current finite `F₂` kernel-check target. -/
theorem boundaryRootSynthesis_of_closedWalkExactShell_and_familyPairingKerEqBot
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure shell.tait.coloring)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (hker : LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) = ⊥) :
    Theorem49BoundaryRootSynthesis emb shell.tait.coloring :=
  theorem49BoundaryRootSynthesis_of_familyPairingKerEqBot
    emb shell.tait.coloring colorings hsubset family hker

/-- Bundled closed-walk form of the explicit family-pairing kernel route. -/
theorem boundaryRootSynthesis_of_closedWalkNeighborhoodPairingKernelShell
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkNeighborhoodPairingKernelShell emb) :
    Theorem49BoundaryRootSynthesis emb shell.exactShell.tait.coloring :=
  boundaryRootSynthesis_of_closedWalkNeighborhoodCancellationShell
    shell.toClosedWalkNeighborhoodCancellationShell

/-- Successor-cycle form of the algebraic cancellation sufficiency. -/
theorem boundaryRootSynthesis_of_successorCycleCancellationShell
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : SuccessorCycleCancellationShell emb) :
    Theorem49BoundaryRootSynthesis emb shell.exactShell.tait.coloring :=
  boundaryRootSynthesis_of_closedWalkCancellationShell
    shell.toClosedWalkCancellationShell

/-- Successor-cycle form of the smaller-family algebraic cancellation route. -/
theorem boundaryRootSynthesis_of_successorCycleNeighborhoodCancellationShell
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : SuccessorCycleNeighborhoodCancellationShell emb) :
    Theorem49BoundaryRootSynthesis emb shell.exactShell.tait.coloring :=
  boundaryRootSynthesis_of_closedWalkNeighborhoodCancellationShell
    shell.toClosedWalkNeighborhoodCancellationShell

/-- Successor-cycle form of the direct family-pairing kernel route. -/
theorem boundaryRootSynthesis_of_successorCycleNeighborhoodPairingKernelShell
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (shell : SuccessorCycleNeighborhoodPairingKernelShell emb) :
    Theorem49BoundaryRootSynthesis emb shell.exactShell.tait.coloring :=
  boundaryRootSynthesis_of_closedWalkNeighborhoodPairingKernelShell
    shell.toClosedWalkNeighborhoodPairingKernelShell

end Mettapedia.GraphTheory.FourColor
