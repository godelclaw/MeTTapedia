import Mettapedia.GraphTheory.FourColor.ShellsCore
import Mettapedia.GraphTheory.FourColor.Theorem49ColoringGeneratorFamilyPairing

/-!
# Algebraic bundled hypothesis shells for the Theorem 4.9 route

The core geometric/v23 shell data lives in `ShellsCore`.  This module adds the
detector and family-kernel shells used by the algebraic repair lanes.
-/

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- The exact closed-walk shell together with the non-geometric algebraic
cancellation certificate suggested by the finite lab: every nonzero
selected-boundary-zero chain pairs nontrivially with some projected
Definition 4.8 generator for the shell's Tait coloring. -/
structure ClosedWalkCancellationShell (emb : PlaneEmbeddingWithBoundary G)
    [Fintype G.edgeSet] where
  exactShell : ClosedWalkExactShell emb
  detector : BoundaryZeroProjectedGeneratorDetector emb exactShell.tait.coloring

/-- The exact closed-walk shell together with a smaller explicit projected-generator detector on
some coloring family inside the shell Tait coloring's edge-Kempe closure.  This matches the
finite-lab certificate shape more closely than the closure-wide detector. -/
structure ClosedWalkNeighborhoodCancellationShell (emb : PlaneEmbeddingWithBoundary G)
    [Fintype G.edgeSet] where
  exactShell : ClosedWalkExactShell emb
  colorings : Set (G.EdgeColoring Color)
  subset_closure : colorings ⊆ G.EdgeKempeClosure exactShell.tait.coloring
  detector : BoundaryZeroProjectedColoringGeneratorDetector emb colorings

/-- The exact closed-walk shell together with an explicit projected-generator family inside the
shell Tait coloring's Kempe closure whose concrete family-evaluation pairing map has trivial
kernel.  This packages the direct kernel-checkable finite `F₂` certificates suggested by the
current lab output. -/
structure ClosedWalkNeighborhoodPairingKernelShell (emb : PlaneEmbeddingWithBoundary G)
    [Fintype G.edgeSet] where
  exactShell : ClosedWalkExactShell emb
  colorings : Set (G.EdgeColoring Color)
  subset_closure : colorings ⊆ G.EdgeKempeClosure exactShell.tait.coloring
  κ : Type*
  family : κ → projectedColoringGeneratorSubspace emb colorings
  pairingKernel_eq_bot :
    LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) = ⊥

/-- Successor-cycle version of the exact shell plus algebraic cancellation
certificate. -/
structure SuccessorCycleCancellationShell (emb : PlaneEmbeddingWithBoundary G)
    [Fintype G.edgeSet] where
  exactShell : SuccessorCycleExactShell emb
  detector : BoundaryZeroProjectedGeneratorDetector emb exactShell.tait.coloring

/-- Successor-cycle version of the exact shell plus an explicit subfamily detector. -/
structure SuccessorCycleNeighborhoodCancellationShell (emb : PlaneEmbeddingWithBoundary G)
    [Fintype G.edgeSet] where
  exactShell : SuccessorCycleExactShell emb
  colorings : Set (G.EdgeColoring Color)
  subset_closure : colorings ⊆ G.EdgeKempeClosure exactShell.tait.coloring
  detector : BoundaryZeroProjectedColoringGeneratorDetector emb colorings

/-- Successor-cycle version of the exact shell plus a direct family-pairing kernel certificate. -/
structure SuccessorCycleNeighborhoodPairingKernelShell (emb : PlaneEmbeddingWithBoundary G)
    [Fintype G.edgeSet] where
  exactShell : SuccessorCycleExactShell emb
  colorings : Set (G.EdgeColoring Color)
  subset_closure : colorings ⊆ G.EdgeKempeClosure exactShell.tait.coloring
  κ : Type*
  family : κ → projectedColoringGeneratorSubspace emb colorings
  pairingKernel_eq_bot :
    LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) = ⊥

/-- Forget the stronger family-kernel certificate down to the smaller-family detector shell. -/
def ClosedWalkNeighborhoodPairingKernelShell.toClosedWalkNeighborhoodCancellationShell
    {emb : PlaneEmbeddingWithBoundary G} [Fintype G.edgeSet]
    (shell : ClosedWalkNeighborhoodPairingKernelShell emb) :
    ClosedWalkNeighborhoodCancellationShell emb where
  exactShell := shell.exactShell
  colorings := shell.colorings
  subset_closure := shell.subset_closure
  detector :=
    detector_of_ker_planarBoundaryZeroFamilyPairingMap_eq_bot
      shell.family shell.pairingKernel_eq_bot

/-- Lower the successor-cycle cancellation shell to the honest closed-walk
version.  The detector certificate is preserved unchanged because the lowered
shell keeps the same embedding and Tait coloring. -/
def SuccessorCycleCancellationShell.toClosedWalkCancellationShell
    {emb : PlaneEmbeddingWithBoundary G} [Fintype G.edgeSet]
    (shell : SuccessorCycleCancellationShell emb) :
    ClosedWalkCancellationShell emb where
  exactShell := shell.exactShell.toClosedWalkExactShell
  detector := shell.detector

/-- Lower the successor-cycle neighborhood-cancellation shell to the honest closed-walk version.
The explicit family and its detector transport unchanged because the lowered shell keeps the same
embedding and Tait coloring. -/
def SuccessorCycleNeighborhoodCancellationShell.toClosedWalkNeighborhoodCancellationShell
    {emb : PlaneEmbeddingWithBoundary G} [Fintype G.edgeSet]
    (shell : SuccessorCycleNeighborhoodCancellationShell emb) :
    ClosedWalkNeighborhoodCancellationShell emb where
  exactShell := shell.exactShell.toClosedWalkExactShell
  colorings := shell.colorings
  subset_closure := by
    simpa using shell.subset_closure
  detector := shell.detector

/-- Lower the successor-cycle pairing-kernel shell to the honest closed-walk version.  The
explicit family and its kernel certificate transport unchanged because the lowered shell keeps the
same embedding and Tait coloring. -/
def SuccessorCycleNeighborhoodPairingKernelShell.toClosedWalkNeighborhoodPairingKernelShell
    {emb : PlaneEmbeddingWithBoundary G} [Fintype G.edgeSet]
    (shell : SuccessorCycleNeighborhoodPairingKernelShell emb) :
    ClosedWalkNeighborhoodPairingKernelShell emb where
  exactShell := shell.exactShell.toClosedWalkExactShell
  colorings := shell.colorings
  subset_closure := by
    simpa using shell.subset_closure
  κ := shell.κ
  family := shell.family
  pairingKernel_eq_bot := by
    simpa using shell.pairingKernel_eq_bot

end Mettapedia.GraphTheory.FourColor
