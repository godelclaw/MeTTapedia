import Mettapedia.GraphTheory.FourColor.Goal
import Mettapedia.GraphTheory.FourColor.Theorem49ColoringGeneratorFamilyPairing
import Mettapedia.GraphTheory.FourColor.Theorem49ColoringGeneratorFamilyRoute

/-!
# Algebraic repair lanes for the FourColor goal

This module keeps the non-geometric detector/cancellation candidates out of the
default geometric `Goal` import surface.
-/

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Uniform non-geometric candidate repair lane: every exact shell already
supplies the projected-generator detector certificate suggested by the finite
lab's explicit algebraic cancellation checks. -/
def AlgebraicCancellationOracle : Prop :=
  ∀ {W : Type} [DecidableEq W] {G : SimpleGraph W} [Fintype G.edgeSet]
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (shell : ClosedWalkExactShell emb),
      BoundaryZeroProjectedGeneratorDetector emb shell.tait.coloring

/-- Weaker and more lab-faithful non-geometric candidate repair lane: every exact shell admits
some explicit coloring family inside the shell Tait coloring's edge-Kempe closure that already
detects every nonzero selected-boundary-zero chain. -/
def AlgebraicNeighborhoodCancellationOracle : Prop :=
  ∀ {W : Type} [DecidableEq W] {G : SimpleGraph W} [Fintype G.edgeSet]
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (shell : ClosedWalkExactShell emb),
      ∃ colorings : Set (G.EdgeColoring Color),
        colorings ⊆ G.EdgeKempeClosure shell.tait.coloring ∧
          BoundaryZeroProjectedColoringGeneratorDetector emb colorings

/-- Direct kernel-check form of the same explicit-family repair lane: every exact shell admits an
explicit Kempe-neighborhood family whose concrete family-evaluation pairing map has trivial
kernel.  This matches the finite-lab certificate shape before upgrading it to the detector
surface. -/
def AlgebraicNeighborhoodPairingKernelOracle : Prop :=
  ∀ {W : Type} [DecidableEq W] {G : SimpleGraph W} [Fintype G.edgeSet]
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (shell : ClosedWalkExactShell emb),
      ∃ colorings : Set (G.EdgeColoring Color),
        colorings ⊆ G.EdgeKempeClosure shell.tait.coloring ∧
          ∃ κ : Type,
            ∃ family : κ → projectedColoringGeneratorSubspace emb colorings,
              LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) = ⊥

theorem theorem49ShellClaim_of_algebraicCancellationOracle
    (h : AlgebraicCancellationOracle) : Theorem49ShellClaim := by
  intro W _ G _ _ emb shell
  exact
    theorem49BoundaryRootSynthesis_of_boundaryZeroProjectedGeneratorDetector
      emb shell.tait.coloring (h emb shell)

theorem algebraicCancellationOracle_of_algebraicNeighborhoodCancellationOracle
    (h : AlgebraicNeighborhoodCancellationOracle) : AlgebraicCancellationOracle := by
  intro W _ G _ _ emb shell
  rcases h emb shell with ⟨colorings, hsubset, hdet⟩
  exact BoundaryZeroProjectedGeneratorDetector.of_coloringFamily hsubset hdet

theorem algebraicNeighborhoodCancellationOracle_of_algebraicNeighborhoodPairingKernelOracle
    (h : AlgebraicNeighborhoodPairingKernelOracle) :
    AlgebraicNeighborhoodCancellationOracle := by
  intro W _ G _ _ emb shell
  rcases h emb shell with ⟨colorings, hsubset, κ, family, hker⟩
  exact ⟨colorings, hsubset,
    detector_of_ker_planarBoundaryZeroFamilyPairingMap_eq_bot family hker⟩

theorem theorem49ShellClaim_of_algebraicNeighborhoodCancellationOracle
    (h : AlgebraicNeighborhoodCancellationOracle) : Theorem49ShellClaim :=
  theorem49ShellClaim_of_algebraicCancellationOracle
    (algebraicCancellationOracle_of_algebraicNeighborhoodCancellationOracle h)

theorem theorem49ShellClaim_of_algebraicNeighborhoodPairingKernelOracle
    (h : AlgebraicNeighborhoodPairingKernelOracle) : Theorem49ShellClaim :=
  theorem49ShellClaim_of_algebraicNeighborhoodCancellationOracle
    (algebraicNeighborhoodCancellationOracle_of_algebraicNeighborhoodPairingKernelOracle h)

end Mettapedia.GraphTheory.FourColor
