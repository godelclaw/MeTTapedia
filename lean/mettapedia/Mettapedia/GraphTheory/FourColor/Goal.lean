import Mettapedia.GraphTheory.FourColor.ShellsCore
import Mettapedia.GraphTheory.FourColor.Theorem49ClosedWalkShellSynthesis
import Mettapedia.GraphTheory.FourColor.Theorem49ResidualBoundaryPositiveGeometry

/-!
# The goal of the FourColor development

This file states what the development is actually for, in dependency order,
so that the target is visible without reading the route files.

## Context (informal)

By Tait's classical reduction, the Four Color Theorem is equivalent to: every
bridgeless cubic planar graph admits a proper 3-edge-coloring
(`IsTaitEdgeColoring`).  Goertzel's manuscript route attacks this through an
inductive boundary argument: Theorem 4.9 of the v23 manuscript claims an
algebraic synthesis (`Theorem49BoundaryRootSynthesis`) — Kirchhoff boundary
algebra spanned by projected Kempe-closure generators — for plane embeddings
with boundary carrying suitable source data.  Tait's reduction itself is not
formalized in this development; the formal work targets the manuscript's
Theorem 4.9 layer, where the audit located the load-bearing gap.

## What this file proves

`Theorem49ShellClaim` is the manuscript-shaped target: synthesis on every
embedding carrying the bundled exact shell.  It follows from any of four
uniform geometric oracles (previous-boundary witness geometry, well-founded
peel-witness data, interior-dual distance-peel data, or the v23.5
residual/current-boundary positive wrapper), or from non-geometric algebraic
cancellation oracles stated either in the projected-generator detector form
or in the more certificate-faithful direct kernel-check form exposed by the
finite lab (see `GoalAlgebraic`).  The four geometric oracles are all provably false, by the
benchmark embeddings that inhabit the shell while refuting the geometry.  The
fourth refutation is the formal answer to the v23.5 revision memo: the
residual lane's current positive wrapper is fixed-embedding equivalent to the
collar-layer surface
(`theorem49ResidualBoundaryPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn`),
so it inherits the same benchmark refutation; the proposed repair is
conservative, not a workaround.  So the manuscript route survives only if
either real same-embedding geometry, strictly stronger than everything the
exact shell supplies, is constructed from hypotheses the benchmarks do not
satisfy; or a genuinely non-geometric shell-wise algebraic cancellation
certificate is built uniformly from the exact shell; or `Theorem49ShellClaim`
itself is refuted on a shell-bearing embedding.  See `ROADMAP.md`.
-/

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Tait colorability: the edge-coloring form of the Four Color Theorem for a
single graph.  By Tait's reduction (not formalized here), the Four Color
Theorem is equivalent to `TaitColorable G` for every bridgeless cubic planar
`G`. -/
def TaitColorable (G : SimpleGraph V) : Prop :=
  ∃ C : G.EdgeColoring Color, IsTaitEdgeColoring G C

/-- The manuscript-shaped Theorem 4.9 target: the boundary-root synthesis on
every plane embedding with boundary that carries the exact closed-walk shell,
for the shell's own Tait coloring. -/
def Theorem49ShellClaim : Prop :=
  ∀ {W : Type} [DecidableEq W] {G : SimpleGraph W} [Fintype G.edgeSet]
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (shell : ClosedWalkExactShell emb),
      Theorem49BoundaryRootSynthesis emb shell.tait.coloring

/-- Uniform oracle: every shell-bearing embedding admits repaired
previous-boundary witness geometry. -/
def PreviousBoundaryGeometryOracle : Prop :=
  ∀ {W : Type} [DecidableEq W] {G : SimpleGraph W}
    (emb : PlaneEmbeddingWithBoundary G), Nonempty (ClosedWalkExactShell emb) →
      Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)

/-- Uniform oracle: every shell-bearing embedding admits explicit well-founded
face-peel witness data. -/
def WellFoundedPeelOracle : Prop :=
  ∀ {W : Type} [DecidableEq W] {G : SimpleGraph W}
    (emb : PlaneEmbeddingWithBoundary G), Nonempty (ClosedWalkExactShell emb) →
      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb)

/-- Uniform oracle: every shell-bearing embedding admits generic interior-dual
boundary-root distance-peel data. -/
def InteriorDualPeelOracle : Prop :=
  ∀ {W : Type} [DecidableEq W] {G : SimpleGraph W}
    (emb : PlaneEmbeddingWithBoundary G), Nonempty (ClosedWalkExactShell emb) →
      Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)

/-- Uniform oracle form of the v23.5 residual/current-boundary repair lane:
every shell-bearing embedding admits the residual positive wrapper. -/
def ResidualBoundaryGeometryOracle : Prop :=
  ∀ {W : Type} [DecidableEq W] {G : SimpleGraph W}
    (emb : PlaneEmbeddingWithBoundary G), Nonempty (ClosedWalkExactShell emb) →
      Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb

/-! ## The claim follows from any uniform oracle -/

theorem theorem49ShellClaim_of_previousBoundaryGeometryOracle
    (h : PreviousBoundaryGeometryOracle) : Theorem49ShellClaim := by
  intro W _ G _ _ emb shell
  obtain ⟨geometry⟩ := h emb ⟨shell⟩
  exact
    theorem49LiveBoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint
      shell.source geometry shell.endpoint shell.tait.coloring shell.tait.isTait

theorem theorem49ShellClaim_of_wellFoundedPeelOracle
    (h : WellFoundedPeelOracle) : Theorem49ShellClaim := by
  intro W _ G _ _ emb shell
  obtain ⟨data⟩ := h emb ⟨shell⟩
  exact
    theorem49LiveBoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      shell.source data shell.endpoint shell.tait.coloring shell.tait.isTait

theorem theorem49ShellClaim_of_interiorDualPeelOracle
    (h : InteriorDualPeelOracle) : Theorem49ShellClaim := by
  intro W _ G _ _ emb shell
  obtain ⟨peel⟩ := h emb ⟨shell⟩
  exact
    theorem49LiveBoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      shell.source
      (closedWalkShellWellFoundedFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
        shell.source peel)
      shell.endpoint shell.tait.coloring shell.tait.isTait

theorem theorem49ShellClaim_of_residualBoundaryGeometryOracle
    (h : ResidualBoundaryGeometryOracle) : Theorem49ShellClaim := by
  intro W _ G _ _ emb shell
  exact
    theorem49BoundaryRootSynthesis_of_residualBoundaryPositiveProjectedGeometryOn
      (h emb ⟨shell⟩) shell.tait.coloring shell.tait.isTait

end Mettapedia.GraphTheory.FourColor
