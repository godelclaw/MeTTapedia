import Mettapedia.GraphTheory.FourColor.CAP5RoutePayoff

/-!
# Concrete CAP5 wheel route data

This module audits a concrete five-edge CAP5 boundary enumeration on the
wheel-with-inner-triangle benchmark.  The support data are exceptional, but the same boundary
already fails the primitive no-gap gate: one side-case would force the three triangle edges to
cross a single vertex side.
-/

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open Theorem49PlanarBoundaryAnnulusWheelWitnessRegression

namespace WheelCAP5RouteData

/-- A concrete five-edge CAP5 boundary enumeration on the wheel benchmark. -/
def wheelCAP5BoundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet
  | ⟨0, _⟩ => wit12
  | ⟨1, _⟩ => wit23
  | ⟨2, _⟩ => wit31
  | ⟨3, _⟩ => wit45
  | ⟨4, _⟩ => wit56

def wheelCAP5RedBlueEdge₁ : Finset wheelWithInnerTriangleGraph.edgeSet :=
  {wit12, wit45}

def wheelCAP5RedBlueEdge₂ : Finset wheelWithInnerTriangleGraph.edgeSet :=
  {wit23, wit31}

def wheelCAP5RedPurpleEdge₁ : Finset wheelWithInnerTriangleGraph.edgeSet :=
  {wit12, wit56}

def wheelCAP5RedPurpleEdge₂ : Finset wheelWithInnerTriangleGraph.edgeSet :=
  {wit23, wit45}

theorem wheelCAP5RedBlueEdge₁_support :
    cap5BoundarySupportOfEdges wheelCAP5BoundaryEdge wheelCAP5RedBlueEdge₁ =
      ({0, 3} : Finset (Fin 5)) := by
  ext i
  fin_cases i <;>
    simp [cap5BoundarySupportOfEdges, wheelCAP5BoundaryEdge, wheelCAP5RedBlueEdge₁,
      wit12, wit23, wit31, wit45, wit56]

theorem wheelCAP5RedBlueEdge₂_support :
    cap5BoundarySupportOfEdges wheelCAP5BoundaryEdge wheelCAP5RedBlueEdge₂ =
      ({1, 2} : Finset (Fin 5)) := by
  ext i
  fin_cases i <;>
    simp [cap5BoundarySupportOfEdges, wheelCAP5BoundaryEdge, wheelCAP5RedBlueEdge₂,
      wit12, wit23, wit31, wit45, wit56]

theorem wheelCAP5RedPurpleEdge₁_support :
    cap5BoundarySupportOfEdges wheelCAP5BoundaryEdge wheelCAP5RedPurpleEdge₁ =
      ({0, 4} : Finset (Fin 5)) := by
  ext i
  fin_cases i <;>
    simp [cap5BoundarySupportOfEdges, wheelCAP5BoundaryEdge, wheelCAP5RedPurpleEdge₁,
      wit12, wit23, wit31, wit45, wit56]

theorem wheelCAP5RedPurpleEdge₂_support :
    cap5BoundarySupportOfEdges wheelCAP5BoundaryEdge wheelCAP5RedPurpleEdge₂ =
      ({1, 3} : Finset (Fin 5)) := by
  ext i
  fin_cases i <;>
    simp [cap5BoundarySupportOfEdges, wheelCAP5BoundaryEdge, wheelCAP5RedPurpleEdge₂,
      wit12, wit23, wit31, wit45, wit56]

/-- The concrete exceptional component-cover core for the wheel CAP5 boundary enumeration. -/
def wheelCAP5ComponentCoverCore :
    CAP5TransportedEdgeComponentCoverCore wheelCAP5BoundaryEdge 0 where
  redBlueEdge₁ := wheelCAP5RedBlueEdge₁
  redBlueEdge₂ := wheelCAP5RedBlueEdge₂
  redPurpleEdge₁ := wheelCAP5RedPurpleEdge₁
  redPurpleEdge₂ := wheelCAP5RedPurpleEdge₂
  redBlue₁ := {0, 3}
  redBlue₂ := {1, 2}
  redPurple₁ := {0, 4}
  redPurple₂ := {1, 3}
  hredBlue₁ := by
    simpa [cap5RotateBoundarySupportN] using wheelCAP5RedBlueEdge₁_support
  hredBlue₂ := by
    simpa [cap5RotateBoundarySupportN] using wheelCAP5RedBlueEdge₂_support
  hredPurple₁ := by
    simpa [cap5RotateBoundarySupportN] using wheelCAP5RedPurpleEdge₁_support
  hredPurple₂ := by
    simpa [cap5RotateBoundarySupportN] using wheelCAP5RedPurpleEdge₂_support
  hredBlue := by
    rw [CAP5BadRedBlueComponentCover]
    refine ⟨by simp, by simp, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro i hi₁ hi₂
      fin_cases i <;> simp at hi₁ hi₂
    · ext i
      fin_cases i <;> simp
  hredPurple := by
    rw [CAP5BadRedPurpleComponentCover]
    refine ⟨by simp, by simp, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro i hi₁ hi₂
      fin_cases i <;> simp at hi₁ hi₂
    · ext i
      fin_cases i <;> simp

theorem wheelCAP5ComponentCoverCore_isExceptional :
    wheelCAP5ComponentCoverCore.IsExceptional := by
  change CAP5BadExceptionalPairingPattern
    ({0, 3} : Finset (Fin 5)) ({1, 2} : Finset (Fin 5))
      ({0, 4} : Finset (Fin 5)) ({1, 3} : Finset (Fin 5))
  rw [CAP5BadExceptionalPairingPattern, CAP5BadRedBlueExceptionalPairing,
    CAP5BadRedPurpleExceptionalPairing]
  exact ⟨Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩

/--
The benchmark has an explicit five-boundary CAP5 support core in the exceptional branch.
-/
theorem wheelCAP5_exceptional_componentCoverCore :
    ∃ (boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet) (n : Nat)
      (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n),
        data.IsExceptional :=
  ⟨wheelCAP5BoundaryEdge, 0, wheelCAP5ComponentCoverCore,
    wheelCAP5ComponentCoverCore_isExceptional⟩

/--
The concrete five-edge wheel boundary cannot enter the no-gap CAP5 route.  If the primitive
checker gap were absent, the `p0Inside/p4Outside` side case would force the three triangle edges
`wit12`, `wit23`, and `wit31` to cross the same vertex side, contradicting triangle parity.
-/
theorem wheelCAP5PrimitiveCheckerGap (side : Fin 7 → Prop) :
    CAP5PrimitiveCheckerGap wheelCAP5BoundaryEdge side := by
  by_contra hno
  let latent : CAP5ExceptionalAnnulusGeneratorLatent wheelCAP5BoundaryEdge :=
    { orientation := .redBlue03_redPurple04
      p0Inside := true
      p4Inside := false }
  have hportal :
      (CAP5ExceptionalAnnulusGeneratorReport.latentNode
        wheelCAP5BoundaryEdge side latent).PortalCrosses :=
    noGap_portalsCross_allLatents hno latent
  have h0 :
      EdgeCrossesVertexSide wheelWithInnerTriangleGraph side
        (wheelCAP5BoundaryEdge 0) := by
    apply hportal
    simp [CAP5ExceptionalAnnulusGeneratorReport.latentNode,
      CAP5ExceptionalAnnulusGeneratorNode.candidate,
      CAP5ExceptionalAnnulusGeneratorLatent.candidate,
      CAP5ExceptionalAnnulusGeneratorLatent.sideCase,
      CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofOrientationAndSideCase,
      CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofPortalCandidate,
      CAP5ExceptionalAnnulusSeparatorPortalCandidate.ofOrientationAndSideCase,
      CAP5ExceptionalAnnulusSideCase.ofPortalSides,
      CAP5ExceptionalAnnulusSideCase.separatorPortalSet, latent]
  have h1 :
      EdgeCrossesVertexSide wheelWithInnerTriangleGraph side
        (wheelCAP5BoundaryEdge 1) := by
    apply hportal
    simp [CAP5ExceptionalAnnulusGeneratorReport.latentNode,
      CAP5ExceptionalAnnulusGeneratorNode.candidate,
      CAP5ExceptionalAnnulusGeneratorLatent.candidate,
      CAP5ExceptionalAnnulusGeneratorLatent.sideCase,
      CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofOrientationAndSideCase,
      CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofPortalCandidate,
      CAP5ExceptionalAnnulusSeparatorPortalCandidate.ofOrientationAndSideCase,
      CAP5ExceptionalAnnulusSideCase.ofPortalSides,
      CAP5ExceptionalAnnulusSideCase.separatorPortalSet, latent]
  have h2 :
      EdgeCrossesVertexSide wheelWithInnerTriangleGraph side
        (wheelCAP5BoundaryEdge 2) := by
    apply hportal
    simp [CAP5ExceptionalAnnulusGeneratorReport.latentNode,
      CAP5ExceptionalAnnulusGeneratorNode.candidate,
      CAP5ExceptionalAnnulusGeneratorLatent.candidate,
      CAP5ExceptionalAnnulusGeneratorLatent.sideCase,
      CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofOrientationAndSideCase,
      CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofPortalCandidate,
      CAP5ExceptionalAnnulusSeparatorPortalCandidate.ofOrientationAndSideCase,
      CAP5ExceptionalAnnulusSideCase.ofPortalSides,
      CAP5ExceptionalAnnulusSideCase.separatorPortalSet, latent]
  have htriangle :=
    not_three_edgeCrossesVertexSide_triangle
      (G := wheelWithInnerTriangleGraph) (side := side)
      (a := (1 : Fin 7)) (b := (2 : Fin 7)) (c := (3 : Fin 7))
      (eab := wit12) (ebc := wit23) (eac := wit31)
      (by simp [wit12]) (by simp [wit23]) (by simp [wit31])
  exact htriangle
    ⟨by simpa [wheelCAP5BoundaryEdge] using h0,
      by simpa [wheelCAP5BoundaryEdge] using h1,
      by simpa [wheelCAP5BoundaryEdge] using h2⟩

/-- No finite no-gap input exists for the concrete five-edge wheel CAP5 core. -/
theorem not_wheelCAP5FiniteNoGapRouteInput
    {colorings : Set (wheelWithInnerTriangleGraph.EdgeColoring Color)}
    {p0Inside p4Inside : Bool} {side : Fin 7 → Prop}
    (input :
      CAP5FiniteNoGapRouteInput wheelCAP5ComponentCoverCore
        wheelWithInnerTriangleEmbedding wheelWithInnerTriangleTaitEdgeColoring
        colorings p0Inside p4Inside side) :
    False :=
  input.noPrimitiveGap (wheelCAP5PrimitiveCheckerGap side)

/-- No finite route-closed witness exists for the concrete five-edge wheel CAP5 core. -/
theorem not_nonempty_wheelCAP5FiniteRouteClosedWitness
    {colorings : Set (wheelWithInnerTriangleGraph.EdgeColoring Color)}
    {p0Inside p4Inside : Bool} {side : Fin 7 → Prop} :
    ¬ Nonempty
      (CAP5FiniteRouteClosedWitness wheelCAP5ComponentCoverCore
        wheelWithInnerTriangleEmbedding wheelWithInnerTriangleTaitEdgeColoring
        colorings p0Inside p4Inside side) := by
  rintro ⟨w⟩
  exact w.noPrimitiveGap (wheelCAP5PrimitiveCheckerGap side)

end WheelCAP5RouteData

end Mettapedia.GraphTheory.FourColor
