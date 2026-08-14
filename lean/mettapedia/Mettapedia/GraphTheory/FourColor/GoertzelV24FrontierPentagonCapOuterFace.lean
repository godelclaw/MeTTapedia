import Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapOpenBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24FrontierPentagonCapOpenRegionComparison
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionFaceTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionGraphFaceTransport

/-!
# The retained outer face of Addendum V's frontier opening

The frontier tangle `X` already has an outer boundary before its interior
pentagon is opened.  This module records that source datum at the rotation
level and transports the complete outer face through the literal one-cap
opening.  It also proves that the transported outer face cannot be the face
of any fresh cap stub.

This is one half of the two-hole geometry.  It does not prove that all five
fresh cap stubs share one inner face, establish Euler or connectedness, select
`X` from a minimal counterexample, or construct the L1 crosscuts.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FrontierPentagonCapOuterFace

open SimpleGraph
open SimpleGraphDartRotation
open GoertzelV24DeletedRegionSlitOpenRegionComparison
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCapOpenBoundary
open GoertzelV24FrontierPentagonCapOpening
open GoertzelV24OpenRegionFaceTransport
open GoertzelV24OpenRegionGraphBacking
open GoertzelV24OpenRegionGraphFaceTransport
open GoertzelV24OpenRegionRotation
open GoertzelV24PentagonCapOpening
open GoertzelV24RotationCutDartDecomposition

attribute [-instance]
  GoertzelV24OpenRegionRotation.retainedVertexFintype
  GoertzelV24OpenRegionRotation.retainedVertexDecidableEq
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

/-- Rotation-level meaning of the frontier's named outer interface: both
darts over every ordered outer edge lie on the face rooted at `data.outer`.
No annular conclusion is bundled into this one-boundary datum. -/
structure FrontierOuterFaceData
    (data : Data G) (frontier : FrontierBoundaryData G outerCount) : Prop where
  outerBoundaryEdgeDarts_on_outerFace :
    ∀ outer : Fin outerCount,
      ∀ dart ∈ data.toRotationSystem.dartsOn
        (frontier.outerBoundaryEdge outer),
        dartOrbitFace data.toRotationSystem dart =
          dartOrbitFace data.toRotationSystem data.toRotationSystem.outer

namespace FrontierOuterFaceData

variable {data : Data G} {frontier : FrontierBoundaryData G outerCount}
  (cap : PentagonCap G)
  (houterRetained : FaceFullyRetained data.toRotationSystem
    (PentagonCap.keep cap) data.toRotationSystem.outer)

local instance retainedVertexFintypeLocal :
    Fintype (RetainedVertex (PentagonCap.keep cap)) :=
  Fintype.ofFinite _

local instance retainedVertexDecidableEqLocal :
    DecidableEq (RetainedVertex (PentagonCap.keep cap)) :=
  Classical.decEq _

local instance openPrimalGraphDecidableRelLocal
    (outer : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (PentagonCap.keep cap)) :
    DecidableRel
      (PrimalGraph data.toRotationSystem (PentagonCap.keep cap) outer).Adj :=
  Classical.decRel _

/-- The old outer-face root, embedded as an old dart of the one-cap literal
opening. -/
def openingOuterRoot :
    GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (PentagonCap.keep cap) :=
  openFaceRoot data.toRotationSystem (PentagonCap.keep cap)
    data.toRotationSystem.outer houterRetained

/-- The literal-open face occupied by the completely retained old outer
face. -/
def openingOuterFace :
    OrbitFace (rotationSystem data.toRotationSystem
      (PentagonCap.keep cap) (openingOuterRoot cap houterRetained)) :=
  openFaceOrbit data.toRotationSystem (PentagonCap.keep cap)
    (openingOuterRoot cap houterRetained)
    data.toRotationSystem.outer houterRetained

/-- A dart over one of the frontier's named outer edges, regarded as a point
of the complete ambient outer-face cycle.  This is the first construction in
the module that uses the source's outer-boundary datum. -/
def ambientOuterBoundaryPoint
    (boundary : FrontierOuterFaceData data frontier)
    (outer : Fin outerCount)
    (dart : data.toRotationSystem.D)
    (hdart : dart ∈ data.toRotationSystem.dartsOn
      (frontier.outerBoundaryEdge outer)) :
    {point // data.toRotationSystem.phi.SameCycle
      data.toRotationSystem.outer point} :=
  ⟨dart, (Quotient.exact
    (boundary.outerBoundaryEdgeDarts_on_outerFace outer dart hdart)).symm⟩

/-- Every named outer-interface dart remains on the transported old outer
face after opening the interior cap. -/
theorem openingOuterFace_contains_outerBoundaryDart
    (boundary : FrontierOuterFaceData data frontier)
    (outer : Fin outerCount)
    (dart : data.toRotationSystem.D)
    (hdart : dart ∈ data.toRotationSystem.dartsOn
      (frontier.outerBoundaryEdge outer)) :
    dartOrbitFace
        (rotationSystem data.toRotationSystem (PentagonCap.keep cap)
          (openingOuterRoot cap houterRetained))
        (openFaceDart data.toRotationSystem (PentagonCap.keep cap)
          data.toRotationSystem.outer houterRetained
          (ambientOuterBoundaryPoint boundary outer dart hdart)) =
      openingOuterFace cap houterRetained := by
  apply Quotient.sound
  exact (openFaceCycleMap data.toRotationSystem (PentagonCap.keep cap)
    (openingOuterRoot cap houterRetained) data.toRotationSystem.outer
    houterRetained (ambientOuterBoundaryPoint boundary outer dart hdart)).2.symm

/-- A fully retained old face contains no fresh boundary stub.  This is a
generic consequence of the exact cycle equivalence: every dart on the old
face image is an old tagged dart. -/
theorem openingOuterFace_ne_stubFace
    (stub : BoundaryDart data.toRotationSystem (PentagonCap.keep cap)) :
    openingOuterFace cap houterRetained ≠
      dartOrbitFace
        (rotationSystem data.toRotationSystem (PentagonCap.keep cap)
          (openingOuterRoot cap houterRetained))
        (Sum.inr stub) := by
  intro hfaces
  have hcycle :
      (rotationSystem data.toRotationSystem (PentagonCap.keep cap)
        (openingOuterRoot cap houterRetained)).phi.SameCycle
          (openFaceRoot data.toRotationSystem (PentagonCap.keep cap)
            data.toRotationSystem.outer houterRetained)
          (Sum.inr stub) := by
    exact Quotient.exact hfaces
  let target : {point //
      (rotationSystem data.toRotationSystem (PentagonCap.keep cap)
        (openingOuterRoot cap houterRetained)).phi.SameCycle
          (openFaceRoot data.toRotationSystem (PentagonCap.keep cap)
            data.toRotationSystem.outer houterRetained) point} :=
    ⟨Sum.inr stub, hcycle⟩
  rcases (openFaceCycleEquiv data.toRotationSystem (PentagonCap.keep cap)
      (openingOuterRoot cap houterRetained)
      data.toRotationSystem.outer houterRetained).surjective target with
    ⟨source, hsource⟩
  have himpossible :
      openFaceDart data.toRotationSystem (PentagonCap.keep cap)
          data.toRotationSystem.outer houterRetained source =
        (Sum.inr stub : GoertzelV24OpenRegionRotation.Dart
          data.toRotationSystem (PentagonCap.keep cap)) :=
    congrArg Subtype.val hsource
  change Sum.inl _ = Sum.inr _ at himpossible
  exact (Sum.inl_ne_inr himpossible).elim

/-- In particular, the retained old outer face is distinct from every face
rooted at one of the five fresh cap stubs. -/
theorem openingOuterFace_ne_capStubFace (step : Fin 5) :
    openingOuterFace cap houterRetained ≠
      dartOrbitFace
        (rotationSystem data.toRotationSystem (PentagonCap.keep cap)
          (openingOuterRoot cap houterRetained))
        (Sum.inr (PentagonCap.openBoundaryDart data cap step)) :=
  openingOuterFace_ne_stubFace cap houterRetained
    (PentagonCap.openBoundaryDart data cap step)

/-- The old outer face transported to the simple-graph backing used by the
annular cellulation API. -/
def openingGraphOuterFace :
    OrbitFace
      (graphData data (PentagonCap.keep cap)
        (openingOuterRoot cap houterRetained)).toRotationSystem :=
  graphFaceEquiv data (PentagonCap.keep cap)
    (openingOuterRoot cap houterRetained)
    (openingOuterFace cap houterRetained)

/-- The distinguished dart of the graph-backed opened rotation lies on the
transported old outer face by construction. -/
theorem graphData_outer_on_openingGraphOuterFace :
    dartOrbitFace
        (graphData data (PentagonCap.keep cap)
          (openingOuterRoot cap houterRetained)).toRotationSystem
        (graphData data (PentagonCap.keep cap)
          (openingOuterRoot cap houterRetained)).toRotationSystem.outer =
      openingGraphOuterFace cap houterRetained := by
  rfl

/-- The same source-specific containment statement on the simple-graph
rotation carrier consumed by the annular cellulation API. -/
theorem openingGraphOuterFace_contains_outerBoundaryDart
    (boundary : FrontierOuterFaceData data frontier)
    (outer : Fin outerCount)
    (dart : data.toRotationSystem.D)
    (hdart : dart ∈ data.toRotationSystem.dartsOn
      (frontier.outerBoundaryEdge outer)) :
    dartOrbitFace
        (graphData data (PentagonCap.keep cap)
          (openingOuterRoot cap houterRetained)).toRotationSystem
        (primalDartEquiv data (PentagonCap.keep cap)
          (openingOuterRoot cap houterRetained)
          (openFaceDart data.toRotationSystem (PentagonCap.keep cap)
            data.toRotationSystem.outer houterRetained
            (ambientOuterBoundaryPoint boundary outer dart hdart))) =
      openingGraphOuterFace cap houterRetained := by
  change
    graphFaceEquiv data (PentagonCap.keep cap)
        (openingOuterRoot cap houterRetained)
        (dartOrbitFace
          (rotationSystem data.toRotationSystem (PentagonCap.keep cap)
            (openingOuterRoot cap houterRetained))
          (openFaceDart data.toRotationSystem (PentagonCap.keep cap)
            data.toRotationSystem.outer houterRetained
            (ambientOuterBoundaryPoint boundary outer dart hdart))) =
      graphFaceEquiv data (PentagonCap.keep cap)
        (openingOuterRoot cap houterRetained)
        (openingOuterFace cap houterRetained)
  exact congrArg (graphFaceEquiv data (PentagonCap.keep cap)
      (openingOuterRoot cap houterRetained))
    (openingOuterFace_contains_outerBoundaryDart cap houterRetained
      boundary outer dart hdart)

/-- The graph-backed outer face remains distinct from the graph-backed face
of each fresh cap stub. -/
theorem openingGraphOuterFace_ne_capStubFace (step : Fin 5) :
    openingGraphOuterFace cap houterRetained ≠
      dartOrbitFace
        (graphData data (PentagonCap.keep cap)
          (openingOuterRoot cap houterRetained)).toRotationSystem
        (primalDartEquiv data (PentagonCap.keep cap)
          (openingOuterRoot cap houterRetained)
          (Sum.inr (PentagonCap.openBoundaryDart data cap step))) := by
  exact graphFaceEquiv_ne data (PentagonCap.keep cap)
    (openingOuterRoot cap houterRetained)
    (openingOuterFace_ne_capStubFace cap houterRetained step)

end FrontierOuterFaceData

end

end GoertzelV24FrontierPentagonCapOuterFace

end Mettapedia.GraphTheory.FourColor
