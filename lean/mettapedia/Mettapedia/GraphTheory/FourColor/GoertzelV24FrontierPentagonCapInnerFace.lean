import Mettapedia.GraphTheory.FourColor.GoertzelV24ComplementaryRegionBoundaryOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapDeletedBoundaryCycle
import Mettapedia.GraphTheory.FourColor.GoertzelV24FrontierPentagonCapOuterFace
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionBoundaryOrbit

/-!
# The inner face of Addendum V's frontier opening

The frontier tangle in Addendum V already has degree-one outer stubs, so the
closed-map hypotheses used by the earlier one-cap laboratory are false on the
source carrier: the ambient rotation is neither globally cubic nor globally
two-sided.  This module isolates the exact local replacement.

Only the five cap vertices must be cubic.  To compare the deleted and retained
first-return orders, each ambient facial orbit must meet the five retained cap
boundary darts at most once.  Under that finite collar condition, the computed
deleted-side pentagon cycle transfers to the retained boundary order, hence all
five fresh stubs lie on one literal opened face.  The old outer face remains
distinct from this inner face by the already-proved retained-face transport.

This is an L1 formation prerequisite, not the L1 crosscut construction.  In
particular, this file does not derive the finite collar condition from the
source-selected frontier tangle, select that tangle, or construct the two
separated crosscuts.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FrontierPentagonCapInnerFace

open SimpleGraph
open SimpleGraphDartRotation
open GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FacialPentagonCap
open GoertzelV24FacialPentagonCapDeletedBoundaryCycle
open GoertzelV24FacialPentagonCapOpenBoundary
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FrontierPentagonCapOpening
open GoertzelV24FrontierPentagonCapOuterFace
open GoertzelV24OpenRegionBoundaryOrbit
open GoertzelV24OpenRegionFaceTransport
open GoertzelV24OpenRegionGraphBacking
open GoertzelV24OpenRegionGraphFaceTransport
open GoertzelV24OpenRegionRotation
open GoertzelV24PentagonCapOpening
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RetainedRegionBoundaryOrder

attribute [-instance]
  GoertzelV24OpenRegionRotation.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

variable {data : Data G}

local instance openPrimalGraphDecidableRelLocal
    (data : Data G) (keep : V → Prop)
    (outer : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem keep) :
    DecidableRel (PrimalGraph data.toRotationSystem keep outer).Adj :=
  Classical.decRel _

/-- Exact local collar condition needed at the opened cap: no ambient facial
orbit contains two different retained-facing cap spokes.  This is strictly
local to the five named occurrences and does not assert global two-sidedness. -/
def CapBoundaryFacesUnique
    (walk : FacialPentagonCapBoundaryWalk data) : Prop :=
  ∀ first second : Fin 5,
    data.toRotationSystem.phi.SameCycle
      (PentagonCap.openBoundaryDart data
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap
        first).1.1
      (PentagonCap.openBoundaryDart data
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap
        second).1.1 →
    first = second

/-- The five-position condition is exactly strong enough to supply the generic
cut-face uniqueness predicate used by complementary boundary-order transport. -/
theorem cutFacesHaveUniqueRetainedBoundaryDart_of_capBoundaryFacesUnique
    (walk : FacialPentagonCapBoundaryWalk data)
    (hunique : CapBoundaryFacesUnique walk) :
    CutFacesHaveUniqueRetainedBoundaryDart data.toRotationSystem
      walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertexSupport := by
  intro left right hface
  obtain ⟨first, hleft⟩ := PentagonCap.exists_openBoundaryDart_eq data
    walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap left
  obtain ⟨second, hright⟩ := PentagonCap.exists_openBoundaryDart_eq data
    walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap right
  rw [hleft, hright] at hface ⊢
  exact congrArg
    (PentagonCap.openBoundaryDart data
      walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap)
    (hunique first second hface)

/-- Conversely, the generic cut-face predicate restricts to the five literal
cap coordinates.  Together with the preceding theorem, this shows that the
local condition is only the source-ordered presentation of the generic
boundary invariant, not an additional geometric assumption.  Neither
direction constructs that invariant on the source frontier. -/
theorem capBoundaryFacesUnique_of_cutFacesHaveUniqueRetainedBoundaryDart
    (walk : FacialPentagonCapBoundaryWalk data)
    (hunique : CutFacesHaveUniqueRetainedBoundaryDart data.toRotationSystem
      walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertexSupport) :
    CapBoundaryFacesUnique walk := by
  intro first second hface
  apply PentagonCap.openBoundaryDart_injective data
    walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap
  exact hunique
    (PentagonCap.openBoundaryDart data
      walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap first)
    (PentagonCap.openBoundaryDart data
      walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap second)
    hface

/-- The source-ordered five-position condition and the generic cut-face
uniqueness predicate are logically equivalent for a literal pentagon cap. -/
theorem capBoundaryFacesUnique_iff_cutFacesHaveUniqueRetainedBoundaryDart
    (walk : FacialPentagonCapBoundaryWalk data) :
    CapBoundaryFacesUnique walk ↔
      CutFacesHaveUniqueRetainedBoundaryDart data.toRotationSystem
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertexSupport :=
  ⟨cutFacesHaveUniqueRetainedBoundaryDart_of_capBoundaryFacesUnique walk,
    capBoundaryFacesUnique_of_cutFacesHaveUniqueRetainedBoundaryDart walk⟩

/-- Well-formed Addendum V frontier data supplies cubicity exactly at the five
interior cap vertices, while allowing the old outer stubs to remain degree one. -/
theorem capVerticesCubic_of_frontierWellFormed
    (frontier : FrontierBoundaryData G outerCount)
    (hfrontier : frontier.WellFormed)
    (walk : FacialPentagonCapBoundaryWalk data)
    (hinterior : frontier.InteriorPentagonCap
      walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap) :
    CapVerticesCubic walk := by
  intro step
  change ({dart : G.Dart |
    dart.fst =
      walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertex
        step} : Finset G.Dart).card = 3
  rw [G.dart_fst_fiber_card_eq_degree]
  rw [← GoertzelV24FramedBoundaryCounts.incidentEdgeFinset_card_eq_degree]
  exact hfrontier.cubic_elsewhere _
    (fun outer => hinterior.capVertex_ne_outerStub step outer)

/-- The literal opened face rooted at the first fresh cap stub. -/
def openingInnerFace
    (walk : FacialPentagonCapBoundaryWalk data)
    (outer : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (PentagonCap.keep
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap)) :
    OrbitFace (rotationSystem data.toRotationSystem
      (PentagonCap.keep
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap)
      outer) :=
  dartOrbitFace
    (rotationSystem data.toRotationSystem
      (PentagonCap.keep
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap)
      outer)
    (Sum.inr (PentagonCap.openBoundaryDart data
      walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap 0))

/-- **Addendum V inner-hole orbit.** Under the exact five-occurrence collar
condition, every fresh cap stub lies on the literal opened inner face.  The
proof compares the two first-return permutations and then invokes the computed
open-region face step; it uses no global cubicity or two-sidedness axiom. -/
theorem openingInnerFace_stub_eq
    (frontier : FrontierBoundaryData G outerCount)
    (hfrontier : frontier.WellFormed)
    (walk : FacialPentagonCapBoundaryWalk data)
    (hinterior : frontier.InteriorPentagonCap
      walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hunique : CapBoundaryFacesUnique walk)
    (outer : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (PentagonCap.keep
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap))
    (step : Fin 5) :
    openingInnerFace walk outer =
      dartOrbitFace
        (rotationSystem data.toRotationSystem
          (PentagonCap.keep
            walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap)
          outer)
        (Sum.inr (PentagonCap.openBoundaryDart data
          walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap
          step)) := by
  apply dartOrbitFace_stub_eq_of_boundarySuccessor_sameCycle
  change
    (retainedRegionBoundarySuccessor data.toRotationSystem
      (deletedRegionKeep
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertexSupport)).SameCycle
      (PentagonCap.openBoundaryDart data
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap 0)
      (PentagonCap.openBoundaryDart data
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap step)
  have horder :=
    retained_boundarySuccessor_eq_deleted_boundarySuccessor_inv_of_cutFacesUnique
      data.toRotationSystem
      walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertexSupport
      (cutFacesHaveUniqueRetainedBoundaryDart_of_capBoundaryFacesUnique
        walk hunique)
  rw [horder, Equiv.Perm.sameCycle_inv]
  exact deletedRegionBoundarySuccessor_openBoundary_sameCycle walk
    (capVerticesCubic_of_frontierWellFormed frontier hfrontier walk hinterior)
    hrotation 0 step

/-- The retained old outer face and the literal opened inner face are distinct.
This conclusion is independent of the collar-cycle hypothesis because the
inner face is rooted definitionally at a fresh stub. -/
theorem openingOuterFace_ne_openingInnerFace
    (walk : FacialPentagonCapBoundaryWalk data)
    (houterRetained : FaceFullyRetained data.toRotationSystem
      (PentagonCap.keep
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap)
      data.toRotationSystem.outer) :
    FrontierOuterFaceData.openingOuterFace
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap
        houterRetained ≠
      openingInnerFace walk
        (FrontierOuterFaceData.openingOuterRoot
          walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap
          houterRetained) :=
  FrontierOuterFaceData.openingOuterFace_ne_capStubFace
    walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap
    houterRetained 0

/-- The inner face transported to the simple-graph rotation carrier consumed
by the annular-cellulation API. -/
def openingGraphInnerFace
    (walk : FacialPentagonCapBoundaryWalk data)
    (houterRetained : FaceFullyRetained data.toRotationSystem
      (PentagonCap.keep
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap)
      data.toRotationSystem.outer) :
    OrbitFace
      (graphData data
        (PentagonCap.keep
          walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap)
        (FrontierOuterFaceData.openingOuterRoot
          walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap
          houterRetained)).toRotationSystem :=
  graphFaceEquiv data
    (PentagonCap.keep
      walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap)
    (FrontierOuterFaceData.openingOuterRoot
      walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap
      houterRetained)
    (openingInnerFace walk
      (FrontierOuterFaceData.openingOuterRoot
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap
        houterRetained))

/-- Under the local collar condition, every fresh cap stub names the same
inner face also on the graph-backed opened rotation. -/
theorem openingGraphInnerFace_stub_eq
    (frontier : FrontierBoundaryData G outerCount)
    (hfrontier : frontier.WellFormed)
    (walk : FacialPentagonCapBoundaryWalk data)
    (hinterior : frontier.InteriorPentagonCap
      walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hunique : CapBoundaryFacesUnique walk)
    (houterRetained : FaceFullyRetained data.toRotationSystem
      (PentagonCap.keep
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap)
      data.toRotationSystem.outer)
    (step : Fin 5) :
    openingGraphInnerFace walk houterRetained =
      dartOrbitFace
        (graphData data
          (PentagonCap.keep
            walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap)
          (FrontierOuterFaceData.openingOuterRoot
            walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap
            houterRetained)).toRotationSystem
        (primalDartEquiv data
          (PentagonCap.keep
            walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap)
          (FrontierOuterFaceData.openingOuterRoot
            walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap
            houterRetained)
          (Sum.inr (PentagonCap.openBoundaryDart data
            walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap
            step))) := by
  rw [← graphFaceEquiv_dartOrbitFace]
  exact congrArg
    (graphFaceEquiv data
      (PentagonCap.keep
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap)
      (FrontierOuterFaceData.openingOuterRoot
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap
        houterRetained))
    (openingInnerFace_stub_eq frontier hfrontier walk hinterior hrotation
      hunique
      (FrontierOuterFaceData.openingOuterRoot
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap
        houterRetained)
      step)

/-- The two source-named hole faces remain distinct on the graph-backed opened
rotation carrier. -/
theorem openingGraphOuterFace_ne_openingGraphInnerFace
    (walk : FacialPentagonCapBoundaryWalk data)
    (houterRetained : FaceFullyRetained data.toRotationSystem
      (PentagonCap.keep
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap)
      data.toRotationSystem.outer) :
    FrontierOuterFaceData.openingGraphOuterFace
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap
        houterRetained ≠
      openingGraphInnerFace walk houterRetained :=
  graphFaceEquiv_ne data
    (PentagonCap.keep
      walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap)
    (FrontierOuterFaceData.openingOuterRoot
      walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap
      houterRetained)
    (openingOuterFace_ne_openingInnerFace walk houterRetained)

end

end GoertzelV24FrontierPentagonCapInnerFace

end Mettapedia.GraphTheory.FourColor
