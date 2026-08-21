import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationSystemPrimalGraphBacking

/-!
# Facial-orbit transport to the computed primal graph

The reductive splice first returns an abstract rotation system.  Once endpoint
simplicity graph-backs that rotation, its literal dart equivalence also
identifies the two facial-orbit quotients.  This file constructs that
equivalence and specializes it to an ordered cut.

This is representation transport.  It neither proves the ordered cut's
endpoint simplicity nor constructs or selects either named annular hole.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationSystemPrimalFaceTransport

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24RetainedSpliceEdgeDecomposition
open GoertzelV24RotationSystemPrimalGraphBacking
open GoertzelV24RotationSystemPrimalEdgePresentation.OrderedCutSpliceData
open GoertzelV24SpliceUnification

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

attribute [-instance] GoertzelV24SeamFaceArcPartition.hitPointFintype

local instance rotationPrimalGraphAdjDecidable (RS : RotationSystem V E) :
    DecidableRel (rotationPrimalGraph RS).Adj :=
  Classical.decRel _

local instance rotationPrimalGraphEdgeDecidableEq (RS : RotationSystem V E) :
    DecidableEq (rotationPrimalGraph RS).edgeSet :=
  Subtype.instDecidableEq

/-- Facial permutation on the computed primal graph is conjugate to the
literal facial permutation. -/
theorem graphData_phi_eq_permCongr (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints) :
    (graphData RS hinjective).toRotationSystem.phi =
      (primalDartEquiv RS hinjective).permCongr RS.phi := by
  apply Equiv.ext
  intro dart
  change (graphData RS hinjective).vertexRotation dart.symm =
    primalDartEquiv RS hinjective
      (RS.phi ((primalDartEquiv RS hinjective).symm dart))
  convert (primalDartEquiv_phi RS hinjective
    ((primalDartEquiv RS hinjective).symm dart)).symm using 1
  simp

/-- Facial orbits of an endpoint-simple rotation system are canonically the
facial orbits of its graph-backed presentation. -/
def graphFaceEquiv (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints) :
    OrbitFace RS ≃ OrbitFace (graphData RS hinjective).toRotationSystem :=
  Quotient.congr (primalDartEquiv RS hinjective) (fun first second => by
    rw [graphData_phi_eq_permCongr RS hinjective]
    exact (permCongr_sameCycle_iff (primalDartEquiv RS hinjective)
      RS.phi first second).symm)

@[simp] theorem graphFaceEquiv_dartOrbitFace (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints) (dart : RS.D) :
    graphFaceEquiv RS hinjective (dartOrbitFace RS dart) =
      dartOrbitFace (graphData RS hinjective).toRotationSystem
        (primalDartEquiv RS hinjective dart) := by
  rfl

namespace OrderedCutSpliceData

variable {RS : RotationSystem V E}
  {n terminalCount faceFragmentCount : Nat}

/-- The ordered-cut output's literal faces and graph-backed faces coincide
once the ambient rotation and the new seam endpoints are simple. -/
def outputGraphFaceEquiv
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (hambient : Function.Injective RS.endpoints)
    (hsimple : OrderedCutEndpointSimple RS data.keep
      data.left.crossingEdge data.right.crossingEdge
      data.leftCrosses data.rightCrosses) :
    OrbitFace data.output ≃
      OrbitFace
        (GoertzelV24RotationSystemPrimalGraphBacking.OrderedCutSpliceData.outputGraphData
          data hambient hsimple).toRotationSystem :=
  graphFaceEquiv data.output
    (output_endpoints_injective data hambient hsimple)

end OrderedCutSpliceData

end

end GoertzelV24RotationSystemPrimalFaceTransport

end Mettapedia.GraphTheory.FourColor
