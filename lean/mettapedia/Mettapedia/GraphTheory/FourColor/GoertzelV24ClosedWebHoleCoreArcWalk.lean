import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebHoleBoundaryOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceArcWalk

/-!
# Core walks along the closed-web hole faces

A radial support path includes its degree-one boundary edge.  Therefore a
sector wall must not join two radial paths by the earlier closed edge arc,
which includes the same stub edges again.  The correct graph-level object is
the facial segment from just after the first stub dart to just before the
reverse dart at the second stub.  Its endpoints are the two neighbours of the
stubs, so it is ready to join the radial paths after their boundary edges are
trimmed.

This module constructs those actual face-ordered walks.  It does not yet claim
that the two complementary choices form simple Jordan walls; that requires
the subsequent disjointness argument.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebHoleCoreArcWalk

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebHoleBoundaryOrder
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open GoertzelV24OrbitFaceArcWalk
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

private theorem mem_faceOrbit_of_orbitFace_eq
    (graphData : Data G) (root target : G.Dart)
    (hface : dartOrbitFace graphData.toRotationSystem target =
      dartOrbitFace graphData.toRotationSystem root) :
    target ∈ graphData.toRotationSystem.faceOrbit root := by
  rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit
    graphData.toRotationSystem root]
  exact (mem_orbitFaceDarts_iff graphData.toRotationSystem
    (dartOrbitFace graphData.toRotationSystem root) target).2 hface

/-- Two darts known to lie on one named face determine the core facial walk
from the terminal vertex of the first dart to the terminal vertex of the
second.  The cut starts after `first` and stops before `alpha second`. -/
theorem exists_coreFaceArcWalk
    (graphData : Data G)
    (face : OrbitFace graphData.toRotationSystem)
    (first second : G.Dart)
    (hfirst : dartOrbitFace graphData.toRotationSystem first = face)
    (hsecondAlpha :
      dartOrbitFace graphData.toRotationSystem
        (graphData.toRotationSystem.alpha second) = face) :
    ∃ arc : G.Walk first.snd second.snd,
      (∀ dart ∈ arc.darts,
        dartOrbitFace graphData.toRotationSystem dart = face) ∧
      arc.length <
        (graphData.toRotationSystem.faceOrbit
          (graphData.toRotationSystem.phi first)).card := by
  let root := graphData.toRotationSystem.phi first
  let target := graphData.toRotationSystem.alpha second
  have hrootFace :
      dartOrbitFace graphData.toRotationSystem root = face := by
    exact (dartOrbitFace_phi_eq graphData.toRotationSystem first).trans hfirst
  have htargetOrbit : target ∈
      graphData.toRotationSystem.faceOrbit root :=
    mem_faceOrbit_of_orbitFace_eq graphData root target
      (hsecondAlpha.trans hrootFace.symm)
  rcases exists_faceArcWalk graphData root target htargetOrbit with
    ⟨raw, _hdarts, hlength, hrawFace⟩
  have hstart : root.fst = first.snd := by
    change (graphData.toRotationSystem.phi first).fst = first.snd
    simpa using (graphData.toRotationSystem.vert_phi_eq_vert_alpha first)
  have hfinish : target.fst = second.snd := by
    change (graphData.toRotationSystem.alpha second).fst = second.snd
    simp
  let arc : G.Walk first.snd second.snd := raw.copy hstart hfinish
  refine ⟨arc, ?_, ?_⟩
  · intro dart hdart
    have hdartRaw : dart ∈ raw.darts := by simpa [arc] using hdart
    have horbit := hrawFace dart hdartRaw
    rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit
      graphData.toRotationSystem root] at horbit
    exact (mem_orbitFaceDarts_iff graphData.toRotationSystem
      (dartOrbitFace graphData.toRotationSystem root) dart).1 horbit |>
        (fun h => h.trans hrootFace)
  · have hpositionLt :=
      (faceArcPosition graphData root target htargetOrbit).isLt
    have harcLength : arc.length = raw.length := by simp [arc]
    rw [harcLength]
    rw [hlength]
    exact hpositionLt

/-- The actual inner-hole segment between two ordered inner stubs, with the
stub spikes removed from its endpoints. -/
theorem exists_innerHoleCoreArcWalk
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) (first second : Fin 5) :
    ∃ arc : G.Walk
        (innerBoundaryDart data hdata first).snd
        (innerBoundaryDart data hdata second).snd,
      (∀ dart ∈ arc.darts,
        dartOrbitFace embedded.RS dart = embedded.cellulation.innerHole) ∧
      arc.length <
        (embedded.RS.faceOrbit
          (embedded.RS.phi (innerBoundaryDart data hdata first))).card := by
  let firstDart := innerBoundaryDart data hdata first
  let secondDart := innerBoundaryDart data hdata second
  have hfirst : dartOrbitFace embedded.RS firstDart =
      embedded.cellulation.innerHole :=
    innerBoundaryDart_on_innerHole embedded hdata first
  have hsecondOn : secondDart ∈
      embedded.RS.dartsOn (data.innerBoundaryEdge second) :=
    innerBoundaryDart_mem_dartsOn embedded hdata second
  have hsecondAlphaOn : embedded.RS.alpha secondDart ∈
      embedded.RS.dartsOn (data.innerBoundaryEdge second) :=
    embedded.RS.alpha_mem_dartsOn hsecondOn
  have hsecondAlpha :
      dartOrbitFace embedded.RS (embedded.RS.alpha secondDart) =
        embedded.cellulation.innerHole :=
    embedded.innerBoundaryEdgeDarts_on_innerHole second
      (embedded.RS.alpha secondDart) hsecondAlphaOn
  exact exists_coreFaceArcWalk embedded.cellulation.rotation
    embedded.cellulation.innerHole firstDart secondDart hfirst hsecondAlpha

/-- The corresponding actual outer-hole core segment. -/
theorem exists_outerHoleCoreArcWalk
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) (first second : Fin outerCount) :
    ∃ arc : G.Walk
        (outerBoundaryDart data hdata first).snd
        (outerBoundaryDart data hdata second).snd,
      (∀ dart ∈ arc.darts,
        dartOrbitFace embedded.RS dart = embedded.cellulation.outerHole) ∧
      arc.length <
        (embedded.RS.faceOrbit
          (embedded.RS.phi (outerBoundaryDart data hdata first))).card := by
  let firstDart := outerBoundaryDart data hdata first
  let secondDart := outerBoundaryDart data hdata second
  have hfirst : dartOrbitFace embedded.RS firstDart =
      embedded.cellulation.outerHole :=
    outerBoundaryDart_on_outerHole embedded hdata first
  have hsecondOn : secondDart ∈
      embedded.RS.dartsOn (data.outerBoundaryEdge second) :=
    outerBoundaryDart_mem_dartsOn embedded hdata second
  have hsecondAlphaOn : embedded.RS.alpha secondDart ∈
      embedded.RS.dartsOn (data.outerBoundaryEdge second) :=
    embedded.RS.alpha_mem_dartsOn hsecondOn
  have hsecondAlpha :
      dartOrbitFace embedded.RS (embedded.RS.alpha secondDart) =
        embedded.cellulation.outerHole :=
    embedded.outerBoundaryEdgeDarts_on_outerHole second
      (embedded.RS.alpha secondDart) hsecondAlphaOn
  exact exists_coreFaceArcWalk embedded.cellulation.rotation
    embedded.cellulation.outerHole firstDart secondDart hfirst hsecondAlpha

end

end GoertzelV24ClosedWebHoleCoreArcWalk

end Mettapedia.GraphTheory.FourColor
