import Mettapedia.GraphTheory.FourColor.TubeNodes

/-!
# The width-five zigzag tube exclusion is executable

The generic embedded-tube exclusion previously carried a finite
stabilisation test as a hypothesis.  For the actual five-port zigzag ring,
the test is true by a kernel-replayed computation.  Consequently a
vertex-minimal counterexample cannot contain an arbitrarily long coherent
embedded width-five zigzag tube satisfying the literal side hypotheses.

This is a conditional *physical* corridor theorem, not a statement that
every large counterexample supplies such a tube.
-/

namespace Mettapedia.GraphTheory.FourColor.GoertzelV24FiveTubeExclusion

open TubeRingOrbit TubeSlab
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24ConnectedEdgeShoreMajority
open SimpleGraphDartRotation

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- All five-port colour words stabilize under the literal zigzag ring
after four steps. The computation includes *all* proper local colourings,
not just those with four fully routed tracked strands. -/
theorem five_ring_stabilizes : stabilizes 5 = true := by
  decide +kernel

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- A genuine embedded five-port zigzag tube of excessive length cannot
occur in a graph-backed vertex-minimal Tait counterexample. This consumes
the checked finite stabilisation fact in the existing physical side and
strict-replacement theorem. -/
theorem embedded_five_tube_length_bound
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {inner : V → Prop} {n : Nat}
    (tube : Tube rotation.toRotationSystem 5 inner n)
    (hcoherent : tube.Coherent)
    (hgood : GoodSide (G := G) inner)
    (hinside : EdgeShoreConnected G (sideShore inner))
    (houtside : EdgeShoreConnected G (ZigzagSlab.compShore (tube.side n))) :
    n ≤ 446403 := by
  have h := Tube.le_of_tube (rotation := rotation) minimal
    five_ring_stabilizes (by omega) tube hcoherent hgood hinside houtside
  norm_num at h
  omega

end Mettapedia.GraphTheory.FourColor.GoertzelV24FiveTubeExclusion
