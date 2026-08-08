import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebRadialPathChords
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebAnnularEmbedding
import Mettapedia.GraphTheory.FourColor.GoertzelV24LocalFaceCutCycleWalkTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphFaceDualConnectedness

/-!
# Oriented face-side transport around a closed-web chord cycle

Every edge endpoint of a same-path chord cycle lies strictly inside the
annular tangle and is therefore locally cubic.  Combining that fact with the
simple-cycle exhaustion lemma lets the exact-cut label propagate along the
selected oriented side of the whole chord-cycle dart chain.

This is still a transport theorem, not Sector Alternation: it identifies no
second chord and assumes no pairwise noncrossing property.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebChordCycleFaceSideTransport

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialPathChords
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedBoundaryCounts
open GoertzelV24SimpleGraphFaceDualConnectedness
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

local instance chordCycleFaceSideGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The exact cut of a same-path chord cycle carries one constant label along
the cycle's oriented dart side.  Local cubicity is derived from annular
well-formedness at the actual cycle vertices. -/
theorem labels_eq_firstDart_lastDart_of_exact_chordCycle_cut
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    {A : Type*} (labels : OrbitFace embedded.RS → A)
    (hexact : ∀ dart : embedded.RS.D,
      labels (dartOrbitFace embedded.RS dart) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha dart)) ↔
        (embedded.RS.edgeOf dart).1 ∈ chord.cycleWalk.edges) :
    labels (dartOrbitFace embedded.RS
        (chord.cycleWalk.firstDart
          (chord.cycleWalk_isCycle htriple).not_nil)) =
      labels (dartOrbitFace embedded.RS
        (chord.cycleWalk.lastDart
          (chord.cycleWalk_isCycle htriple).not_nil)) := by
  have hcycle : chord.cycleWalk.IsCycle :=
    chord.cycleWalk_isCycle htriple
  have hrotation : VertexRotationCyclic embedded.RS :=
    hasCyclicVertexRotations_implies_vertexRotationCyclic
      G embedded.cellulation.rotation
        embedded.cellulation.vertexRotation_cyclic
  apply embedded.cellulation.rotation
    |>.cycle_labels_eq_firstDart_lastDart_of_local_cubic
      hrotation labels chord.cycleWalk hcycle hexact
  intro dart hdart
  have hedge : dart.edge ∈ chord.cycleWalk.edges :=
    List.mem_map_of_mem hdart
  have hvertex : dart.fst ∈ (dart.edge : Sym2 V) := by
    simp [SimpleGraph.Dart.edge]
  have hincident :=
    chord.cycleWalk_edge_endpoint_incidentEdgeFinset_card_eq_three
      hdata htriple ⟨dart.edge, dart.edge_mem⟩ hedge hvertex
  change ({candidate : G.Dart | candidate.fst = dart.fst} :
    Finset G.Dart).card = 3
  rw [G.dart_fst_fiber_card_eq_degree]
  rw [← incidentEdgeFinset_card_eq_degree]
  exact hincident

end

end GoertzelV24ClosedWebChordCycleFaceSideTransport

end Mettapedia.GraphTheory.FourColor
