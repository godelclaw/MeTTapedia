import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoverySmallCycle
import Mettapedia.GraphTheory.FourColor.GoertzelV24SharedFacesThreeEdgeSeparator

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24SharedFacesThreeEdgeSeparator
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace ClosureRecoveryFaceCircuit

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- Explicit two-arc normal form for a recovery circuit. -/
def IsDigon (circuit : ClosureRecoveryFaceCircuit rebaseCircuit) : Prop :=
  ∃ second : ClosureRecoveryFaceArc rebaseCircuit,
    circuit.rest = [second] ∧
      ClosureRecoveryFaceArc.Follows circuit.first second ∧
      ClosureRecoveryFaceArc.Follows second circuit.first

/-- Explicit three-arc normal form for a recovery circuit. -/
def IsTriangle (circuit : ClosureRecoveryFaceCircuit rebaseCircuit) : Prop :=
  ∃ second third : ClosureRecoveryFaceArc rebaseCircuit,
    circuit.rest = [second, third] ∧
      ClosureRecoveryFaceArc.Follows circuit.first second ∧
      ClosureRecoveryFaceArc.Follows second third ∧
      ClosureRecoveryFaceArc.Follows third circuit.first

/-- A shortest recovery circuit has one of the two explicit small-cycle
normal forms. -/
theorem IsLengthMinimal.isDigon_or_isTriangle
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    circuit.IsDigon ∨ circuit.IsTriangle := by
  rcases hminimal.arcLength_eq_two_or_three with hlength | hlength
  · cases hrest : circuit.rest with
    | nil => exact False.elim (circuit.rest_ne_nil hrest)
    | cons second tail =>
        cases htail : tail with
        | nil =>
            left
            refine ⟨second, by simp [hrest, htail], ?_, ?_⟩
            · simpa [hrest, htail] using circuit.consecutive
            · simpa [hrest, htail] using circuit.closing
        | cons third more =>
            have hthree : 3 ≤ circuit.arcLength := by
              simp [arcLength, hrest, htail]
            omega
  · cases hrest : circuit.rest with
    | nil => exact False.elim (circuit.rest_ne_nil hrest)
    | cons second tail =>
        cases htail : tail with
        | nil =>
            have htwo : circuit.arcLength = 2 := by
              simp [arcLength, hrest, htail]
            omega
        | cons third final =>
            cases hfinal : final with
            | nil =>
                right
                have hchain := circuit.consecutive
                rw [hrest, htail, hfinal] at hchain
                refine ⟨second, third, by simp [hrest, htail, hfinal],
                  (List.isChain_cons_cons.mp hchain).1, ?_, ?_⟩
                · simpa using (List.isChain_cons_cons.mp hchain).2
                · simpa [hrest, htail, hfinal] using circuit.closing
            | cons fourth more =>
                have hfour : 4 ≤ circuit.arcLength := by
                  simp [arcLength, hrest, htail, hfinal]
                omega

/-- The three source faces and three support edges in a recovery triangle
are pairwise distinct in cyclic order. -/
theorem IsTriangle.sourceFaces_and_edges_pairwise_ne
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (htriangle : circuit.IsTriangle) :
    ∃ second third : ClosureRecoveryFaceArc rebaseCircuit,
      circuit.rest = [second, third] ∧
      circuit.first.sourceFace ≠ second.sourceFace ∧
      second.sourceFace ≠ third.sourceFace ∧
      third.sourceFace ≠ circuit.first.sourceFace ∧
      circuit.first.edge ≠ second.edge ∧
      second.edge ≠ third.edge ∧
      third.edge ≠ circuit.first.edge := by
  rcases htriangle with
    ⟨second, third, hrest, hfirstSecond, hsecondThird, hthirdFirst⟩
  have hfirstSecondFace :
      circuit.first.sourceFace ≠ second.sourceFace := by
    intro hface
    exact circuit.first.targetFace_ne_sourceFace
      (hfirstSecond.trans hface.symm)
  have hsecondThirdFace : second.sourceFace ≠ third.sourceFace := by
    intro hface
    exact second.targetFace_ne_sourceFace
      (hsecondThird.trans hface.symm)
  have hthirdFirstFace :
      third.sourceFace ≠ circuit.first.sourceFace := by
    intro hface
    exact third.targetFace_ne_sourceFace
      (hthirdFirst.trans hface.symm)
  exact ⟨second, third, hrest, hfirstSecondFace, hsecondThirdFace,
    hthirdFirstFace, hfirstSecond.edge_ne, hsecondThird.edge_ne,
    hthirdFirst.edge_ne⟩

/-- In a shortest recovery triangle, every support edge is incident to
the two source faces opposite its own source. -/
theorem IsLengthMinimal.exists_triangle_support
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal)
    (htriangle : circuit.IsTriangle) :
    ∃ second third : ClosureRecoveryFaceArc rebaseCircuit,
      circuit.rest = [second, third] ∧
      circuit.first.sourceFace ≠ second.sourceFace ∧
      second.sourceFace ≠ third.sourceFace ∧
      third.sourceFace ≠ circuit.first.sourceFace ∧
      circuit.first.edge ≠ second.edge ∧
      second.edge ≠ third.edge ∧
      third.edge ≠ circuit.first.edge ∧
      circuit.first.edge ∈ orbitFaceBoundary graphData.toRotationSystem
        second.sourceFace ∧
      circuit.first.edge ∈ orbitFaceBoundary graphData.toRotationSystem
        third.sourceFace ∧
      second.edge ∈ orbitFaceBoundary graphData.toRotationSystem
        third.sourceFace ∧
      second.edge ∈ orbitFaceBoundary graphData.toRotationSystem
        circuit.first.sourceFace ∧
      third.edge ∈ orbitFaceBoundary graphData.toRotationSystem
        circuit.first.sourceFace ∧
      third.edge ∈ orbitFaceBoundary graphData.toRotationSystem
        second.sourceFace := by
  rcases htriangle with
    ⟨second, third, hrest, hfirstSecond, hsecondThird, hthirdFirst⟩
  have hfirstSecondFace :
      circuit.first.sourceFace ≠ second.sourceFace := by
    intro hface
    exact circuit.first.targetFace_ne_sourceFace
      (hfirstSecond.trans hface.symm)
  have hsecondThirdFace : second.sourceFace ≠ third.sourceFace := by
    intro hface
    exact second.targetFace_ne_sourceFace
      (hsecondThird.trans hface.symm)
  have hthirdFirstFace :
      third.sourceFace ≠ circuit.first.sourceFace := by
    intro hface
    exact third.targetFace_ne_sourceFace
      (hthirdFirst.trans hface.symm)
  have hfirstEdgeSecond : circuit.first.edge ∈
      orbitFaceBoundary graphData.toRotationSystem second.sourceFace := by
    rw [← hfirstSecond]
    exact circuit.first.edge_mem_targetFace
  have hfirstEdgeThird : circuit.first.edge ∈
      orbitFaceBoundary graphData.toRotationSystem third.sourceFace := by
    rcases hminimal.sourceArc_eq_anchor_or_anchorEdge_mem_sourceFace
        circuit.first third (by simp [hrest]) (by simp [hrest]) with
      heq | hmem
    · exact False.elim
        (hthirdFirstFace (congrArg ClosureRecoveryFaceArc.sourceFace heq))
    · exact hmem
  have hsecondEdgeThird : second.edge ∈
      orbitFaceBoundary graphData.toRotationSystem third.sourceFace := by
    rw [← hsecondThird]
    exact second.edge_mem_targetFace
  have hsecondEdgeFirst : second.edge ∈
      orbitFaceBoundary graphData.toRotationSystem
        circuit.first.sourceFace := by
    rcases hminimal.sourceArc_eq_anchor_or_anchorEdge_mem_sourceFace
        second circuit.first (by simp [hrest]) (by simp [hrest]) with
      heq | hmem
    · exact False.elim
        (hfirstSecondFace (congrArg ClosureRecoveryFaceArc.sourceFace heq))
    · exact hmem
  have hthirdEdgeFirst : third.edge ∈
      orbitFaceBoundary graphData.toRotationSystem
        circuit.first.sourceFace := by
    rw [← hthirdFirst]
    exact third.edge_mem_targetFace
  have hthirdEdgeSecond : third.edge ∈
      orbitFaceBoundary graphData.toRotationSystem second.sourceFace := by
    rcases hminimal.sourceArc_eq_anchor_or_anchorEdge_mem_sourceFace
        third second (by simp [hrest]) (by simp [hrest]) with
      heq | hmem
    · exact False.elim
        (hsecondThirdFace (congrArg ClosureRecoveryFaceArc.sourceFace heq))
    · exact hmem
  exact ⟨second, third, hrest, hfirstSecondFace, hsecondThirdFace,
    hthirdFirstFace, hfirstSecond.edge_ne, hsecondThird.edge_ne,
    hthirdFirst.edge_ne, hfirstEdgeSecond, hfirstEdgeThird,
    hsecondEdgeThird, hsecondEdgeFirst, hthirdEdgeFirst,
    hthirdEdgeSecond⟩

/-- The support edges of a shortest recovery triangle disconnect the
underlying primal graph. -/
theorem IsLengthMinimal.not_connected_deleteEdges_of_isTriangle
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal)
    (htriangle : circuit.IsTriangle) :
    ∃ second third : ClosureRecoveryFaceArc rebaseCircuit,
      circuit.rest = [second, third] ∧
      ¬ (G.deleteEdges ({third.edge.1, circuit.first.edge.1,
          second.edge.1} : Set (Sym2 V))).Connected := by
  rcases hminimal.exists_triangle_support htriangle with
    ⟨second, third, hrest, hfirstSecondFace, hsecondThirdFace,
      hthirdFirstFace, hfirstSecondEdge, hsecondThirdEdge,
      hthirdFirstEdge, hfirstEdgeSecond, hfirstEdgeThird,
      hsecondEdgeThird, hsecondEdgeFirst, hthirdEdgeFirst,
      hthirdEdgeSecond⟩
  have hconnected : G.Connected := by
    rw [← GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
      G graphData]
    exact minimal.primalConnected
  have hdual := orbitFaceInteriorDual_connected
    graphData.toRotationSystem minimal.spherical.cubic
      minimal.primalConnected minimal.vertexRotationCyclic
  refine ⟨second, third, hrest, ?_⟩
  exact not_connected_deleteEdges_triple_of_face_triangle
    graphData minimal.facesTwoSided hdual hconnected minimal.spherical
    hfirstSecondFace hsecondThirdFace hthirdFirstFace
    hthirdFirstEdge hsecondThirdEdge.symm
    hthirdEdgeFirst hthirdEdgeSecond hfirstEdgeSecond hfirstEdgeThird
    hsecondEdgeThird hsecondEdgeFirst

/-- Consequently a shortest recovery circuit is either a digon or a
triangle whose three support edges form a primal separator. -/
theorem IsLengthMinimal.isDigon_or_exists_triangle_separator
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    circuit.IsDigon ∨
      ∃ second third : ClosureRecoveryFaceArc rebaseCircuit,
        circuit.rest = [second, third] ∧
        ¬ (G.deleteEdges ({third.edge.1, circuit.first.edge.1,
            second.edge.1} : Set (Sym2 V))).Connected := by
  rcases hminimal.isDigon_or_isTriangle with hdigon | htriangle
  · exact Or.inl hdigon
  · exact Or.inr (hminimal.not_connected_deleteEdges_of_isTriangle htriangle)

end ClosureRecoveryFaceCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
