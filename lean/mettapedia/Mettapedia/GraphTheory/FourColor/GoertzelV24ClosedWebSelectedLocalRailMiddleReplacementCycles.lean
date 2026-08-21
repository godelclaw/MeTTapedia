import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacement
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalDualTriangleClassification
import Mettapedia.GraphTheory.FourColor.GoertzelV24SelectedDualCycleSeparator

/-!
# Short dual cycles exposed by the middle rail replacement

The canonical middle-replacement collision has already been normalized to
the source ladder's centre, triangle, and square shapes.  This module turns
the four non-centre shapes into literal simple closed walks of length three or
four in the annular facial dual.  Their complete support remains in the
annular interior.

This is positive geometric data for the rotor/square consumer.  It does not
apply either reduction, eliminate the two centre cases, construct the rolling
transition, attach end caps, or close the separated-crosscut obligation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24MinimalDualTriangleClassification
open GoertzelV24SelectedDualCycleSeparator

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {firstInterior : CorridorInterior blockLength}
    {hfirstNext : firstInterior.center.val + 2 < blockLength}
    {hbridgeNext :
      (nextCorridorInterior firstInterior hfirstNext).center.val + 2 < blockLength}
    {hlastNext :
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center.val +
          2 < blockLength}
    {firstPlacement : SelectedInternalHexRungPlacement corridor rungs firstInterior}
    {secondPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior firstInterior hfirstNext)}
    {thirdPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)}
    {fourthPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
        hlastNext)}
    {firstSuccessor : SeparatedSelectedSourceLocalRailSuccessor hfirstNext
      firstPlacement secondPlacement}
    {bridge : SeparatedSelectedSourceLocalRailSuccessor hbridgeNext
      secondPlacement thirdPlacement}
    {lastSuccessor : SeparatedSelectedSourceLocalRailSuccessor hlastNext
      thirdPlacement fourthPlacement}
    {firstIncomingBefore firstIncomingAfter :
      {position // position ∈ selectedPlacementSidePositions firstPlacement}}
    {firstLeft : SeparatedSelectedSourceLocalRailPaths firstPlacement
      firstIncomingBefore firstIncomingAfter firstSuccessor.frame.leftBefore
      firstSuccessor.frame.leftAfter}

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev SelectedDualGraph :=
  interiorDualGraph (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))

/-- A literal short dual cycle through the collision face, retaining a
complete choice of primal crossing together with its source-rung anchor. -/
structure MiddleReplacementShortDualCycle
    (face : SelectedFace (web := web)) where
  start : SelectedFace (web := web)
  walk : SelectedDualGraph (web := web).Walk start start
  isCycle : walk.IsCycle
  length_eq_three_or_four : walk.length = 3 ∨ walk.length = 4
  face_mem_support : face ∈ walk.support
  support_internal : ∀ current ∈ walk.support,
    current.1 ∈ web.annular.cellulation.interiorFaces
  anchor : Fin walk.length
  anchorEdge : G.edgeSet
  anchorEdge_mem_shared : anchorEdge ∈ sharedInteriorEdges
    (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))
    (walk.getVert anchor.val).1 (walk.getVert (anchor.val + 1)).1
  crossingEdge : Fin walk.length → G.edgeSet
  crossing_mem_shared : ∀ step,
    crossingEdge step ∈ sharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (walk.getVert step.val).1 (walk.getVert (step.val + 1)).1
  crossingEdge_anchor : crossingEdge anchor = anchorEdge

/-- Build the legacy anchor-pinned presentation while retaining the complete
crossing selection it chooses.  Later source consumers may replace that
selection without changing the walk geometry. -/
noncomputable def MiddleReplacementShortDualCycle.ofAnchoredWalk
    {face start : SelectedFace (web := web)}
    (walk : SelectedDualGraph (web := web).Walk start start)
    (isCycle : walk.IsCycle)
    (length_eq_three_or_four : walk.length = 3 ∨ walk.length = 4)
    (face_mem_support : face ∈ walk.support)
    (support_internal : ∀ current ∈ walk.support,
      current.1 ∈ web.annular.cellulation.interiorFaces)
    (anchor : Fin walk.length)
    (anchorEdge : G.edgeSet)
    (anchorEdge_mem_shared : anchorEdge ∈ sharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (walk.getVert anchor.val).1 (walk.getVert (anchor.val + 1)).1) :
    MiddleReplacementShortDualCycle (web := web) face := by
  let selected := SelectedDualCycle.ofWalkWithCrossingAt web.annular.RS walk
    isCycle anchor anchorEdge anchorEdge_mem_shared
  exact {
    start := start
    walk := walk
    isCycle := isCycle
    length_eq_three_or_four := length_eq_three_or_four
    face_mem_support := face_mem_support
    support_internal := support_internal
    anchor := anchor
    anchorEdge := anchorEdge
    anchorEdge_mem_shared := anchorEdge_mem_shared
    crossingEdge := selected.crossingEdge
    crossing_mem_shared := selected.crossing_mem_shared
    crossingEdge_anchor := by
      exact SelectedDualCycle.ofWalkWithCrossingAt_crossingEdge
        web.annular.RS walk isCycle anchor anchorEdge anchorEdge_mem_shared
  }

/-- A short-cycle packet whose source geometry proves that it is the
four-step distance-two square branch.  Keeping this equality in the type
prevents a later consumer from confusing it with either adjacent triangle. -/
structure MiddleReplacementSquareDualCycle
    (face : SelectedFace (web := web)) where
  cycle : MiddleReplacementShortDualCycle (web := web) face
  length_eq_four : cycle.walk.length = 4

/-- The four-step closed walk around a common neighbour of corridor centres
two positions apart. -/
private def dualSquareWalk
    {first second third fourth : SelectedFace (web := web)}
    (hfirstSecond : SelectedDualGraph (web := web).Adj first second)
    (hsecondThird : SelectedDualGraph (web := web).Adj second third)
    (hthirdFourth : SelectedDualGraph (web := web).Adj third fourth)
    (hfourthFirst : SelectedDualGraph (web := web).Adj fourth first) :
    SelectedDualGraph (web := web).Walk first first :=
  .cons hfirstSecond
    (.cons hsecondThird (.cons hthirdFourth (.cons hfourthFirst .nil)))

@[simp] private theorem dualSquareWalk_length
    {first second third fourth : SelectedFace (web := web)}
    (hfirstSecond : SelectedDualGraph (web := web).Adj first second)
    (hsecondThird : SelectedDualGraph (web := web).Adj second third)
    (hthirdFourth : SelectedDualGraph (web := web).Adj third fourth)
    (hfourthFirst : SelectedDualGraph (web := web).Adj fourth first) :
    (dualSquareWalk hfirstSecond hsecondThird hthirdFourth hfourthFirst).length = 4 := by
  simp [dualSquareWalk]

private theorem dualSquareWalk_isCycle
    {first second third fourth : SelectedFace (web := web)}
    (hfirstSecond : SelectedDualGraph (web := web).Adj first second)
    (hsecondThird : SelectedDualGraph (web := web).Adj second third)
    (hthirdFourth : SelectedDualGraph (web := web).Adj third fourth)
    (hfourthFirst : SelectedDualGraph (web := web).Adj fourth first)
    (hfirstThird : first ≠ third) (hsecondFourth : second ≠ fourth) :
    (dualSquareWalk hfirstSecond hsecondThird hthirdFourth hfourthFirst).IsCycle := by
  simp [dualSquareWalk, SimpleGraph.Walk.isCycle_def,
    SimpleGraph.Walk.isTrail_def, hfirstSecond.ne, hfirstSecond.ne.symm,
    hsecondThird.ne, hthirdFourth.ne, hfourthFirst.ne,
    hfourthFirst.ne.symm, hfirstThird, hfirstThird.symm, hsecondFourth]

include rungs

/-- Literal four-step cycle for the first-to-third distance-two branch. -/
private noncomputable def firstThirdSquareCycle
    {face : SelectedFace (web := web)}
    (hfirst : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        firstInterior.center) face)
    (hthird : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) :
    MiddleReplacementSquareDualCycle (web := web) face := by
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  have hfirstSecond : SelectedDualGraph (web := web).Adj
      (skeleton.faceAt firstInterior.center)
      (skeleton.faceAt (nextCorridorInterior firstInterior hfirstNext).center) :=
    skeleton.consecutive_adjacent firstInterior.center
      (nextCorridorInterior firstInterior hfirstNext).center rfl
  have hsecondThird : SelectedDualGraph (web := web).Adj
      (skeleton.faceAt (nextCorridorInterior firstInterior hfirstNext).center)
      (skeleton.faceAt (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center) :=
    skeleton.consecutive_adjacent
      (nextCorridorInterior firstInterior hfirstNext).center
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center rfl
  let walk := dualSquareWalk hfirstSecond hsecondThird hthird hfirst.symm
  have hfirstThird : skeleton.faceAt firstInterior.center ≠
      skeleton.faceAt (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center :=
    skeleton.faceAt_ne (by
      intro h
      have hval := congrArg Fin.val h
      change firstInterior.center.val =
        firstInterior.center.val + 1 + 1 at hval
      omega)
  let cycle : MiddleReplacementShortDualCycle (web := web) face :=
    MiddleReplacementShortDualCycle.ofAnchoredWalk
      walk
      (dualSquareWalk_isCycle hfirstSecond hsecondThird hthird
        hfirst.symm hfirstThird (by exact fun h => hfaceSecond h.symm))
      (.inr (dualSquareWalk_length hfirstSecond hsecondThird hthird hfirst.symm))
      (by simp [walk, dualSquareWalk])
      (by
      intro current hcurrent
      simp only [walk, dualSquareWalk, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons] at hcurrent
      rcases hcurrent with hcurrent | hcurrent | hcurrent | hcurrent | hcurrent
      · subst current
        exact corridor.face_internal firstInterior.center
      · subst current
        exact corridor.face_internal
          (nextCorridorInterior firstInterior hfirstNext).center
      · subst current
        exact corridor.face_internal (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center
      · subst current
        exact corridor.neighbor_internal firstInterior.center face hfirst
      · rcases hcurrent with hcurrent | hcurrent
        · subst current
          exact corridor.face_internal firstInterior.center
        · simp at hcurrent
      )
      ⟨0, by simp [walk, dualSquareWalk]⟩
      (rungs.edge firstInterior.outgoing)
      (by simpa [walk, dualSquareWalk] using
        rungs.mem_shared firstInterior.outgoing)
  exact ⟨cycle, by
    change walk.length = 4
    simp [walk, dualSquareWalk]⟩

/-- Literal four-step cycle for the second-to-fourth distance-two branch. -/
private noncomputable def secondFourthSquareCycle
    {face : SelectedFace (web := web)}
    (hsecond : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) face)
    (hfourth : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
          hlastNext).center) face)
    (hfaceThird : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center) :
    MiddleReplacementSquareDualCycle (web := web) face := by
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let secondInterior := nextCorridorInterior firstInterior hfirstNext
  let thirdInterior := nextCorridorInterior secondInterior hbridgeNext
  let fourthInterior := nextCorridorInterior thirdInterior hlastNext
  have hsecondThird : SelectedDualGraph (web := web).Adj
      (skeleton.faceAt secondInterior.center)
      (skeleton.faceAt thirdInterior.center) :=
    skeleton.consecutive_adjacent secondInterior.center thirdInterior.center rfl
  have hthirdFourth : SelectedDualGraph (web := web).Adj
      (skeleton.faceAt thirdInterior.center)
      (skeleton.faceAt fourthInterior.center) :=
    skeleton.consecutive_adjacent thirdInterior.center fourthInterior.center rfl
  let walk := dualSquareWalk hsecondThird hthirdFourth hfourth hsecond.symm
  have hsecondFourth : skeleton.faceAt secondInterior.center ≠
      skeleton.faceAt fourthInterior.center :=
    skeleton.faceAt_ne (by
      intro h
      have hval := congrArg Fin.val h
      dsimp [fourthInterior, thirdInterior, secondInterior,
        nextCorridorInterior] at hval
      omega)
  let cycle : MiddleReplacementShortDualCycle (web := web) face :=
    MiddleReplacementShortDualCycle.ofAnchoredWalk
      walk
      (dualSquareWalk_isCycle hsecondThird hthirdFourth hfourth
        hsecond.symm hsecondFourth (by exact fun h => hfaceThird h.symm))
      (.inr (dualSquareWalk_length hsecondThird hthirdFourth hfourth hsecond.symm))
      (by simp [walk, dualSquareWalk])
      (by
      intro current hcurrent
      simp only [walk, dualSquareWalk, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons] at hcurrent
      rcases hcurrent with hcurrent | hcurrent | hcurrent | hcurrent | hcurrent
      · subst current
        exact corridor.face_internal secondInterior.center
      · subst current
        exact corridor.face_internal thirdInterior.center
      · subst current
        exact corridor.face_internal fourthInterior.center
      · subst current
        exact corridor.neighbor_internal secondInterior.center face hsecond
      · rcases hcurrent with hcurrent | hcurrent
        · subst current
          exact corridor.face_internal secondInterior.center
        · simp at hcurrent
      )
      ⟨0, by simp [walk, dualSquareWalk]⟩
      (rungs.edge secondInterior.outgoing)
      (by
      change rungs.edge secondInterior.outgoing ∈ sharedInteriorEdges
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        (skeleton.faceAt secondInterior.center).1
        (skeleton.faceAt thirdInterior.center).1
      simpa [thirdInterior] using rungs.mem_shared secondInterior.outgoing
      )
  exact ⟨cycle, by
    change walk.length = 4
    simp [walk, dualSquareWalk]⟩

/-- Public constructor for the typed first-to-third square packet. -/
noncomputable def squareDualCycle_of_firstThirdSquare
    {face : SelectedFace (web := web)}
    (hfirst : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        firstInterior.center) face)
    (hthird : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) :
    MiddleReplacementSquareDualCycle (web := web) face :=
  firstThirdSquareCycle (rungs := rungs) hfirst hthird hfaceSecond

/-! ### L1: public coordinates of the canonical first--third square

The construction above deliberately hides its concrete four-cons walk.  The
following small interface exposes only the four vertices in their source
order.  Later pointed-crossing arguments can therefore name the two
collision-adjacent sides without unfolding the cycle constructor or replacing
the source square by an arbitrary four-cycle.
-/

@[simp] theorem squareDualCycle_of_firstThirdSquare_getVert_zero
    {face : SelectedFace (web := web)}
    (hfirst : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        firstInterior.center) face)
    (hthird : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) :
    ((squareDualCycle_of_firstThirdSquare (rungs := rungs)
      hfirst hthird hfaceSecond).cycle.walk.getVert 0) =
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        firstInterior.center := by
  rfl

@[simp] theorem squareDualCycle_of_firstThirdSquare_getVert_one
    {face : SelectedFace (web := web)}
    (hfirst : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        firstInterior.center) face)
    (hthird : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) :
    ((squareDualCycle_of_firstThirdSquare (rungs := rungs)
      hfirst hthird hfaceSecond).cycle.walk.getVert 1) =
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center := by
  rfl

@[simp] theorem squareDualCycle_of_firstThirdSquare_getVert_two
    {face : SelectedFace (web := web)}
    (hfirst : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        firstInterior.center) face)
    (hthird : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) :
    ((squareDualCycle_of_firstThirdSquare (rungs := rungs)
      hfirst hthird hfaceSecond).cycle.walk.getVert 2) =
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center := by
  rfl

@[simp] theorem squareDualCycle_of_firstThirdSquare_getVert_three
    {face : SelectedFace (web := web)}
    (hfirst : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        firstInterior.center) face)
    (hthird : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) :
    ((squareDualCycle_of_firstThirdSquare (rungs := rungs)
      hfirst hthird hfaceSecond).cycle.walk.getVert 3) = face := by
  rfl

/-- **L1 second source anchor of the first--third square.**  Besides the
distinguished first outgoing rung stored in the cycle packet, the next
centre-to-centre side is crossed by the literal outgoing rung of the second
corridor interior.  This is crossing provenance only; it does not identify a
pointed rail edge with either collision-adjacent square side. -/
theorem squareDualCycle_of_firstThirdSquare_secondRung_mem_shared
    {face : SelectedFace (web := web)}
    (hfirst : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        firstInterior.center) face)
    (hthird : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      face)
    (hfaceSecond : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) :
    rungs.edge (nextCorridorInterior firstInterior hfirstNext).outgoing ∈
      sharedInteriorEdges
        (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))
        ((squareDualCycle_of_firstThirdSquare (rungs := rungs)
          hfirst hthird hfaceSecond).cycle.walk.getVert 1).1
        ((squareDualCycle_of_firstThirdSquare (rungs := rungs)
          hfirst hthird hfaceSecond).cycle.walk.getVert 2).1 := by
  simpa using rungs.mem_shared
    (nextCorridorInterior firstInterior hfirstNext).outgoing

/-- Public constructor for the typed second-to-fourth square packet. -/
noncomputable def squareDualCycle_of_secondFourthSquare
    {face : SelectedFace (web := web)}
    (hsecond : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center) face)
    (hfourth : SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
          hlastNext).center) face)
    (hfaceThird : face ≠
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center) :
    MiddleReplacementSquareDualCycle (web := web) face :=
  secondFourthSquareCycle (rungs := rungs) hsecond hfourth hfaceThird

/-- Every normalized non-centre collision produces an actual simple short
dual cycle.  The two centre cases remain explicit and are not converted into
spurious cycles. -/
theorem ExactSelectedLocalRailMiddleReplacementLadderGeometry.center_or_shortCycle
    {face : SelectedFace (web := web)}
    (geometry : ExactSelectedLocalRailMiddleReplacementLadderGeometry
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) face) :
    face = corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center ∨
      face = corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center ∨
      Nonempty (MiddleReplacementShortDualCycle (web := web) face) := by
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  have hfirstSecond : SelectedDualGraph (web := web).Adj
      (skeleton.faceAt firstInterior.center)
      (skeleton.faceAt (nextCorridorInterior firstInterior hfirstNext).center) :=
    skeleton.consecutive_adjacent firstInterior.center
      (nextCorridorInterior firstInterior hfirstNext).center rfl
  have hsecondThird : SelectedDualGraph (web := web).Adj
      (skeleton.faceAt (nextCorridorInterior firstInterior hfirstNext).center)
      (skeleton.faceAt (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center) :=
    skeleton.consecutive_adjacent
      (nextCorridorInterior firstInterior hfirstNext).center
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center rfl
  have hthirdFourth : SelectedDualGraph (web := web).Adj
      (skeleton.faceAt (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center)
      (skeleton.faceAt (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
        hlastNext).center) :=
    skeleton.consecutive_adjacent
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center
      (nextCorridorInterior
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext)
        hlastNext).center rfl
  cases geometry with
  | secondCenter face_eq => exact .inl face_eq
  | thirdCenter face_eq => exact .inr (.inl face_eq)
  | firstSecondTriangle hfirst hsecond =>
      let walk := dualTriangleWalk web.annular.cellulation.rotation
        hfirstSecond hsecond hfirst.symm
      refine .inr (.inr ⟨MiddleReplacementShortDualCycle.ofAnchoredWalk
        walk
        ?_ ?_ ?_ ?_ ⟨0, by simp [walk, dualTriangleWalk]⟩
        (rungs.edge firstInterior.outgoing) ?_⟩)
      · exact dualTriangleWalk_isCycle web.annular.cellulation.rotation
          hfirstSecond hsecond hfirst.symm
      · exact .inl (dualTriangleWalk_length web.annular.cellulation.rotation
          hfirstSecond hsecond hfirst.symm)
      · simp [walk, dualTriangleWalk]
      · intro current hcurrent
        simp only [walk, dualTriangleWalk, SimpleGraph.Walk.support_cons,
          SimpleGraph.Walk.support_nil, List.mem_cons] at hcurrent
        rcases hcurrent with hcurrent | hcurrent | hcurrent | hcurrent
        · subst current
          exact corridor.face_internal firstInterior.center
        · subst current
          exact corridor.face_internal
            (nextCorridorInterior firstInterior hfirstNext).center
        · subst current
          exact corridor.neighbor_internal firstInterior.center face hfirst
        · rcases hcurrent with hcurrent | hcurrent
          · subst current
            exact corridor.face_internal firstInterior.center
          · simp at hcurrent
      · simpa [walk, dualTriangleWalk] using
          rungs.mem_shared firstInterior.outgoing
  | firstThirdSquare hfirst hthird hfaceSecond =>
      let walk := dualSquareWalk hfirstSecond hsecondThird hthird hfirst.symm
      have hfirstThird : skeleton.faceAt firstInterior.center ≠
          skeleton.faceAt (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center :=
        skeleton.faceAt_ne (by
          intro h
          have hval := congrArg Fin.val h
          change firstInterior.center.val =
            firstInterior.center.val + 1 + 1 at hval
          omega)
      refine .inr (.inr ⟨MiddleReplacementShortDualCycle.ofAnchoredWalk
        walk
        ?_ ?_ ?_ ?_ ⟨0, by simp [walk, dualSquareWalk]⟩
        (rungs.edge firstInterior.outgoing) ?_⟩)
      · exact dualSquareWalk_isCycle hfirstSecond hsecondThird hthird hfirst.symm
          hfirstThird (by exact fun h => hfaceSecond h.symm)
      · exact .inr (dualSquareWalk_length hfirstSecond hsecondThird hthird hfirst.symm)
      · simp [walk, dualSquareWalk]
      · intro current hcurrent
        simp only [walk, dualSquareWalk, SimpleGraph.Walk.support_cons,
          SimpleGraph.Walk.support_nil, List.mem_cons] at hcurrent
        rcases hcurrent with hcurrent | hcurrent | hcurrent | hcurrent | hcurrent
        · subst current
          exact corridor.face_internal firstInterior.center
        · subst current
          exact corridor.face_internal
            (nextCorridorInterior firstInterior hfirstNext).center
        · subst current
          exact corridor.face_internal (nextCorridorInterior
            (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center
        · subst current
          exact corridor.neighbor_internal firstInterior.center face hfirst
        · rcases hcurrent with hcurrent | hcurrent
          · subst current
            exact corridor.face_internal firstInterior.center
          · simp at hcurrent
      · simpa [walk, dualSquareWalk] using
          rungs.mem_shared firstInterior.outgoing
  | secondFourthSquare hsecond hfourth hfaceThird =>
      let thirdInterior := nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext
      let fourthInterior := nextCorridorInterior thirdInterior hlastNext
      let walk := dualSquareWalk hsecondThird hthirdFourth hfourth hsecond.symm
      have hsecondFourth :
          skeleton.faceAt (nextCorridorInterior firstInterior hfirstNext).center ≠
          skeleton.faceAt fourthInterior.center :=
        skeleton.faceAt_ne (by
          intro h
          have hval := congrArg Fin.val h
          dsimp [fourthInterior, thirdInterior, nextCorridorInterior] at hval
          omega)
      refine .inr (.inr ⟨MiddleReplacementShortDualCycle.ofAnchoredWalk
        walk
        ?_ ?_ ?_ ?_ ⟨0, by simp [walk, dualSquareWalk]⟩
        (rungs.edge (nextCorridorInterior firstInterior hfirstNext).outgoing) ?_⟩)
      · exact dualSquareWalk_isCycle hsecondThird hthirdFourth hfourth hsecond.symm
          hsecondFourth (by exact fun h => hfaceThird h.symm)
      · exact .inr (dualSquareWalk_length hsecondThird hthirdFourth hfourth hsecond.symm)
      · simp [walk, dualSquareWalk]
      · intro current hcurrent
        simp only [walk, dualSquareWalk, SimpleGraph.Walk.support_cons,
          SimpleGraph.Walk.support_nil, List.mem_cons] at hcurrent
        rcases hcurrent with hcurrent | hcurrent | hcurrent | hcurrent | hcurrent
        · subst current
          exact corridor.face_internal
            (nextCorridorInterior firstInterior hfirstNext).center
        · subst current
          exact corridor.face_internal thirdInterior.center
        · subst current
          exact corridor.face_internal fourthInterior.center
        · subst current
          exact corridor.neighbor_internal
            (nextCorridorInterior firstInterior hfirstNext).center face hsecond
        · rcases hcurrent with hcurrent | hcurrent
          · subst current
            exact corridor.face_internal
              (nextCorridorInterior firstInterior hfirstNext).center
          · simp at hcurrent
      · simpa [walk, dualSquareWalk] using
          rungs.mem_shared
            (nextCorridorInterior firstInterior hfirstNext).outgoing
  | thirdFourthTriangle hthird hfourth =>
      let thirdInterior := nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext
      let walk := dualTriangleWalk web.annular.cellulation.rotation
        hthirdFourth hfourth hthird.symm
      refine .inr (.inr ⟨MiddleReplacementShortDualCycle.ofAnchoredWalk
        walk
        ?_ ?_ ?_ ?_ ⟨0, by
          rw [dualTriangleWalk_length]
          omega⟩
        (rungs.edge thirdInterior.outgoing) ?_⟩)
      · exact dualTriangleWalk_isCycle web.annular.cellulation.rotation
          hthirdFourth hfourth hthird.symm
      · exact .inl (dualTriangleWalk_length web.annular.cellulation.rotation
          hthirdFourth hfourth hthird.symm)
      · have hget : walk.getVert 2 = face := rfl
        rw [← hget]
        exact walk.getVert_mem_support 2
      · intro current hcurrent
        simp only [walk, dualTriangleWalk, SimpleGraph.Walk.support_cons,
          SimpleGraph.Walk.support_nil, List.mem_cons] at hcurrent
        rcases hcurrent with hcurrent | hcurrent | hcurrent | hcurrent
        · subst current
          exact corridor.face_internal thirdInterior.center
        · subst current
          exact corridor.face_internal
            (nextCorridorInterior thirdInterior hlastNext).center
        · subst current
          exact corridor.neighbor_internal thirdInterior.center face hthird
        · rcases hcurrent with hcurrent | hcurrent
          · subst current
            exact corridor.face_internal thirdInterior.center
          · simp at hcurrent
      · change rungs.edge thirdInterior.outgoing ∈ sharedInteriorEdges
          (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS))
          (skeleton.faceAt thirdInterior.center).1
          (skeleton.faceAt
            (nextCorridorInterior thirdInterior hlastNext).center).1
        exact rungs.mem_shared thirdInterior.outgoing

/-- Source-facing composition: a surviving replacement collision is either
one of the two literal centre cases or carries a concrete short interior dual
cycle. -/
theorem ExactSelectedLocalRailMiddleReplacementCollision.center_or_shortCycle
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    {trace : ExactSelectedLocalRailConstructionTrace bridge
      (firstSuccessor.rightRailsAsNextLeft bridge)}
    {face : SelectedFace (web := web)}
    (collision : ExactSelectedLocalRailMiddleReplacementCollision
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (lastSuccessor := lastSuccessor) (firstLeft := firstLeft) trace face) :
    face = corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior firstInterior hfirstNext).center ∨
      face = corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (nextCorridorInterior
          (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center ∨
      Nonempty (MiddleReplacementShortDualCycle (web := web) face) :=
  (collision.hasLadderGeometry hsource).center_or_shortCycle (rungs := rungs)

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
