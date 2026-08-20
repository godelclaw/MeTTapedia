import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSecondBandAdvance

/-!
# L1: a literal center bridge for the advanced second-band endpoint

After the fourth-cell far endpoint is advanced through the next four-cell
window, exact support provenance locates any surviving occurrence near the
fourth--fifth or sixth--seventh corridor-center pair.  This module constructs
the corresponding walk from the old second-center attachment through the
literal consecutive corridor centers to that future attachment.

The bridge avoids the old collision face by the retained endpoint geometry and
the corridor skeleton's separation theorem.  Its support receipt lists only
the two attachments and centers two through seven.  It does not yet splice the
old and new rails, prove companion separation, consume a new collision outcome,
attach end caps, or close Fable flag L1.
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
    {firstInterior : CorridorInterior blockLength}
    {hfirstNext : firstInterior.center.val + 2 < blockLength}
    {hbridgeNext :
      (nextCorridorInterior firstInterior hfirstNext).center.val + 2 < blockLength}
    {hlastNext :
      (nextCorridorInterior
        (nextCorridorInterior firstInterior hfirstNext) hbridgeNext).center.val +
          2 < blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
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

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev SelectedDualGraph :=
  interiorDualGraph (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev SecondInterior :=
  nextCorridorInterior firstInterior hfirstNext

private abbrev ThirdInterior :=
  nextCorridorInterior
    (SecondInterior (firstInterior := firstInterior) (hfirstNext := hfirstNext))
    hbridgeNext

private abbrev FourthInterior :=
  nextCorridorInterior
    (ThirdInterior (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext)) hlastNext

variable
    {hfourthNext :
      (FourthInterior (firstInterior := firstInterior) (hfirstNext := hfirstNext)
        (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)).center.val + 2 <
          blockLength}
    {hfifthNext :
      (nextCorridorInterior
        (FourthInterior (firstInterior := firstInterior) (hfirstNext := hfirstNext)
          (hbridgeNext := hbridgeNext) (hlastNext := hlastNext))
        hfourthNext).center.val + 2 < blockLength}
    {hsixthNext :
      (nextCorridorInterior
        (nextCorridorInterior
          (FourthInterior (firstInterior := firstInterior) (hfirstNext := hfirstNext)
            (hbridgeNext := hbridgeNext) (hlastNext := hlastNext))
          hfourthNext)
        hfifthNext).center.val + 2 < blockLength}

private abbrev FifthInterior :=
  nextCorridorInterior
    (FourthInterior (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)) hfourthNext

private abbrev SixthInterior :=
  nextCorridorInterior
    (FifthInterior (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext)) hfifthNext

private abbrev SeventhInterior :=
  nextCorridorInterior
    (SixthInterior (firstInterior := firstInterior) (hfirstNext := hfirstNext)
      (hbridgeNext := hbridgeNext) (hlastNext := hlastNext)
      (hfourthNext := hfourthNext) (hfifthNext := hfifthNext)) hsixthNext

/-- A bridge from the old rail attachment to the future suffix attachment,
with an exact finite support envelope and collision avoidance. -/
structure SecondToFutureCenterBridge
    (face left right : SelectedFace (web := web)) where
  walk : SelectedDualGraph (web := web).Walk left right
  avoids : face ∉ walk.support
  support_receipt : ∀ current ∈ walk.support,
    current ∈
      [left,
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (SecondInterior (firstInterior := firstInterior)
            (hfirstNext := hfirstNext)).center,
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (ThirdInterior (firstInterior := firstInterior)
            (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)).center,
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (FourthInterior (firstInterior := firstInterior)
            (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
            (hlastNext := hlastNext)).center,
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (FifthInterior (firstInterior := firstInterior)
            (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
            (hlastNext := hlastNext) (hfourthNext := hfourthNext)).center,
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (SixthInterior (firstInterior := firstInterior)
            (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
            (hlastNext := hlastNext) (hfourthNext := hfourthNext)
            (hfifthNext := hfifthNext)).center,
        corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
          (SeventhInterior (firstInterior := firstInterior)
            (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
            (hlastNext := hlastNext) (hfourthNext := hfourthNext)
            (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)).center,
        right]

/-- The retained endpoint geometry and exact future-window location construct
the literal face-avoiding bridge required by the cross-splice. -/
theorem SecondFourthFarEndpoint.exists_secondToFutureCenterBridge
    {face left right : SelectedFace (web := web)}
    (endpoint : SecondFourthFarEndpoint
      (firstSuccessor := firstSuccessor) (bridge := bridge)
      (fourthPlacement := fourthPlacement) (lastSuccessor := lastSuccessor) face)
    (hleft : SelectedDualGraph (web := web).Adj left
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (SecondInterior (firstInterior := firstInterior)
          (hfirstNext := hfirstNext)).center))
    (hright : FaceNearExactTerminalCenterPairs
      (corridor := corridor)
      (firstInterior := FourthInterior (firstInterior := firstInterior)
        (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
        (hlastNext := hlastNext))
      (hfirstNext := hfourthNext) (hbridgeNext := hfifthNext)
      (hlastNext := hsixthNext) right)
    (hfaceLeft : face ≠ left) (hfaceRight : face ≠ right) :
    Nonempty (SecondToFutureCenterBridge
      (corridor := corridor) (firstInterior := firstInterior)
      (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
      (hlastNext := hlastNext) (hfourthNext := hfourthNext)
      (hfifthNext := hfifthNext) (hsixthNext := hsixthNext) face left right) := by
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let second := SecondInterior (firstInterior := firstInterior)
    (hfirstNext := hfirstNext)
  let third := ThirdInterior (firstInterior := firstInterior)
    (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
  let fourth := FourthInterior (firstInterior := firstInterior)
    (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
    (hlastNext := hlastNext)
  let fifth := FifthInterior (firstInterior := firstInterior)
    (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
    (hlastNext := hlastNext) (hfourthNext := hfourthNext)
  let sixth := SixthInterior (firstInterior := firstInterior)
    (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
    (hlastNext := hlastNext) (hfourthNext := hfourthNext)
    (hfifthNext := hfifthNext)
  let seventh := SeventhInterior (firstInterior := firstInterior)
    (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
    (hlastNext := hlastNext) (hfourthNext := hfourthNext)
    (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
  have hsecondThird : SelectedDualGraph (web := web).Adj
      (skeleton.faceAt second.center) (skeleton.faceAt third.center) :=
    skeleton.consecutive_adjacent second.center third.center rfl
  have hthirdFourth : SelectedDualGraph (web := web).Adj
      (skeleton.faceAt third.center) (skeleton.faceAt fourth.center) :=
    skeleton.consecutive_adjacent third.center fourth.center rfl
  have hfourthFifth : SelectedDualGraph (web := web).Adj
      (skeleton.faceAt fourth.center) (skeleton.faceAt fifth.center) :=
    skeleton.consecutive_adjacent fourth.center fifth.center rfl
  have hfifthSixth : SelectedDualGraph (web := web).Adj
      (skeleton.faceAt fifth.center) (skeleton.faceAt sixth.center) :=
    skeleton.consecutive_adjacent fifth.center sixth.center rfl
  have hsixthSeventh : SelectedDualGraph (web := web).Adj
      (skeleton.faceAt sixth.center) (skeleton.faceAt seventh.center) :=
    skeleton.consecutive_adjacent sixth.center seventh.center rfl
  have hneSecond : face ≠ skeleton.faceAt second.center := by
    exact endpoint.secondAdjacent.ne.symm
  have hneThird : face ≠ skeleton.faceAt third.center := by
    exact endpoint.neThirdCenter
  have hneFourth : face ≠ skeleton.faceAt fourth.center := by
    exact endpoint.fourthAdjacent.ne.symm
  have hneFifth : face ≠ skeleton.faceAt fifth.center := by
    apply endpoint.neCenter_of_second_add_one_lt (futureInterior := fifth)
    dsimp [second, fifth, FourthInterior, ThirdInterior, SecondInterior]
    omega
  have hneSixth : face ≠ skeleton.faceAt sixth.center := by
    apply endpoint.neCenter_of_second_add_one_lt (futureInterior := sixth)
    dsimp [second, sixth, FifthInterior, FourthInterior, ThirdInterior,
      SecondInterior]
    omega
  have hneSeventh : face ≠ skeleton.faceAt seventh.center := by
    apply endpoint.neCenter_of_second_add_one_lt (futureInterior := seventh)
    dsimp [second, seventh, SixthInterior, FifthInterior, FourthInterior,
      ThirdInterior, SecondInterior]
    omega
  let envelope :=
    [left, skeleton.faceAt second.center, skeleton.faceAt third.center,
      skeleton.faceAt fourth.center, skeleton.faceAt fifth.center,
      skeleton.faceAt sixth.center, skeleton.faceAt seventh.center, right]
  have hfaceEnvelope : face ∉ envelope := by
    simp only [envelope, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hfaceLeft, hneSecond, hneThird, hneFourth, hneFifth, hneSixth,
      hneSeventh, hfaceRight⟩
  have hmemLeft : left ∈ envelope := by simp [envelope]
  have hmemSecond : skeleton.faceAt second.center ∈ envelope := by
    simp [envelope]
  have hmemThird : skeleton.faceAt third.center ∈ envelope := by
    simp [envelope]
  have hmemFourth : skeleton.faceAt fourth.center ∈ envelope := by
    simp [envelope]
  have hmemFifth : skeleton.faceAt fifth.center ∈ envelope := by
    simp [envelope]
  have hmemSixth : skeleton.faceAt sixth.center ∈ envelope := by
    simp [envelope]
  have hmemSeventh : skeleton.faceAt seventh.center ∈ envelope := by
    simp [envelope]
  have hmemRight : right ∈ envelope := by simp [envelope]
  have package
      (walk : SelectedDualGraph (web := web).Walk left right)
      (hreceipt : ∀ current ∈ walk.support, current ∈ envelope) :
      Nonempty (SecondToFutureCenterBridge
        (corridor := corridor) (firstInterior := firstInterior)
        (hfirstNext := hfirstNext) (hbridgeNext := hbridgeNext)
        (hlastNext := hlastNext) (hfourthNext := hfourthNext)
        (hfifthNext := hfifthNext) (hsixthNext := hsixthNext)
        face left right) := by
    have havoid : face ∉ walk.support := by
      intro hface
      exact hfaceEnvelope (hreceipt face hface)
    exact ⟨⟨walk, havoid, by
      intro current hcurrent
      have hmem := hreceipt current hcurrent
      simpa [envelope, skeleton, second, third, fourth, fifth, sixth, seventh]
        using hmem⟩⟩
  rcases hright with hnearFirst | hnearLast
  · rcases hnearFirst with hrightFourth | hrightFifth |
        hrightFourth | hrightFifth
    · subst right
      let walk : SelectedDualGraph (web := web).Walk left
          (skeleton.faceAt fourth.center) :=
        .cons hleft (.cons hsecondThird (.cons hthirdFourth .nil))
      apply package walk
      intro current hcurrent
      simp only [walk, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hcurrent
      rcases hcurrent with rfl | rfl | rfl | rfl
      · exact hmemLeft
      · exact hmemSecond
      · exact hmemThird
      · exact hmemFourth
    · subst right
      let walk : SelectedDualGraph (web := web).Walk left
          (skeleton.faceAt fifth.center) :=
        .cons hleft (.cons hsecondThird (.cons hthirdFourth
          (.cons hfourthFifth .nil)))
      apply package walk
      intro current hcurrent
      simp only [walk, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hcurrent
      rcases hcurrent with rfl | rfl | rfl | rfl | rfl
      · exact hmemLeft
      · exact hmemSecond
      · exact hmemThird
      · exact hmemFourth
      · exact hmemFifth
    · let walk : SelectedDualGraph (web := web).Walk left right :=
        .cons hleft (.cons hsecondThird (.cons hthirdFourth
          (.cons hrightFourth .nil)))
      apply package walk
      intro current hcurrent
      simp only [walk, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hcurrent
      rcases hcurrent with rfl | rfl | rfl | rfl | rfl
      · exact hmemLeft
      · exact hmemSecond
      · exact hmemThird
      · exact hmemFourth
      · exact hmemRight
    · let walk : SelectedDualGraph (web := web).Walk left right :=
        .cons hleft (.cons hsecondThird (.cons hthirdFourth
          (.cons hfourthFifth (.cons hrightFifth .nil))))
      apply package walk
      intro current hcurrent
      simp only [walk, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hcurrent
      rcases hcurrent with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hmemLeft
      · exact hmemSecond
      · exact hmemThird
      · exact hmemFourth
      · exact hmemFifth
      · exact hmemRight
  · rcases hnearLast with hrightSixth | hrightSeventh |
        hrightSixth | hrightSeventh
    · subst right
      let walk : SelectedDualGraph (web := web).Walk left
          (skeleton.faceAt sixth.center) :=
        .cons hleft (.cons hsecondThird (.cons hthirdFourth
          (.cons hfourthFifth (.cons hfifthSixth .nil))))
      apply package walk
      intro current hcurrent
      simp only [walk, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hcurrent
      rcases hcurrent with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hmemLeft
      · exact hmemSecond
      · exact hmemThird
      · exact hmemFourth
      · exact hmemFifth
      · exact hmemSixth
    · subst right
      let walk : SelectedDualGraph (web := web).Walk left
          (skeleton.faceAt seventh.center) :=
        .cons hleft (.cons hsecondThird (.cons hthirdFourth
          (.cons hfourthFifth (.cons hfifthSixth
            (.cons hsixthSeventh .nil)))))
      apply package walk
      intro current hcurrent
      simp only [walk, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hcurrent
      rcases hcurrent with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hmemLeft
      · exact hmemSecond
      · exact hmemThird
      · exact hmemFourth
      · exact hmemFifth
      · exact hmemSixth
      · exact hmemSeventh
    · let walk : SelectedDualGraph (web := web).Walk left right :=
        .cons hleft (.cons hsecondThird (.cons hthirdFourth
          (.cons hfourthFifth (.cons hfifthSixth
            (.cons hrightSixth .nil)))))
      apply package walk
      intro current hcurrent
      simp only [walk, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hcurrent
      rcases hcurrent with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hmemLeft
      · exact hmemSecond
      · exact hmemThird
      · exact hmemFourth
      · exact hmemFifth
      · exact hmemSixth
      · exact hmemRight
    · let walk : SelectedDualGraph (web := web).Walk left right :=
        .cons hleft (.cons hsecondThird (.cons hthirdFourth
          (.cons hfourthFifth (.cons hfifthSixth
            (.cons hsixthSeventh (.cons hrightSeventh .nil))))))
      apply package walk
      intro current hcurrent
      simp only [walk, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hcurrent
      rcases hcurrent with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hmemLeft
      · exact hmemSecond
      · exact hmemThird
      · exact hmemFourth
      · exact hmemFifth
      · exact hmemSixth
      · exact hmemSeventh
      · exact hmemRight

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
