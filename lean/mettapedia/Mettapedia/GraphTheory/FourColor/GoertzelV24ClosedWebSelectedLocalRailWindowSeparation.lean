import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailAppendComplete

/-!
# L1: remote separation for provenance-tracked selected rail windows

The unconditional adjacent append may reroute through either of its two
Cell-3 centre faces.  Consequently the older invariant saying that every rail
face is adjacent to one generating centre is too narrow for iteration.  The
right finite-window invariant is the closed neighbourhood of the two centres:
each retained face is either one of those centres or adjacent to one of them.

This module proves the remote half of that invariant.  Two arbitrary supports
carried by such adjacent two-centre windows are disjoint once their left
centres differ by more than three corridor positions.  Equal-centre and
centre-neighbour collisions are excluded by the corridor skeleton; a face
adjacent to both windows is excluded by source boundary-cleanliness.

This is a separation theorem for an explicitly supplied support provenance.
It does not yet prove that every branch of `appendLocalSuccessorComplete`
carries that provenance, construct the finite-state induction, attach either
annular end cap, or close Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceDualConnectedness
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
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev SelectedDualGraph :=
  interiorDualGraph (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))

/-- A face belongs to the closed dual neighbourhood of one of two corridor
centres.  Equality is retained separately because dual adjacency is
irreflexive. -/
def FaceNearSelectedCenterPair
    (left right : Fin blockLength) (face : SelectedFace (web := web)) : Prop :=
  face = (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      |>.faceAt left) ∨
    face = (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      |>.faceAt right) ∨
    SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt left) face ∨
    SelectedDualGraph (web := web).Adj
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt right) face

/-- A finite facial support is carried by the closed neighbourhood of a
two-centre selected Cell-3 window. -/
def SupportNearSelectedCenterPair
    (left right : Fin blockLength) (support : List (SelectedFace (web := web))) :
    Prop :=
  ∀ face ∈ support,
    FaceNearSelectedCenterPair (corridor := corridor) left right face

/-- **L1 remote two-window separation.** Closed-neighbourhood provenance is
exactly strong enough to separate arbitrary selected rail supports belonging
to sufficiently remote adjacent Cell-3 windows. -/
theorem supports_disjoint_of_near_selected_center_pairs_of_add_three_lt
    {leftInterior : CorridorInterior blockLength}
    {hleftNext : leftInterior.center.val + 2 < blockLength}
    {rightInterior : CorridorInterior blockLength}
    {hrightNext : rightInterior.center.val + 2 < blockLength}
    (hsource : web.annular.SourceRealizesBoundaryCleanOrbitHexCorridor
      blockLength corridor)
    (leftSupport rightSupport : List (SelectedFace (web := web)))
    (hleft : SupportNearSelectedCenterPair (corridor := corridor)
      leftInterior.center (nextCorridorInterior leftInterior hleftNext).center
      leftSupport)
    (hright : SupportNearSelectedCenterPair (corridor := corridor)
      rightInterior.center (nextCorridorInterior rightInterior hrightNext).center
      rightSupport)
    (hseparated : leftInterior.center.val + 3 < rightInterior.center.val) :
    leftSupport.Disjoint rightSupport := by
  let skeleton :=
    corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  have h00ne : skeleton.faceAt leftInterior.center ≠
      skeleton.faceAt rightInterior.center :=
    skeleton.faceAt_ne (by
      intro h
      have hvalues := congrArg Fin.val h
      omega)
  have h01ne : skeleton.faceAt leftInterior.center ≠
      skeleton.faceAt (nextCorridorInterior rightInterior hrightNext).center :=
    skeleton.faceAt_ne (by
      intro h
      have hvalues := congrArg Fin.val h
      change leftInterior.center.val = rightInterior.center.val + 1 at hvalues
      omega)
  have h10ne : skeleton.faceAt
        (nextCorridorInterior leftInterior hleftNext).center ≠
      skeleton.faceAt rightInterior.center :=
    skeleton.faceAt_ne (by
      intro h
      have hvalues := congrArg Fin.val h
      change leftInterior.center.val + 1 = rightInterior.center.val at hvalues
      omega)
  have h11ne : skeleton.faceAt
        (nextCorridorInterior leftInterior hleftNext).center ≠
      skeleton.faceAt (nextCorridorInterior rightInterior hrightNext).center :=
    skeleton.faceAt_ne (by
      intro h
      have hvalues := congrArg Fin.val h
      change leftInterior.center.val + 1 = rightInterior.center.val + 1 at hvalues
      omega)
  have h00notadj : ¬ SelectedDualGraph (web := web).Adj
      (skeleton.faceAt leftInterior.center)
      (skeleton.faceAt rightInterior.center) :=
    skeleton.separated_not_adjacent leftInterior.center rightInterior.center
      (by omega)
  have h01notadj : ¬ SelectedDualGraph (web := web).Adj
      (skeleton.faceAt leftInterior.center)
      (skeleton.faceAt (nextCorridorInterior rightInterior hrightNext).center) :=
    skeleton.separated_not_adjacent leftInterior.center
      (nextCorridorInterior rightInterior hrightNext).center (by
        change leftInterior.center.val + 1 < rightInterior.center.val + 1
        omega)
  have h10notadj : ¬ SelectedDualGraph (web := web).Adj
      (skeleton.faceAt (nextCorridorInterior leftInterior hleftNext).center)
      (skeleton.faceAt rightInterior.center) :=
    skeleton.separated_not_adjacent
      (nextCorridorInterior leftInterior hleftNext).center rightInterior.center
      (by
        change leftInterior.center.val + 1 + 1 < rightInterior.center.val
        omega)
  have h11notadj : ¬ SelectedDualGraph (web := web).Adj
      (skeleton.faceAt (nextCorridorInterior leftInterior hleftNext).center)
      (skeleton.faceAt (nextCorridorInterior rightInterior hrightNext).center) :=
    skeleton.separated_not_adjacent
      (nextCorridorInterior leftInterior hleftNext).center
      (nextCorridorInterior rightInterior hrightNext).center (by
        change leftInterior.center.val + 1 + 1 < rightInterior.center.val + 1
        omega)
  rw [List.disjoint_left]
  intro face hfaceLeft hfaceRight
  rcases hleft face hfaceLeft with hleft0 | hleft1 | hleft0adj | hleft1adj
  · rcases hright face hfaceRight with
      hright0 | hright1 | hright0adj | hright1adj
    · exact h00ne (hleft0.symm.trans hright0)
    · exact h01ne (hleft0.symm.trans hright1)
    · subst face
      exact h00notadj hright0adj.symm
    · subst face
      exact h01notadj hright1adj.symm
  · rcases hright face hfaceRight with
      hright0 | hright1 | hright0adj | hright1adj
    · exact h10ne (hleft1.symm.trans hright0)
    · exact h11ne (hleft1.symm.trans hright1)
    · subst face
      exact h10notadj hright0adj.symm
    · subst face
      exact h11notadj hright1adj.symm
  · rcases hright face hfaceRight with
      hright0 | hright1 | hright0adj | hright1adj
    · subst face
      exact h00notadj hleft0adj
    · subst face
      exact h01notadj hleft0adj
    · exact corridor.no_common_fullNeighbor_of_add_two_lt hsource
        leftInterior.center rightInterior.center (by omega)
        ⟨face, hleft0adj, hright0adj⟩
    · exact corridor.no_common_fullNeighbor_of_add_two_lt hsource
        leftInterior.center
        (nextCorridorInterior rightInterior hrightNext).center (by
          change leftInterior.center.val + 2 < rightInterior.center.val + 1
          omega)
        ⟨face, hleft0adj, hright1adj⟩
  · rcases hright face hfaceRight with
      hright0 | hright1 | hright0adj | hright1adj
    · subst face
      exact h10notadj hleft1adj
    · subst face
      exact h11notadj hleft1adj
    · exact corridor.no_common_fullNeighbor_of_add_two_lt hsource
        (nextCorridorInterior leftInterior hleftNext).center
        rightInterior.center (by
          change leftInterior.center.val + 1 + 2 < rightInterior.center.val
          omega)
        ⟨face, hleft1adj, hright0adj⟩
    · exact corridor.no_common_fullNeighbor_of_add_two_lt hsource
        (nextCorridorInterior leftInterior hleftNext).center
        (nextCorridorInterior rightInterior hrightNext).center (by
          change leftInterior.center.val + 1 + 2 < rightInterior.center.val + 1
          omega)
        ⟨face, hleft1adj, hright1adj⟩

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
