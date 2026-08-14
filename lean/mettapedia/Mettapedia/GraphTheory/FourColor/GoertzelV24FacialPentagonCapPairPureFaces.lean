import Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapPairFaceCounts
import Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapPairDeletedCycle
import Mettapedia.GraphTheory.FourColor.GoertzelV24PlanarBondSpliceEuler
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphRotationBridge
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoPentagonCapOpeningCounts

/-!
# The two pure deleted faces of a facial pentagon-cap pair

The C-3 Euler comparison needs the ambient faces split into three literal
classes: faces touched by the ten cap spokes, faces wholly retained, and faces
wholly deleted.  The touched class was counted separately.  This file proves
the local input for the remaining class: one facial pentagon cap supports
exactly one pure deleted ambient face.

The proof is not the picture assertion that a pentagon bounds a disc.  The
named facial cap supplies one pure face, while the connected induced five-cycle
and spherical cycle-space rank bound show that there cannot be a second one.
The later pair theorem combines the two remote cap components.

This is C-3 face arithmetic.  It does not construct retained-complement
connectedness, the annular cellulation, or the source-selected cap pair.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FacialPentagonCapPairPureFaces

open SimpleGraphDartRotation
open GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24FacialPentagonCapOpenHoleOrbit
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PentagonCapOpening
open GoertzelV24PentagonCapOpeningComparison
open GoertzelV24PlanarBondBoundaryOrder
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24TwoPentagonCapOpening

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24OpenRegionRotation.retainedVertexFintype
  GoertzelV24OpenRegionRotation.retainedVertexDecidableEq
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq

namespace PentagonCap

/-- The literal cap vertex support has five members. -/
@[simp] theorem vertexSupport_card (cap : PentagonCap G) :
    cap.vertexSupport.card = 5 := by
  rw [PentagonCap.vertexSupport, Finset.card_map]
  simp

/-- An ambient edge has both endpoints in the cap exactly when it is one of
the five named cap-cycle edges. -/
theorem graphEdgesAllOnSide_vertexSupport_eq_cycleSupport
    (cap : PentagonCap G) :
    graphEdgesAllOnSide G (fun vertex => vertex ∈ cap.vertexSupport) =
      cap.cycleSupport.image Subtype.val := by
  ext edge
  rw [mem_graphEdgesAllOnSide_iff]
  constructor
  · rintro ⟨hedge, hall⟩
    by_contra hnotCycle
    obtain ⟨⟨first, second⟩, hrep⟩ := Quot.exists_rep edge
    have hfirstMem : first ∈ edge := by
      rw [← hrep]
      exact Sym2.mem_mk_left first second
    have hsecondMem : second ∈ edge := by
      rw [← hrep]
      exact Sym2.mem_mk_right first second
    rcases (cap.mem_vertexSupport_iff first).1 (hall first hfirstMem) with
      ⟨firstStep, hfirstStep⟩
    rcases (cap.mem_vertexSupport_iff second).1 (hall second hsecondMem) with
      ⟨secondStep, hsecondStep⟩
    have hnotRemoved : edge ∉ edgeFinsetValueSet cap.cycleSupport := by
      intro hremoved
      rcases (mem_edgeFinsetValueSet_iff cap.cycleSupport edge).1 hremoved with
        ⟨cycleEdge, hcycleEdge, hvalue⟩
      exact hnotCycle (Finset.mem_image.2 ⟨cycleEdge, hcycleEdge, hvalue⟩)
    have hopenEdge : edge ∈ cap.openGraph.edgeSet :=
      (cap.mem_openGraph_edgeSet_iff edge hedge).2 hnotRemoved
    have hopen : cap.openGraph.Adj (cap.vertex firstStep)
        (cap.vertex secondStep) := by
      simpa [SimpleGraph.mem_edgeSet, ← hrep, hfirstStep, hsecondStep] using
        hopenEdge
    exact GoertzelV24PentagonCapOpeningComparison.PentagonCap.not_openGraph_adj_capVertices
      cap firstStep secondStep hopen
  · intro hcycleValue
    rcases Finset.mem_image.1 hcycleValue with ⟨cycleEdge, hcycleEdge, hvalue⟩
    rcases Finset.mem_map.1 hcycleEdge with ⟨step, -, hstep⟩
    have hedgeValue : (cap.cycleEdge step).1 = edge := by
      exact (congrArg Subtype.val hstep).trans hvalue
    refine ⟨by simpa [← hedgeValue] using (cap.cycleEdge step).2, ?_⟩
    intro vertex hvertex
    rcases cap.cycleEdge_endpoint_eq_vertex step vertex
        (by simpa [hedgeValue] using hvertex) with
      ⟨vertexStep, hvertexStep⟩
    exact (cap.mem_vertexSupport_iff vertex).2 ⟨vertexStep, hvertexStep⟩

/-- Exactly five ambient edges lie wholly in the cap support. -/
@[simp] theorem card_graphEdgesAllOnSide_vertexSupport
    (cap : PentagonCap G) :
    (graphEdgesAllOnSide G (fun vertex => vertex ∈ cap.vertexSupport)).card = 5 := by
  rw [graphEdgesAllOnSide_vertexSupport_eq_cycleSupport cap]
  rw [Finset.card_image_iff.mpr Subtype.val_injective.injOn]
  exact _root_.Mettapedia.GraphTheory.FourColor.GoertzelV24TwoPentagonCapOpeningCounts.PentagonCap.cycleSupport_card
    cap

/-- The selected-side vertex count of a cap is five. -/
@[simp] theorem sideVertexCount_vertexSupport (cap : PentagonCap G) :
    sideVertexCount (fun vertex => vertex ∈ cap.vertexSupport) = 5 := by
  classical
  rw [sideVertexCount_eq_card_sideVertex]
  let equivalence :
      SideVertex (fun vertex => vertex ∈ cap.vertexSupport) ≃
        ↑cap.vertexSupport :=
    { toFun := fun vertex => ⟨vertex.1, vertex.2⟩
      invFun := fun vertex => ⟨vertex.1, vertex.2⟩
      left_inv := fun vertex => Subtype.ext rfl
      right_inv := fun vertex => Subtype.ext rfl }
  calc
    Fintype.card (SideVertex
        (fun vertex => vertex ∈ cap.vertexSupport)) =
        Fintype.card ↑cap.vertexSupport := Fintype.card_congr equivalence
    _ = cap.vertexSupport.card := Fintype.card_coe cap.vertexSupport
    _ = 5 := vertexSupport_card cap

end PentagonCap

namespace OrientedFacialPentagonCap

variable {data : Data G}

/-- The named facial pentagon is a pure face of its own cap-vertex side. -/
theorem namedFace_mem_allOnVertexSupport (cap : OrientedFacialPentagonCap data) :
    dartOrbitFace data.toRotationSystem cap.toFacialPentagonCap.faceDart ∈
      orbitFacesAllOnSide data.toRotationSystem
        (fun vertex => vertex ∈ cap.toFacialPentagonCap.toPentagonCap.vertexSupport) := by
  rw [mem_orbitFacesAllOnSide_iff]
  intro dart hdart
  have hedge : data.toRotationSystem.edgeOf dart ∈
      data.toRotationSystem.faceEdges cap.toFacialPentagonCap.faceDart := by
    apply (data.toRotationSystem.mem_faceEdges_iff).2
    refine ⟨dart, ?_, rfl⟩
    rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit]
    exact hdart
  rcases (cap.toFacialPentagonCap.mem_faceEdges_iff _).1 hedge with ⟨step, hstep⟩
  have hvertex : data.toRotationSystem.vertOf dart ∈
      (cap.toFacialPentagonCap.toPentagonCap.cycleEdge step).1 := by
    have hendpoint : data.toRotationSystem.vertOf dart ∈
        data.toRotationSystem.endpoints
          (data.toRotationSystem.edgeOf dart) := by
      apply (data.toRotationSystem.mem_endpoints_iff).2
      exact ⟨dart, by simp, rfl⟩
    have hgraphEndpoint : data.toRotationSystem.vertOf dart ∈
        ((data.toRotationSystem.edgeOf dart : G.edgeSet) : Sym2 V) :=
      (mem_simpleGraphRotationSystem_endpoints_iff data
        (data.toRotationSystem.edgeOf dart) _).1 hendpoint
    rw [← congrArg Subtype.val hstep] at hgraphEndpoint
    exact hgraphEndpoint
  rcases cap.toFacialPentagonCap.toPentagonCap.cycleEdge_endpoint_eq_vertex
      step _ hvertex with
    ⟨vertexStep, hvertexStep⟩
  exact (cap.toFacialPentagonCap.toPentagonCap.mem_vertexSupport_iff _).2
    ⟨vertexStep, hvertexStep⟩

/-- A facial pentagon is the unique ambient face lying wholly on its five
cap vertices. -/
theorem card_orbitFacesAllOnVertexSupport_eq_one
    (cap : OrientedFacialPentagonCap data)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic data.toRotationSystem) :
    (orbitFacesAllOnSide data.toRotationSystem
      (fun vertex => vertex ∈
        cap.toFacialPentagonCap.toPentagonCap.vertexSupport)).card = 1 := by
  have hprimal : (rotationPrimalGraph data.toRotationSystem).Connected := by
    rw [rotationPrimalGraph_toRotationSystem_eq]
    exact hconnected
  have hdual := orbitFaceInteriorDual_connected data.toRotationSystem
    hsphere.cubic hprimal hrotation
  have hsideConnected :
      (G.induce {vertex | vertex ∈
        cap.toFacialPentagonCap.toPentagonCap.vertexSupport}).Connected :=
    GoertzelV24FacialPentagonCapOpenHoleOrbit.OrientedFacialPentagonCap.induce_vertexSupport_connected
      cap
  let support := cap.toFacialPentagonCap.toPentagonCap.vertexSupport
  have hselected : ∃ vertex, vertex ∈ support :=
    ⟨cap.toFacialPentagonCap.toPentagonCap.vertex 0,
      (cap.toFacialPentagonCap.toPentagonCap.mem_vertexSupport_iff _).2
        ⟨0, rfl⟩⟩
  have hretained : ∃ vertex, deletedRegionKeep support vertex :=
    ⟨cap.toFacialPentagonCap.toPentagonCap.spokeOuter 0, by
      exact cap.toFacialPentagonCap.toPentagonCap.spokeOuter_not_mem_vertexSupport 0⟩
  have hdeleted : ∃ vertex, Not (deletedRegionKeep support vertex) := by
    rcases hselected with ⟨vertex, hvertex⟩
    exact ⟨vertex, by simpa [deletedRegionKeep] using hvertex⟩
  rcases cutSideTransitionFaces_nonempty_of_connected data support hconnected
      hretained hdeleted with ⟨touchedFace, htouchedFace⟩
  have hnotPure : ∃ face : OrbitFace data.toRotationSystem,
      face ∉ orbitFacesAllOnSide data.toRotationSystem
        (fun vertex => vertex ∈ support) := by
    refine ⟨touchedFace, ?_⟩
    intro hpure
    have hpureOff : touchedFace ∈ orbitFacesAllOnSide data.toRotationSystem
        (fun vertex => Not (deletedRegionKeep support vertex)) := by
      simpa [deletedRegionKeep] using hpure
    exact (Finset.disjoint_left.1
      (cutSideTransitionFaces_disjoint_allOffSide
        data.toRotationSystem support)) htouchedFace hpureOff
  have hrank := pureSideFace_cycleRankBound_of_connected data htwoSided hdual
    (fun vertex => vertex ∈ support) hsideConnected hnotPure
  have hnamed := namedFace_mem_allOnVertexSupport cap
  have hpositive : 0 < (orbitFacesAllOnSide data.toRotationSystem
      (fun vertex => vertex ∈ support)).card :=
    Finset.card_pos.2 ⟨_, hnamed⟩
  have hvertices : sideVertexCount (fun vertex => vertex ∈ support) = 5 := by
    exact _root_.Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapPairPureFaces.PentagonCap.sideVertexCount_vertexSupport
      cap.toFacialPentagonCap.toPentagonCap
  have hedges : (graphEdgesAllOnSide G
      (fun vertex => vertex ∈ support)).card = 5 := by
    exact _root_.Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapPairPureFaces.PentagonCap.card_graphEdgesAllOnSide_vertexSupport
      cap.toFacialPentagonCap.toPentagonCap
  simpa [support] using (show
    (orbitFacesAllOnSide data.toRotationSystem
      (fun vertex => vertex ∈ support)).card = 1 by omega)

end OrientedFacialPentagonCap

namespace FacialPentagonCapBoundaryWalkPair

variable {data : Data G}

private abbrev pair (caps : FacialPentagonCapBoundaryWalkPair data) :
    PentagonCapPair G := caps.toPentagonCapPair

/-- No ambient edge joins the two cap supports.  The proof reduces arbitrary
support members to the literal `Fin 5` coordinates and uses the simultaneous
opening separation theorem. -/
theorem not_adj_of_mem_innerSupport_of_mem_outerSupport
    (caps : FacialPentagonCapBoundaryWalkPair data)
    {innerVertex outerVertex : V}
    (hinner : innerVertex ∈ (pair caps).inner.vertexSupport)
    (houter : outerVertex ∈ (pair caps).outer.vertexSupport) :
    ¬ G.Adj innerVertex outerVertex := by
  rcases ((pair caps).inner.mem_vertexSupport_iff innerVertex).1 hinner with
    ⟨innerStep, hinnerStep⟩
  rcases ((pair caps).outer.mem_vertexSupport_iff outerVertex).1 houter with
    ⟨outerStep, houterStep⟩
  subst innerVertex
  subst outerVertex
  exact
    GoertzelV24FacialPentagonCapPairDeletedCycle.FacialPentagonCapBoundaryWalkPair.not_adj_inner_outerVertices
      caps innerStep outerStep

/-- On an ambient face wholly supported by the two remote caps, membership in
the inner cap is constant around the facial permutation. -/
theorem innerSupport_eq_on_face_allOn_deletedSupport
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (face : OrbitFace data.toRotationSystem)
    (hpure : face ∈ orbitFacesAllOnSide data.toRotationSystem
      (fun vertex => vertex ∈ (pair caps).deletedVertexSupport))
    (root : data.toRotationSystem.D)
    (hroot : dartOrbitFace data.toRotationSystem root = face)
    {dart : data.toRotationSystem.D}
    (hsame : data.toRotationSystem.phi.SameCycle root dart) :
    (data.toRotationSystem.vertOf root ∈
        (pair caps).inner.vertexSupport) =
      (data.toRotationSystem.vertOf dart ∈
        (pair caps).inner.vertexSupport) := by
  apply predicate_eq_of_sameCycle_of_step_eq
    data.toRotationSystem.phi
    (fun point => data.toRotationSystem.vertOf point ∈
      (pair caps).inner.vertexSupport)
    root
  · intro point hpointCycle
    have hpointFace : dartOrbitFace data.toRotationSystem point = face :=
      (Quotient.sound hpointCycle.symm).trans hroot
    have hpointMem : point ∈
        orbitFaceDarts data.toRotationSystem face :=
      (mem_orbitFaceDarts_iff data.toRotationSystem face point).2 hpointFace
    have hnextFace : dartOrbitFace data.toRotationSystem
        (data.toRotationSystem.phi point) = face :=
      (dartOrbitFace_phi_eq data.toRotationSystem point).trans hpointFace
    have hnextMem : data.toRotationSystem.phi point ∈
        orbitFaceDarts data.toRotationSystem face :=
      (mem_orbitFaceDarts_iff data.toRotationSystem face _).2 hnextFace
    have hpointDeleted :=
      (mem_orbitFacesAllOnSide_iff data.toRotationSystem _ face).1 hpure
        point hpointMem
    have hnextDeleted :=
      (mem_orbitFacesAllOnSide_iff data.toRotationSystem _ face).1 hpure
        (data.toRotationSystem.phi point) hnextMem
    change data.toRotationSystem.vertOf point ∈
        (pair caps).inner.vertexSupport ∪
          (pair caps).outer.vertexSupport at hpointDeleted
    change data.toRotationSystem.vertOf (data.toRotationSystem.phi point) ∈
        (pair caps).inner.vertexSupport ∪
          (pair caps).outer.vertexSupport at hnextDeleted
    rw [Finset.mem_union] at hpointDeleted hnextDeleted
    have hadj : G.Adj
        (data.toRotationSystem.vertOf point)
        (data.toRotationSystem.vertOf
          (data.toRotationSystem.phi point)) := by
      rw [data.toRotationSystem.vert_phi_eq_vert_alpha]
      simpa [SimpleGraphDartRotation.Data.toRotationSystem_vertOf,
        SimpleGraphDartRotation.Data.toRotationSystem_alpha] using point.edge_mem
    apply propext
    constructor
    · intro hinner
      rcases hnextDeleted with hnextInner | hnextOuter
      · exact hnextInner
      · exact False.elim
          (not_adj_of_mem_innerSupport_of_mem_outerSupport
            caps hinner hnextOuter hadj)
    · intro hnextInner
      rcases hpointDeleted with hpointInner | hpointOuter
      · exact hpointInner
      · exact False.elim
          (not_adj_of_mem_innerSupport_of_mem_outerSupport
            caps hnextInner hpointOuter (G.adj_symm hadj))
  · exact hsame

/-- A face wholly supported by the two separated caps is wholly supported by
exactly one of them. -/
theorem allOn_deletedSupport_iff_allOn_inner_or_outer
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (face : OrbitFace data.toRotationSystem) :
    face ∈ orbitFacesAllOnSide data.toRotationSystem
        (fun vertex => vertex ∈ (pair caps).deletedVertexSupport) ↔
      face ∈ orbitFacesAllOnSide data.toRotationSystem
          (fun vertex => vertex ∈ (pair caps).inner.vertexSupport) ∨
        face ∈ orbitFacesAllOnSide data.toRotationSystem
          (fun vertex => vertex ∈ (pair caps).outer.vertexSupport) := by
  constructor
  · intro hpure
    rcases exists_dartOrbitFace_eq data.toRotationSystem face with
      ⟨root, hroot⟩
    have hrootMem : root ∈ orbitFaceDarts data.toRotationSystem face :=
      (mem_orbitFaceDarts_iff data.toRotationSystem face root).2 hroot
    have hrootDeleted :=
      (mem_orbitFacesAllOnSide_iff data.toRotationSystem _ face).1 hpure
        root hrootMem
    change data.toRotationSystem.vertOf root ∈
        (pair caps).inner.vertexSupport ∪
          (pair caps).outer.vertexSupport at hrootDeleted
    rw [Finset.mem_union] at hrootDeleted
    rcases hrootDeleted with hrootInner | hrootOuter
    · left
      rw [mem_orbitFacesAllOnSide_iff]
      intro dart hdart
      have hsame : data.toRotationSystem.phi.SameCycle root dart := by
        rw [← data.toRotationSystem.mem_faceOrbit]
        rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit]
        simpa [hroot] using hdart
      have heq := innerSupport_eq_on_face_allOn_deletedSupport
        caps face hpure root hroot hsame
      rw [← heq]
      exact hrootInner
    · right
      rw [mem_orbitFacesAllOnSide_iff]
      intro dart hdart
      have hsame : data.toRotationSystem.phi.SameCycle root dart := by
        rw [← data.toRotationSystem.mem_faceOrbit]
        rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit]
        simpa [hroot] using hdart
      have heq := innerSupport_eq_on_face_allOn_deletedSupport
        caps face hpure root hroot hsame
      have hnotInnerRoot : data.toRotationSystem.vertOf root ∉
          (pair caps).inner.vertexSupport := by
        intro hinnerRoot
        exact (Finset.disjoint_left.1 (pair caps).vertexSupport_disjoint)
          hinnerRoot hrootOuter
      have hnotInnerDart : data.toRotationSystem.vertOf dart ∉
          (pair caps).inner.vertexSupport := by
        rwa [heq] at hnotInnerRoot
      have hdartDeleted :=
        (mem_orbitFacesAllOnSide_iff data.toRotationSystem _ face).1 hpure
          dart hdart
      change data.toRotationSystem.vertOf dart ∈
          (pair caps).inner.vertexSupport ∪
            (pair caps).outer.vertexSupport at hdartDeleted
      exact (Finset.mem_union.1 hdartDeleted).resolve_left hnotInnerDart
  · rintro (hinner | houter)
    · rw [mem_orbitFacesAllOnSide_iff] at hinner ⊢
      intro dart hdart
      exact Finset.mem_union_left _ (hinner dart hdart)
    · rw [mem_orbitFacesAllOnSide_iff] at houter ⊢
      intro dart hdart
      exact Finset.mem_union_right _ (houter dart hdart)

/-- Pure faces of the simultaneous deleted support are exactly the union of
the pure faces of its two cap components. -/
theorem orbitFacesAllOnSide_deletedSupport_eq_union
    (caps : FacialPentagonCapBoundaryWalkPair data) :
    orbitFacesAllOnSide data.toRotationSystem
        (fun vertex => vertex ∈ (pair caps).deletedVertexSupport) =
      orbitFacesAllOnSide data.toRotationSystem
          (fun vertex => vertex ∈ (pair caps).inner.vertexSupport) ∪
        orbitFacesAllOnSide data.toRotationSystem
          (fun vertex => vertex ∈ (pair caps).outer.vertexSupport) := by
  ext face
  rw [Finset.mem_union]
  exact allOn_deletedSupport_iff_allOn_inner_or_outer caps face

/-- The two pure-face families of the separated cap supports are disjoint. -/
theorem orbitFacesAllOnSide_inner_disjoint_outer
    (caps : FacialPentagonCapBoundaryWalkPair data) :
    Disjoint
      (orbitFacesAllOnSide data.toRotationSystem
        (fun vertex => vertex ∈ (pair caps).inner.vertexSupport))
      (orbitFacesAllOnSide data.toRotationSystem
        (fun vertex => vertex ∈ (pair caps).outer.vertexSupport)) := by
  rw [Finset.disjoint_left]
  intro face hinner houter
  rcases exists_dartOrbitFace_eq data.toRotationSystem face with
    ⟨dart, hdartFace⟩
  have hdart : dart ∈ orbitFaceDarts data.toRotationSystem face :=
    (mem_orbitFaceDarts_iff data.toRotationSystem face dart).2 hdartFace
  have hinnerVertex :=
    (mem_orbitFacesAllOnSide_iff data.toRotationSystem _ face).1 hinner
      dart hdart
  have houterVertex :=
    (mem_orbitFacesAllOnSide_iff data.toRotationSystem _ face).1 houter
      dart hdart
  exact (Finset.disjoint_left.1 (pair caps).vertexSupport_disjoint)
    hinnerVertex houterVertex

/-- Exactly two ambient faces lie wholly in the union of the two facial
pentagon supports: the named inner and outer pentagon faces. -/
theorem card_orbitFacesAllOnDeletedSupport_eq_two
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic data.toRotationSystem) :
    (orbitFacesAllOnSide data.toRotationSystem
      (fun vertex => vertex ∈ (pair caps).deletedVertexSupport)).card = 2 := by
  rw [orbitFacesAllOnSide_deletedSupport_eq_union caps,
    Finset.card_union_of_disjoint
      (orbitFacesAllOnSide_inner_disjoint_outer caps)]
  have hinner :=
    OrientedFacialPentagonCap.card_orbitFacesAllOnVertexSupport_eq_one
      caps.toOrientedFacialPentagonCapPair.innerOriented
      hsphere htwoSided hconnected hrotation
  have houter :=
    OrientedFacialPentagonCap.card_orbitFacesAllOnVertexSupport_eq_one
      caps.toOrientedFacialPentagonCapPair.outerOriented
      hsphere htwoSided hconnected hrotation
  change (orbitFacesAllOnSide data.toRotationSystem
    (fun vertex => vertex ∈ (pair caps).inner.vertexSupport)).card = 1 at hinner
  change (orbitFacesAllOnSide data.toRotationSystem
    (fun vertex => vertex ∈ (pair caps).outer.vertexSupport)).card = 1 at houter
  simpa using congrArg₂ (fun left right : Nat => left + right) hinner houter

end FacialPentagonCapBoundaryWalkPair

end

end GoertzelV24FacialPentagonCapPairPureFaces

end Mettapedia.GraphTheory.FourColor
