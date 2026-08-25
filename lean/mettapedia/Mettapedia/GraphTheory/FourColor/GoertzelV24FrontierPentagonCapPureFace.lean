import Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapPairPureFaces
import Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapPairRemoteSeparation
import Mettapedia.GraphTheory.FourColor.GoertzelV24FrontierPentagonCapFaceCounts

/-!
# The unique pure face of Addendum V's deleted pentagon

The earlier two-cap laboratory bounded pure deleted faces with a global
spherical cycle-rank argument.  Addendum V's actual frontier is already open,
so that argument cannot be used there.  The one-cap statement is nevertheless
local.

At each cap vertex the named facial orientation follows the two pentagon
edges.  In the reverse orientation, cap-local cubicity forces the next turn
onto the unique spoke.  The following face step is therefore based outside
the cap.  Hence no second ambient face can be supported wholly by the five cap
vertices, and the named facial pentagon is the unique pure deleted face.

This is the last local face-count atom of the one-cap surgery.  It does not
derive the collar-uniqueness premise, an Euler equation, or the source-selected
frontier tangle.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FrontierPentagonCapPureFace

open SimpleGraph
open SimpleGraphDartRotation
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24FacialPentagonCapDeletedBoundaryCycle
open GoertzelV24FacialPentagonCapOpenBoundary
open GoertzelV24FacialPentagonCapPairPureFaces
open GoertzelV24FacialPentagonCapPairRemoteSeparation
open GoertzelV24FrontierPentagonCapInnerFace
open GoertzelV24FrontierPentagonCapOpening
open GoertzelV24PentagonCapOpening
open GoertzelV24PlanarBondBoundaryOrder

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

attribute [-instance]
  GoertzelV24OpenRegionRotation.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype

variable {data : Data G}

private abbrev capOf (walk : FacialPentagonCapBoundaryWalk data) : PentagonCap G :=
  walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap

/-- A pure cap-side face cannot be rooted in the reverse orientation of a
named pentagon edge: two face steps would reach the retained spoke endpoint. -/
private theorem dartOrbitFace_eq_named_of_allOnVertexSupport
    (frontier : FrontierBoundaryData G outerCount)
    (hfrontier : frontier.WellFormed)
    (walk : FacialPentagonCapBoundaryWalk data)
    (hinterior : frontier.InteriorPentagonCap (capOf walk))
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (root : G.Dart)
    (hpure : dartOrbitFace data.toRotationSystem root ∈
      orbitFacesAllOnSide data.toRotationSystem
        (fun vertex => vertex ∈ (capOf walk).vertexSupport)) :
    dartOrbitFace data.toRotationSystem root =
      dartOrbitFace data.toRotationSystem
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.faceDart := by
  let RS := data.toRotationSystem
  let cap := capOf walk
  have hrootMem : root ∈ orbitFaceDarts RS (dartOrbitFace RS root) := by
    exact (mem_orbitFaceDarts_iff RS (dartOrbitFace RS root) root).2 rfl
  have hphiMem : RS.phi root ∈ orbitFaceDarts RS (dartOrbitFace RS root) := by
    exact (mem_orbitFaceDarts_iff RS (dartOrbitFace RS root) (RS.phi root)).2
      (dartOrbitFace_phi_eq RS root)
  have hrootInside : root.fst ∈ cap.vertexSupport :=
    (mem_orbitFacesAllOnSide_iff RS _ _).1 hpure root hrootMem
  have hphiInside : (RS.phi root).fst ∈ cap.vertexSupport :=
    (mem_orbitFacesAllOnSide_iff RS _ _).1 hpure (RS.phi root) hphiMem
  have halphaInside : (RS.alpha root).fst ∈ cap.vertexSupport := by
    have hbase := RS.vert_phi_eq_vert_alpha root
    change (RS.phi root).fst = (RS.alpha root).fst at hbase
    rw [← hbase]
    exact hphiInside
  have hedgeAll : root.edge ∈
      graphEdgesAllOnSide G (fun vertex => vertex ∈ cap.vertexSupport) := by
    apply (mem_graphEdgesAllOnSide_iff G _ root.edge).2
    refine ⟨root.edge_mem, ?_⟩
    intro vertex hvertex
    rcases (Sym2.mem_iff.1 hvertex) with rfl | rfl
    · exact hrootInside
    · exact halphaInside
  rw [PentagonCap.graphEdgesAllOnSide_vertexSupport_eq_cycleSupport] at hedgeAll
  rcases Finset.mem_image.1 hedgeAll with ⟨cycleEdge, hcycleEdge, hcycleValue⟩
  rcases Finset.mem_map.1 hcycleEdge with ⟨step, -, hstep⟩
  have hedge : root.edge = (walk.boundaryDart step).edge := by
    have hstepValue := congrArg Subtype.val hstep
    have hboundaryValue := congrArg Subtype.val (walk.boundaryDart_edge step)
    calc
      root.edge = (cycleEdge : G.edgeSet).1 := hcycleValue.symm
      _ = (cap.cycleEdge step).1 := hstepValue.symm
      _ = (walk.boundaryDart step).edge := by
        simpa [RS, SimpleGraphDartRotation.Data.toRotationSystem_edgeOf]
          using hboundaryValue.symm
  rcases (SimpleGraph.dart_edge_eq_iff root (walk.boundaryDart step)).1 hedge with
    hforward | hreverse
  · rw [hforward]
    exact FacialPentagonCapBoundaryWalk.dartOrbitFace_boundaryDart_eq_faceDart
      walk step
  · exfalso
    have hcubic := capVerticesCubic_of_frontierWellFormed
      frontier hfrontier walk hinterior
    let spoke := (capDeletedBoundaryDart data cap step).1.1
    have hrootStep : RS.phi root = spoke := by
      rw [hreverse]
      change RS.phi (RS.alpha (walk.boundaryDart step)) = spoke
      rw [RotationSystem.phi_apply, RS.alpha_involutive]
      exact rho_boundaryDart_eq_capDeletedBoundaryDart walk hcubic hrotation step
    have hspokeNextMem : RS.phi spoke ∈
        orbitFaceDarts RS (dartOrbitFace RS root) := by
      rw [mem_orbitFaceDarts_iff]
      calc
        dartOrbitFace RS (RS.phi spoke) = dartOrbitFace RS spoke :=
          dartOrbitFace_phi_eq RS spoke
        _ = dartOrbitFace RS (RS.phi root) := by rw [hrootStep]
        _ = dartOrbitFace RS root := dartOrbitFace_phi_eq RS root
    have hspokeNextInside : (RS.phi spoke).fst ∈ cap.vertexSupport :=
      (mem_orbitFacesAllOnSide_iff RS _ _).1 hpure
        (RS.phi spoke) hspokeNextMem
    have hspokeNextBase : (RS.phi spoke).fst = cap.spokeOuter step := by
      have hbase := RS.vert_phi_eq_vert_alpha spoke
      change (RS.phi spoke).fst = (RS.alpha spoke).fst at hbase
      calc
        (RS.phi spoke).fst = (RS.alpha spoke).fst := hbase
        _ = spoke.snd := by
          simp [RS, SimpleGraphDartRotation.Data.toRotationSystem_alpha]
        _ = cap.spokeOuter step := capDeletedBoundaryDart_snd data cap step
    apply cap.spokeOuter_not_mem_vertexSupport step
    rw [← hspokeNextBase]
    exact hspokeNextInside

/-- **Addendum V pure cap face.** On the literal already-open frontier, the
named facial pentagon is the unique ambient face wholly supported by the five
cap vertices.  Only cap-local cubicity and the recorded vertex rotation are
used. -/
theorem card_orbitFacesAllOnVertexSupport_eq_one
    (frontier : FrontierBoundaryData G outerCount)
    (hfrontier : frontier.WellFormed)
    (walk : FacialPentagonCapBoundaryWalk data)
    (hinterior : frontier.InteriorPentagonCap (capOf walk))
    (hrotation : VertexRotationCyclic data.toRotationSystem) :
    (orbitFacesAllOnSide data.toRotationSystem
      (fun vertex => vertex ∈ (capOf walk).vertexSupport)).card = 1 := by
  let named := dartOrbitFace data.toRotationSystem
    walk.toOrientedFacialPentagonCap.toFacialPentagonCap.faceDart
  have hset : orbitFacesAllOnSide data.toRotationSystem
      (fun vertex => vertex ∈ (capOf walk).vertexSupport) = {named} := by
    ext face
    rw [Finset.mem_singleton]
    constructor
    · intro hpure
      obtain ⟨root, rfl⟩ := exists_dartOrbitFace_eq data.toRotationSystem face
      exact dartOrbitFace_eq_named_of_allOnVertexSupport frontier hfrontier walk
        hinterior hrotation root hpure
    · intro hface
      rw [hface]
      exact OrientedFacialPentagonCap.namedFace_mem_allOnVertexSupport
        walk.toOrientedFacialPentagonCap
  rw [hset]
  simp

end

end GoertzelV24FrontierPentagonCapPureFace

end Mettapedia.GraphTheory.FourColor
