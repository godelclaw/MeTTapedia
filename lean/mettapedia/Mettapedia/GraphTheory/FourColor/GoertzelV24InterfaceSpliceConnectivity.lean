import Mettapedia.GraphTheory.FourColor.GoertzelV24DualPathConnectivityProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24SquareGraphComposition

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24InterfaceSpliceConnectivity

open GoertzelV24CorridorProfile
open GoertzelV24DualPathConnectivityProfile
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24WindingClassification
open SimpleGraph

/-- Replacing one graph factor by another with the same component relation on
an interface preserves reachability after union with a fixed exterior factor.
The two switch hypotheses say that a walk can change factors only at the
interface; they are discharged from concrete region intersections below. -/
theorem reachable_sup_iff_of_interface_component_equiv
    {N : Type*} (exterior left right : SimpleGraph N)
    (interface : N → Prop)
    (hswitchLeft : ∀ {x middle y}, x ≠ middle → middle ≠ y →
      exterior.Reachable x middle → left.Reachable middle y →
      interface middle)
    (hswitchRight : ∀ {x middle y}, x ≠ middle → middle ≠ y →
      exterior.Reachable x middle → right.Reachable middle y →
      interface middle)
    (hcomponents : ∀ u v : Subtype interface,
      left.Reachable u v ↔ right.Reachable u v)
    {start finish : N} (hstart : interface start)
    (hfinish : interface finish) :
    (exterior ⊔ left).Reachable start finish ↔
      (exterior ⊔ right).Reachable start finish := by
  rw [reachable_sup_iff_subtype_componentClosure
      exterior left interface start finish hstart hfinish hswitchLeft,
    reachable_sup_iff_subtype_componentClosure
      exterior right interface start finish hstart hfinish hswitchRight]
  constructor
  · intro hreach
    exact hreach.mono fun u v hstep =>
      hstep.elim Or.inl (fun hlocal => Or.inr ((hcomponents u v).1 hlocal))
  · intro hreach
    exact hreach.mono fun u v hstep =>
      hstep.elim Or.inl (fun hlocal => Or.inr ((hcomponents u v).2 hlocal))

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- A nontrivial component switch between two regional tracked-edge graphs
can occur only on an edge belonging to both regions. -/
theorem regionalTrackedEdgeGraph_switch_mem_inter
    (RS : RotationSystem V E) (leftRegion rightRegion : Finset E)
    (C : E → Color) (a b : Color) {x middle y : E}
    (hx : x ≠ middle) (hy : middle ≠ y)
    (hleft : (regionalTrackedEdgeGraph RS leftRegion C a b).Reachable x middle)
    (hright : (regionalTrackedEdgeGraph RS rightRegion C a b).Reachable middle y) :
    middle ∈ leftRegion ∩ rightRegion := by
  let leftGraph := regionalTrackedEdgeGraph RS leftRegion C a b
  let rightGraph := regionalTrackedEdgeGraph RS rightRegion C a b
  have hleftSupport : middle ∈ leftGraph.support :=
    SimpleGraph.mem_support_of_reachable hx.symm hleft.symm
  have hrightSupport : middle ∈ rightGraph.support :=
    SimpleGraph.mem_support_of_reachable hy hright
  rcases (SimpleGraph.mem_support leftGraph).1 hleftSupport with
    ⟨leftNeighbor, hleftAdj⟩
  rcases (SimpleGraph.mem_support rightGraph).1 hrightSupport with
    ⟨rightNeighbor, hrightAdj⟩
  exact Finset.mem_inter.2 ⟨hleftAdj.2.1, hrightAdj.2.1⟩

/-- Concrete regional splice theorem. If each candidate interior overlaps a
fixed exterior only on the cut, and the two interiors induce the same
component relation on cut edges, substituting either interior preserves
tracked reachability between all cut edges. -/
theorem regionalTrackedEdgeGraph_sup_reachable_iff_of_cut_connectivity
    (RS : RotationSystem V E)
    (exteriorRegion leftRegion rightRegion cut : Finset E)
    (C : E → Color) (a b : Color)
    (hleftMeet : exteriorRegion ∩ leftRegion ⊆ cut)
    (hrightMeet : exteriorRegion ∩ rightRegion ⊆ cut)
    (hcomponents : ∀ u v : E, u ∈ cut → v ∈ cut →
      ((regionalTrackedEdgeGraph RS leftRegion C a b).Reachable u v ↔
        (regionalTrackedEdgeGraph RS rightRegion C a b).Reachable u v))
    {start finish : E} (hstart : start ∈ cut) (hfinish : finish ∈ cut) :
    (regionalTrackedEdgeGraph RS exteriorRegion C a b ⊔
        regionalTrackedEdgeGraph RS leftRegion C a b).Reachable start finish ↔
      (regionalTrackedEdgeGraph RS exteriorRegion C a b ⊔
        regionalTrackedEdgeGraph RS rightRegion C a b).Reachable start finish := by
  apply reachable_sup_iff_of_interface_component_equiv
    (regionalTrackedEdgeGraph RS exteriorRegion C a b)
    (regionalTrackedEdgeGraph RS leftRegion C a b)
    (regionalTrackedEdgeGraph RS rightRegion C a b)
    (fun edge => edge ∈ cut)
  · intro x middle y hx hy hexterior hleft
    exact hleftMeet (regionalTrackedEdgeGraph_switch_mem_inter
      RS exteriorRegion leftRegion C a b hx hy hexterior hleft)
  · intro x middle y hx hy hexterior hright
    exact hrightMeet (regionalTrackedEdgeGraph_switch_mem_inter
      RS exteriorRegion rightRegion C a b hx hy hexterior hright)
  · intro u v
    exact hcomponents u.val v.val u.property v.property
  · exact hstart
  · exact hfinish

/-- Equality of two computed dual-path profiles gives equality of raw
regional component relations on every crossing edge, including the reflexive
untracked case suppressed by the guarded Boolean matrix. -/
theorem dualPathCutProfile_eq_implies_crossing_reachability_iff
    (RS : RotationSystem V E) (leftRegion rightRegion : Finset E)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (walk : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start finish)
    (hleftCrossing : dualWalkCrossingEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk ⊆ leftRegion)
    (hrightCrossing : dualWalkCrossingEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk ⊆ rightRegion)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (hprofiles : dualPathCutProfile RS leftRegion hunique walk C hC =
      dualPathCutProfile RS rightRegion hunique walk C hC)
    (pair : TrackedColorPair) (left right : Fin walk.length) :
    let colors := trackedColorPairColors pair
    let leftEdge := dualWalkCrossingEdge (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk left
    let rightEdge := dualWalkCrossingEdge (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk right
    (regionalTrackedEdgeGraph RS leftRegion C colors.1 colors.2).Reachable
        leftEdge rightEdge ↔
      (regionalTrackedEdgeGraph RS rightRegion C colors.1 colors.2).Reachable
        leftEdge rightEdge := by
  dsimp only
  let leftEdge := dualWalkCrossingEdge (orbitFaceBoundary RS)
    (Finset.univ : Finset (OrbitFace RS)) hunique walk left
  let rightEdge := dualWalkCrossingEdge (orbitFaceBoundary RS)
    (Finset.univ : Finset (OrbitFace RS)) hunique walk right
  change
    (regionalTrackedEdgeGraph RS leftRegion C
      (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2).Reachable leftEdge rightEdge ↔
    (regionalTrackedEdgeGraph RS rightRegion C
      (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2).Reachable leftEdge rightEdge
  have hleftMem : leftEdge ∈ leftRegion := hleftCrossing
    ((mem_dualWalkCrossingEdges_iff (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk leftEdge).2
        ⟨left, rfl⟩)
  have hrightMem : rightEdge ∈ leftRegion := hleftCrossing
    ((mem_dualWalkCrossingEdges_iff (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk rightEdge).2
        ⟨right, rfl⟩)
  have hleftMem' : leftEdge ∈ rightRegion := hrightCrossing
    ((mem_dualWalkCrossingEdges_iff (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk leftEdge).2
        ⟨left, rfl⟩)
  have hrightMem' : rightEdge ∈ rightRegion := hrightCrossing
    ((mem_dualWalkCrossingEdges_iff (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk rightEdge).2
        ⟨right, rfl⟩)
  have hmatrix :
      regionalTrackedConnectivity RS leftRegion C pair leftEdge rightEdge =
        regionalTrackedConnectivity RS rightRegion C pair leftEdge rightEdge := by
    have h := congrFun (congrFun (congrFun
      (congrArg CorridorCutProfile.strandConnected hprofiles) pair)
        (.inl left)) (.inl right)
    exact h
  by_cases hedges : leftEdge = rightEdge
  · constructor
    · intro _
      rw [← hedges]
    · intro _
      rw [← hedges]
  · constructor
    · intro hreach
      have htrue := regionalTrackedConnectivity_eq_true_of_reachable_of_ne
        RS leftRegion C pair leftEdge rightEdge hleftMem hrightMem hedges hreach
      have htrue' :
          regionalTrackedConnectivity RS rightRegion C pair leftEdge rightEdge =
            true := hmatrix ▸ htrue
      exact (regionalTrackedConnectivity_eq_true_iff
        RS rightRegion C pair leftEdge rightEdge).1 htrue' |>.2.2.2.2
    · intro hreach
      have htrue := regionalTrackedConnectivity_eq_true_of_reachable_of_ne
        RS rightRegion C pair leftEdge rightEdge hleftMem' hrightMem' hedges hreach
      have htrue' :
          regionalTrackedConnectivity RS leftRegion C pair leftEdge rightEdge =
            true := hmatrix.symm ▸ htrue
      exact (regionalTrackedConnectivity_eq_true_iff
        RS leftRegion C pair leftEdge rightEdge).1 htrue' |>.2.2.2.2

/-- Graph-level component splice for a computed dual-path profile. The same
exterior factor can be glued to either regional factor whenever their only
overlap is the actual crossing set; profile equality then preserves the
complete tracked component relation visible at every ordered crossing port.
This theorem works on one fixed ambient edge carrier; construction of the
shortened rotation system and its face embedding is a separate step. -/
theorem dualPathCutProfile_eq_preserves_regional_splice_reachability
    (RS : RotationSystem V E)
    (exteriorRegion leftRegion rightRegion : Finset E)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (walk : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start finish)
    (hleftCrossing : dualWalkCrossingEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk ⊆ leftRegion)
    (hrightCrossing : dualWalkCrossingEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk ⊆ rightRegion)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (hprofiles : dualPathCutProfile RS leftRegion hunique walk C hC =
      dualPathCutProfile RS rightRegion hunique walk C hC)
    (hleftMeet : exteriorRegion ∩ leftRegion ⊆
      dualWalkCrossingEdges (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) hunique walk)
    (hrightMeet : exteriorRegion ∩ rightRegion ⊆
      dualWalkCrossingEdges (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) hunique walk)
    (pair : TrackedColorPair) (left right : Fin walk.length) :
    let colors := trackedColorPairColors pair
    let leftEdge := dualWalkCrossingEdge (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk left
    let rightEdge := dualWalkCrossingEdge (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk right
    (regionalTrackedEdgeGraph RS exteriorRegion C colors.1 colors.2 ⊔
        regionalTrackedEdgeGraph RS leftRegion C colors.1 colors.2).Reachable
          leftEdge rightEdge ↔
      (regionalTrackedEdgeGraph RS exteriorRegion C colors.1 colors.2 ⊔
        regionalTrackedEdgeGraph RS rightRegion C colors.1 colors.2).Reachable
          leftEdge rightEdge := by
  dsimp only
  refine regionalTrackedEdgeGraph_sup_reachable_iff_of_cut_connectivity
    RS exteriorRegion leftRegion rightRegion
    (dualWalkCrossingEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk)
    C (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
    hleftMeet hrightMeet ?_ ?_ ?_
  · intro first second hfirst hsecond
    rcases (mem_dualWalkCrossingEdges_iff (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk first).1 hfirst with
      ⟨firstStep, rfl⟩
    rcases (mem_dualWalkCrossingEdges_iff (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk second).1 hsecond with
      ⟨secondStep, rfl⟩
    exact dualPathCutProfile_eq_implies_crossing_reachability_iff
      RS leftRegion rightRegion hunique walk hleftCrossing hrightCrossing
      C hC hprofiles pair firstStep secondStep
  · exact (mem_dualWalkCrossingEdges_iff (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk _).2 ⟨left, rfl⟩
  · exact (mem_dualWalkCrossingEdges_iff (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk _).2 ⟨right, rfl⟩

end

end GoertzelV24InterfaceSpliceConnectivity

end Mettapedia.GraphTheory.FourColor
