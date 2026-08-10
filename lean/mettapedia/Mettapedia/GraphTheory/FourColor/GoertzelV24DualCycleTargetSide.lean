import Mettapedia.GraphTheory.FourColor.GoertzelV24DualCycleBoundaryFaceOrientation
import Mettapedia.GraphTheory.FourColor.GoertzelV24FiniteDeletionCyclicCut
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceArcWalk

/-!
# Target-side face arcs of a dual-cycle wall

Consecutive crossings of a facial-dual cycle meet one literal face.  Removing
the two crossing edges leaves the complementary facial arc, which joins the
two target-side endpoints without crossing the wall.  This is the local
graph-theoretic piece of the Jordan-side construction used by the source
crosscut splice.

No profile, catalogue, or covering-style reduction is involved here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DualCycleTargetSide

open GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceDualConnectedness
open GoertzelV24DualPathTransversal
open GoertzelV24DualCycleBond
open GoertzelV24DualCycleBoundaryFaceOrientation
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24OrbitFaceArcWalk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24OrbitFaceWalk
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/- Keep the finite edge carrier aligned with the crosscut and rotation-system
   modules.  Several imported splice files install a proposition-indexed
   instance; the ordinary subtype instance is the one used by `Data G`. -/
local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The actual source-face dart of a closed facial-dual step.  The open
crosscut API carries this object already; the closed-loop side construction
uses the same literal incidence witness rather than choosing an endpoint. -/
theorem exists_dualWalkSourceFaceDart
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (walk : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start finish)
    (step : Fin walk.length) :
    ∃ dart : RS.D,
      dart ∈ orbitFaceDarts RS (walk.getVert step.val).1 ∧
        RS.edgeOf dart = dualWalkCrossingEdge (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS)) hunique walk step := by
  exact (mem_orbitFaceBoundary_iff RS
    (walk.getVert step.val).1
    (dualWalkCrossingEdge (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk step)).1
        (dualWalkCrossingEdge_mem_leftFace (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS)) hunique walk step)

/-- Chosen source-face occurrence of a closed facial-dual step. -/
noncomputable def dualWalkSourceFaceDart
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (walk : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start finish)
    (step : Fin walk.length) : RS.D :=
  Classical.choose (exists_dualWalkSourceFaceDart hunique walk step)

theorem dualWalkSourceFaceDart_face
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (walk : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start finish)
    (step : Fin walk.length) :
    dartOrbitFace RS (dualWalkSourceFaceDart hunique walk step) =
      (walk.getVert step.val).1 := by
  exact (mem_orbitFaceDarts_iff RS
    (walk.getVert step.val).1
    (dualWalkSourceFaceDart hunique walk step)).1
      (Classical.choose_spec (exists_dualWalkSourceFaceDart hunique walk step)).1

theorem dualWalkSourceFaceDart_edge
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (walk : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start finish)
    (step : Fin walk.length) :
    RS.edgeOf (dualWalkSourceFaceDart hunique walk step) =
      dualWalkCrossingEdge (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) hunique walk step :=
  (Classical.choose_spec (exists_dualWalkSourceFaceDart hunique walk step)).2

/-- In a two-sided map, reversing the literal source-face dart gives the
unique target-face dart of the same closed dual step. -/
theorem alpha_dualWalkSourceFaceDart_face
    {RS : RotationSystem V G.edgeSet}
    (htwoSided : OrbitFacesTwoSided RS)
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (walk : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start finish)
    (step : Fin walk.length) :
    dartOrbitFace RS (RS.alpha (dualWalkSourceFaceDart hunique walk step)) =
      (walk.getVert (step.val + 1)).1 := by
  let sourceFace := (walk.getVert step.val).1
  let targetFace := (walk.getVert (step.val + 1)).1
  let dart := dualWalkSourceFaceDart hunique walk step
  have hsourceTargetNe : sourceFace ≠ targetFace := by
    intro hfaces
    exact (walk.adj_getVert_succ step.isLt).ne (Subtype.ext hfaces)
  have hsourceEdge : RS.edgeOf dart =
      dualWalkCrossingEdge (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) hunique walk step :=
    dualWalkSourceFaceDart_edge hunique walk step
  have hsourceBoundary : RS.edgeOf dart ∈ orbitFaceBoundary RS sourceFace := by
    rw [hsourceEdge]
    simpa [sourceFace] using
      (dualWalkCrossingEdge_mem_leftFace (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) hunique walk step)
  have htargetBoundary : RS.edgeOf dart ∈ orbitFaceBoundary RS targetFace := by
    rw [hsourceEdge]
    simpa [targetFace] using
      (dualWalkCrossingEdge_mem_rightFace (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) hunique walk step)
  have halphaBoundary : RS.edgeOf dart ∈
      orbitFaceBoundary RS (dartOrbitFace RS (RS.alpha dart)) := by
    rw [← RS.edge_alpha dart]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS (RS.alpha dart)
  have halphaCases :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS))
      (orbitFace_incidence_le_two RS)
      (by simpa [sourceFace] using (show sourceFace ∈ Finset.univ from Finset.mem_univ _))
      (by simpa [targetFace] using (show targetFace ∈ Finset.univ from Finset.mem_univ _))
      (by simp)
      hsourceTargetNe hsourceBoundary htargetBoundary halphaBoundary
  rcases halphaCases with halphaSource | halphaTarget
  · exact (htwoSided dart
      ((dualWalkSourceFaceDart_face hunique walk step).trans
        halphaSource.symm)).elim
  · exact halphaTarget

/-- The independently chosen target-face incidence dart is forced to be the
alpha-opposite of the source-face dart.  This removes any arbitrary endpoint
choice before the deleted-edge component argument begins. -/
theorem dualWalkTargetFaceDart_eq_alpha_sourceFaceDart
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (walk : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start finish)
    (step : Fin walk.length) :
    dualWalkTargetFaceDart hunique walk step =
      RS.alpha (dualWalkSourceFaceDart hunique walk step) := by
  have htargetEdge := dualWalkTargetFaceDart_edge hunique walk step
  have hsourceEdge := dualWalkSourceFaceDart_edge hunique walk step
  rcases RS.edge_fiber_two_cases hsourceEdge htargetEdge with heq | heq
  · have htargetFace := dualWalkTargetFaceDart_face hunique walk step
    have hsourceFace := dualWalkSourceFaceDart_face hunique walk step
    exfalso
    apply (walk.adj_getVert_succ step.isLt).ne
    apply Subtype.ext
    exact hsourceFace.symm.trans (by simpa [heq] using htargetFace)
  · simpa using heq

/-- On a two-sided face, the open facial arc beginning immediately after
`first` and ending immediately before `alpha second` avoids both endpoint
edges.  Its endpoints are the terminal vertices of `first` and `second`.

This is the exact local route around a dual wall face: callers identify the
two endpoint edges with consecutive dual crossings and then use the arc in
the graph with that wall deleted. -/
theorem exists_coreFaceArcWalk_avoids_endpoint_edges_of_twoSided
    (data : Data G)
    (face : OrbitFace data.toRotationSystem)
    (first second : G.Dart)
    (hfirst : dartOrbitFace data.toRotationSystem first = face)
    (hsecondAlpha : dartOrbitFace data.toRotationSystem
      (data.toRotationSystem.alpha second) = face)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem) :
    ∃ arc : G.Walk first.snd second.snd,
      (∀ dart ∈ arc.darts,
        dartOrbitFace data.toRotationSystem dart = face) ∧
      first.edge ∉ arc.edges ∧ second.edge ∉ arc.edges := by
  let root := data.toRotationSystem.phi first
  let target := data.toRotationSystem.alpha second
  have hrootFace : dartOrbitFace data.toRotationSystem root = face := by
    exact (dartOrbitFace_phi_eq data.toRotationSystem first).trans hfirst
  have htargetOrbit : target ∈
      data.toRotationSystem.faceOrbit root := by
    rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit
      data.toRotationSystem root]
    exact (mem_orbitFaceDarts_iff data.toRotationSystem
      (dartOrbitFace data.toRotationSystem root) target).2
        (hsecondAlpha.trans hrootFace.symm)
  rcases exists_faceArcWalk data root target htargetOrbit with
    ⟨raw, hdarts, _hlength, hrawFace⟩
  have hfirstNot : first ∉
      faceArcDarts data root target htargetOrbit :=
    predecessor_not_mem_faceArcDarts data root target first htargetOrbit rfl
  have htargetNot : target ∉
      faceArcDarts data root target htargetOrbit :=
    target_not_mem_faceArcDarts data root target htargetOrbit
  have halphaFirstNot : data.toRotationSystem.alpha first ∉
      faceArcDarts data root target htargetOrbit := by
    intro hmem
    have halphaOrbit : data.toRotationSystem.alpha first ∈
        data.toRotationSystem.faceOrbit root := by
      have hraw := hrawFace (data.toRotationSystem.alpha first) (by
        rw [hdarts]
        exact hmem)
      exact hraw
    have halphaFace : dartOrbitFace data.toRotationSystem
        (data.toRotationSystem.alpha first) = face := by
      rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit
        data.toRotationSystem root] at halphaOrbit
      exact (mem_orbitFaceDarts_iff data.toRotationSystem
        (dartOrbitFace data.toRotationSystem root)
        (data.toRotationSystem.alpha first)).1 halphaOrbit |>.trans hrootFace
    exact htwoSided first (hfirst.trans halphaFace.symm)
  have hsecondNot : second ∉
      faceArcDarts data root target htargetOrbit := by
    intro hmem
    have hsecondOrbit : second ∈
        data.toRotationSystem.faceOrbit root := by
      have hraw := hrawFace second (by
        rw [hdarts]
        exact hmem)
      exact hraw
    have hsecondFace : dartOrbitFace data.toRotationSystem second = face := by
      rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit
        data.toRotationSystem root] at hsecondOrbit
      exact (mem_orbitFaceDarts_iff data.toRotationSystem
        (dartOrbitFace data.toRotationSystem root) second).1 hsecondOrbit |>.trans hrootFace
    exact htwoSided second (hsecondFace.trans hsecondAlpha.symm)
  have hfirstEdgeRaw : first.edge ∉ raw.edges := by
    intro hedge
    rw [SimpleGraph.Walk.edges, hdarts] at hedge
    rcases List.mem_map.mp hedge with ⟨dart, hdart, hedgeEq⟩
    rcases (SimpleGraph.dart_edge_eq_iff dart first).1 hedgeEq with heq | heq
    · exact hfirstNot (heq ▸ hdart)
    · have halpha : dart = data.toRotationSystem.alpha first := by
        simpa using heq
      exact halphaFirstNot (halpha ▸ hdart)
  have hsecondEdgeRaw : second.edge ∉ raw.edges := by
    intro hedge
    rw [SimpleGraph.Walk.edges, hdarts] at hedge
    rcases List.mem_map.mp hedge with ⟨dart, hdart, hedgeEq⟩
    rcases (SimpleGraph.dart_edge_eq_iff dart second).1 hedgeEq with heq | heq
    · exact hsecondNot (heq ▸ hdart)
    · have halpha : dart = target := by
        simpa [target] using heq
      exact htargetNot (halpha ▸ hdart)
  have hstart : root.fst = first.snd := by
    change (data.toRotationSystem.phi first).fst = first.snd
    simpa using (data.toRotationSystem.vert_phi_eq_vert_alpha first)
  have hfinish : target.fst = second.snd := by
    change (data.toRotationSystem.alpha second).fst = second.snd
    simp
  let arc : G.Walk first.snd second.snd := raw.copy hstart hfinish
  refine ⟨arc, ?_, ?_, ?_⟩
  · intro dart hdart
    have hdartRaw : dart ∈ raw.darts := by simpa [arc] using hdart
    have hfaceMem := hrawFace dart hdartRaw
    rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit
      data.toRotationSystem root] at hfaceMem
    exact (mem_orbitFaceDarts_iff data.toRotationSystem
      (dartOrbitFace data.toRotationSystem root) dart).1 hfaceMem |>.trans hrootFace
  · simpa [arc] using hfirstEdgeRaw
  · simpa [arc] using hsecondEdgeRaw

/-- The target-side endpoints of two cyclically consecutive dual crossings
are joined by a literal primal face arc that avoids every edge crossed by the
whole dual cycle.  This is the local component propagation step behind the
combinatorial Jordan-side construction. -/
theorem exists_dualCycleTargetSideArc_avoiding_crossings
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)))
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Walk start start)
    (hcycle : walk.IsCycle)
    (step : Fin walk.length) :
    ∃ arc : G.Walk
        (dualWalkSourceFaceDart hunique walk step).snd
        (dualWalkSourceFaceDart hunique walk
          (finRotate walk.length step)).snd,
      ∀ edge : G.edgeSet, (edge : Sym2 V) ∈ arc.edges →
        edge ∉ dualWalkCrossingEdges
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset (OrbitFace data.toRotationSystem))
          hunique walk := by
  let RS := data.toRotationSystem
  let current := dualWalkSourceFaceDart hunique walk step
  let next := dualWalkSourceFaceDart hunique walk
    (finRotate walk.length step)
  let face := (walk.getVert (step.val + 1)).1
  let crossing := dualWalkCrossingEdge
    (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
  let removed := dualWalkCrossingEdges
    (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
  have hfirstFace : dartOrbitFace RS next = face := by
    dsimp [next, face]
    rw [dualWalkSourceFaceDart_face,
      ← getVert_succ_eq_getVert_finRotate walk hcycle step]
  have hsecondAlpha : dartOrbitFace RS (RS.alpha current) = face := by
    dsimp [current, face]
    exact alpha_dualWalkSourceFaceDart_face htwoSided hunique walk step
  rcases exists_coreFaceArcWalk_avoids_endpoint_edges_of_twoSided
      data face next current hfirstFace hsecondAlpha htwoSided with
    ⟨core, hcoreFace, hnextAvoid, hcurrentAvoid⟩
  let arc : G.Walk current.snd next.snd := core.reverse
  refine ⟨arc, ?_⟩
  intro edge hedge
  have htwoLength : 2 ≤ walk.length :=
    le_trans (by omega) hcycle.three_le_length
  have hrotateNe : finRotate walk.length step ≠ step := by
    rw [← Equiv.Perm.mem_support,
      support_finRotate_of_le htwoLength]
    exact Finset.mem_univ _
  have hcrossingInjective : Function.Injective crossing :=
    dualWalkCrossingEdge_injective_of_isCycle
      (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS))
      (orbitFace_incidence_le_two RS) hunique walk hcycle
  have hcurrentNextNe : crossing step ≠
      crossing (finRotate walk.length step) := by
    intro hedges
    exact hrotateNe (hcrossingInjective hedges.symm)
  have hcurrentInRemoved : crossing step ∈ removed := by
    exact (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS))
      hunique walk (crossing step)).2 ⟨step, rfl⟩
  have hnextInRemoved : crossing (finRotate walk.length step) ∈ removed := by
    exact (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS))
      hunique walk (crossing (finRotate walk.length step))).2
        ⟨finRotate walk.length step, rfl⟩
  have hcurrentInFace : crossing step ∈ orbitFaceBoundary RS face := by
    dsimp [crossing, face]
    exact dualWalkCrossingEdge_mem_rightFace
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk step
  have hnextInFace : crossing (finRotate walk.length step) ∈
      orbitFaceBoundary RS face := by
    dsimp [crossing, face]
    have hmem := dualWalkCrossingEdge_mem_leftFace
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
      (finRotate walk.length step)
    rw [← getVert_succ_eq_getVert_finRotate walk hcycle step] at hmem
    exact hmem
  have hpairSubset : {crossing step, crossing (finRotate walk.length step)} ⊆
      removed ∩ orbitFaceBoundary RS face := by
    intro candidate hcandidate
    rw [Finset.mem_insert, Finset.mem_singleton] at hcandidate
    rcases hcandidate with rfl | rfl
    · exact Finset.mem_inter.2 ⟨hcurrentInRemoved, hcurrentInFace⟩
    · exact Finset.mem_inter.2 ⟨hnextInRemoved, hnextInFace⟩
  have hpairCard : ({crossing step, crossing (finRotate walk.length step)} :
      Finset G.edgeSet).card = 2 :=
    Finset.card_pair hcurrentNextNe
  have hremovedAtFaceCardLe :
      (removed ∩ orbitFaceBoundary RS face).card ≤ 2 := by
    dsimp [removed, face, RS]
    exact card_dualWalkCrossingEdges_inter_faceBoundary_le_two_of_isCycle
      data hunique walk hcycle (walk.getVert (step.val + 1)).1
  have hremovedAtFaceEq : removed ∩ orbitFaceBoundary RS face =
      {crossing step, crossing (finRotate walk.length step)} := by
    symm
    apply Finset.eq_of_subset_of_card_le hpairSubset
    have hlower : 2 ≤ (removed ∩ orbitFaceBoundary RS face).card := by
      rw [← hpairCard]
      exact Finset.card_le_card hpairSubset
    omega
  intro hedgeRemoved
  have hedgeCore : (edge : Sym2 V) ∈ core.edges := by
    simpa [arc, SimpleGraph.Walk.edges_reverse] using hedge
  have hedgeCoreEdges := hedgeCore
  rw [SimpleGraph.Walk.edges] at hedgeCore
  rcases List.mem_map.mp hedgeCore with ⟨dart, hdart, hdartEdge⟩
  have hdartFace : dartOrbitFace RS dart = face := by
    exact hcoreFace dart hdart
  have hedgeFace : edge ∈ orbitFaceBoundary RS face := by
    have hraw := edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS dart
    rw [hdartFace] at hraw
    apply (show RS.edgeOf dart = edge by
      apply Subtype.ext
      exact hdartEdge).symm ▸ hraw
  have hedgeRemovedFace : edge ∈ removed ∩ orbitFaceBoundary RS face :=
    Finset.mem_inter.2 ⟨by simpa [removed] using hedgeRemoved, hedgeFace⟩
  rw [hremovedAtFaceEq, Finset.mem_insert, Finset.mem_singleton] at hedgeRemovedFace
  rcases hedgeRemovedFace with hedgeCurrent | hedgeNext
  · apply hcurrentAvoid
    have hcurrentEdge : current.edge = (crossing step).1 := by
      change (RS.edgeOf current).1 = (crossing step).1
      exact congrArg Subtype.val (dualWalkSourceFaceDart_edge hunique walk step)
    simpa [hcurrentEdge, hedgeCurrent] using hedgeCoreEdges
  · apply hnextAvoid
    have hnextEdge : next.edge = (crossing (finRotate walk.length step)).1 := by
      change (RS.edgeOf next).1 =
        (crossing (finRotate walk.length step)).1
      exact congrArg Subtype.val (dualWalkSourceFaceDart_edge hunique walk
        (finRotate walk.length step))
    simpa [hnextEdge, hedgeNext] using hedgeCoreEdges

/-- The preceding local arc is expressed directly at the canonical target
face darts.  Thus the target-side vertices of cyclically consecutive dual
steps lie in the same deleted-edge component. -/
theorem exists_dualCycleTargetFaceArc_avoiding_crossings
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)))
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Walk start start)
    (hcycle : walk.IsCycle)
    (step : Fin walk.length) :
    ∃ arc : G.Walk
        (data.toRotationSystem.vertOf
          (dualWalkTargetFaceDart hunique walk step))
        (data.toRotationSystem.vertOf
          (dualWalkTargetFaceDart hunique walk
            (finRotate walk.length step))),
      ∀ edge : G.edgeSet, (edge : Sym2 V) ∈ arc.edges →
        edge ∉ dualWalkCrossingEdges
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset (OrbitFace data.toRotationSystem))
          hunique walk := by
  let current := dualWalkSourceFaceDart hunique walk step
  let next := dualWalkSourceFaceDart hunique walk
    (finRotate walk.length step)
  rcases exists_dualCycleTargetSideArc_avoiding_crossings
      data htwoSided hunique walk hcycle step with ⟨raw, hraw⟩
  have hcurrent : dualWalkTargetFaceDart hunique walk step =
      data.toRotationSystem.alpha current := by
    dsimp [current]
    exact dualWalkTargetFaceDart_eq_alpha_sourceFaceDart hunique walk step
  have hnext : dualWalkTargetFaceDart hunique walk
      (finRotate walk.length step) = data.toRotationSystem.alpha next := by
    dsimp [next]
    exact dualWalkTargetFaceDart_eq_alpha_sourceFaceDart hunique walk
      (finRotate walk.length step)
  have hstart : current.snd = data.toRotationSystem.vertOf
      (dualWalkTargetFaceDart hunique walk step) := by
    rw [hcurrent]
    rfl
  have hfinish : next.snd = data.toRotationSystem.vertOf
      (dualWalkTargetFaceDart hunique walk
        (finRotate walk.length step)) := by
    rw [hnext]
    rfl
  refine ⟨raw.copy hstart hfinish, ?_⟩
  simpa using hraw

/-- The target-face endpoints of consecutive steps of a simple facial-dual
cycle are on the same side of every component after deleting the crossed
primal wall.  This converts the local face arc into the component invariant
needed by the crosscut boundary construction. -/
theorem dualWalkTargetFaceDart_component_mem_iff_finRotate
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)))
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Walk start start)
    (hcycle : walk.IsCycle)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        (dualWalkCrossingEdges (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset (OrbitFace data.toRotationSystem))
          hunique walk))).ConnectedComponent)
    (step : Fin walk.length) :
    (data.toRotationSystem.vertOf
        (dualWalkTargetFaceDart hunique walk step) ∈ component.supp) ↔
      (data.toRotationSystem.vertOf
        (dualWalkTargetFaceDart hunique walk
          (finRotate walk.length step)) ∈ component.supp) := by
  let removed := dualWalkCrossingEdges
    (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
  rcases exists_dualCycleTargetFaceArc_avoiding_crossings
      data htwoSided hunique walk hcycle step with ⟨arc, harc⟩
  apply component_side_iff_of_walk_avoiding_removed removed component arc
  intro edge hedge hvalue
  rcases (mem_edgeFinsetValueSet_iff removed edge.1).1 hvalue with
    ⟨other, hother, hotherValue⟩
  apply harc edge hedge
  have hotherRemoved : other ∈ dualWalkCrossingEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk := by
    simpa [removed] using hother
  simpa [Subtype.ext hotherValue] using hotherRemoved

/-- All target-face endpoints of a simple facial-dual cycle lie on one fixed
side of any component of its deleted primal wall.  The cycle action is used
only to propagate the concrete consecutive-face arcs proved above. -/
theorem dualWalkTargetFaceDart_component_mem_iff
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)))
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Walk start start)
    (hcycle : walk.IsCycle)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        (dualWalkCrossingEdges (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset (OrbitFace data.toRotationSystem))
          hunique walk))).ConnectedComponent)
    (first second : Fin walk.length) :
    (data.toRotationSystem.vertOf
        (dualWalkTargetFaceDart hunique walk first) ∈ component.supp) ↔
      (data.toRotationSystem.vertOf
        (dualWalkTargetFaceDart hunique walk second) ∈ component.supp) := by
  have htwoLength : 2 ≤ walk.length :=
    le_trans (by omega) hcycle.three_le_length
  have hrotateNe (step : Fin walk.length) :
      finRotate walk.length step ≠ step := by
    rw [← Equiv.Perm.mem_support,
      support_finRotate_of_le htwoLength]
    exact Finset.mem_univ _
  have hsameCycle :
      (finRotate walk.length).SameCycle first second :=
    (isCycle_finRotate_of_le htwoLength).sameCycle
      (hrotateNe first) (hrotateNe second)
  rcases hsameCycle.exists_nat_pow_eq with ⟨power, hpower⟩
  have hiterate : ∀ exponent : Nat,
      (data.toRotationSystem.vertOf
          (dualWalkTargetFaceDart hunique walk first) ∈ component.supp) ↔
        (data.toRotationSystem.vertOf
          (dualWalkTargetFaceDart hunique walk
            (((finRotate walk.length) ^ exponent) first)) ∈ component.supp) := by
    intro exponent
    induction exponent with
    | zero => simp
    | succ previous ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact ih.trans
          (dualWalkTargetFaceDart_component_mem_iff_finRotate
            data htwoSided hunique walk hcycle component _)
  have hiteratePower := hiterate power
  rw [hpower] at hiteratePower
  exact hiteratePower

end

end GoertzelV24DualCycleTargetSide

end Mettapedia.GraphTheory.FourColor
