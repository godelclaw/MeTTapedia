import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutLoop
import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicFaceCutTrailTransport

/-!
# Local closed-seam separation of paired annular layer boundaries

The source uses two simple transverse layer boundaries and performs its basic
splice on the resulting open interfaces.  When one additionally closes that
interface to an ordinary loopless rotation system, their dual paths already
rule out a primal endpoint collision through every interior face.  This file
isolates the residual finite checks at the two named hole faces.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance layerGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace RotationSystem

/-- Two distinct edges at one vertex of a cyclic cubic rotation system share
a quotient face.  This is the local planar fact which turns a putative seam
loop into a shared layer face. -/
theorem exists_common_orbitFace_of_distinct_incident_edges_for_layer
    {E : Type*} [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    {first second : E} (hne : first ≠ second) {vertex : V}
    (hfirst : vertex ∈ RS.endpoints first)
    (hsecond : vertex ∈ RS.endpoints second) :
    ∃ face : OrbitFace RS,
      first ∈ orbitFaceBoundary RS face ∧
        second ∈ orbitFaceBoundary RS face := by
  rcases (RS.mem_endpoints_iff).1 hfirst with
    ⟨firstDart, hfirstOn, hfirstVertex⟩
  rcases (RS.mem_endpoints_iff).1 hsecond with
    ⟨secondDart, hsecondOn, hsecondVertex⟩
  have hfirstEdge : RS.edgeOf firstDart = first :=
    (RS.mem_dartsOn).1 hfirstOn
  have hsecondEdge : RS.edgeOf secondDart = second :=
    (RS.mem_dartsOn).1 hsecondOn
  have hdartsNe : firstDart ≠ secondDart := by
    intro hdarts
    apply hne
    calc
      first = RS.edgeOf firstDart := hfirstEdge.symm
      _ = RS.edgeOf secondDart := congrArg RS.edgeOf hdarts
      _ = second := hsecondEdge
  have hbase : RS.vertOf secondDart = RS.vertOf firstDart :=
    hsecondVertex.trans hfirstVertex.symm
  rcases RS.rho_eq_or_rho_eq_of_cubic hcubic hrotation hbase hdartsNe with
    hforward | hreverse
  · refine ⟨dartOrbitFace RS secondDart, ?_, ?_⟩
    · have hmem :=
        edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS (RS.alpha firstDart)
      rw [RS.edge_alpha, hfirstEdge,
        dartOrbitFace_alpha_eq_dartOrbitFace_rho RS firstDart,
        hforward] at hmem
      exact hmem
    · rw [← hsecondEdge]
      exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS secondDart
  · refine ⟨dartOrbitFace RS firstDart, ?_, ?_⟩
    · rw [← hfirstEdge]
      exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS firstDart
    · have hmem :=
        edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS (RS.alpha secondDart)
      rw [RS.edge_alpha, hsecondEdge,
        dartOrbitFace_alpha_eq_dartOrbitFace_rho RS secondDart,
        hreverse] at hmem
      exact hmem

end RotationSystem

namespace SimpleDualCrosscut

/-- Any face incident to a crossed edge of a source transversal occurs in
that transversal's dual support.  The result uses only the two-sided facial
incidence bound, so it applies directly to the actual annular crosscuts. -/
theorem face_mem_walk_support_of_mem_crossingEdge_of_mem_boundary
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (crosscut : SimpleDualCrosscut (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {edge : G.edgeSet} {face : OrbitFace RS}
    (hedge : edge ∈ crosscut.crossingEdges hunique)
    (hface : edge ∈ orbitFaceBoundary RS face) :
    (⟨face, Finset.mem_univ face⟩ : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))) ∈ crosscut.walk.support := by
  rcases (crosscut.mem_crossingEdges_iff hunique edge).1 hedge with
    ⟨step, hstep⟩
  let left := crosscut.walk.getVert step.val
  let right := crosscut.walk.getVert (step.val + 1)
  have hadj := crosscut.walk.adj_getVert_succ step.isLt
  have hleftRight : left.1 ≠ right.1 := by
    intro hfaces
    exact hadj.ne (Subtype.ext hfaces)
  have hleft : edge ∈ orbitFaceBoundary RS left.1 := by
    rw [← hstep]
    exact dualWalkCrossingEdge_mem_leftFace
      (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS))
      hunique crosscut.walk step
  have hright : edge ∈ orbitFaceBoundary RS right.1 := by
    rw [← hstep]
    exact dualWalkCrossingEdge_mem_rightFace
      (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS))
      hunique crosscut.walk step
  have hcases :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS))
      (orbitFace_incidence_le_two RS) left.2 right.2 (Finset.mem_univ face)
      hleftRight hleft hright hface
  rcases hcases with hfaceLeft | hfaceRight
  · have hvertices :
        (⟨face, Finset.mem_univ face⟩ : AmbientFace
          (Finset.univ : Finset (OrbitFace RS))) = left :=
      Subtype.ext hfaceLeft
    rw [hvertices]
    exact crosscut.walk.getVert_mem_support step.val
  · have hvertices :
        (⟨face, Finset.mem_univ face⟩ : AmbientFace
          (Finset.univ : Finset (OrbitFace RS))) = right :=
      Subtype.ext hfaceRight
    rw [hvertices]
    exact crosscut.walk.getVert_mem_support (step.val + 1)

end SimpleDualCrosscut

namespace SeparatedAlignedSimpleDualCrosscuts

/-- The only residual geometric check after paired simple-transversal
disjointness: at either named hole face, matched crossings may meet the same
face but may not meet the same *primal endpoint*.  This is the actual finite
boundary-port condition: both crosscuts necessarily touch each hole, so merely
forbidding a common hole face would be false.  All interior shared-face cases
are excluded by the dual-path disjointness already stored in the pair. -/
def MatchedCrossingsAvoidEndpointFaces
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique) : Prop :=
  ∀ step : Fin pair.left.walk.length, ∀ vertex : V,
    vertex ∈ data.toRotationSystem.endpoints
        (pair.left.crossingEdge hunique step) →
      vertex ∈ data.toRotationSystem.endpoints
        (pair.right.crossingEdge hunique (Fin.cast pair.length_eq step)) →
        ¬ ((pair.left.crossingEdge hunique step ∈
              orbitFaceBoundary data.toRotationSystem start.1 ∧
            pair.right.crossingEdge hunique (Fin.cast pair.length_eq step) ∈
              orbitFaceBoundary data.toRotationSystem start.1) ∨
          (pair.left.crossingEdge hunique step ∈
              orbitFaceBoundary data.toRotationSystem finish.1 ∧
            pair.right.crossingEdge hunique (Fin.cast pair.length_eq step) ∈
              orbitFaceBoundary data.toRotationSystem finish.1))

/-- The primal endpoint separation needed by the graph-level retained splice
is automatic away from the two holes.  With the finite endpoint-face checks
above, it follows for every matched interface position. -/
theorem matchedCrossingsEndpointSeparation_of_avoidEndpointFaces
    (data : Data G)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (hboundary : pair.MatchedCrossingsAvoidEndpointFaces data) :
    ∀ step : Fin pair.left.walk.length, ∀ left right : V,
      left ∈ data.toRotationSystem.endpoints
          (pair.left.crossingEdge hunique step) →
        right ∈ data.toRotationSystem.endpoints
          (pair.right.crossingEdge hunique (Fin.cast pair.length_eq step)) →
          left ≠ right := by
  intro step left right hleft hright hsame
  have hedgeNe : pair.left.crossingEdge hunique step ≠
      pair.right.crossingEdge hunique (Fin.cast pair.length_eq step) := by
    intro hedge
    have hleftMem : pair.left.crossingEdge hunique step ∈
        pair.left.crossingEdges hunique :=
      (pair.left.mem_crossingEdges_iff hunique _).2 ⟨step, rfl⟩
    have hrightMem : pair.left.crossingEdge hunique step ∈
        pair.right.crossingEdges hunique := by
      rw [hedge]
      exact (pair.right.mem_crossingEdges_iff hunique _).2
        ⟨Fin.cast pair.length_eq step, rfl⟩
    exact (Finset.disjoint_left.1 pair.crossing_disjoint hleftMem hrightMem).elim
  rcases RotationSystem.exists_common_orbitFace_of_distinct_incident_edges_for_layer
      data.toRotationSystem hcubic hrotation hedgeNe hleft (hsame ▸ hright) with
    ⟨face, hleftFace, hrightFace⟩
  have hleftSupport :
      (⟨face, Finset.mem_univ face⟩ : AmbientFace
        (Finset.univ : Finset (OrbitFace data.toRotationSystem))) ∈
        pair.left.walk.support :=
    pair.left.face_mem_walk_support_of_mem_crossingEdge_of_mem_boundary
      hunique
      ((pair.left.mem_crossingEdges_iff hunique _).2 ⟨step, rfl⟩)
      hleftFace
  have hrightSupport :
      (⟨face, Finset.mem_univ face⟩ : AmbientFace
        (Finset.univ : Finset (OrbitFace data.toRotationSystem))) ∈
        pair.right.walk.support :=
    pair.right.face_mem_walk_support_of_mem_crossingEdge_of_mem_boundary
      hunique
      ((pair.right.mem_crossingEdges_iff hunique _).2
        ⟨Fin.cast pair.length_eq step, rfl⟩)
      hrightFace
  by_cases hstart : face = start.1
  · subst face
    exact (hboundary step left hleft (hsame ▸ hright))
      (Or.inl ⟨hleftFace, hrightFace⟩)
  by_cases hfinish : face = finish.1
  · subst face
    exact (hboundary step left hleft (hsame ▸ hright))
      (Or.inr ⟨hleftFace, hrightFace⟩)
  have hleftTail :
      (⟨face, Finset.mem_univ face⟩ : AmbientFace
        (Finset.univ : Finset (OrbitFace data.toRotationSystem))) ∈
        pair.left.walk.support.tail := by
    rw [← pair.left.walk.cons_tail_support] at hleftSupport
    rcases List.mem_cons.mp hleftSupport with hfaceStart | htail
    · exact (hstart (congrArg Subtype.val hfaceStart)).elim
    · exact htail
  have hrightReverseSupport :
      (⟨face, Finset.mem_univ face⟩ : AmbientFace
        (Finset.univ : Finset (OrbitFace data.toRotationSystem))) ∈
        pair.right.walk.reverse.support := by
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hrightSupport
  have hrightTail :
      (⟨face, Finset.mem_univ face⟩ : AmbientFace
        (Finset.univ : Finset (OrbitFace data.toRotationSystem))) ∈
        pair.right.walk.reverse.support.tail := by
    rw [← pair.right.walk.reverse.cons_tail_support] at hrightReverseSupport
    rcases List.mem_cons.mp hrightReverseSupport with hfaceFinish | htail
    · exact (hfinish (congrArg Subtype.val hfaceFinish)).elim
    · exact htail
  exact (List.disjoint_left.1 pair.transverse_disjoint hleftTail hrightTail).elim

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
