import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebHoleBoundaryOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceArcWalk

/-!
# Core walks along the closed-web hole faces

A radial support path includes its degree-one boundary edge.  Therefore a
sector wall must not join two radial paths by the earlier closed edge arc,
which includes the same stub edges again.  The correct graph-level object is
the facial segment from just after the first stub dart to just before the
reverse dart at the second stub.  Its endpoints are the two neighbours of the
stubs, so it is ready to join the radial paths after their boundary edges are
trimmed.

This module constructs those actual face-ordered walks.  It does not yet claim
that the two complementary choices form simple Jordan walls; that requires
the subsequent disjointness argument.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebHoleCoreArcWalk

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebHoleBoundaryOrder
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open GoertzelV24OrbitFaceArcWalk
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

/-- A vertex rotation fixes the unique outgoing dart at a degree-one graph
vertex. -/
private theorem vertexRotation_eq_self_of_unique_incident_edge
    (graphData : Data G) (dart : G.Dart)
    (hunique : incidentEdgeFinset G dart.fst =
      {(⟨dart.edge, dart.edge_mem⟩ : G.edgeSet)}) :
    graphData.vertexRotation dart = dart := by
  let rotated := graphData.vertexRotation dart
  have hfst : rotated.fst = dart.fst := graphData.vertexRotation_fst dart
  have hmem : (⟨rotated.edge, rotated.edge_mem⟩ : G.edgeSet) ∈
      incidentEdgeFinset G dart.fst := by
    simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    change dart.fst ∈ s(rotated.fst, rotated.snd)
    rw [hfst]
    exact Sym2.mem_iff.mpr (Or.inl rfl)
  rw [hunique] at hmem
  have hedge : rotated.edge = dart.edge :=
    congrArg Subtype.val (Finset.mem_singleton.mp hmem)
  rcases (SimpleGraph.dart_edge_eq_iff rotated dart).1 hedge with heq | heq
  · exact heq
  · exfalso
    have hvertices := congrArg (fun current : G.Dart => current.fst) heq
    simp [rotated, hfst] at hvertices

/-- At an inner degree-one stub, the face successor of the reverse boundary
dart is the outward boundary dart itself. -/
theorem phi_alpha_innerBoundaryDart
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) (inner : Fin 5) :
    embedded.RS.phi
        (embedded.RS.alpha (innerBoundaryDart data hdata inner)) =
      innerBoundaryDart data hdata inner := by
  let dart := innerBoundaryDart data hdata inner
  have hunique := data.innerStub_incidentEdgeFinset_eq_singleton hdata inner
  have hfst : dart.fst = data.innerStub inner :=
    innerBoundaryDart_fst data hdata inner
  have hedge : (⟨dart.edge, dart.edge_mem⟩ : G.edgeSet) =
      data.innerBoundaryEdge inner := by
    apply Subtype.ext
    exact innerBoundaryDart_edge data hdata inner
  have hunique' : incidentEdgeFinset G dart.fst =
      {(⟨dart.edge, dart.edge_mem⟩ : G.edgeSet)} := by
    rw [hfst, hunique, hedge]
  have hrotation : embedded.cellulation.rotation.vertexRotation dart = dart :=
    vertexRotation_eq_self_of_unique_incident_edge
      embedded.cellulation.rotation dart hunique'
  change embedded.cellulation.rotation.vertexRotation dart = dart
  exact hrotation

/-- The same degree-one face-successor fact at an outer stub. -/
theorem phi_alpha_outerBoundaryDart
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) (outer : Fin outerCount) :
    embedded.RS.phi
        (embedded.RS.alpha (outerBoundaryDart data hdata outer)) =
      outerBoundaryDart data hdata outer := by
  let dart := outerBoundaryDart data hdata outer
  have hunique := data.outerStub_incidentEdgeFinset_eq_singleton hdata outer
  have hfst : dart.fst = data.outerStub outer :=
    outerBoundaryDart_fst data hdata outer
  have hedge : (⟨dart.edge, dart.edge_mem⟩ : G.edgeSet) =
      data.outerBoundaryEdge outer := by
    apply Subtype.ext
    exact outerBoundaryDart_edge data hdata outer
  have hunique' : incidentEdgeFinset G dart.fst =
      {(⟨dart.edge, dart.edge_mem⟩ : G.edgeSet)} := by
    rw [hfst, hunique, hedge]
  have hrotation : embedded.cellulation.rotation.vertexRotation dart = dart :=
    vertexRotation_eq_self_of_unique_incident_edge
      embedded.cellulation.rotation dart hunique'
  change embedded.cellulation.rotation.vertexRotation dart = dart
  exact hrotation

/-- A different inner boundary dart cannot be the face successor immediately
after the first stub spike. -/
theorem innerBoundaryDart_ne_phi_innerBoundaryDart
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) {first second : Fin 5}
    (hne : first ≠ second) :
    innerBoundaryDart data hdata second ≠
      embedded.RS.phi (innerBoundaryDart data hdata first) := by
  intro heq
  let firstDart := innerBoundaryDart data hdata first
  let secondDart := innerBoundaryDart data hdata second
  have hsnd : firstDart.snd = secondDart.fst := by
    have hadj := GoertzelV24OrbitFaceWalk.dartAdj_phi
      embedded.cellulation.rotation firstDart
    exact hadj.trans (congrArg (fun dart : G.Dart => dart.fst) heq.symm)
  have hfirstAtSecond :
      (⟨firstDart.edge, firstDart.edge_mem⟩ : G.edgeSet) ∈
        incidentEdgeFinset G (data.innerStub second) := by
    simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    change data.innerStub second ∈ s(firstDart.fst, firstDart.snd)
    rw [← innerBoundaryDart_fst data hdata second, ← hsnd]
    exact Sym2.mem_iff.mpr (Or.inr rfl)
  rw [data.innerStub_incidentEdgeFinset_eq_singleton hdata second] at hfirstAtSecond
  have hedges : data.innerBoundaryEdge first =
      data.innerBoundaryEdge second := by
    rw [← Finset.mem_singleton.mp hfirstAtSecond]
    apply Subtype.ext
    exact (innerBoundaryDart_edge data hdata first).symm
  exact hne (data.innerBoundaryEdge.injective hedges)

/-- The same non-wrapping fact for distinct outer boundary darts. -/
theorem outerBoundaryDart_ne_phi_outerBoundaryDart
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) {first second : Fin outerCount}
    (hne : first ≠ second) :
    outerBoundaryDart data hdata second ≠
      embedded.RS.phi (outerBoundaryDart data hdata first) := by
  intro heq
  let firstDart := outerBoundaryDart data hdata first
  let secondDart := outerBoundaryDart data hdata second
  have hsnd : firstDart.snd = secondDart.fst := by
    have hadj := GoertzelV24OrbitFaceWalk.dartAdj_phi
      embedded.cellulation.rotation firstDart
    exact hadj.trans (congrArg (fun dart : G.Dart => dart.fst) heq.symm)
  have hfirstAtSecond :
      (⟨firstDart.edge, firstDart.edge_mem⟩ : G.edgeSet) ∈
        incidentEdgeFinset G (data.outerStub second) := by
    simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    change data.outerStub second ∈ s(firstDart.fst, firstDart.snd)
    rw [← outerBoundaryDart_fst data hdata second, ← hsnd]
    exact Sym2.mem_iff.mpr (Or.inr rfl)
  rw [data.outerStub_incidentEdgeFinset_eq_singleton hdata second] at hfirstAtSecond
  have hedges : data.outerBoundaryEdge first =
      data.outerBoundaryEdge second := by
    rw [← Finset.mem_singleton.mp hfirstAtSecond]
    apply Subtype.ext
    exact (outerBoundaryDart_edge data hdata first).symm
  exact hne (data.outerBoundaryEdge.injective hedges)

private theorem mem_faceOrbit_of_orbitFace_eq
    (graphData : Data G) (root target : G.Dart)
    (hface : dartOrbitFace graphData.toRotationSystem target =
      dartOrbitFace graphData.toRotationSystem root) :
    target ∈ graphData.toRotationSystem.faceOrbit root := by
  rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit
    graphData.toRotationSystem root]
  exact (mem_orbitFaceDarts_iff graphData.toRotationSystem
    (dartOrbitFace graphData.toRotationSystem root) target).2 hface

/-- Two darts known to lie on one named face determine the core facial walk
from the terminal vertex of the first dart to the terminal vertex of the
second.  The cut starts after `first` and stops before `alpha second`. -/
theorem exists_coreFaceArcWalk
    (graphData : Data G)
    (face : OrbitFace graphData.toRotationSystem)
    (first second : G.Dart)
    (hfirst : dartOrbitFace graphData.toRotationSystem first = face)
    (hsecondAlpha :
      dartOrbitFace graphData.toRotationSystem
        (graphData.toRotationSystem.alpha second) = face) :
    ∃ arc : G.Walk first.snd second.snd,
      (∀ dart ∈ arc.darts,
        dartOrbitFace graphData.toRotationSystem dart = face) ∧
      arc.length <
        (graphData.toRotationSystem.faceOrbit
          (graphData.toRotationSystem.phi first)).card := by
  let root := graphData.toRotationSystem.phi first
  let target := graphData.toRotationSystem.alpha second
  have hrootFace :
      dartOrbitFace graphData.toRotationSystem root = face := by
    exact (dartOrbitFace_phi_eq graphData.toRotationSystem first).trans hfirst
  have htargetOrbit : target ∈
      graphData.toRotationSystem.faceOrbit root :=
    mem_faceOrbit_of_orbitFace_eq graphData root target
      (hsecondAlpha.trans hrootFace.symm)
  rcases exists_faceArcWalk graphData root target htargetOrbit with
    ⟨raw, _hdarts, hlength, hrawFace⟩
  have hstart : root.fst = first.snd := by
    change (graphData.toRotationSystem.phi first).fst = first.snd
    simpa using (graphData.toRotationSystem.vert_phi_eq_vert_alpha first)
  have hfinish : target.fst = second.snd := by
    change (graphData.toRotationSystem.alpha second).fst = second.snd
    simp
  let arc : G.Walk first.snd second.snd := raw.copy hstart hfinish
  refine ⟨arc, ?_, ?_⟩
  · intro dart hdart
    have hdartRaw : dart ∈ raw.darts := by simpa [arc] using hdart
    have horbit := hrawFace dart hdartRaw
    rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit
      graphData.toRotationSystem root] at horbit
    exact (mem_orbitFaceDarts_iff graphData.toRotationSystem
      (dartOrbitFace graphData.toRotationSystem root) dart).1 horbit |>
        (fun h => h.trans hrootFace)
  · have hpositionLt :=
      (faceArcPosition graphData root target htargetOrbit).isLt
    have harcLength : arc.length = raw.length := by simp [arc]
    rw [harcLength]
    rw [hlength]
    exact hpositionLt

/-! The same canonical core arc is a trail when the named face is
two-sided.  This deliberately proves only edge simplicity; vertex simplicity
and the resulting Jordan placement remain separate obligations. -/

theorem exists_coreFaceArcWalk_isTrail
    (graphData : Data G)
    (face : OrbitFace graphData.toRotationSystem)
    (first second : G.Dart)
    (hfirst : dartOrbitFace graphData.toRotationSystem first = face)
    (hsecondAlpha :
      dartOrbitFace graphData.toRotationSystem
        (graphData.toRotationSystem.alpha second) = face)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem) :
    ∃ arc : G.Walk first.snd second.snd,
      arc.IsTrail ∧
      (∀ dart ∈ arc.darts,
        dartOrbitFace graphData.toRotationSystem dart = face) ∧
      arc.length <
        (graphData.toRotationSystem.faceOrbit
          (graphData.toRotationSystem.phi first)).card := by
  let root := graphData.toRotationSystem.phi first
  let target := graphData.toRotationSystem.alpha second
  have hrootFace :
      dartOrbitFace graphData.toRotationSystem root = face := by
    exact (dartOrbitFace_phi_eq graphData.toRotationSystem first).trans hfirst
  have htargetOrbit : target ∈
      graphData.toRotationSystem.faceOrbit root :=
    mem_faceOrbit_of_orbitFace_eq graphData root target
      (hsecondAlpha.trans hrootFace.symm)
  rcases exists_faceArcWalk_isTrail graphData htwoSided root target
      htargetOrbit with
    ⟨raw, hrawTrail, _hdarts, hlength, hrawFace⟩
  have hstart : root.fst = first.snd := by
    change (graphData.toRotationSystem.phi first).fst = first.snd
    simpa using (graphData.toRotationSystem.vert_phi_eq_vert_alpha first)
  have hfinish : target.fst = second.snd := by
    change (graphData.toRotationSystem.alpha second).fst = second.snd
    simp
  let arc : G.Walk first.snd second.snd := raw.copy hstart hfinish
  refine ⟨arc, ?_, ?_, ?_⟩
  · simpa [arc] using hrawTrail
  · intro dart hdart
    have hdartRaw : dart ∈ raw.darts := by simpa [arc] using hdart
    have horbit := hrawFace dart hdartRaw
    rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit
      graphData.toRotationSystem root] at horbit
    exact (mem_orbitFaceDarts_iff graphData.toRotationSystem
      (dartOrbitFace graphData.toRotationSystem root) dart).1 horbit |>
        (fun h => h.trans hrootFace)
  · have hpositionLt :=
      (faceArcPosition graphData root target htargetOrbit).isLt
    have harcLength : arc.length = raw.length := by simp [arc]
    rw [harcLength]
    rw [hlength]
    exact hpositionLt

/-! The local version keeps the two-sidedness premise only on the retained
facial prefix.  A framed hole can contain a bridge stub, so global
`OrbitFacesTwoSided` is intentionally not required here. -/

theorem exists_coreFaceArcWalk_isTrail_of_local_twoSided
    (graphData : Data G)
    (face : OrbitFace graphData.toRotationSystem)
    (first second : G.Dart)
    (hfirst : dartOrbitFace graphData.toRotationSystem first = face)
    (hsecondAlpha :
      dartOrbitFace graphData.toRotationSystem
        (graphData.toRotationSystem.alpha second) = face)
    (htargetOrbit : graphData.toRotationSystem.alpha second ∈
      graphData.toRotationSystem.faceOrbit
        (graphData.toRotationSystem.phi first))
    (hlocal : ∀ dart ∈ faceArcDarts graphData
        (graphData.toRotationSystem.phi first)
        (graphData.toRotationSystem.alpha second) htargetOrbit,
      dartOrbitFace graphData.toRotationSystem dart ≠
        dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.alpha dart)) :
    ∃ arc : G.Walk first.snd second.snd,
      arc.IsTrail ∧
      (∀ dart ∈ arc.darts,
        dartOrbitFace graphData.toRotationSystem dart = face) ∧
      arc.length <
        (graphData.toRotationSystem.faceOrbit
          (graphData.toRotationSystem.phi first)).card := by
  let root := graphData.toRotationSystem.phi first
  let target := graphData.toRotationSystem.alpha second
  have hrootFace :
      dartOrbitFace graphData.toRotationSystem root = face := by
    exact (dartOrbitFace_phi_eq graphData.toRotationSystem first).trans hfirst
  rcases exists_faceArcWalk_isTrail_of_local_twoSided
      graphData root target htargetOrbit hlocal with
    ⟨raw, hrawTrail, _hdarts, hlength, hrawFace⟩
  have hstart : root.fst = first.snd := by
    change (graphData.toRotationSystem.phi first).fst = first.snd
    simpa using (graphData.toRotationSystem.vert_phi_eq_vert_alpha first)
  have hfinish : target.fst = second.snd := by
    change (graphData.toRotationSystem.alpha second).fst = second.snd
    simp
  let arc : G.Walk first.snd second.snd := raw.copy hstart hfinish
  refine ⟨arc, ?_, ?_, ?_⟩
  · simpa [arc] using hrawTrail
  · intro dart hdart
    have hdartRaw : dart ∈ raw.darts := by simpa [arc] using hdart
    have horbit := hrawFace dart hdartRaw
    rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit
      graphData.toRotationSystem root] at horbit
    exact (mem_orbitFaceDarts_iff graphData.toRotationSystem
      (dartOrbitFace graphData.toRotationSystem root) dart).1 horbit |>
        (fun h => h.trans hrootFace)
  · have hpositionLt :=
      (faceArcPosition graphData root target htargetOrbit).isLt
    have harcLength : arc.length = raw.length := by simp [arc]
    rw [harcLength, hlength]
    exact hpositionLt

/-- With the two degree-one successor equations and non-wrapping endpoint
facts, the core facial arc contains neither endpoint edge. -/
theorem exists_coreFaceArcWalk_avoids_endpoint_edges
    (graphData : Data G)
    (face : OrbitFace graphData.toRotationSystem)
    (first second : G.Dart)
    (hfirst : dartOrbitFace graphData.toRotationSystem first = face)
    (hsecondAlpha :
      dartOrbitFace graphData.toRotationSystem
        (graphData.toRotationSystem.alpha second) = face)
    (hphiAlphaFirst : graphData.toRotationSystem.phi
      (graphData.toRotationSystem.alpha first) = first)
    (hphiAlphaSecond : graphData.toRotationSystem.phi
      (graphData.toRotationSystem.alpha second) = second)
    (hfirstTarget : first ≠ graphData.toRotationSystem.alpha second)
    (hsecondRoot : second ≠ graphData.toRotationSystem.phi first) :
    ∃ arc : G.Walk first.snd second.snd,
      (∀ dart ∈ arc.darts,
        dartOrbitFace graphData.toRotationSystem dart = face) ∧
      arc.length <
        (graphData.toRotationSystem.faceOrbit
          (graphData.toRotationSystem.phi first)).card ∧
      first.edge ∉ arc.edges ∧ second.edge ∉ arc.edges := by
  let root := graphData.toRotationSystem.phi first
  let target := graphData.toRotationSystem.alpha second
  have hrootFace :
      dartOrbitFace graphData.toRotationSystem root = face := by
    exact (dartOrbitFace_phi_eq graphData.toRotationSystem first).trans hfirst
  have htargetOrbit : target ∈
      graphData.toRotationSystem.faceOrbit root :=
    mem_faceOrbit_of_orbitFace_eq graphData root target
      (hsecondAlpha.trans hrootFace.symm)
  rcases exists_faceArcWalk graphData root target htargetOrbit with
    ⟨raw, hdarts, hlength, hrawFace⟩
  have hfirstNot : first ∉
      faceArcDarts graphData root target htargetOrbit :=
    predecessor_not_mem_faceArcDarts graphData root target first
      htargetOrbit rfl
  have htargetNot : target ∉
      faceArcDarts graphData root target htargetOrbit :=
    target_not_mem_faceArcDarts graphData root target htargetOrbit
  have hsecondNot : second ∉
      faceArcDarts graphData root target htargetOrbit := by
    have hnoWrap : graphData.toRotationSystem.phi target ≠ root := by
      change graphData.toRotationSystem.phi
          (graphData.toRotationSystem.alpha second) ≠
        graphData.toRotationSystem.phi first
      rw [hphiAlphaSecond]
      exact hsecondRoot
    have hafter := phi_target_not_mem_faceArcDarts
      graphData root target htargetOrbit hnoWrap
    rw [hphiAlphaSecond] at hafter
    exact hafter
  have halphaFirstNot : graphData.toRotationSystem.alpha first ∉
      faceArcDarts graphData root target htargetOrbit := by
    intro hmem
    have hneSuccessor : graphData.toRotationSystem.phi
        (graphData.toRotationSystem.alpha first) ≠ target := by
      change graphData.toRotationSystem.phi
          (graphData.toRotationSystem.alpha first) ≠
        graphData.toRotationSystem.alpha second
      rw [hphiAlphaFirst]
      exact hfirstTarget
    have hsuccessor := phi_mem_faceArcDarts_of_mem_of_ne_target
      graphData root target (graphData.toRotationSystem.alpha first)
      htargetOrbit hmem hneSuccessor
    rw [hphiAlphaFirst] at hsuccessor
    exact hfirstNot hsuccessor
  have hfirstEdgeRaw : first.edge ∉ raw.edges := by
    intro hedge
    rw [SimpleGraph.Walk.edges, hdarts] at hedge
    rcases List.mem_map.mp hedge with ⟨dart, hdart, hedgeEq⟩
    rcases (SimpleGraph.dart_edge_eq_iff dart first).1 hedgeEq with
      hdartEq | hdartEq
    · exact hfirstNot (hdartEq ▸ hdart)
    · have halpha : dart = graphData.toRotationSystem.alpha first := by
        simpa using hdartEq
      exact halphaFirstNot (halpha ▸ hdart)
  have hsecondEdgeRaw : second.edge ∉ raw.edges := by
    intro hedge
    rw [SimpleGraph.Walk.edges, hdarts] at hedge
    rcases List.mem_map.mp hedge with ⟨dart, hdart, hedgeEq⟩
    rcases (SimpleGraph.dart_edge_eq_iff dart second).1 hedgeEq with
      hdartEq | hdartEq
    · exact hsecondNot (hdartEq ▸ hdart)
    · have halpha : dart = target := by simpa [target] using hdartEq
      exact htargetNot (halpha ▸ hdart)
  have hstart : root.fst = first.snd := by
    change (graphData.toRotationSystem.phi first).fst = first.snd
    simpa using (graphData.toRotationSystem.vert_phi_eq_vert_alpha first)
  have hfinish : target.fst = second.snd := by
    change (graphData.toRotationSystem.alpha second).fst = second.snd
    simp
  let arc : G.Walk first.snd second.snd := raw.copy hstart hfinish
  refine ⟨arc, ?_, ?_, ?_, ?_⟩
  · intro dart hdart
    have hdartRaw : dart ∈ raw.darts := by simpa [arc] using hdart
    have horbit := hrawFace dart hdartRaw
    rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit
      graphData.toRotationSystem root] at horbit
    exact (mem_orbitFaceDarts_iff graphData.toRotationSystem
      (dartOrbitFace graphData.toRotationSystem root) dart).1 horbit |>
        (fun h => h.trans hrootFace)
  · have hpositionLt :=
      (faceArcPosition graphData root target htargetOrbit).isLt
    have harcLength : arc.length = raw.length := by simp [arc]
    rw [harcLength, hlength]
    exact hpositionLt
  · simpa [arc] using hfirstEdgeRaw
  · simpa [arc] using hsecondEdgeRaw

/-! The endpoint-avoiding form with the same prefix-local trail premise. -/

theorem exists_coreFaceArcWalk_isTrail_of_local_twoSided_avoids_endpoint_edges
    (graphData : Data G)
    (face : OrbitFace graphData.toRotationSystem)
    (first second : G.Dart)
    (hfirst : dartOrbitFace graphData.toRotationSystem first = face)
    (hsecondAlpha :
      dartOrbitFace graphData.toRotationSystem
        (graphData.toRotationSystem.alpha second) = face)
    (hphiAlphaFirst : graphData.toRotationSystem.phi
      (graphData.toRotationSystem.alpha first) = first)
    (hphiAlphaSecond : graphData.toRotationSystem.phi
      (graphData.toRotationSystem.alpha second) = second)
    (hfirstTarget : first ≠ graphData.toRotationSystem.alpha second)
    (hsecondRoot : second ≠ graphData.toRotationSystem.phi first)
    (htargetOrbit : graphData.toRotationSystem.alpha second ∈
      graphData.toRotationSystem.faceOrbit
        (graphData.toRotationSystem.phi first))
    (hlocal : ∀ dart ∈ faceArcDarts graphData
        (graphData.toRotationSystem.phi first)
        (graphData.toRotationSystem.alpha second) htargetOrbit,
      dartOrbitFace graphData.toRotationSystem dart ≠
        dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.alpha dart)) :
    ∃ arc : G.Walk first.snd second.snd,
      arc.IsTrail ∧
      (∀ dart ∈ arc.darts,
        dartOrbitFace graphData.toRotationSystem dart = face) ∧
      arc.length <
        (graphData.toRotationSystem.faceOrbit
          (graphData.toRotationSystem.phi first)).card ∧
      first.edge ∉ arc.edges ∧ second.edge ∉ arc.edges := by
  let root := graphData.toRotationSystem.phi first
  let target := graphData.toRotationSystem.alpha second
  have hrootFace :
      dartOrbitFace graphData.toRotationSystem root = face := by
    exact (dartOrbitFace_phi_eq graphData.toRotationSystem first).trans hfirst
  rcases exists_faceArcWalk_isTrail_of_local_twoSided
      graphData root target htargetOrbit hlocal with
    ⟨raw, hrawTrail, hdarts, hlength, hrawFace⟩
  have hfirstNot : first ∉
      faceArcDarts graphData root target htargetOrbit :=
    predecessor_not_mem_faceArcDarts graphData root target first
      htargetOrbit rfl
  have htargetNot : target ∉
      faceArcDarts graphData root target htargetOrbit :=
    target_not_mem_faceArcDarts graphData root target htargetOrbit
  have hsecondNot : second ∉
      faceArcDarts graphData root target htargetOrbit := by
    have hnoWrap : graphData.toRotationSystem.phi target ≠ root := by
      change graphData.toRotationSystem.phi
          (graphData.toRotationSystem.alpha second) ≠
        graphData.toRotationSystem.phi first
      rw [hphiAlphaSecond]
      exact hsecondRoot
    have hafter := phi_target_not_mem_faceArcDarts
      graphData root target htargetOrbit hnoWrap
    rw [hphiAlphaSecond] at hafter
    exact hafter
  have halphaFirstNot : graphData.toRotationSystem.alpha first ∉
      faceArcDarts graphData root target htargetOrbit := by
    intro hmem
    have hneSuccessor : graphData.toRotationSystem.phi
        (graphData.toRotationSystem.alpha first) ≠ target := by
      change graphData.toRotationSystem.phi
          (graphData.toRotationSystem.alpha first) ≠
        graphData.toRotationSystem.alpha second
      rw [hphiAlphaFirst]
      exact hfirstTarget
    have hsuccessor := phi_mem_faceArcDarts_of_mem_of_ne_target
      graphData root target (graphData.toRotationSystem.alpha first)
      htargetOrbit hmem hneSuccessor
    rw [hphiAlphaFirst] at hsuccessor
    exact hfirstNot hsuccessor
  have hfirstEdgeRaw : first.edge ∉ raw.edges := by
    intro hedge
    rw [SimpleGraph.Walk.edges, hdarts] at hedge
    rcases List.mem_map.mp hedge with ⟨dart, hdart, hedgeEq⟩
    rcases (SimpleGraph.dart_edge_eq_iff dart first).1 hedgeEq with
      hdartEq | hdartEq
    · exact hfirstNot (hdartEq ▸ hdart)
    · have halpha : dart = graphData.toRotationSystem.alpha first := by
        simpa using hdartEq
      exact halphaFirstNot (halpha ▸ hdart)
  have hsecondEdgeRaw : second.edge ∉ raw.edges := by
    intro hedge
    rw [SimpleGraph.Walk.edges, hdarts] at hedge
    rcases List.mem_map.mp hedge with ⟨dart, hdart, hedgeEq⟩
    rcases (SimpleGraph.dart_edge_eq_iff dart second).1 hedgeEq with
      hdartEq | hdartEq
    · exact hsecondNot (hdartEq ▸ hdart)
    · have halpha : dart = target := by simpa [target] using hdartEq
      exact htargetNot (halpha ▸ hdart)
  have hstart : root.fst = first.snd := by
    change (graphData.toRotationSystem.phi first).fst = first.snd
    simpa using (graphData.toRotationSystem.vert_phi_eq_vert_alpha first)
  have hfinish : target.fst = second.snd := by
    change (graphData.toRotationSystem.alpha second).fst = second.snd
    simp
  let arc : G.Walk first.snd second.snd := raw.copy hstart hfinish
  refine ⟨arc, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [arc] using hrawTrail
  · intro dart hdart
    have hdartRaw : dart ∈ raw.darts := by simpa [arc] using hdart
    have horbit := hrawFace dart hdartRaw
    rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit
      graphData.toRotationSystem root] at horbit
    exact (mem_orbitFaceDarts_iff graphData.toRotationSystem
      (dartOrbitFace graphData.toRotationSystem root) dart).1 horbit |>
        (fun h => h.trans hrootFace)
  · have hpositionLt :=
      (faceArcPosition graphData root target htargetOrbit).isLt
    have harcLength : arc.length = raw.length := by simp [arc]
    rw [harcLength, hlength]
    exact hpositionLt
  · simpa [arc] using hfirstEdgeRaw
  · simpa [arc] using hsecondEdgeRaw

/-- The actual inner-hole segment between two ordered inner stubs, with the
stub spikes removed from its endpoints. -/
theorem exists_innerHoleCoreArcWalk
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) (first second : Fin 5) :
    ∃ arc : G.Walk
        (innerBoundaryDart data hdata first).snd
        (innerBoundaryDart data hdata second).snd,
      (∀ dart ∈ arc.darts,
        dartOrbitFace embedded.RS dart = embedded.cellulation.innerHole) ∧
      arc.length <
        (embedded.RS.faceOrbit
          (embedded.RS.phi (innerBoundaryDart data hdata first))).card := by
  let firstDart := innerBoundaryDart data hdata first
  let secondDart := innerBoundaryDart data hdata second
  have hfirst : dartOrbitFace embedded.RS firstDart =
      embedded.cellulation.innerHole :=
    innerBoundaryDart_on_innerHole embedded hdata first
  have hsecondOn : secondDart ∈
      embedded.RS.dartsOn (data.innerBoundaryEdge second) :=
    innerBoundaryDart_mem_dartsOn embedded hdata second
  have hsecondAlphaOn : embedded.RS.alpha secondDart ∈
      embedded.RS.dartsOn (data.innerBoundaryEdge second) :=
    embedded.RS.alpha_mem_dartsOn hsecondOn
  have hsecondAlpha :
      dartOrbitFace embedded.RS (embedded.RS.alpha secondDart) =
        embedded.cellulation.innerHole :=
    embedded.innerBoundaryEdgeDarts_on_innerHole second
      (embedded.RS.alpha secondDart) hsecondAlphaOn
  exact exists_coreFaceArcWalk embedded.cellulation.rotation
    embedded.cellulation.innerHole firstDart secondDart hfirst hsecondAlpha

/-! A trail-producing annular wrapper with a *local* two-sidedness premise.
The premise is stated on the canonical retained prefix, so it remains
compatible with the degree-one interface spikes that make global
`OrbitFacesTwoSided` unavailable for a framed web. -/

theorem exists_innerHoleCoreArcWalk_isTrail_of_local_twoSided
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) (first second : Fin 5)
    (htargetOrbit : embedded.RS.alpha
        (innerBoundaryDart data hdata second) ∈
      embedded.RS.faceOrbit
        (embedded.RS.phi (innerBoundaryDart data hdata first)))
    (hlocal : ∀ dart ∈ faceArcDarts embedded.cellulation.rotation
        (embedded.RS.phi (innerBoundaryDart data hdata first))
        (embedded.RS.alpha (innerBoundaryDart data hdata second))
        htargetOrbit,
      dartOrbitFace embedded.RS dart ≠
        dartOrbitFace embedded.RS (embedded.RS.alpha dart)) :
    ∃ arc : G.Walk
        (innerBoundaryDart data hdata first).snd
        (innerBoundaryDart data hdata second).snd,
      arc.IsTrail ∧
      (∀ dart ∈ arc.darts,
        dartOrbitFace embedded.RS dart = embedded.cellulation.innerHole) ∧
      arc.length <
        (embedded.RS.faceOrbit
          (embedded.RS.phi (innerBoundaryDart data hdata first))).card := by
  let firstDart := innerBoundaryDart data hdata first
  let secondDart := innerBoundaryDart data hdata second
  have hfirst : dartOrbitFace embedded.RS firstDart =
      embedded.cellulation.innerHole :=
    innerBoundaryDart_on_innerHole embedded hdata first
  have hsecondOn : secondDart ∈
      embedded.RS.dartsOn (data.innerBoundaryEdge second) :=
    innerBoundaryDart_mem_dartsOn embedded hdata second
  have hsecondAlphaOn : embedded.RS.alpha secondDart ∈
      embedded.RS.dartsOn (data.innerBoundaryEdge second) :=
    embedded.RS.alpha_mem_dartsOn hsecondOn
  have hsecondAlpha :
      dartOrbitFace embedded.RS (embedded.RS.alpha secondDart) =
        embedded.cellulation.innerHole :=
    embedded.innerBoundaryEdgeDarts_on_innerHole second
      (embedded.RS.alpha secondDart) hsecondAlphaOn
  rcases exists_coreFaceArcWalk_isTrail_of_local_twoSided
      embedded.cellulation.rotation embedded.cellulation.innerHole
      firstDart secondDart hfirst hsecondAlpha htargetOrbit hlocal with
    ⟨arc, htrail, hface, hlength⟩
  exact ⟨arc, htrail, hface, hlength⟩

/-- For two distinct inner anchors, the core arc avoids both named boundary
edges and therefore does not duplicate either radial-path stub edge. -/
theorem exists_innerHoleCoreArcWalk_avoids_boundaryEdges
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) {first second : Fin 5}
    (hne : first ≠ second) :
    ∃ arc : G.Walk
        (innerBoundaryDart data hdata first).snd
        (innerBoundaryDart data hdata second).snd,
      (∀ dart ∈ arc.darts,
        dartOrbitFace embedded.RS dart = embedded.cellulation.innerHole) ∧
      arc.length <
        (embedded.RS.faceOrbit
          (embedded.RS.phi (innerBoundaryDart data hdata first))).card ∧
      (data.innerBoundaryEdge first).1 ∉ arc.edges ∧
      (data.innerBoundaryEdge second).1 ∉ arc.edges := by
  let firstDart := innerBoundaryDart data hdata first
  let secondDart := innerBoundaryDart data hdata second
  have hfirst : dartOrbitFace embedded.RS firstDart =
      embedded.cellulation.innerHole :=
    innerBoundaryDart_on_innerHole embedded hdata first
  have hsecondOn : secondDart ∈
      embedded.RS.dartsOn (data.innerBoundaryEdge second) :=
    innerBoundaryDart_mem_dartsOn embedded hdata second
  have hsecondAlphaOn : embedded.RS.alpha secondDart ∈
      embedded.RS.dartsOn (data.innerBoundaryEdge second) :=
    embedded.RS.alpha_mem_dartsOn hsecondOn
  have hsecondAlpha :
      dartOrbitFace embedded.RS (embedded.RS.alpha secondDart) =
        embedded.cellulation.innerHole :=
    embedded.innerBoundaryEdgeDarts_on_innerHole second
      (embedded.RS.alpha secondDart) hsecondAlphaOn
  have hfirstTarget : firstDart ≠ embedded.RS.alpha secondDart := by
    intro hdarts
    have hdartEdges := congrArg (fun dart : G.Dart => dart.edge) hdarts
    have hedges : data.innerBoundaryEdge first =
        data.innerBoundaryEdge second := by
      apply Subtype.ext
      calc
        (data.innerBoundaryEdge first).1 = firstDart.edge :=
          (innerBoundaryDart_edge data hdata first).symm
        _ = secondDart.edge := by simpa using hdartEdges
        _ = (data.innerBoundaryEdge second).1 :=
          innerBoundaryDart_edge data hdata second
    exact hne (data.innerBoundaryEdge.injective hedges)
  rcases exists_coreFaceArcWalk_avoids_endpoint_edges
      embedded.cellulation.rotation embedded.cellulation.innerHole
      firstDart secondDart hfirst hsecondAlpha
      (phi_alpha_innerBoundaryDart embedded hdata first)
      (phi_alpha_innerBoundaryDart embedded hdata second)
      hfirstTarget
      (innerBoundaryDart_ne_phi_innerBoundaryDart embedded hdata hne) with
    ⟨arc, hface, hlength, hfirstEdge, hsecondEdge⟩
  refine ⟨arc, hface, hlength, ?_, ?_⟩
  · simpa [firstDart] using hfirstEdge
  · simpa [secondDart] using hsecondEdge

/-- The corresponding actual outer-hole core segment. -/
theorem exists_outerHoleCoreArcWalk
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) (first second : Fin outerCount) :
    ∃ arc : G.Walk
        (outerBoundaryDart data hdata first).snd
        (outerBoundaryDart data hdata second).snd,
      (∀ dart ∈ arc.darts,
        dartOrbitFace embedded.RS dart = embedded.cellulation.outerHole) ∧
      arc.length <
        (embedded.RS.faceOrbit
          (embedded.RS.phi (outerBoundaryDart data hdata first))).card := by
  let firstDart := outerBoundaryDart data hdata first
  let secondDart := outerBoundaryDart data hdata second
  have hfirst : dartOrbitFace embedded.RS firstDart =
      embedded.cellulation.outerHole :=
    outerBoundaryDart_on_outerHole embedded hdata first
  have hsecondOn : secondDart ∈
      embedded.RS.dartsOn (data.outerBoundaryEdge second) :=
    outerBoundaryDart_mem_dartsOn embedded hdata second
  have hsecondAlphaOn : embedded.RS.alpha secondDart ∈
      embedded.RS.dartsOn (data.outerBoundaryEdge second) :=
    embedded.RS.alpha_mem_dartsOn hsecondOn
  have hsecondAlpha :
      dartOrbitFace embedded.RS (embedded.RS.alpha secondDart) =
        embedded.cellulation.outerHole :=
    embedded.outerBoundaryEdgeDarts_on_outerHole second
      (embedded.RS.alpha secondDart) hsecondAlphaOn
  exact exists_coreFaceArcWalk embedded.cellulation.rotation
    embedded.cellulation.outerHole firstDart secondDart hfirst hsecondAlpha

theorem exists_outerHoleCoreArcWalk_isTrail_of_local_twoSided
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) (first second : Fin outerCount)
    (htargetOrbit : embedded.RS.alpha
        (outerBoundaryDart data hdata second) ∈
      embedded.RS.faceOrbit
        (embedded.RS.phi (outerBoundaryDart data hdata first)))
    (hlocal : ∀ dart ∈ faceArcDarts embedded.cellulation.rotation
        (embedded.RS.phi (outerBoundaryDart data hdata first))
        (embedded.RS.alpha (outerBoundaryDart data hdata second))
        htargetOrbit,
      dartOrbitFace embedded.RS dart ≠
        dartOrbitFace embedded.RS (embedded.RS.alpha dart)) :
    ∃ arc : G.Walk
        (outerBoundaryDart data hdata first).snd
        (outerBoundaryDart data hdata second).snd,
      arc.IsTrail ∧
      (∀ dart ∈ arc.darts,
        dartOrbitFace embedded.RS dart = embedded.cellulation.outerHole) ∧
      arc.length <
        (embedded.RS.faceOrbit
          (embedded.RS.phi (outerBoundaryDart data hdata first))).card := by
  let firstDart := outerBoundaryDart data hdata first
  let secondDart := outerBoundaryDart data hdata second
  have hfirst : dartOrbitFace embedded.RS firstDart =
      embedded.cellulation.outerHole :=
    outerBoundaryDart_on_outerHole embedded hdata first
  have hsecondOn : secondDart ∈
      embedded.RS.dartsOn (data.outerBoundaryEdge second) :=
    outerBoundaryDart_mem_dartsOn embedded hdata second
  have hsecondAlphaOn : embedded.RS.alpha secondDart ∈
      embedded.RS.dartsOn (data.outerBoundaryEdge second) :=
    embedded.RS.alpha_mem_dartsOn hsecondOn
  have hsecondAlpha :
      dartOrbitFace embedded.RS (embedded.RS.alpha secondDart) =
        embedded.cellulation.outerHole :=
    embedded.outerBoundaryEdgeDarts_on_outerHole second
      (embedded.RS.alpha secondDart) hsecondAlphaOn
  rcases exists_coreFaceArcWalk_isTrail_of_local_twoSided
      embedded.cellulation.rotation embedded.cellulation.outerHole
      firstDart secondDart hfirst hsecondAlpha htargetOrbit hlocal with
    ⟨arc, htrail, hface, hlength⟩
  exact ⟨arc, htrail, hface, hlength⟩

/-- For two distinct outer anchors, the outer core arc likewise avoids both
radial-path boundary edges. -/
theorem exists_outerHoleCoreArcWalk_avoids_boundaryEdges
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) {first second : Fin outerCount}
    (hne : first ≠ second) :
    ∃ arc : G.Walk
        (outerBoundaryDart data hdata first).snd
        (outerBoundaryDart data hdata second).snd,
      (∀ dart ∈ arc.darts,
        dartOrbitFace embedded.RS dart = embedded.cellulation.outerHole) ∧
      arc.length <
        (embedded.RS.faceOrbit
          (embedded.RS.phi (outerBoundaryDart data hdata first))).card ∧
      (data.outerBoundaryEdge first).1 ∉ arc.edges ∧
      (data.outerBoundaryEdge second).1 ∉ arc.edges := by
  let firstDart := outerBoundaryDart data hdata first
  let secondDart := outerBoundaryDart data hdata second
  have hfirst : dartOrbitFace embedded.RS firstDart =
      embedded.cellulation.outerHole :=
    outerBoundaryDart_on_outerHole embedded hdata first
  have hsecondOn : secondDart ∈
      embedded.RS.dartsOn (data.outerBoundaryEdge second) :=
    outerBoundaryDart_mem_dartsOn embedded hdata second
  have hsecondAlphaOn : embedded.RS.alpha secondDart ∈
      embedded.RS.dartsOn (data.outerBoundaryEdge second) :=
    embedded.RS.alpha_mem_dartsOn hsecondOn
  have hsecondAlpha :
      dartOrbitFace embedded.RS (embedded.RS.alpha secondDart) =
        embedded.cellulation.outerHole :=
    embedded.outerBoundaryEdgeDarts_on_outerHole second
      (embedded.RS.alpha secondDart) hsecondAlphaOn
  have hfirstTarget : firstDart ≠ embedded.RS.alpha secondDart := by
    intro hdarts
    have hdartEdges := congrArg (fun dart : G.Dart => dart.edge) hdarts
    have hedges : data.outerBoundaryEdge first =
        data.outerBoundaryEdge second := by
      apply Subtype.ext
      calc
        (data.outerBoundaryEdge first).1 = firstDart.edge :=
          (outerBoundaryDart_edge data hdata first).symm
        _ = secondDart.edge := by simpa using hdartEdges
        _ = (data.outerBoundaryEdge second).1 :=
          outerBoundaryDart_edge data hdata second
    exact hne (data.outerBoundaryEdge.injective hedges)
  rcases exists_coreFaceArcWalk_avoids_endpoint_edges
      embedded.cellulation.rotation embedded.cellulation.outerHole
      firstDart secondDart hfirst hsecondAlpha
      (phi_alpha_outerBoundaryDart embedded hdata first)
      (phi_alpha_outerBoundaryDart embedded hdata second)
      hfirstTarget
      (outerBoundaryDart_ne_phi_outerBoundaryDart embedded hdata hne) with
    ⟨arc, hface, hlength, hfirstEdge, hsecondEdge⟩
  refine ⟨arc, hface, hlength, ?_, ?_⟩
  · simpa [firstDart] using hfirstEdge
  · simpa [secondDart] using hsecondEdge

end

end GoertzelV24ClosedWebHoleCoreArcWalk

end Mettapedia.GraphTheory.FourColor
