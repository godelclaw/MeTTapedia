import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicFaceCutTrailTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedMeshResidualSiteFacialBond

/-!
# Facial bonds at distinct sites are laminar

`GoertzelV24OrderedMeshResidualSiteFacialBond` supplies, at every global mesh
step, a `ProperAlternatingSiteFacialBondWitness`: a simple ambient cycle
together with the face set it separates, both of whose shores induce connected
subgraphs of the facial dual.  Its docstring deliberately disclaims any
relation between the face sets chosen at two different sites.

This file supplies that relation.  Two such face sets are **laminar** — nested,
disjoint, or jointly exhausting — as soon as the two primal cycles are
vertex-disjoint.

The proof is local, and it is the cubic rotation that carries it.  Write
`BothSidesIn faces d` for "both facial sides of `d`'s edge lie in `faces`".
If two darts sit at one vertex of a cubic map and neither of their edges
separates `faces`, then one of them is the rotation successor of the other,
so the two edges share a facial sector and `BothSidesIn` agrees on them.
Walking that step along the second cycle — none of whose edges lies on the
first cycle — makes `BothSidesIn facesOne` constant on the second cycle.  A
crossing pair would force it to be both true and false there: connectedness of
`facesOne` produces a second-cycle edge with both sides inside `facesOne`, and
connectedness of the complement produces one with both sides outside.

Vertex-disjointness enters only through the edge-disjointness it implies, and
`vertexDisjoint_iff_edgeDisjoint_of_isCubic` shows the two hypotheses coincide
for cycles in a cubic map: a shared vertex leaves only three edges for two
pairs.  Neither is a graph-theoretic substitute for the geometry on its own --
`crossing_edgeDisjoint_bonds_in_dual_four_cycle` exhibits a dual four-cycle in
which two edge-disjoint bonds with connected shores cross, so the primal-cycle
and rotation data really are consumed.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FacialBondLaminarity

open SimpleGraph
open SimpleGraphDartRotation
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24PrimalCycleFacialBond
open GoertzelV24TwoEdgeCutMinimality

/-! ## A predicate constant along a chain -/

/-- A predicate that agrees across every consecutive pair of a chain agrees
across every pair of its entries. -/
theorem isChain_pred_iff {α : Type*} {R : α → α → Prop} {P : α → Prop} :
    ∀ list : List α, list.IsChain R →
      (∀ first ∈ list, ∀ second ∈ list, R first second → (P first ↔ P second)) →
      ∀ first ∈ list, ∀ second ∈ list, (P first ↔ P second) := by
  intro list
  induction list with
  | nil =>
      intro _ _ first hfirst
      simp at hfirst
  | cons head tail ih =>
      intro hchain hstep
      have hhead : ∀ entry ∈ head :: tail, (P entry ↔ P head) := by
        cases tail with
        | nil =>
            intro entry hentry
            simp only [List.mem_singleton] at hentry
            subst hentry
            exact Iff.rfl
        | cons second rest =>
            obtain ⟨hlink, hchainTail⟩ := List.isChain_cons_cons.mp hchain
            have hsub : ∀ entry ∈ second :: rest, entry ∈ head :: second :: rest :=
              fun entry hentry => List.mem_cons_of_mem _ hentry
            have ihtail := ih hchainTail
              (fun a ha b hb hab => hstep a (hsub a ha) b (hsub b hb) hab)
            have hlinkIff : P head ↔ P second :=
              hstep head (by simp) second (by simp) hlink
            intro entry hentry
            rcases List.mem_cons.mp hentry with hentry | hentry
            · subst hentry
              exact Iff.rfl
            · exact (ihtail entry hentry second (by simp)).trans hlinkIff.symm
      intro first hfirst second hsecond
      exact (hhead first hfirst).trans (hhead second hsecond).symm

/-! ## Two-sided membership of an edge -/

section Rotation

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Both facial sides of a dart's edge lie in the selected face set. -/
def BothSidesIn (RS : RotationSystem V E)
    (faces : Finset (OrbitFace RS)) (dart : RS.D) : Prop :=
  dartOrbitFace RS dart ∈ faces ∧
    dartOrbitFace RS (RS.alpha dart) ∈ faces

/-- The edge does not separate the face set. -/
def JointSides (RS : RotationSystem V E)
    (faces : Finset (OrbitFace RS)) (dart : RS.D) : Prop :=
  dartOrbitFace RS dart ∈ faces ↔
    dartOrbitFace RS (RS.alpha dart) ∈ faces

/-- Two-sided membership is a property of the edge, not of its orientation. -/
theorem bothSidesIn_alpha (RS : RotationSystem V E)
    (faces : Finset (OrbitFace RS)) (dart : RS.D) :
    BothSidesIn RS faces (RS.alpha dart) ↔ BothSidesIn RS faces dart := by
  unfold BothSidesIn
  rw [RS.alpha_involutive dart]
  exact and_comm

/-- Non-separation is a property of the edge, not of its orientation. -/
theorem jointSides_alpha (RS : RotationSystem V E)
    (faces : Finset (OrbitFace RS)) {dart : RS.D}
    (hjoint : JointSides RS faces dart) :
    JointSides RS faces (RS.alpha dart) := by
  unfold JointSides at hjoint ⊢
  rw [RS.alpha_involutive dart]
  exact hjoint.symm

/-- On a non-separating edge, two-sided membership is decided by the near
side alone. -/
theorem bothSidesIn_iff_near (RS : RotationSystem V E)
    (faces : Finset (OrbitFace RS)) {dart : RS.D}
    (hjoint : JointSides RS faces dart) :
    BothSidesIn RS faces dart ↔ dartOrbitFace RS dart ∈ faces :=
  ⟨fun hboth => hboth.1, fun hnear => ⟨hnear, hjoint.1 hnear⟩⟩

/-- On a non-separating edge, two-sided membership is decided by the far
side alone. -/
theorem bothSidesIn_iff_far (RS : RotationSystem V E)
    (faces : Finset (OrbitFace RS)) {dart : RS.D}
    (hjoint : JointSides RS faces dart) :
    BothSidesIn RS faces dart ↔ dartOrbitFace RS (RS.alpha dart) ∈ faces :=
  ⟨fun hboth => hboth.2, fun hfar => ⟨hjoint.2 hfar, hfar⟩⟩

/-- **The local step.**  Two darts at one vertex of a cubic map share a facial
sector, because one is the rotation successor of the other and
`dartOrbitFace (alpha d) = dartOrbitFace (rho d)`.  If neither edge separates
the face set, two-sided membership agrees on them. -/
theorem bothSidesIn_iff_of_vertOf_eq (RS : RotationSystem V E)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (faces : Finset (OrbitFace RS)) {first second : RS.D}
    (hbase : RS.vertOf second = RS.vertOf first)
    (hfirst : JointSides RS faces first)
    (hsecond : JointSides RS faces second) :
    BothSidesIn RS faces first ↔ BothSidesIn RS faces second := by
  by_cases hne : first = second
  · subst hne
    exact Iff.rfl
  rcases RS.rho_eq_or_rho_eq_of_cubic hcubic hrotation hbase hne with
    hforward | hbackward
  · have hshare : dartOrbitFace RS (RS.alpha first) = dartOrbitFace RS second := by
      rw [dartOrbitFace_alpha_eq_dartOrbitFace_rho RS first, hforward]
    rw [bothSidesIn_iff_far RS faces hfirst,
      bothSidesIn_iff_near RS faces hsecond, hshare]
  · have hshare : dartOrbitFace RS (RS.alpha second) = dartOrbitFace RS first := by
      rw [dartOrbitFace_alpha_eq_dartOrbitFace_rho RS second, hbackward]
    rw [bothSidesIn_iff_near RS faces hfirst,
      bothSidesIn_iff_far RS faces hsecond, hshare]

end Rotation

/-! ## Facial bonds of a graph-backed rotation system -/

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance facialBondLaminarityEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The primal edges of `cycle` are exactly the edges separating `faces` from
its complement.  This is the `cycle_separates_faces` field of
`ProperAlternatingSiteFacialBondWitness`, named for reuse. -/
def CycleSeparatesFaces (data : Data G) {root : V} (cycle : G.Walk root root)
    (faces : Finset (OrbitFace data.toRotationSystem)) : Prop :=
  ∀ dart : data.toRotationSystem.D,
    (data.toRotationSystem.edgeOf dart).1 ∈ cycle.edges ↔
      ((dartOrbitFace data.toRotationSystem dart ∈ faces ∧
          dartOrbitFace data.toRotationSystem
            (data.toRotationSystem.alpha dart) ∉ faces) ∨
        (dartOrbitFace data.toRotationSystem dart ∉ faces ∧
          dartOrbitFace data.toRotationSystem
            (data.toRotationSystem.alpha dart) ∈ faces))

/-- A facial-dual adjacency is realized by an oriented primal edge. -/
theorem exists_dart_of_orbitFaceDualGraph_adj (data : Data G)
    {left right : OrbitFace data.toRotationSystem}
    (hadj : (orbitFaceDualGraph data).Adj left right) :
    ∃ dart : data.toRotationSystem.D,
      dartOrbitFace data.toRotationSystem dart = left ∧
      dartOrbitFace data.toRotationSystem
        (data.toRotationSystem.alpha dart) = right := by
  rcases (interiorDualGraph_adj_iff (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).1 hadj with
    ⟨hne, edge, _hinterior, hleft, hright⟩
  rcases (mem_orbitFaceBoundary_iff data.toRotationSystem left edge).1 hleft with
    ⟨leftDart, hleftDart, hleftEdge⟩
  rcases (mem_orbitFaceBoundary_iff data.toRotationSystem right edge).1 hright with
    ⟨rightDart, hrightDart, hrightEdge⟩
  have hleftFace : dartOrbitFace data.toRotationSystem leftDart = left :=
    (mem_orbitFaceDarts_iff data.toRotationSystem left leftDart).1 hleftDart
  have hrightFace : dartOrbitFace data.toRotationSystem rightDart = right :=
    (mem_orbitFaceDarts_iff data.toRotationSystem right rightDart).1 hrightDart
  rcases data.toRotationSystem.edge_fiber_two_cases hleftEdge hrightEdge with
    hsame | hflip
  · exact absurd (hleftFace.symm.trans
      ((congrArg (dartOrbitFace data.toRotationSystem) hsame).symm.trans
        hrightFace)) hne
  · refine ⟨leftDart, hleftFace, ?_⟩
    rw [← hflip]
    exact hrightFace

/-- Inside a connected face shore meeting a second face set and its
complement, some primal edge has both facial sides in the shore while its two
sides split the second set. -/
theorem exists_dart_bothSidesIn_separating (data : Data G)
    (shore : Set (OrbitFace data.toRotationSystem))
    (hshore : ((orbitFaceDualGraph data).induce shore).Connected)
    (faces : Finset (OrbitFace data.toRotationSystem))
    {selected unselected : OrbitFace data.toRotationSystem}
    (hselectedShore : selected ∈ shore) (hunselectedShore : unselected ∈ shore)
    (hselected : selected ∈ faces) (hunselected : unselected ∉ faces) :
    ∃ dart : data.toRotationSystem.D,
      dartOrbitFace data.toRotationSystem dart ∈ shore ∧
      dartOrbitFace data.toRotationSystem
        (data.toRotationSystem.alpha dart) ∈ shore ∧
      dartOrbitFace data.toRotationSystem dart ∈ faces ∧
      dartOrbitFace data.toRotationSystem
        (data.toRotationSystem.alpha dart) ∉ faces := by
  classical
  obtain ⟨walk⟩ := hshore.preconnected ⟨selected, hselectedShore⟩
    ⟨unselected, hunselectedShore⟩
  obtain ⟨boundaryDart, _hmem, hnear, hfar⟩ :=
    walk.exists_boundary_dart
      {face : shore | (face : OrbitFace data.toRotationSystem) ∈ faces}
      hselected hunselected
  have hadj : (orbitFaceDualGraph data).Adj boundaryDart.fst.1 boundaryDart.snd.1 :=
    boundaryDart.adj
  obtain ⟨dart, hleft, hright⟩ :=
    exists_dart_of_orbitFaceDualGraph_adj data hadj
  refine ⟨dart, ?_, ?_, ?_, ?_⟩
  · rw [hleft]
    exact boundaryDart.fst.2
  · rw [hright]
    exact boundaryDart.snd.2
  · rw [hleft]
    exact hnear
  · rw [hright]
    exact hfar

/-- An edge of a walk is carried by one of the walk's own darts, and two-sided
membership does not distinguish a dart from its reverse. -/
theorem exists_walkDart_bothSidesIn_iff (data : Data G)
    (faces : Finset (OrbitFace data.toRotationSystem))
    {root : V} (cycle : G.Walk root root)
    {dart : data.toRotationSystem.D}
    (hedge : (data.toRotationSystem.edgeOf dart).1 ∈ cycle.edges) :
    ∃ walkDart ∈ cycle.darts,
      (BothSidesIn data.toRotationSystem faces walkDart ↔
        BothSidesIn data.toRotationSystem faces dart) := by
  have hmap : (data.toRotationSystem.edgeOf dart).1 ∈
      cycle.darts.map SimpleGraph.Dart.edge := hedge
  obtain ⟨walkDart, hwalkDart, hwalkEdge⟩ := List.mem_map.1 hmap
  have hedgeEq : data.toRotationSystem.edgeOf walkDart =
      data.toRotationSystem.edgeOf dart := Subtype.ext hwalkEdge
  rcases data.toRotationSystem.edge_fiber_two_cases
      (rfl : data.toRotationSystem.edgeOf dart = data.toRotationSystem.edgeOf dart)
      hedgeEq with hsame | hflip
  · exact ⟨walkDart, hwalkDart, by rw [hsame]⟩
  · exact ⟨walkDart, hwalkDart, by
      rw [hflip]
      exact bothSidesIn_alpha data.toRotationSystem faces dart⟩

/-! ## Laminarity -/

/-- **Target theorem.**  Two facial bonds of a cubic rotation system whose
primal cycles share no edge have laminar face sets.

Only the first bond's two shores are required to be connected; the second
bond enters only through its separator property. -/
theorem faces_laminar_of_edgeDisjoint_separating_cycles
    (data : Data G) (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    {rootOne rootTwo : V}
    (cycleOne : G.Walk rootOne rootOne) (cycleTwo : G.Walk rootTwo rootTwo)
    (facesOne facesTwo : Finset (OrbitFace data.toRotationSystem))
    (hseparatesOne : CycleSeparatesFaces data cycleOne facesOne)
    (hseparatesTwo : CycleSeparatesFaces data cycleTwo facesTwo)
    (hselectedConnected :
      ((orbitFaceDualGraph data).induce {face | face ∈ facesOne}).Connected)
    (hcomplementConnected :
      ((orbitFaceDualGraph data).induce {face | face ∉ facesOne}).Connected)
    (hedgeDisjoint : ∀ edge ∈ cycleTwo.edges, edge ∉ cycleOne.edges) :
    facesOne ⊆ facesTwo ∨ facesTwo ⊆ facesOne ∨
      Disjoint facesOne facesTwo ∨ facesOne ∪ facesTwo = Finset.univ := by
  classical
  by_contra hcross
  push_neg at hcross
  obtain ⟨hnotSubset, hnotSuperset, hnotDisjoint, hnotCover⟩ := hcross
  obtain ⟨onlyOne, honlyOneIn, honlyOneOut⟩ := Finset.not_subset.1 hnotSubset
  obtain ⟨both, hbothOne, hbothTwo⟩ := Finset.not_disjoint_iff.1 hnotDisjoint
  obtain ⟨onlyTwo, honlyTwoIn, honlyTwoOut⟩ := Finset.not_subset.1 hnotSuperset
  obtain ⟨neither, hneitherOne, hneitherTwo⟩ :
      ∃ face, face ∉ facesOne ∧ face ∉ facesTwo := by
    by_contra hall
    push_neg at hall
    refine hnotCover (Finset.eq_univ_of_forall fun face => ?_)
    rw [Finset.mem_union]
    by_cases hface : face ∈ facesOne
    · exact Or.inl hface
    · exact Or.inr (hall face hface)
  obtain ⟨insideDart, hinsideNear, hinsideFar, hinsideTwo, hinsideNotTwo⟩ :=
    exists_dart_bothSidesIn_separating data
      ({face | face ∈ facesOne} : Set (OrbitFace data.toRotationSystem))
      hselectedConnected facesTwo hbothOne honlyOneIn hbothTwo honlyOneOut
  obtain ⟨outsideDart, houtsideNear, houtsideFar, houtsideTwo, houtsideNotTwo⟩ :=
    exists_dart_bothSidesIn_separating data
      ({face | face ∉ facesOne} : Set (OrbitFace data.toRotationSystem))
      hcomplementConnected facesTwo honlyTwoOut hneitherOne honlyTwoIn hneitherTwo
  have hinsideEdge : (data.toRotationSystem.edgeOf insideDart).1 ∈ cycleTwo.edges :=
    (hseparatesTwo insideDart).2 (Or.inl ⟨hinsideTwo, hinsideNotTwo⟩)
  have houtsideEdge : (data.toRotationSystem.edgeOf outsideDart).1 ∈ cycleTwo.edges :=
    (hseparatesTwo outsideDart).2 (Or.inl ⟨houtsideTwo, houtsideNotTwo⟩)
  have hinsideBoth : BothSidesIn data.toRotationSystem facesOne insideDart :=
    ⟨hinsideNear, hinsideFar⟩
  have houtsideNotBoth : ¬ BothSidesIn data.toRotationSystem facesOne outsideDart :=
    fun hboth => houtsideNear hboth.1
  have hjoint : ∀ walkDart ∈ cycleTwo.darts,
      JointSides data.toRotationSystem facesOne walkDart := by
    intro walkDart hwalkDart
    have hwalkEdgeTwo : (data.toRotationSystem.edgeOf walkDart).1 ∈ cycleTwo.edges :=
      List.mem_map_of_mem hwalkDart
    have hwalkEdgeNotOne :
        (data.toRotationSystem.edgeOf walkDart).1 ∉ cycleOne.edges :=
      hedgeDisjoint _ hwalkEdgeTwo
    constructor
    · intro hnear
      by_contra hfar
      exact hwalkEdgeNotOne ((hseparatesOne walkDart).2 (Or.inl ⟨hnear, hfar⟩))
    · intro hfar
      by_contra hnear
      exact hwalkEdgeNotOne ((hseparatesOne walkDart).2 (Or.inr ⟨hnear, hfar⟩))
  have hconstant := isChain_pred_iff
    (P := BothSidesIn data.toRotationSystem facesOne)
    cycleTwo.darts (SimpleGraph.Walk.isChain_dartAdj_darts cycleTwo) ?_
  · obtain ⟨insideWalkDart, hinsideWalkMem, hinsideWalkIff⟩ :=
      exists_walkDart_bothSidesIn_iff data facesOne cycleTwo hinsideEdge
    obtain ⟨outsideWalkDart, houtsideWalkMem, houtsideWalkIff⟩ :=
      exists_walkDart_bothSidesIn_iff data facesOne cycleTwo houtsideEdge
    exact houtsideNotBoth (houtsideWalkIff.1
      ((hconstant insideWalkDart hinsideWalkMem outsideWalkDart
        houtsideWalkMem).1 (hinsideWalkIff.2 hinsideBoth)))
  · intro first hfirst second hsecond hlink
    have hbase : data.toRotationSystem.vertOf second =
        data.toRotationSystem.vertOf (data.toRotationSystem.alpha first) := by
      change second.fst = (first.symm).fst
      exact hlink.symm
    refine (bothSidesIn_alpha data.toRotationSystem facesOne first).symm.trans ?_
    exact bothSidesIn_iff_of_vertOf_eq data.toRotationSystem hcubic hrotation
      facesOne hbase
      (jointSides_alpha data.toRotationSystem facesOne (hjoint first hfirst))
      (hjoint second hsecond)

/-- The requested form: vertex-disjoint primal cycles. -/
theorem faces_laminar_of_vertexDisjoint_separating_cycles
    (data : Data G) (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    {rootOne rootTwo : V}
    (cycleOne : G.Walk rootOne rootOne) (cycleTwo : G.Walk rootTwo rootTwo)
    (facesOne facesTwo : Finset (OrbitFace data.toRotationSystem))
    (hseparatesOne : CycleSeparatesFaces data cycleOne facesOne)
    (hseparatesTwo : CycleSeparatesFaces data cycleTwo facesTwo)
    (hselectedConnected :
      ((orbitFaceDualGraph data).induce {face | face ∈ facesOne}).Connected)
    (hcomplementConnected :
      ((orbitFaceDualGraph data).induce {face | face ∉ facesOne}).Connected)
    (hvertexDisjoint :
      ∀ vertex ∈ cycleTwo.support, vertex ∉ cycleOne.support) :
    facesOne ⊆ facesTwo ∨ facesTwo ⊆ facesOne ∨
      Disjoint facesOne facesTwo ∨ facesOne ∪ facesTwo = Finset.univ := by
  refine faces_laminar_of_edgeDisjoint_separating_cycles data hcubic hrotation
    cycleOne cycleTwo facesOne facesTwo hseparatesOne hseparatesTwo
    hselectedConnected hcomplementConnected ?_
  intro edge hedgeTwo hedgeOne
  induction edge using Sym2.ind with
  | _ left _right =>
      exact hvertexDisjoint left
        (cycleTwo.fst_mem_support_of_mem_edges hedgeTwo)
        (cycleOne.fst_mem_support_of_mem_edges hedgeOne)

/-! ## Vertex-disjointness and edge-disjointness agree on a cubic map -/

/-- Two cycles through a vertex of degree three share an edge: the vertex
carries three edges and each cycle uses two of them. -/
theorem exists_common_edge_of_common_support_of_ncard_neighborSet_eq_three
    {rootOne rootTwo : V}
    {cycleOne : G.Walk rootOne rootOne} {cycleTwo : G.Walk rootTwo rootTwo}
    (hcycleOne : cycleOne.IsCycle) (hcycleTwo : cycleTwo.IsCycle)
    {vertex : V} (hdegree : (G.neighborSet vertex).ncard = 3)
    (honeSupport : vertex ∈ cycleOne.support)
    (htwoSupport : vertex ∈ cycleTwo.support) :
    ∃ edge ∈ cycleOne.edges, edge ∈ cycleTwo.edges := by
  classical
  have hcardOne : (cycleOne.toSubgraph.neighborSet vertex).ncard = 2 :=
    hcycleOne.ncard_neighborSet_toSubgraph_eq_two honeSupport
  have hcardTwo : (cycleTwo.toSubgraph.neighborSet vertex).ncard = 2 :=
    hcycleTwo.ncard_neighborSet_toSubgraph_eq_two htwoSupport
  have hsubOne : cycleOne.toSubgraph.neighborSet vertex ⊆ G.neighborSet vertex :=
    fun _ hother => cycleOne.toSubgraph.adj_sub hother
  have hsubTwo : cycleTwo.toSubgraph.neighborSet vertex ⊆ G.neighborSet vertex :=
    fun _ hother => cycleTwo.toSubgraph.adj_sub hother
  have hunion :
      (cycleOne.toSubgraph.neighborSet vertex ∪
        cycleTwo.toSubgraph.neighborSet vertex).ncard ≤ 3 := by
    rw [← hdegree]
    exact Set.ncard_le_ncard (Set.union_subset hsubOne hsubTwo) (Set.toFinite _)
  have hsum := Set.ncard_union_add_ncard_inter
    (cycleOne.toSubgraph.neighborSet vertex)
    (cycleTwo.toSubgraph.neighborSet vertex)
  have hinter : (cycleOne.toSubgraph.neighborSet vertex ∩
      cycleTwo.toSubgraph.neighborSet vertex).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, Set.ncard_empty, hcardOne, hcardTwo] at hsum
    omega
  obtain ⟨other, hotherOne, hotherTwo⟩ := hinter
  exact ⟨s(vertex, other),
    SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.1 hotherOne,
    SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.1 hotherTwo⟩

/-- On a cubic map the two disjointness hypotheses coincide for cycles, so
`faces_laminar_of_edgeDisjoint_separating_cycles` is exactly the
vertex-disjoint statement. -/
theorem vertexDisjoint_iff_edgeDisjoint_of_isCubic
    (data : Data G) (hcubic : data.toRotationSystem.IsCubic)
    {rootOne rootTwo : V}
    {cycleOne : G.Walk rootOne rootOne} {cycleTwo : G.Walk rootTwo rootTwo}
    (hcycleOne : cycleOne.IsCycle) (hcycleTwo : cycleTwo.IsCycle) :
    (∀ vertex ∈ cycleTwo.support, vertex ∉ cycleOne.support) ↔
      (∀ edge ∈ cycleTwo.edges, edge ∉ cycleOne.edges) := by
  constructor
  · intro hvertex edge hedgeTwo hedgeOne
    induction edge using Sym2.ind with
    | _ left _right =>
        exact hvertex left
          (cycleTwo.fst_mem_support_of_mem_edges hedgeTwo)
          (cycleOne.fst_mem_support_of_mem_edges hedgeOne)
  · intro hedge vertex htwoSupport honeSupport
    have hregular := data.toRotationSystem_isCubic_iff.1 hcubic
    have hdegree : (G.neighborSet vertex).ncard = 3 := by
      rw [Set.ncard_eq_toFinset_card', Set.toFinset_card,
        G.card_neighborSet_eq_degree]
      exact (SimpleGraph.degree_instance_independent vertex _ _).trans
        (hregular vertex)
    obtain ⟨edge, hedgeOne, hedgeTwo⟩ :=
      exists_common_edge_of_common_support_of_ncard_neighborSet_eq_three
        hcycleOne hcycleTwo hdegree honeSupport htwoSupport
    exact hedge edge hedgeTwo hedgeOne

/-! ## The site-to-site compatibility -/

/-- **The disclaimed compatibility, supplied.**  The face sets selected by two
residual-site facial bonds of one global pairing are laminar whenever their
alternating cycles are vertex-disjoint. -/
theorem bond_faces_laminar_of_vertexDisjoint
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {sigma : MatchingParity.Pairing V} {firstOne secondOne firstTwo secondTwo : V}
    (bondOne : ProperAlternatingSiteFacialBondWitness rotation sigma
      firstOne secondOne)
    (bondTwo : ProperAlternatingSiteFacialBondWitness rotation sigma
      firstTwo secondTwo)
    (hvertexDisjoint : ∀ vertex ∈ bondTwo.site.cycle.support,
      vertex ∉ bondOne.site.cycle.support) :
    bondOne.faces ⊆ bondTwo.faces ∨ bondTwo.faces ⊆ bondOne.faces ∨
      Disjoint bondOne.faces bondTwo.faces ∨
      bondOne.faces ∪ bondTwo.faces = Finset.univ :=
  faces_laminar_of_vertexDisjoint_separating_cycles rotation
    minimal.spherical.cubic minimal.vertexRotationCyclic
    bondOne.site.cycle bondTwo.site.cycle bondOne.faces bondTwo.faces
    bondOne.cycle_separates_faces bondTwo.cycle_separates_faces
    bondOne.selected_faces_connected bondOne.complement_faces_connected
    hvertexDisjoint

/-- The same conclusion from disjoint alternating carriers, the finite form
the residual development manipulates. -/
theorem bond_faces_laminar_of_disjoint_carriers
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {sigma : MatchingParity.Pairing V} {firstOne secondOne firstTwo secondTwo : V}
    (bondOne : ProperAlternatingSiteFacialBondWitness rotation sigma
      firstOne secondOne)
    (bondTwo : ProperAlternatingSiteFacialBondWitness rotation sigma
      firstTwo secondTwo)
    (hdisjoint : Disjoint bondOne.site.carrier bondTwo.site.carrier) :
    bondOne.faces ⊆ bondTwo.faces ∨ bondTwo.faces ⊆ bondOne.faces ∨
      Disjoint bondOne.faces bondTwo.faces ∨
      bondOne.faces ∪ bondTwo.faces = Finset.univ := by
  refine bond_faces_laminar_of_vertexDisjoint rotation minimal bondOne bondTwo ?_
  intro vertex htwoSupport honeSupport
  have hmemTwo : vertex ∈ bondTwo.site.carrier := by
    rw [← bondTwo.site.cycle_support_eq]
    exact List.mem_toFinset.2 htwoSupport
  have hmemOne : vertex ∈ bondOne.site.carrier := by
    rw [← bondOne.site.cycle_support_eq]
    exact List.mem_toFinset.2 honeSupport
  exact (Finset.disjoint_left.1 hdisjoint hmemOne) hmemTwo

end

/-! ## Edge-disjointness alone is not a substitute for the geometry -/

/-- A graph in which any two vertices are equal or adjacent is connected. -/
theorem connected_of_forall_eq_or_adj {α : Type*} [hnonempty : Nonempty α]
    (graph : SimpleGraph α)
    (hclique : ∀ left right : α, left = right ∨ graph.Adj left right) :
    graph.Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨fun left right => ?_, hnonempty⟩
  rcases hclique left right with hEq | hAdj
  · subst hEq
    exact SimpleGraph.Reachable.refl left
  · exact hAdj.reachable

/-- A two-element side carrying an edge induces a connected subgraph. -/
theorem induce_pair_connected {α : Type*} (graph : SimpleGraph α)
    (side : Set α) {near far : α} (hnear : near ∈ side)
    (hside : ∀ vertex ∈ side, vertex = near ∨ vertex = far)
    (hadj : graph.Adj near far) :
    (graph.induce side).Connected := by
  haveI : Nonempty ↥side := ⟨⟨near, hnear⟩⟩
  refine connected_of_forall_eq_or_adj _ ?_
  rintro ⟨leftValue, hleft⟩ ⟨rightValue, hright⟩
  rcases hside leftValue hleft with rfl | rfl <;>
    rcases hside rightValue hright with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr hadj
  · exact Or.inr hadj.symm
  · exact Or.inl rfl

/-- Four sets that pairwise overlap in all four patterns are not laminar. -/
theorem not_laminar_of_crossing {α : Type*} [DecidableEq α] [Fintype α]
    {first second : Finset α}
    (honlyFirst : ∃ face, face ∈ first ∧ face ∉ second)
    (hboth : ∃ face, face ∈ first ∧ face ∈ second)
    (honlySecond : ∃ face, face ∉ first ∧ face ∈ second)
    (hneither : ∃ face, face ∉ first ∧ face ∉ second) :
    ¬ (first ⊆ second ∨ second ⊆ first ∨ Disjoint first second ∨
        first ∪ second = Finset.univ) := by
  obtain ⟨onlyFirst, honlyFirstIn, honlyFirstOut⟩ := honlyFirst
  obtain ⟨overlap, hoverlapFirst, hoverlapSecond⟩ := hboth
  obtain ⟨onlySecond, honlySecondOut, honlySecondIn⟩ := honlySecond
  obtain ⟨neither, hneitherFirst, hneitherSecond⟩ := hneither
  rintro (hsubset | hsuperset | hdisjoint | hcover)
  · exact honlyFirstOut (hsubset honlyFirstIn)
  · exact honlySecondOut (hsuperset honlySecondIn)
  · exact (Finset.disjoint_left.1 hdisjoint hoverlapFirst) hoverlapSecond
  · rcases Finset.mem_union.1 (hcover ▸ Finset.mem_univ neither) with
      hmem | hmem
    · exact hneitherFirst hmem
    · exact hneitherSecond hmem

/-- The four-cycle `0-1-2-3-0`, read as an abstract facial dual. -/
def dualFourCycle : SimpleGraph (Fin 4) where
  Adj left right := left.val % 2 ≠ right.val % 2
  symm := ⟨fun _ _ hadj => Ne.symm hadj⟩
  loopless := ⟨fun _ hadj => hadj rfl⟩

instance dualFourCycleDecidableAdj : DecidableRel dualFourCycle.Adj :=
  fun left right => inferInstanceAs (Decidable (left.val % 2 ≠ right.val % 2))

instance dualFourCycleInduceDecidableAdj (side : Set (Fin 4)) :
    DecidableRel (dualFourCycle.induce side).Adj :=
  fun left right =>
    inferInstanceAs (Decidable (dualFourCycle.Adj left.1 right.1))

/-- Selected side of the first abstract bond. -/
def crossingFirst : Finset (Fin 4) := {0, 1}

/-- Selected side of the second abstract bond. -/
def crossingSecond : Finset (Fin 4) := {1, 2}

/-- **Companion.**  In the dual four-cycle the face sets `{0,1}` and `{1,2}`
each have a connected selected side and a connected complement, and the two
bonds share no dual edge, yet all four of `F₁ ∩ F₂`, `F₁ \ F₂`, `F₂ \ F₁` and
`(F₁ ∪ F₂)ᶜ` are inhabited, so they cross.

Connected shores plus edge-disjoint bonds therefore do not imply laminarity on
their own.  `faces_laminar_of_edgeDisjoint_separating_cycles` escapes this
because its bonds are the edge sets of primal cycles in a cubic rotation
system: the local rotation step is exactly the extra input, and a cubic graph
has no room for two cycles to meet at a vertex without sharing an edge, so
there vertex-disjointness and edge-disjointness say the same thing. -/
theorem crossing_edgeDisjoint_bonds_in_dual_four_cycle :
    (dualFourCycle.induce {face | face ∈ crossingFirst}).Connected ∧
    (dualFourCycle.induce {face | face ∉ crossingFirst}).Connected ∧
    (dualFourCycle.induce {face | face ∈ crossingSecond}).Connected ∧
    (dualFourCycle.induce {face | face ∉ crossingSecond}).Connected ∧
    (∀ left right : Fin 4, dualFourCycle.Adj left right →
      ¬ ((left ∈ crossingFirst ↔ right ∉ crossingFirst) ∧
        (left ∈ crossingSecond ↔ right ∉ crossingSecond))) ∧
    ¬ (crossingFirst ⊆ crossingSecond ∨ crossingSecond ⊆ crossingFirst ∨
        Disjoint crossingFirst crossingSecond ∨
        crossingFirst ∪ crossingSecond = Finset.univ) := by
  refine ⟨?_, ?_, ?_, ?_, by decide, ?_⟩
  · exact induce_pair_connected dualFourCycle _ (near := 0) (far := 1)
      (by decide) (by decide) (by decide)
  · exact induce_pair_connected dualFourCycle _ (near := 2) (far := 3)
      (by decide) (by decide) (by decide)
  · exact induce_pair_connected dualFourCycle _ (near := 1) (far := 2)
      (by decide) (by decide) (by decide)
  · exact induce_pair_connected dualFourCycle _ (near := 3) (far := 0)
      (by decide) (by decide) (by decide)
  · exact not_laminar_of_crossing (by decide) (by decide) (by decide) (by decide)

end GoertzelV24FacialBondLaminarity

end Mettapedia.GraphTheory.FourColor
