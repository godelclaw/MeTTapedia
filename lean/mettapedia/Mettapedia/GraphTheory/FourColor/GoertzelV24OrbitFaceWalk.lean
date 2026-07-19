import Mettapedia.GraphTheory.FourColor.GoertzelV24HexFaceRungType
import Mathlib.Data.List.ChainOfFn

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

namespace GoertzelV24OrbitFaceWalk

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The actual darts of one quotient face, enumerated from a chosen root in
face-permutation order. -/
def faceOrbitDarts (graphData : Data G) (root : G.Dart) : List G.Dart :=
  List.ofFn (faceCycleDart graphData.toRotationSystem root)

@[simp] theorem length_faceOrbitDarts
    (graphData : Data G) (root : G.Dart) :
    (faceOrbitDarts graphData root).length =
      (graphData.toRotationSystem.faceOrbit root).card := by
  simp [faceOrbitDarts]

theorem faceOrbitDarts_ne_nil
    (graphData : Data G) (root : G.Dart) :
    faceOrbitDarts graphData root ≠ [] := by
  rw [← List.length_pos_iff]
  rw [length_faceOrbitDarts]
  exact
    Finset.card_pos.mpr
      ⟨root, graphData.toRotationSystem.mem_faceOrbit_self root⟩

/-- Every dart in the bounded facial enumeration represents the same
quotient face as its root. -/
theorem dartOrbitFace_eq_of_mem_faceOrbitDarts
    (graphData : Data G) (root dart : G.Dart)
    (hdart : dart ∈ faceOrbitDarts graphData root) :
    dartOrbitFace graphData.toRotationSystem dart =
      dartOrbitFace graphData.toRotationSystem root := by
  simp only [faceOrbitDarts, List.mem_ofFn] at hdart
  rcases hdart with ⟨position, rfl⟩
  apply (mem_orbitFaceDarts_iff graphData.toRotationSystem
    (dartOrbitFace graphData.toRotationSystem root) _).1
  rw [orbitFaceDarts_dartOrbitFace_eq_faceOrbit]
  exact faceCycleDart_mem graphData.toRotationSystem root position

/-- A face-permutation step is a valid consecutive-dart step in the
underlying simple graph. -/
theorem dartAdj_phi (graphData : Data G) (dart : G.Dart) :
    G.DartAdj dart (graphData.toRotationSystem.phi dart) := by
  change dart.snd = (graphData.toRotationSystem.phi dart).fst
  simpa using
    (graphData.toRotationSystem.vert_phi_eq_vert_alpha dart).symm

/-- Consecutive darts in the bounded facial enumeration have exactly the
edge obtained by one face-permutation step. -/
theorem faceOrbitDarts_isPhiEdgeChain
    (graphData : Data G) (root : G.Dart) :
    List.IsChain
      (fun first second : G.Dart =>
        graphData.toRotationSystem.edgeOf second =
          graphData.toRotationSystem.edgeOf
            (graphData.toRotationSystem.phi first))
      (faceOrbitDarts graphData root) := by
  rw [faceOrbitDarts, List.isChain_ofFn]
  intro index hnext
  have hsuccessor :
      faceCycleDart graphData.toRotationSystem root
          ⟨index + 1, hnext⟩ =
        graphData.toRotationSystem.phi
          (faceCycleDart graphData.toRotationSystem root
            ⟨index, Nat.lt_of_succ_lt hnext⟩) := by
    simp only [faceCycleDart, pow_succ', Equiv.Perm.coe_mul,
      Function.comp_apply]
  exact congrArg graphData.toRotationSystem.edgeOf hsuccessor

/-- The bounded face-orbit enumeration is a graph-dart chain. -/
theorem faceOrbitDarts_isChain
    (graphData : Data G) (root : G.Dart) :
    List.IsChain G.DartAdj (faceOrbitDarts graphData root) := by
  rw [faceOrbitDarts, List.isChain_ofFn]
  intro index hnext
  have hsuccessor :
      faceCycleDart graphData.toRotationSystem root
          ⟨index + 1, hnext⟩ =
        graphData.toRotationSystem.phi
          (faceCycleDart graphData.toRotationSystem root
            ⟨index, Nat.lt_of_succ_lt hnext⟩) := by
    simp only [faceCycleDart, pow_succ', Equiv.Perm.coe_mul,
      Function.comp_apply]
  rw [hsuccessor]
  exact dartAdj_phi graphData _

/-- The first bounded face-orbit dart is the chosen root. -/
theorem faceOrbitDarts_head
    (graphData : Data G) (root : G.Dart) :
    (faceOrbitDarts graphData root).head
        (faceOrbitDarts_ne_nil graphData root) = root := by
  rw [List.head_eq_getElem_zero]
  simp [faceOrbitDarts, faceCycleDart]

/-- The last enumerated face dart is adjacent back to the chosen root. -/
theorem faceOrbitDarts_getLast_dartAdj_root
    (graphData : Data G) (root : G.Dart) :
    G.DartAdj
      ((faceOrbitDarts graphData root).getLast
        (faceOrbitDarts_ne_nil graphData root)) root := by
  let RS := graphData.toRotationSystem
  have hpositive : 0 < (RS.faceOrbit root).card :=
    Finset.card_pos.mpr ⟨root, RS.mem_faceOrbit_self root⟩
  let lastPosition : Fin (RS.faceOrbit root).card :=
    ⟨(RS.faceOrbit root).card - 1, Nat.sub_lt hpositive (by omega)⟩
  have hlast :
      (faceOrbitDarts graphData root).getLast
          (faceOrbitDarts_ne_nil graphData root) =
        faceCycleDart RS root lastPosition := by
    simpa only [faceOrbitDarts, lastPosition, RS,
      SimpleGraphDartRotation.Data.toRotationSystem] using
      (List.getLast_ofFn (f := faceCycleDart
        graphData.toRotationSystem root)
        (faceOrbitDarts_ne_nil graphData root))
  have hwrap :
      RS.phi (faceCycleDart RS root lastPosition) = root := by
    have hpow := (faceOrbit_isCycleOn RS root).pow_card_apply
      (RS.mem_faceOrbit_self root)
    have hsuccessor : (RS.faceOrbit root).card - 1 + 1 =
        (RS.faceOrbit root).card := Nat.sub_add_cancel (by omega)
    calc
      RS.phi (faceCycleDart RS root lastPosition) =
          (RS.phi ^ ((RS.faceOrbit root).card - 1 + 1)) root := by
        simp only [faceCycleDart, lastPosition, pow_succ',
          Equiv.Perm.coe_mul, Function.comp_apply]
      _ = (RS.phi ^ (RS.faceOrbit root).card) root := by
        rw [hsuccessor]
      _ = root := hpow
  rw [hlast]
  change (faceCycleDart RS root lastPosition).snd = root.fst
  calc
    (faceCycleDart RS root lastPosition).snd =
        (RS.phi (faceCycleDart RS root lastPosition)).fst :=
      dartAdj_phi graphData _
    _ = root.fst := congrArg (fun dart : G.Dart => dart.fst) hwrap

/-- Under two-sidedness, the facial dart enumeration has no repeated
underlying edge. -/
theorem map_edge_faceOrbitDarts_nodup
    (graphData : Data G)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (root : G.Dart) :
    ((faceOrbitDarts graphData root).map fun dart => dart.edge).Nodup := by
  rw [faceOrbitDarts, List.map_ofFn, List.nodup_ofFn]
  intro left right hedge
  apply faceCycleEdge_injective graphData.toRotationSystem htwoSided root
  apply Subtype.ext
  exact hedge

/-- The rooted facial enumeration realizes a closed graph trail, with its
edge list exactly the ordered underlying face edges. -/
theorem exists_rootedFaceTrail
    (graphData : Data G)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (root : G.Dart) :
    ∃ trail : G.Walk root.fst root.fst,
      trail.IsTrail ∧
        trail.darts = faceOrbitDarts graphData root ∧
        (∀ edge : G.edgeSet,
          edge.1 ∈ trail.edges ↔
            edge ∈ orbitFaceBoundary graphData.toRotationSystem
              (dartOrbitFace graphData.toRotationSystem root)) := by
  let darts := faceOrbitDarts graphData root
  have hdartsNe : darts ≠ [] := faceOrbitDarts_ne_nil graphData root
  have hchain : List.IsChain G.DartAdj darts :=
    faceOrbitDarts_isChain graphData root
  have hhead : darts.head hdartsNe = root :=
    faceOrbitDarts_head graphData root
  have hlastAdj : G.DartAdj (darts.getLast hdartsNe) root :=
    faceOrbitDarts_getLast_dartAdj_root graphData root
  let openTrail : G.Walk (darts.head hdartsNe).fst
      (darts.getLast hdartsNe).snd :=
    SimpleGraph.Walk.ofDarts darts hdartsNe hchain
  let trail : G.Walk root.fst root.fst :=
    openTrail.copy (congrArg (fun dart : G.Dart => dart.fst) hhead)
      (show (darts.getLast hdartsNe).snd = root.fst from hlastAdj)
  have htrailDarts : trail.darts = darts := by
    simp [trail, openTrail]
  have htrailEdges : trail.edges =
      darts.map (fun dart => dart.edge) := by
    simp [SimpleGraph.Walk.edges, htrailDarts]
  refine ⟨trail, ?_, htrailDarts, ?_⟩
  · refine ⟨?_⟩
    rw [htrailEdges]
    exact map_edge_faceOrbitDarts_nodup graphData htwoSided root
  · intro edge
    constructor
    · intro hedge
      rw [htrailEdges] at hedge
      rcases List.mem_map.mp hedge with ⟨dart, hdart, hdartEdge⟩
      dsimp only [darts] at hdart
      simp only [faceOrbitDarts, List.mem_ofFn] at hdart
      rcases hdart with ⟨position, hposition⟩
      have hboundary := faceCycleEdge_mem graphData.toRotationSystem
        root position
      have hedgeEq :
          faceCycleEdge graphData.toRotationSystem root position = edge := by
        apply Subtype.ext
        simpa [faceCycleEdge, hposition] using hdartEdge
      rw [← hedgeEq]
      exact hboundary
    · intro hedge
      rcases existsUnique_faceCycleEdge_eq graphData.toRotationSystem
          htwoSided root edge hedge with
        ⟨position, hposition, _hunique⟩
      rw [htrailEdges]
      dsimp only [darts]
      rw [faceOrbitDarts, List.map_ofFn]
      simp only [List.mem_ofFn]
      refine ⟨position, ?_⟩
      exact congrArg Subtype.val hposition

/-- Removing the rooted face edge leaves exactly the other edges of that
facial boundary, in face order, as an edge-simple bypass. -/
theorem exists_rootedFaceBypass_exact
    (graphData : Data G)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (root : G.Dart) :
    ∃ bypass : G.Walk root.snd root.fst,
      bypass.IsTrail ∧
        root.edge ∉ bypass.edges ∧
        bypass.darts = (faceOrbitDarts graphData root).tail ∧
        (∀ edge : G.edgeSet,
          edge.1 ∈ bypass.edges ↔
            edge ∈ orbitFaceBoundary graphData.toRotationSystem
                (dartOrbitFace graphData.toRotationSystem root) ∧
              edge.1 ≠ root.edge) := by
  rcases exists_rootedFaceTrail graphData htwoSided root with
    ⟨trail, htrail, hdarts, hedgeExact⟩
  have hdartsNe : trail.darts ≠ [] := by
    rw [hdarts]
    exact faceOrbitDarts_ne_nil graphData root
  have htrailNotNil : ¬trail.Nil :=
    SimpleGraph.Walk.darts_eq_nil.not.mp hdartsNe
  have hheadDarts :
      trail.darts.head
          (SimpleGraph.Walk.darts_eq_nil.not.mpr htrailNotNil) = root := by
    simpa only [hdarts] using faceOrbitDarts_head graphData root
  have hfirstDart : trail.firstDart htrailNotNil = root := by
    rw [trail.firstDart_eq_head_darts htrailNotNil]
    exact hheadDarts
  have hsnd : trail.snd = root.snd := by
    exact congrArg (fun dart : G.Dart => dart.snd) hfirstDart
  let bypass : G.Walk root.snd root.fst := trail.tail.copy hsnd rfl
  have hbypassDarts : bypass.darts =
      (faceOrbitDarts graphData root).tail := by
    simp [bypass, SimpleGraph.Walk.tail,
      SimpleGraph.Walk.darts_drop, hdarts]
  have hbypassEdges : bypass.edges = trail.edges.tail := by
    simp [bypass, SimpleGraph.Walk.tail,
      SimpleGraph.Walk.edges_drop]
  have hedgesNe : trail.edges ≠ [] := by
    simpa [SimpleGraph.Walk.edges] using hdartsNe
  have hheadEdge : trail.edges.head hedgesNe = root.edge := by
    have hheadMap := congrArg (fun dart : G.Dart => dart.edge) hheadDarts
    simpa [SimpleGraph.Walk.edges, List.head_map] using hheadMap
  have hdecomp : root.edge :: trail.edges.tail = trail.edges := by
    rw [← hheadEdge]
    exact List.cons_head_tail hedgesNe
  have hrootNotMem : root.edge ∉ bypass.edges := by
    rw [hbypassEdges]
    have hnodup := htrail.edges_nodup
    rw [← hdecomp, List.nodup_cons] at hnodup
    exact hnodup.1
  refine ⟨bypass, ?_, hrootNotMem, hbypassDarts, ?_⟩
  · refine ⟨?_⟩
    rw [hbypassEdges]
    exact htrail.edges_nodup.tail
  · intro edge
    constructor
    · intro hedge
      refine ⟨?_, ?_⟩
      · apply (hedgeExact edge).1
        rw [hbypassEdges] at hedge
        exact List.mem_of_mem_tail hedge
      · intro hedgeRoot
        exact hrootNotMem (hedgeRoot ▸ hedge)
    · rintro ⟨hedgeFace, hedgeRoot⟩
      have hedgeTrail : edge.1 ∈ trail.edges :=
        (hedgeExact edge).2 hedgeFace
      rw [← hdecomp] at hedgeTrail
      rcases List.mem_cons.mp hedgeTrail with hroot | htail
      · exact False.elim (hedgeRoot hroot)
      · simpa only [hbypassEdges] using htail

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem exists_walk_eq_append_cons_of_mem_edges
    {start finish : V} (walk : G.Walk start finish)
    (edge : Sym2 V) (hedge : edge ∈ walk.edges) :
    ∃ (left right : V) (adj : G.Adj left right)
        (before : G.Walk start left) (after : G.Walk right finish),
      edge = s(left, right) ∧
        walk = before.append (Walk.cons adj after) := by
  induction walk with
  | nil => simp at hedge
  | @cons start next finish adj tail inductionHypothesis =>
      rw [Walk.edges_cons, List.mem_cons] at hedge
      rcases hedge with hfirst | htail
      · exact ⟨start, next, adj, Walk.nil, tail, hfirst, rfl⟩
      · rcases inductionHypothesis htail with
          ⟨left, right, selectedAdj, before, after,
            hedgeValue, hdecomp⟩
        refine ⟨left, right, selectedAdj, Walk.cons adj before, after,
          hedgeValue, ?_⟩
        rw [hdecomp]
        rfl

/-- A second edge of a rooted face canonically splits the facial bypass
into the two ordered arcs on either side of that edge. -/
theorem exists_rootedFaceBypass_splitAtEdge
    (graphData : Data G)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (root : G.Dart) (selected : G.edgeSet)
    (hselected : selected ∈
      orbitFaceBoundary graphData.toRotationSystem
        (dartOrbitFace graphData.toRotationSystem root))
    (hselectedRoot : selected.1 ≠ root.edge) :
    ∃ (left right : V) (adj : G.Adj left right)
        (before : G.Walk root.snd left)
        (after : G.Walk right root.fst),
      selected.1 = s(left, right) ∧
        (before.append (Walk.cons adj after)).IsTrail ∧
        (before.append (Walk.cons adj after)).darts =
          (faceOrbitDarts graphData root).tail ∧
        (∀ edge : G.edgeSet,
          edge.1 ∈ (before.append (Walk.cons adj after)).edges ↔
            edge ∈ orbitFaceBoundary graphData.toRotationSystem
                (dartOrbitFace graphData.toRotationSystem root) ∧
              edge.1 ≠ root.edge) := by
  rcases exists_rootedFaceBypass_exact graphData htwoSided root with
    ⟨bypass, hbypass, _hroot, hdarts, hexact⟩
  have hselectedBypass : selected.1 ∈ bypass.edges :=
    (hexact selected).2 ⟨hselected, hselectedRoot⟩
  rcases exists_walk_eq_append_cons_of_mem_edges bypass selected.1
      hselectedBypass with
    ⟨left, right, adj, before, after, hedgeValue, hdecomp⟩
  refine ⟨left, right, adj, before, after, hedgeValue, ?_, ?_, ?_⟩
  · rw [← hdecomp]
    exact hbypass
  · rw [← hdecomp]
    exact hdarts
  · intro edge
    rw [← hdecomp]
    exact hexact edge

/-- Removing the rooted face edge leaves an edge-simple facial bypass from
its terminal endpoint back to its initial endpoint. -/
theorem exists_rootedFaceBypass
    (graphData : Data G)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (root : G.Dart) :
    ∃ bypass : G.Walk root.snd root.fst,
      bypass.IsTrail ∧
        root.edge ∉ bypass.edges ∧
        (∀ edge : G.edgeSet,
          edge.1 ∈ bypass.edges →
            edge ∈ orbitFaceBoundary graphData.toRotationSystem
              (dartOrbitFace graphData.toRotationSystem root)) := by
  rcases exists_rootedFaceBypass_exact graphData htwoSided root with
    ⟨bypass, hbypass, hroot, _hdarts, hexact⟩
  exact ⟨bypass, hbypass, hroot, fun edge hedge => (hexact edge).1 hedge |>.1⟩

end

end GoertzelV24OrbitFaceWalk

end Mettapedia.GraphTheory.FourColor
