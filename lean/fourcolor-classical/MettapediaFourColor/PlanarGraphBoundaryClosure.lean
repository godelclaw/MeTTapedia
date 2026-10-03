import MettapediaFourColor.GraphColoringBridge
import MettapediaFourColor.KempeBoundarySplit

/-!
# Kempe closure of a vertex-coloured triangulated disk

Duality turns each triangular inner face into a cubic node. Mirroring makes
the dual boundary follow the original facial order. The reference Kempe
theorem then applies. Both directions of the colouring correspondence retain
every ordered boundary vertex, not only the existence of some colouring.

The proof uses the Gonthier/Emery Kempe theorem and the existing dart-to-vertex
colouring bridge. No Four Colour existence theorem or reduction certificate
is used. Recognition of these disk hypotheses after deleting a patch is a
separate geometric obligation.
-/

namespace FourColor.PlanarGraphBoundaryClosure

open SimpleGraphBridge KempeBoundarySplit

noncomputable section

variable {V : Type*} {G : SimpleGraph V}

/-- The mirror chooses the original, rather than reversed, facial order. -/
def view (H : Hypermap G.Dart) : Hypermap G.Dart := H.dual.mirror

@[simp] theorem view_node (H : Hypermap G.Dart) : (view H).node = H.face := by
  simp [view]

theorem coloring_iff (H : Hypermap G.Dart) (k : G.Dart → Color) :
    (view H).Coloring k ↔ H.GraphColoring k := by
  constructor
  · intro h
    exact (Hypermap.coloring_dual_iff k).mp h.of_mirror
  · intro h
    have hd := (Hypermap.coloring_dual_iff k).mpr h
    have hh : H.dual.mirror.mirror.Coloring k := by simpa using hd
    exact hh.of_mirror

/-- A genuine graph colouring and its dual face colouring have exactly the
same edge trace at the entire supplied boundary. -/
theorem ringTrace_iff (H : Hypermap G.Dart)
    (edge : ∀ d : G.Dart, H.edge d = d.symm)
    (node : ∀ d : G.Dart, (H.node d).fst = d.fst)
    (cycles : ∀ a b : G.Dart, a.fst = b.fst → H.CNode a b)
    (r : List G.Dart) (et : List Color) :
    (view H).RingTrace r et ↔ GraphTrace G (r.map (fun d => d.fst)) et := by
  constructor
  · rintro ⟨k, hk, ht⟩
    have hg := (coloring_iff H k).mp hk
    let C := coloringOfDarts H edge cycles k hg
    refine ⟨C, ht.trans ?_⟩
    apply congrArg trace
    rw [List.map_map]
    apply List.map_congr_left
    intro d _
    exact (coloringOfDarts_apply_dart H edge cycles k hg d).symm
  · rintro ⟨C, ht⟩
    refine ⟨(fun d => C d.fst), (coloring_iff H _).mpr
      (graphColoring_of_vertexColoring H edge node C), ?_⟩
    simpa only [List.map_map, Function.comp_def] using ht

/-- A facial step cannot fix a dart of a simple graph: it moves its tail
to the opposite endpoint of that edge. -/
theorem face_ne (H : Hypermap G.Dart)
    (edge : ∀ d : G.Dart, H.edge d = d.symm)
    (node : ∀ d : G.Dart, (H.node d).fst = d.fst) (d : G.Dart) :
    H.face d ≠ d := by
  intro fixed
  have h := congrArg (fun x : G.Dart => x.fst) (H.edgeK d.symm)
  rw [edge, d.symm_symm, node, fixed] at h
  exact d.fst_ne_snd h

/-- A planar rotation with one duplicate-free facial boundary and triangular
remaining faces supplies closure of the actual graph-colouring observation. -/
theorem closed [Finite V] (H : Hypermap G.Dart)
    (edge : ∀ d : G.Dart, H.edge d = d.symm)
    (node : ∀ d : G.Dart, (H.node d).fst = d.fst)
    (cycles : ∀ a b : G.Dart, a.fst = b.fst → H.CNode a b)
    (planar : H.Planar) (r : List G.Dart)
    (boundary : IsCyclicChain (fun a b => b = H.face a) r)
    (distinct : r.Nodup)
    (triangles : ∀ d, d ∉ r → H.face (H.face (H.face d)) = d) :
    KempeClosed (GraphTrace G (r.map (fun d => d.fst))) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have plain : H.Plain := by
    constructor
    · intro d
      rw [edge, edge]
      exact d.symm_symm
    · intro d
      rw [edge]
      exact d.symm_ne
  have geo : (view H).UcyclePlanarPlainQuasicubic r := by
    refine ⟨⟨⟨?_, ?_⟩, ?_, distinct⟩, ?_⟩
    · exact (Hypermap.plain_mirror _).mpr ((Hypermap.plain_dual _).mpr plain)
    · constructor
      · simpa only [view_node, Set.mem_ofPred_eq] using triangles
      · intro d _
        exact face_ne H edge node d
    · simpa only [view_node] using boundary
    · exact (Hypermap.planar_mirror _).mpr ((Hypermap.planar_dual _).mpr planar)
  have h := Hypermap.Kempe_map (view H) r geo
  have same : (view H).RingTrace r = GraphTrace G (r.map (fun d => d.fst)) :=
    funext fun et => propext (ringTrace_iff H edge node cycles r et)
  rwa [same] at h

open Mettapedia.GraphTheory.FourColor.SimpleGraphDartRotation

variable {W : Type} [Fintype W] [DecidableEq W]
  {K : SimpleGraph W} [DecidableRel K.Adj]

/-- Apply the exact bridge to the graph-backed rotation already used by the
embedded patch and exterior developments. -/
theorem rotation_closed (data : Data K) (cyclic : data.IsVertexwiseCyclic)
    (planar : (rotationHypermap data).Planar) (r : List K.Dart)
    (boundary : IsCyclicChain (fun a b => b = data.toRotationSystem.phi a) r)
    (distinct : r.Nodup)
    (triangles : ∀ d, d ∉ r → data.toRotationSystem.phi
      (data.toRotationSystem.phi (data.toRotationSystem.phi d)) = d) :
    KempeClosed (GraphTrace K (r.map (fun d => d.fst))) :=
  closed (rotationHypermap data) (rotationHypermap_edge data)
    (rotationHypermap_node_fst data)
    (fun a b he => (rotationHypermap_cnode_iff data cyclic a b).mpr he)
    planar r boundary distinct triangles

end
end FourColor.PlanarGraphBoundaryClosure
