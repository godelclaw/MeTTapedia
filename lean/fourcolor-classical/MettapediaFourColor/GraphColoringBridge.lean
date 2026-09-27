import MettapediaFourColor.ClassicalAssembly
import MettapediaFourColor.HypermapDictionary
import Mettapedia.GraphTheory.FourColor.SimpleGraphRotationSystem
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# From embedded dart colourings to simple-graph colourings

A colouring constant on every outgoing-dart fiber gives a colouring of the
vertices of the original graph. The construction retains the supplied dart
colours and assigns zero to isolated vertices. No vertex-surjectivity or
connectedness assumption is needed.

For the graph-backed rotation data, vertexwise cyclicity identifies the node
orbits with the nonempty vertex fibers. The classical argument then colours
every finite simple graph supplied with such a planar rotation. The existence
of this rotation from a topological embedding is a separate obligation.
-/

namespace FourColor.SimpleGraphBridge

open Hypermap

variable {V : Type*} (G : SimpleGraph V)

/-- Read a colour from any outgoing dart; an isolated vertex receives zero. -/
noncomputable def vertexColor (k : G.Dart → Color) (v : V) : Color := by
  classical
  exact if h : ∃ d : G.Dart, d.fst = v then k h.choose else 0

/-- The vertex assignment reads back the exact supplied colour at every dart. -/
theorem vertexColor_dart (k : G.Dart → Color)
    (hconstant : ∀ a b : G.Dart, a.fst = b.fst → k a = k b) (d : G.Dart) :
    vertexColor G k d.fst = k d := by
  classical
  unfold vertexColor
  have h : ∃ a : G.Dart, a.fst = d.fst := ⟨d, rfl⟩
  rw [dite_eq_left h]
  exact hconstant _ d h.choose_spec

theorem vertexColor_isolated (k : G.Dart → Color) (v : V)
    (hisolated : ∀ w, ¬ G.Adj v w) : vertexColor G k v = 0 := by
  classical
  unfold vertexColor
  apply dite_eq_right
  rintro ⟨d, hd⟩
  exact hisolated d.snd (hd ▸ d.adj)

variable {G}

/-- The map colouring descends to its original graph, without changing any
of the colours visible on darts. -/
noncomputable def coloringOfDarts (H : Hypermap G.Dart)
    (hedge : ∀ d : G.Dart, H.edge d = d.symm)
    (hcycles : ∀ a b : G.Dart, a.fst = b.fst → H.CNode a b)
    (k : G.Dart → Color) (hk : H.GraphColoring k) : G.Coloring Color :=
  SimpleGraph.Coloring.mk (vertexColor G k) (by
    intro v w hvw
    let d : G.Dart := ⟨(v, w), hvw⟩
    have hconstant : ∀ a b : G.Dart, a.fst = b.fst → k a = k b :=
      fun a b hab => congr_of_sameCycle hk.node (hcycles a b hab)
    have hv := vertexColor_dart G k hconstant d
    have hw := vertexColor_dart G k hconstant d.symm
    change vertexColor G k w = k d.symm at hw
    change vertexColor G k v ≠ vertexColor G k w
    rw [hv, hw]
    exact fun heq => hk.edge d ((congrArg k (hedge d)).trans heq.symm))

theorem coloringOfDarts_apply_dart (H : Hypermap G.Dart)
    (hedge : ∀ d : G.Dart, H.edge d = d.symm)
    (hcycles : ∀ a b : G.Dart, a.fst = b.fst → H.CNode a b)
    (k : G.Dart → Color) (hk : H.GraphColoring k) (d : G.Dart) :
    coloringOfDarts H hedge hcycles k hk d.fst = k d :=
  vertexColor_dart G k
    (fun a b hab => congr_of_sameCycle hk.node (hcycles a b hab)) d

/-- Conversely, vertex colourings pull back to dart colourings whenever the
node permutation preserves the tail and edges reverse their endpoints. -/
theorem graphColoring_of_vertexColoring (H : Hypermap G.Dart)
    (hedge : ∀ d : G.Dart, H.edge d = d.symm)
    (hnode : ∀ d : G.Dart, (H.node d).fst = d.fst)
    (c : G.Coloring Color) : H.GraphColoring (fun d => c d.fst) where
  edge d := by
    rw [hedge d]
    exact fun heq => c.valid d.adj heq.symm
  node d := congrArg c (hnode d)

/-- A fixed identification with Mathlib's four-colour palette. -/
def palette : Color ↪ Fin 4 where
  toFun
    | .c0 => 0
    | .c1 => 1
    | .c2 => 2
    | .c3 => 3
  inj' := by decide

theorem colorable_of_dartGraphColoring (H : Hypermap G.Dart)
    (hedge : ∀ d : G.Dart, H.edge d = d.symm)
    (hcycles : ∀ a b : G.Dart, a.fst = b.fst → H.CNode a b)
    (hcolor : H.GraphFourColorable) : G.Colorable 4 := by
  obtain ⟨k, hk⟩ := hcolor
  exact ⟨G.recolorOfEmbedding palette (coloringOfDarts H hedge hcycles k hk)⟩

/-- Simplicity of the original graph rules out a node containing both ends
of an edge; no global connectivity assumption is used. -/
theorem loopless_of_dartGraph (H : Hypermap G.Dart)
    (hedge : ∀ d : G.Dart, H.edge d = d.symm)
    (hnode : ∀ d : G.Dart, (H.node d).fst = d.fst) : H.Loopless := by
  intro d hd
  have heq := congr_of_sameCycle (F := fun d : G.Dart => d.fst) hnode hd
  rw [hedge d] at heq
  exact d.fst_ne_snd heq

section Finite

variable {V : Type} {G : SimpleGraph V}

/-- The finite simple-graph endpoint follows by colouring the dual and reading
back its node colours. This also covers an empty dart set. -/
theorem colorable_of_planarDarts
    [Finite V]
    (noCounterexample : ∀ {D : Type} [Finite D] (H : Hypermap D),
      ¬ H.MinimalCounterExample)
    (H : Hypermap G.Dart)
    (hedge : ∀ d : G.Dart, H.edge d = d.symm)
    (hnode : ∀ d : G.Dart, (H.node d).fst = d.fst)
    (hcycles : ∀ a b : G.Dart, a.fst = b.fst → H.CNode a b)
    (hplanar : H.Planar) : G.Colorable 4 := by
  classical
  let := Fintype.ofFinite V
  have hdual : H.dual.PlanarBridgeless :=
    ⟨(planar_dual H).mpr hplanar,
      (bridgeless_dual H).mpr (loopless_of_dartGraph H hedge hnode)⟩
  have hcolor := fourColorable_of_no_minimalCounterExample noCounterexample H.dual hdual
  exact colorable_of_dartGraphColoring H hedge hcycles
    ((fourColorable_dual_iff (G := H)).mp hcolor)

open Mettapedia.GraphTheory.FourColor.SimpleGraphDartRotation
open Mettapedia.GraphTheory.Hypermap.Reference

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The existing graph-backed rotation, with exactly the same dart carrier. -/
noncomputable def rotationHypermap (data : Data G) : Hypermap G.Dart :=
  toReference (Mettapedia.GraphTheory.Hypermap.ofRotationSystem data.toRotationSystem)

@[simp] theorem rotationHypermap_edge (data : Data G) (d : G.Dart) :
    (rotationHypermap data).edge d = d.symm := rfl

theorem rotationHypermap_node_fst (data : Data G) (d : G.Dart) :
    ((rotationHypermap data).node d).fst = d.fst := by
  change (data.vertexRotation.symm d).fst = d.fst
  have h := data.vertexRotation_fst (data.vertexRotation.symm d)
  rw [data.vertexRotation.apply_symm_apply] at h
  exact h.symm

/-- Cyclicity is the substantive condition needed to identify node orbits
with vertices; preserving the tail alone would not suffice. -/
theorem rotationHypermap_cnode_iff (data : Data G) (hcyclic : data.IsVertexwiseCyclic)
    (a b : G.Dart) : (rotationHypermap data).CNode a b ↔ a.fst = b.fst := by
  constructor
  · exact congr_of_sameCycle (F := fun d : G.Dart => d.fst)
      (rotationHypermap_node_fst data)
  · intro hab
    change data.vertexRotation⁻¹.SameCycle a b
    rw [Equiv.Perm.sameCycle_inv]
    exact (hcyclic a.fst).2 (by rfl) hab.symm

theorem colorable_of_planarRotation
    (noCounterexample : ∀ {D : Type} [Finite D] (H : Hypermap D),
      ¬ H.MinimalCounterExample)
    (data : Data G) (hcyclic : data.IsVertexwiseCyclic)
    (hplanar : (Mettapedia.GraphTheory.Hypermap.ofRotationSystem
      data.toRotationSystem).Planar) : G.Colorable 4 :=
  colorable_of_planarDarts noCounterexample (rotationHypermap data)
    (rotationHypermap_edge data) (rotationHypermap_node_fst data)
    (fun a b hab => (rotationHypermap_cnode_iff data hcyclic a b).mpr hab)
    ((planar_iff _).mpr hplanar)

/-- The catalogue and presentation obligations now imply Mathlib's ordinary
vertex-colouring conclusion for every supplied planar graph rotation. -/
theorem colorable_of_checks (hred : Reducibility)
    (e5 : ExcludedArity (RedpartSound theRedpart) 5)
    (e6 : ExcludedArity (RedpartSound theRedpart) 6)
    (e7 : ExcludedArity (RedpartSound theRedpart) 7)
    (e8 : ExcludedArity (RedpartSound theRedpart) 8)
    (e9 : ExcludedArity (RedpartSound theRedpart) 9)
    (e10 : ExcludedArity (RedpartSound theRedpart) 10)
    (e11 : ExcludedArity (RedpartSound theRedpart) 11)
    (data : Data G) (hcyclic : data.IsVertexwiseCyclic)
    (hplanar : (Mettapedia.GraphTheory.Hypermap.ofRotationSystem
      data.toRotationSystem).Planar) : G.Colorable 4 :=
  colorable_of_planarRotation
    (ClassicalAssembly.no_minimalCounterExample_of_checks hred e5 e6 e7 e8 e9 e10 e11)
    data hcyclic hplanar

end Finite

#print axioms coloringOfDarts_apply_dart
#print axioms rotationHypermap_cnode_iff
#print axioms colorable_of_checks

end FourColor.SimpleGraphBridge
