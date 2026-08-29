import Mettapedia.GraphTheory.FourColor.GoertzelV24KauffmanFormationParity
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalGraphBackedPresentation

/-!
# Kauffman parity on endpoint-simple rotation systems

The spherical formation-parity theorem is stated on a graph-backed rotation
system.  Ordered-cut constructions instead produce a literal rotation system,
whose edge carrier need not definitionally be the edge set of its primal
graph.  This file proves that canonical graph backing commutes with selecting
and switching a Kempe component.  It then transports the exact spherical
Kauffman theorem back to any endpoint-simple literal rotation system.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationSystemKauffmanParity

open GoertzelV24KauffmanFormationParity
open GoertzelV24KauffmanParity
open GoertzelV24FaceDualConnectedness
open GoertzelV24MinimalGraphBackedPresentation
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationSystemPrimalColorTransport
open GoertzelV24RotationSystemPrimalEdgePresentation
open GoertzelV24RotationSystemPrimalGraphBacking
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

local instance primalAdjDecidable (RS : RotationSystem V E) :
    DecidableRel (rotationPrimalGraph RS).Adj :=
  Classical.decRel _

/-- Canonical graph backing preserves each bicoloured subgraph, including its
selected vertex subtype. -/
def graphBicoloredSubgraphIso
    (RS : RotationSystem V E) (hinjective : Function.Injective RS.endpoints)
    (C : RS.EdgeColoring Color) (a b : Color) :
    C.bicoloredSubgraph a b ≃g
      (graphEdgeColoring RS hinjective C).bicoloredSubgraph a b where
  toFun edge := ⟨edgeEquiv RS hinjective edge.1, by
    have hselected : C edge.1 = a ∨ C edge.1 = b := edge.2
    change graphEdgeColoring RS hinjective C
        (edgeEquiv RS hinjective edge.1) = a ∨
      graphEdgeColoring RS hinjective C
        (edgeEquiv RS hinjective edge.1) = b
    simpa only [graphEdgeColoring_apply] using hselected⟩
  invFun edge := ⟨(edgeEquiv RS hinjective).symm edge.1, by
    have hselected : graphEdgeColoring RS hinjective C edge.1 = a ∨
        graphEdgeColoring RS hinjective C edge.1 = b := edge.2
    have happly : graphEdgeColoring RS hinjective C edge.1 =
        C ((edgeEquiv RS hinjective).symm edge.1) := by
      simpa using graphEdgeColoring_apply RS hinjective C
        ((edgeEquiv RS hinjective).symm edge.1)
    change C ((edgeEquiv RS hinjective).symm edge.1) = a ∨
      C ((edgeEquiv RS hinjective).symm edge.1) = b
    rw [← happly]
    exact hselected⟩
  left_inv edge := by
    apply Subtype.ext
    exact (edgeEquiv RS hinjective).left_inv edge.1
  right_inv edge := by
    apply Subtype.ext
    exact (edgeEquiv RS hinjective).right_inv edge.1
  map_rel_iff' := by
    intro left right
    change (rotationPrimalGraph RS).lineGraph.Adj
        (edgeEquiv RS hinjective left.1)
        (edgeEquiv RS hinjective right.1) ↔
      RS.edgeAdjacencyGraph.Adj left.1 right.1
    exact (edgeAdjacencyIso RS hinjective).map_rel_iff

/-- A literal Kempe component, presented on the canonical primal graph. -/
def graphKempeComponent
    (RS : RotationSystem V E) (hinjective : Function.Injective RS.endpoints)
    (C : RS.EdgeColoring Color) (a b : Color)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    ((graphEdgeColoring RS hinjective C).bicoloredSubgraph a b).ConnectedComponent :=
  (graphBicoloredSubgraphIso RS hinjective C a b).connectedComponentEquiv K

/-- Membership in a Kempe component is preserved and reflected by canonical
graph backing. -/
theorem edgeEquiv_mem_graphKempeComponentSet_iff
    (RS : RotationSystem V E) (hinjective : Function.Injective RS.endpoints)
    (C : RS.EdgeColoring Color) (a b : Color)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) (edge : E) :
    edgeEquiv RS hinjective edge ∈
        (graphEdgeColoring RS hinjective C).kempeComponentSet a b
          (graphKempeComponent RS hinjective C a b K) ↔
      edge ∈ C.kempeComponentSet a b K := by
  let iso := graphBicoloredSubgraphIso RS hinjective C a b
  have hselected : edge ∈ C.bicoloredSet a b ↔
      edgeEquiv RS hinjective edge ∈
        (graphEdgeColoring RS hinjective C).bicoloredSet a b := by
    change (C edge = a ∨ C edge = b) ↔
      (graphEdgeColoring RS hinjective C
          (edgeEquiv RS hinjective edge) = a ∨
        graphEdgeColoring RS hinjective C
          (edgeEquiv RS hinjective edge) = b)
    simp only [graphEdgeColoring_apply]
  constructor
  · rintro ⟨hgraphSelected, hcomponent⟩
    have hliteralSelected := hselected.mpr hgraphSelected
    refine ⟨hliteralSelected, ?_⟩
    have hmapped :
        ((graphEdgeColoring RS hinjective C).bicoloredSubgraph a b).connectedComponentMk
            (iso ⟨edge, hliteralSelected⟩) =
          iso.connectedComponentEquiv K := by
      simpa [iso, graphBicoloredSubgraphIso, graphKempeComponent] using
        hcomponent
    exact
      (SimpleGraph.ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp
        (G := C.bicoloredSubgraph a b)
        (G' := (graphEdgeColoring RS hinjective C).bicoloredSubgraph a b)
        (φ := iso) (v := ⟨edge, hliteralSelected⟩) (C := K)).mp hmapped
  · rintro ⟨hliteralSelected, hcomponent⟩
    have hgraphSelected := hselected.mp hliteralSelected
    refine ⟨hgraphSelected, ?_⟩
    have hmapped :
        ((graphEdgeColoring RS hinjective C).bicoloredSubgraph a b).connectedComponentMk
            (iso ⟨edge, hliteralSelected⟩) =
          iso.connectedComponentEquiv K :=
      (SimpleGraph.ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp
        (G := C.bicoloredSubgraph a b)
        (G' := (graphEdgeColoring RS hinjective C).bicoloredSubgraph a b)
        (φ := iso) (v := ⟨edge, hliteralSelected⟩) (C := K)).mpr hcomponent
    simpa [iso, graphBicoloredSubgraphIso, graphKempeComponent] using hmapped

/-- Canonical graph backing commutes with a switch on the corresponding Kempe
component. -/
theorem graphEdgeColoring_swapOnKempeComponent
    (RS : RotationSystem V E) (hinjective : Function.Injective RS.endpoints)
    (C : RS.EdgeColoring Color) (a b : Color)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    graphEdgeColoring RS hinjective (C.swapOnKempeComponent a b K) =
      (graphEdgeColoring RS hinjective C).swapOnKempeComponent a b
        (graphKempeComponent RS hinjective C a b K) := by
  apply DFunLike.ext _ _
  intro graphEdge
  let edge := (edgeEquiv RS hinjective).symm graphEdge
  have hgraphEdge : edgeEquiv RS hinjective edge = graphEdge :=
    (edgeEquiv RS hinjective).apply_symm_apply graphEdge
  rw [← hgraphEdge, graphEdgeColoring_apply]
  by_cases hmember : edge ∈ C.kempeComponentSet a b K
  · have hgraphMember :=
      (edgeEquiv_mem_graphKempeComponentSet_iff
        RS hinjective C a b K edge).2 hmember
    rw [C.swapOnKempeComponent_apply_of_mem hmember,
      (graphEdgeColoring RS hinjective C).swapOnKempeComponent_apply_of_mem
        hgraphMember, graphEdgeColoring_apply]
  · have hgraphMember : edgeEquiv RS hinjective edge ∉
        (graphEdgeColoring RS hinjective C).kempeComponentSet a b
          (graphKempeComponent RS hinjective C a b K) :=
      fun h => hmember ((edgeEquiv_mem_graphKempeComponentSet_iff
        RS hinjective C a b K edge).1 h)
    rw [C.swapOnKempeComponent_apply_of_not_mem hmember,
      (graphEdgeColoring RS hinjective C).swapOnKempeComponent_apply_of_not_mem
        hgraphMember, graphEdgeColoring_apply]

/-- The number of two-colour components is invariant under canonical graph
backing. -/
theorem bicoloredComponentCount_graphEdgeColoring
    (RS : RotationSystem V E) (hinjective : Function.Injective RS.endpoints)
    (C : RS.EdgeColoring Color) (a b : Color) :
    bicoloredComponentCount (graphEdgeColoring RS hinjective C) a b =
      bicoloredComponentCount C a b := by
  unfold bicoloredComponentCount
  exact Nat.card_congr
    (graphBicoloredSubgraphIso RS hinjective C a b).connectedComponentEquiv.symm

/-- Formation parity itself is invariant under canonical graph backing. -/
theorem formationParity_graphEdgeColoring
    (RS : RotationSystem V E) (hinjective : Function.Injective RS.endpoints)
    (C : RS.EdgeColoring Color) (a b c : Color) :
    formationParity (graphEdgeColoring RS hinjective C) a b c =
      formationParity C a b c := by
  unfold formationParity formationCurveCount
  rw [bicoloredComponentCount_graphEdgeColoring,
    bicoloredComponentCount_graphEdgeColoring,
    bicoloredComponentCount_graphEdgeColoring]

/-- **Spherical Kauffman parity on a literal rotation system.**  Endpoint
simplicity is used only to form the canonical simple-graph presentation; all
topological hypotheses are transported from the literal map. -/
theorem formationParity_swapOnKempeComponent_spherical
    (RS : RotationSystem V E) (hinjective : Function.Injective RS.endpoints)
    (hclass : BridgelessSphericalCubicMapData RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    {a b : Color} (hab : ValidColorPair a b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    formationParity (C.swapOnKempeComponent a b K) a b (a + b) =
      formationParity C a b (a + b) := by
  let graphC := graphEdgeColoring RS hinjective C
  let graphK := graphKempeComponent RS hinjective C a b K
  have hgraph :=
    GoertzelV24KauffmanFormationParity.formationParity_swapOnKempeComponent_spherical
      (graphData RS hinjective)
      (graphData_bridgelessSphericalCubicMapData RS hinjective hclass)
      (graphData_orbitFacesTwoSided RS hinjective htwoSided)
      graphC (graphEdgeColoring_isTait RS hinjective C hC) hab graphK
  rw [← graphEdgeColoring_swapOnKempeComponent RS hinjective C a b K]
    at hgraph
  exact (formationParity_graphEdgeColoring RS hinjective
    (C.swapOnKempeComponent a b K) a b (a + b)).symm.trans
      (hgraph.trans (formationParity_graphEdgeColoring RS hinjective
        C a b (a + b)))

end

end GoertzelV24RotationSystemKauffmanParity

end Mettapedia.GraphTheory.FourColor
