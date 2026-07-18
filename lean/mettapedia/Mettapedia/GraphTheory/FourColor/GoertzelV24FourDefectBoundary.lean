import Mettapedia.GraphTheory.FourColor.GoertzelV24Square
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoDefectParity

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FourDefectBoundary

open SimpleGraph
open scoped BigOperators
open GoertzelV24TwoDefectParity

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- A finite ordered boundary of degree-two vertices in an otherwise cubic
graph. The order records how a replacement gadget attaches to the ports. -/
structure DegreeTwoBoundaryData (G : SimpleGraph V) (portCount : Nat) where
  defectVertex : Fin portCount → V

namespace DegreeTwoBoundaryData

/-- Structural validity of a degree-two boundary: distinct ports, degree two
at every port, and degree three at every other vertex. -/
def WellFormed {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount) : Prop :=
  Function.Injective data.defectVertex ∧
  (∀ port, (incidentEdgeFinset G (data.defectVertex port)).card = 2) ∧
  ∀ vertex, (∀ port, vertex ≠ data.defectVertex port) →
    (incidentEdgeFinset G vertex).card = 3

/-- The ordered word of colors requested at the degree-two boundary ports. -/
def colorWord {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (C : G.EdgeColoring Color) : Fin portCount → Color :=
  fun port ↦ vertexKirchhoffSum G C (data.defectVertex port)

/-- Relabel a degree-two boundary without changing its underlying graph or
boundary vertices. -/
def reindex {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (index : Equiv.Perm (Fin portCount)) :
    DegreeTwoBoundaryData G portCount where
  defectVertex := data.defectVertex ∘ index

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem reindex_defectVertex {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (index : Equiv.Perm (Fin portCount)) (port : Fin portCount) :
    (data.reindex index).defectVertex port = data.defectVertex (index port) :=
  rfl

/-- Structural validity is invariant under relabeling the boundary ports. -/
theorem WellFormed.reindex {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    (hdata : data.WellFormed)
    (index : Equiv.Perm (Fin portCount)) :
    (data.reindex index).WellFormed := by
  refine ⟨hdata.1.comp index.injective, ?_, ?_⟩
  · intro port
    exact hdata.2.1 (index port)
  · intro vertex hvertex
    apply hdata.2.2 vertex
    intro port heq
    apply hvertex (index.symm port)
    change vertex = data.defectVertex (index (index.symm port))
    rw [index.apply_symm_apply]
    exact heq

@[simp]
theorem colorWord_reindex {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (index : Equiv.Perm (Fin portCount))
    (C : G.EdgeColoring Color) (port : Fin portCount) :
    (data.reindex index).colorWord C port = data.colorWord C (index port) :=
  rfl

end DegreeTwoBoundaryData

/-- At a degree-two vertex of a Tait-colored graph, the Kirchhoff sum of the
two incident colors is nonzero. -/
theorem vertexKirchhoffSum_ne_zero_of_card_two
    (C : G.EdgeColoring Color)
    (vertex : V) (hcard : (incidentEdgeFinset G vertex).card = 2) :
    vertexKirchhoffSum G C vertex ≠ 0 := by
  rcases Finset.card_eq_two.mp hcard with ⟨first, second, hne, hset⟩
  have hfirstVertex : vertex ∈ (first.1 : Sym2 V) := by
    have : first ∈ incidentEdgeFinset G vertex := by
      rw [hset]
      simp
    simpa [incidentEdgeFinset] using this
  have hsecondVertex : vertex ∈ (second.1 : Sym2 V) := by
    have : second ∈ incidentEdgeFinset G vertex := by
      rw [hset]
      simp
    simpa [incidentEdgeFinset] using this
  have hcolors : C first ≠ C second :=
    C.valid ((SimpleGraph.lineGraph_adj_iff_exists).2
      ⟨hne, vertex, hfirstVertex, hsecondVertex⟩)
  unfold vertexKirchhoffSum
  rw [hset]
  simpa [hne] using add_ne_zero_of_ne hcolors

/-- Every entry of a well-formed degree-two boundary word is a nonzero Tait
color. -/
theorem DegreeTwoBoundaryData.colorWord_ne_zero {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color)
    (port : Fin portCount) :
    data.colorWord C port ≠ 0 := by
  exact vertexKirchhoffSum_ne_zero_of_card_two C _ (hdata.2.1 port)

/-- The requested color at a degree-two boundary port differs from both
colors already incident there. -/
theorem DegreeTwoBoundaryData.colorWord_ne_incidentColor
    {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (port : Fin portCount) (edge : G.edgeSet)
    (hedge : edge ∈ incidentEdgeFinset G (data.defectVertex port)) :
    data.colorWord C port ≠ C edge := by
  rcases Finset.card_eq_two.mp (hdata.2.1 port) with
    ⟨first, second, hne, hset⟩
  have hfirstMem : first ∈
      incidentEdgeFinset G (data.defectVertex port) := by
    rw [hset]
    simp
  have hsecondMem : second ∈
      incidentEdgeFinset G (data.defectVertex port) := by
    rw [hset]
    simp
  have hfirstVertex : data.defectVertex port ∈ (first.1 : Sym2 V) := by
    simpa [incidentEdgeFinset] using hfirstMem
  have hsecondVertex : data.defectVertex port ∈ (second.1 : Sym2 V) := by
    simpa [incidentEdgeFinset] using hsecondMem
  have hcolors : C first ≠ C second :=
    C.valid ((SimpleGraph.lineGraph_adj_iff_exists).2
      ⟨hne, data.defectVertex port, hfirstVertex, hsecondVertex⟩)
  have hword : data.colorWord C port = C first + C second := by
    simp [DegreeTwoBoundaryData.colorWord, vertexKirchhoffSum, hset, hne]
  have hthird := third_color_properties (hC first) (hC second) hcolors
  rw [hset] at hedge
  simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
  rcases hedge with rfl | rfl
  · rw [hword]
    exact hthird.2.1
  · rw [hword]
    exact hthird.2.2

/-- Boundary parity for an arbitrary number of degree-two ports: the sum of
all requested colors is zero. -/
theorem DegreeTwoBoundaryData.sum_colorWord_eq_zero {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    (∑ port : Fin portCount, data.colorWord C port) = 0 := by
  let boundary : Finset V := Finset.univ.image data.defectVertex
  have hinterior : ∀ vertex ∉ boundary,
      vertexKirchhoffSum G C vertex = 0 := by
    intro vertex hvertex
    apply vertexKirchhoffSum_eq_zero_of_card_three C hC
    apply hdata.2.2 vertex
    intro port heq
    apply hvertex
    exact Finset.mem_image.2 ⟨port, by simp, heq.symm⟩
  calc
    (∑ port : Fin portCount, data.colorWord C port) =
        ∑ vertex ∈ boundary, vertexKirchhoffSum G C vertex := by
      unfold DegreeTwoBoundaryData.colorWord boundary
      refine (Finset.sum_image ?_).symm
      intro first _hfirst second _hsecond heq
      exact hdata.1 heq
    _ = 0 := sum_vertexKirchhoffSum_on_boundary_eq_zero C boundary hinterior

/-- Three nonzero boundary requests with zero total sum are the three
distinct Tait colors, hence form the local coloring of one restored cubic
vertex. -/
theorem properColorTriple_of_three_nonzero_sum_zero :
    ∀ word : Fin 3 → Color,
      (∀ port, word port ≠ 0) →
      (∑ port : Fin 3, word port) = 0 →
      ProperColorTriple (word 0) (word 1) (word 2) := by
  decide

/-- A well-formed three-port degree-two boundary is automatically fillable
by a single cubic vertex. -/
theorem DegreeTwoBoundaryData.three_colorWord_proper
    (data : DegreeTwoBoundaryData G 3) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    ProperColorTriple
      (data.colorWord C 0) (data.colorWord C 1) (data.colorWord C 2) := by
  apply properColorTriple_of_three_nonzero_sum_zero
  · intro port
    exact data.colorWord_ne_zero hdata C port
  · exact data.sum_colorWord_eq_zero hdata C hC

/-- Four nonzero colors with zero total sum have exactly the all-equal or
one-of-three-pairings forms. -/
theorem fourColorBoundaryWord_classification :
    ∀ word : SquareBoundaryWord,
      word.Nonzero →
      (∑ port : Fin 4, word port) = 0 →
      word.AllEqual ∨ word.AdjacentPairs ∨ word.OppositePairs := by
  decide

/-- Local coloring condition for restoring two adjacent cubic vertices.
Ports `0,1` meet the first vertex, ports `2,3` meet the second, and `bridge`
colors their common edge. -/
def IsTwoVertexBridgeExtension
    (word : SquareBoundaryWord) (bridge : Color) : Prop :=
  ProperColorTriple (word 0) (word 1) bridge ∧
  ProperColorTriple (word 2) (word 3) bridge
  deriving Decidable

/-- All colors that can be assigned to the common edge of the restored
two-vertex bridge. -/
def twoVertexBridgeExtensions (word : SquareBoundaryWord) : Finset Color :=
  Finset.univ.filter (IsTwoVertexBridgeExtension word)

@[simp]
theorem mem_twoVertexBridgeExtensions_iff
    {word : SquareBoundaryWord} {bridge : Color} :
    bridge ∈ twoVertexBridgeExtensions word ↔
      IsTwoVertexBridgeExtension word bridge := by
  simp [twoVertexBridgeExtensions]

/-- Cardinality form of the exact two-vertex bridge transfer table. -/
theorem twoVertexBridgeExtension_card :
    ∀ word : SquareBoundaryWord,
      (twoVertexBridgeExtensions word).card =
        if word.Nonzero ∧ (word.Adjacent12_30 ∨ word.OppositePairs)
        then 1 else 0 := by
  decide

/-- The exact finite extension table for the two-vertex bridge gadget. It
extends precisely the cross-paired and opposite-paired four-port words. -/
theorem exists_twoVertexBridgeExtension_iff :
    ∀ word : SquareBoundaryWord,
      (∃ bridge : Color, IsTwoVertexBridgeExtension word bridge) ↔
        word.Nonzero ∧ (word.Adjacent12_30 ∨ word.OppositePairs) := by
  decide

/-- On the parity-valid nonzero sector, failure to restore the adjacent
vertex pair is exactly equality of the two requests on each side. -/
theorem not_exists_twoVertexBridgeExtension_iff_sameSidePairs :
    ∀ word : SquareBoundaryWord,
      word.Nonzero →
      (∑ port : Fin 4, word port) = 0 →
      ((¬ ∃ bridge : Color, IsTwoVertexBridgeExtension word bridge) ↔
        word 0 = word 1 ∧ word 2 = word 3) := by
  decide

/-- A Tait-colored four-defect graph has one of the four parity-permitted
boundary types. -/
theorem DegreeTwoBoundaryData.four_colorWord_classification
    (data : DegreeTwoBoundaryData G 4) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    SquareBoundaryWord.AllEqual (data.colorWord C) ∨
      SquareBoundaryWord.AdjacentPairs (data.colorWord C) ∨
      SquareBoundaryWord.OppositePairs (data.colorWord C) := by
  apply fourColorBoundaryWord_classification
  · exact ⟨data.colorWord_ne_zero hdata C 0,
      data.colorWord_ne_zero hdata C 1,
      data.colorWord_ne_zero hdata C 2,
      data.colorWord_ne_zero hdata C 3⟩
  · exact data.sum_colorWord_eq_zero hdata C hC

/-- Exact obstruction theorem for a graph-backed four-port boundary: the
deleted adjacent vertex pair can be restored unless both same-side request
pairs are equal. -/
theorem DegreeTwoBoundaryData.not_exists_twoVertexBridgeExtension_iff
    (data : DegreeTwoBoundaryData G 4) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    ((¬ ∃ bridge : Color,
        IsTwoVertexBridgeExtension (data.colorWord C) bridge) ↔
      data.colorWord C 0 = data.colorWord C 1 ∧
        data.colorWord C 2 = data.colorWord C 3) := by
  apply not_exists_twoVertexBridgeExtension_iff_sameSidePairs
  · exact ⟨data.colorWord_ne_zero hdata C 0,
      data.colorWord_ne_zero hdata C 1,
      data.colorWord_ne_zero hdata C 2,
      data.colorWord_ne_zero hdata C 3⟩
  · exact data.sum_colorWord_eq_zero hdata C hC

end

end GoertzelV24FourDefectBoundary

end Mettapedia.GraphTheory.FourColor
