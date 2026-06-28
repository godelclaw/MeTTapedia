import Mettapedia.GraphTheory.EdgeColoring
import Mettapedia.GraphTheory.FourColor.ColorAlgebra

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- A valid Goertzel/Kauffman color pair consists of two distinct nonzero colors in `𝔽₂²`. -/
def ValidColorPair (a b : Color) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b

/-- An edge coloring using the nonzero `𝔽₂²` colors. This is the Tait-world notion relevant to
Goertzel v23 Definition 4.8. -/
def IsTaitEdgeColoring (G : SimpleGraph V) (C : G.EdgeColoring Color) : Prop :=
  ∀ e, C e ≠ 0

theorem false_of_four_pairwise_distinct_nonzero_colors
    {a b c d : Color} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) : False := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  all_goals
    first
    | exact ha rfl
    | exact hb rfl
    | exact hc rfl
    | exact hd rfl
    | exact hab rfl
    | exact hac rfl
    | exact had rfl
    | exact hbc rfl
    | exact hbd rfl
    | exact hcd rfl

omit [DecidableEq V] in
theorem IsTaitEdgeColoring.false_of_four_pairwise_adjacent_edges
    {G : SimpleGraph V} {C : G.EdgeColoring Color}
    (hC : IsTaitEdgeColoring G C) {e₁ e₂ e₃ e₄ : G.edgeSet}
    (h₁₂ : G.lineGraph.Adj e₁ e₂) (h₁₃ : G.lineGraph.Adj e₁ e₃)
    (h₁₄ : G.lineGraph.Adj e₁ e₄) (h₂₃ : G.lineGraph.Adj e₂ e₃)
    (h₂₄ : G.lineGraph.Adj e₂ e₄) (h₃₄ : G.lineGraph.Adj e₃ e₄) :
    False :=
  false_of_four_pairwise_distinct_nonzero_colors
    (hC e₁) (hC e₂) (hC e₃) (hC e₄)
    (C.valid h₁₂) (C.valid h₁₃) (C.valid h₁₄)
    (C.valid h₂₃) (C.valid h₂₄) (C.valid h₃₄)

omit [DecidableEq V] in
theorem not_exists_taitEdgeColoring_of_four_pairwise_adjacent_edges
    {G : SimpleGraph V} {e₁ e₂ e₃ e₄ : G.edgeSet}
    (h₁₂ : G.lineGraph.Adj e₁ e₂) (h₁₃ : G.lineGraph.Adj e₁ e₃)
    (h₁₄ : G.lineGraph.Adj e₁ e₄) (h₂₃ : G.lineGraph.Adj e₂ e₃)
    (h₂₄ : G.lineGraph.Adj e₂ e₄) (h₃₄ : G.lineGraph.Adj e₃ e₄) :
    ¬ ∃ C : G.EdgeColoring Color, IsTaitEdgeColoring G C := by
  rintro ⟨C, hC⟩
  exact hC.false_of_four_pairwise_adjacent_edges h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄

/-- The boundary edges of a face carrying one of the selected colors.
This is the boundary support of the `(a,b)`-Kempe components meeting that face boundary. -/
def boundaryBicoloredEdges {G : SimpleGraph V} (C : G.EdgeColoring Color)
    (a b : Color) (faceBoundary : Finset G.edgeSet) : Finset G.edgeSet :=
  faceBoundary.filter fun e => C e = a ∨ C e = b

omit [DecidableEq V] in
@[simp] theorem mem_boundaryBicoloredEdges_iff {G : SimpleGraph V} (C : G.EdgeColoring Color)
    (a b : Color) {faceBoundary : Finset G.edgeSet} {e : G.edgeSet} :
    e ∈ boundaryBicoloredEdges C a b faceBoundary ↔
      e ∈ faceBoundary ∧ (C e = a ∨ C e = b) := by
  simp [boundaryBicoloredEdges]

/-- The purified boundary-only generator produced after the exact v23 Step 2 cancellation.
It records the full `(a,b)`-boundary support with coefficient `a + b`, rather than only the
`a`-colored half tracked by the exact v23 Step 1 generator. -/
def polarizedFaceGenerator {G : SimpleGraph V} (C : G.EdgeColoring Color)
    (a b : Color) (faceBoundary : Finset G.edgeSet) : G.edgeSet → Color :=
  indicatorChain (a + b) (boundaryBicoloredEdges C a b faceBoundary)

theorem polarizedFaceGenerator_eq_third_of_mem {G : SimpleGraph V} (C : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet} {e : G.edgeSet}
    (he : e ∈ faceBoundary) (hcolor : C e = a ∨ C e = b) :
    polarizedFaceGenerator C a b faceBoundary e = a + b := by
  apply indicatorChain_apply_of_mem
  exact (mem_boundaryBicoloredEdges_iff C a b).2 ⟨he, hcolor⟩

theorem polarizedFaceGenerator_eq_zero_of_not_mem_boundary {G : SimpleGraph V}
    (C : G.EdgeColoring Color) {a b : Color} {faceBoundary : Finset G.edgeSet} {e : G.edgeSet}
    (he : e ∉ faceBoundary) :
    polarizedFaceGenerator C a b faceBoundary e = 0 := by
  apply indicatorChain_apply_of_not_mem
  intro hmem
  exact he ((mem_boundaryBicoloredEdges_iff C a b).1 hmem).1

theorem polarizedFaceGenerator_eq_zero_of_not_bicolored {G : SimpleGraph V}
    (C : G.EdgeColoring Color) {a b : Color} {faceBoundary : Finset G.edgeSet} {e : G.edgeSet}
    (hcolor : ¬ (C e = a ∨ C e = b)) :
    polarizedFaceGenerator C a b faceBoundary e = 0 := by
  by_cases he : e ∈ faceBoundary
  · apply indicatorChain_apply_of_not_mem
    intro hmem
    exact hcolor ((mem_boundaryBicoloredEdges_iff C a b).1 hmem).2
  · exact polarizedFaceGenerator_eq_zero_of_not_mem_boundary C he

theorem polarizedFaceGenerator_nonzero_weight {G : SimpleGraph V} (C : G.EdgeColoring Color)
    {a b : Color} {faceBoundary : Finset G.edgeSet}
    (hab : ValidColorPair a b) :
    ∀ e ∈ boundaryBicoloredEdges C a b faceBoundary, polarizedFaceGenerator C a b faceBoundary e ≠ 0 := by
  intro e he
  rw [polarizedFaceGenerator_eq_third_of_mem C ((mem_boundaryBicoloredEdges_iff C a b).1 he).1
    ((mem_boundaryBicoloredEdges_iff C a b).1 he).2]
  exact (third_color_properties hab.1 hab.2.1 hab.2.2).1

/-- The simplified Kempe-closure generator family attached to a base coloring and a face-boundary
map. This packages the usable boundary-vector content of Definition 4.8. -/
def kempeClosureGeneratorFamily {G : SimpleGraph V} {F : Type*}
    (faceBoundary : F → Finset G.edgeSet) (C₀ : G.EdgeColoring Color) :
    Set (G.edgeSet → Color) :=
  {x | ∃ C ∈ G.EdgeKempeClosure C₀, ∃ f : F, ∃ a b : Color,
      ValidColorPair a b ∧ x = polarizedFaceGenerator C a b (faceBoundary f)}

theorem mem_kempeClosureGeneratorFamily_iff {G : SimpleGraph V} {F : Type*}
    (faceBoundary : F → Finset G.edgeSet) (C₀ : G.EdgeColoring Color) (x : G.edgeSet → Color) :
    x ∈ kempeClosureGeneratorFamily faceBoundary C₀ ↔
      ∃ C ∈ G.EdgeKempeClosure C₀, ∃ f : F, ∃ a b : Color,
        ValidColorPair a b ∧ x = polarizedFaceGenerator C a b (faceBoundary f) := by
  rfl

end Mettapedia.GraphTheory.FourColor
