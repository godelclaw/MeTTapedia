import Mettapedia.GraphTheory.FourColor.GoertzelDefinition48
import Mettapedia.GraphTheory.FourColor.RotationSystemEdgeColoring

namespace Mettapedia.GraphTheory.FourColor

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The four outer colors of a square, in cyclic order. -/
abbrev SquareBoundaryWord := Fin 4 → Color

/-- Colors of the four square edges, in the same cyclic order. -/
abbrev SquareInternalColoring := Fin 4 → Color

/-- Three colors meeting at a cubic vertex are nonzero and pairwise
distinct. -/
def ProperColorTriple (a b c : Color) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c
  deriving Decidable

/-- The exact local properness test for extending four outer colors across a
square. Internal edge `i` joins outer vertices `i` and `i+1` cyclically. -/
def IsSquareExtension
    (w : SquareBoundaryWord) (x : SquareInternalColoring) : Prop :=
  ProperColorTriple (w 0) (x 3) (x 0) ∧
  ProperColorTriple (w 1) (x 0) (x 1) ∧
  ProperColorTriple (w 2) (x 1) (x 2) ∧
  ProperColorTriple (w 3) (x 2) (x 3)
  deriving Decidable

/-- All proper internal colorings extending a fixed square boundary word. -/
def squareExtensions (w : SquareBoundaryWord) : Finset SquareInternalColoring :=
  Finset.univ.filter (IsSquareExtension w)

@[simp]
theorem mem_squareExtensions_iff
    {w : SquareBoundaryWord} {x : SquareInternalColoring} :
    x ∈ squareExtensions w ↔ IsSquareExtension w x := by
  simp [squareExtensions]

namespace SquareBoundaryWord

/-- Every outer square edge has a nonzero color. -/
def Nonzero (w : SquareBoundaryWord) : Prop :=
  w 0 ≠ 0 ∧ w 1 ≠ 0 ∧ w 2 ≠ 0 ∧ w 3 ≠ 0
  deriving Decidable

/-- The all-equal square boundary word. -/
def AllEqual (w : SquareBoundaryWord) : Prop :=
  w 0 = w 1 ∧ w 1 = w 2 ∧ w 2 = w 3
  deriving Decidable

/-- Adjacent equal pairs on edges `0,1` and `2,3`. -/
def Adjacent01_23 (w : SquareBoundaryWord) : Prop :=
  w 0 = w 1 ∧ w 2 = w 3 ∧ w 0 ≠ w 2
  deriving Decidable

/-- Adjacent equal pairs on edges `1,2` and `3,0`. -/
def Adjacent12_30 (w : SquareBoundaryWord) : Prop :=
  w 1 = w 2 ∧ w 3 = w 0 ∧ w 1 ≠ w 3
  deriving Decidable

/-- Either of the two adjacent-pair word types associated to the two planar
square reductions. -/
def AdjacentPairs (w : SquareBoundaryWord) : Prop :=
  w.Adjacent01_23 ∨ w.Adjacent12_30
  deriving Decidable

/-- The opposite-pair Birkhoff word type. -/
def OppositePairs (w : SquareBoundaryWord) : Prop :=
  w 0 = w 2 ∧ w 1 = w 3 ∧ w 0 ≠ w 1
  deriving Decidable

end SquareBoundaryWord

/-- SQ1, the complete square fiber table. For all four-color words, the
number of proper internal colorings is two for a nonzero all-equal word, one
for a nonzero adjacent-pair word, and zero otherwise. This includes words
with a zero outer color instead of silently assuming the Tait condition. -/
theorem squareFiberTable :
    ∀ w : SquareBoundaryWord,
      (squareExtensions w).card =
        if w.Nonzero ∧ w.AllEqual then 2
        else if w.Nonzero ∧ w.AdjacentPairs then 1 else 0 := by
  decide

/-- Every colorable square boundary word is all-equal or adjacent-paired;
the opposite-pair pattern never occurs. -/
theorem squareExtension_boundary_classification :
    ∀ w : SquareBoundaryWord, ∀ x : SquareInternalColoring,
      IsSquareExtension w x → w.AllEqual ∨ w.AdjacentPairs := by
  decide

/-- The Birkhoff obstruction in exact finite form: an opposite-pair word has
no proper square extension. -/
theorem squareOppositePairs_uncolorable :
    ∀ w : SquareBoundaryWord,
      w.OppositePairs → squareExtensions w = ∅ := by
  decide

/-- One local square-cycle move swaps the two colors appearing on the square
cycle. The fixed choice from internal edges `0` and `1` is canonical in the
only nontrivial, all-equal fiber. -/
def IsSquareCycleSwitch
    (x y : SquareInternalColoring) : Prop :=
  x 0 ≠ 0 ∧ x 1 ≠ 0 ∧ x 0 ≠ x 1 ∧
    ∀ i : Fin 4, y i = Color.swap (x 0) (x 1) (x i)
  deriving Decidable

/-- Every square fiber is internally connected: its two extensions are
equal or differ by the square's own bicolored cycle switch. -/
theorem squareFibers_internallyConnected :
    ∀ w : SquareBoundaryWord,
      ∀ x ∈ squareExtensions w, ∀ y ∈ squareExtensions w,
        x = y ∨ IsSquareCycleSwitch x y := by
  decide

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E)

/-- Named vertices and edges of a facial-square reduction. Structural
validity is kept in the computed predicate `WellFormed`. -/
structure FacialSquareData where
  w : V
  x : V
  y : V
  z : V
  wx : E
  xy : E
  yz : E
  zw : E
  outerW : E
  outerX : E
  outerY : E
  outerZ : E

namespace FacialSquareData

/-- Computed rotation-system conditions for a facial square with one outer
edge at each cubic corner. -/
def WellFormed (Q : @FacialSquareData V E) : Prop :=
  ({Q.w, Q.x, Q.y, Q.z} : Finset V).card = 4 ∧
  RS.incidentEdges Q.w = {Q.outerW, Q.zw, Q.wx} ∧
  RS.incidentEdges Q.x = {Q.outerX, Q.wx, Q.xy} ∧
  RS.incidentEdges Q.y = {Q.outerY, Q.xy, Q.yz} ∧
  RS.incidentEdges Q.z = {Q.outerZ, Q.yz, Q.zw} ∧
  ({Q.wx, Q.xy, Q.yz, Q.zw} : Finset E) ∈ RS.internalFaces

/-- A four-entry function used to expose the cyclic local colors without
introducing an additional data carrier. -/
def colorQuad (a b c d : Color) (i : Fin 4) : Color :=
  if i = 0 then a else if i = 1 then b else if i = 2 then c else d

/-- Outer colors extracted from a graph-level coloring. -/
def boundaryWord
    (Q : @FacialSquareData V E) (C : E → Color) : SquareBoundaryWord :=
  colorQuad (C Q.outerW) (C Q.outerX) (C Q.outerY) (C Q.outerZ)

/-- Internal square-edge colors extracted from a graph-level coloring. -/
def internalColoring
    (Q : @FacialSquareData V E) (C : E → Color) : SquareInternalColoring :=
  colorQuad (C Q.wx) (C Q.xy) (C Q.yz) (C Q.zw)

end FacialSquareData

private theorem pairwise_ne_of_triple_card_eq_three
    {a b c : E} (hcard : ({a, b, c} : Finset E).card = 3) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  constructor
  · intro hab
    subst b
    have hcard' : ({a, c} : Finset E).card = 3 := by simpa using hcard
    have hle : ({a, c} : Finset E).card ≤ 2 := Finset.card_le_two
    omega
  · constructor
    · intro hac
      subst c
      have hcard' : ({b, a} : Finset E).card = 3 := by simpa using hcard
      have hle : ({b, a} : Finset E).card ≤ 2 := Finset.card_le_two
      omega
    · intro hbc
      subst c
      have hcard' : ({a, b} : Finset E).card = 3 := by simpa using hcard
      have hle : ({a, b} : Finset E).card ≤ 2 := Finset.card_le_two
      omega

/-- A graph-level Tait coloring of a well-formed facial square restricts to
an entry of the exact local square fiber. -/
theorem facialSquare_internalColoring_isSquareExtension
    (Q : @FacialSquareData V E) (hQ : Q.WellFormed RS)
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) :
    IsSquareExtension (Q.boundaryWord C) (Q.internalColoring C) := by
  have hwCard : ({Q.outerW, Q.zw, Q.wx} : Finset E).card = 3 := by
    rw [← hQ.2.1]
    exact RS.incidentEdges_card_eq_three_of_isCubic hCubic Q.w
  have hxCard : ({Q.outerX, Q.wx, Q.xy} : Finset E).card = 3 := by
    rw [← hQ.2.2.1]
    exact RS.incidentEdges_card_eq_three_of_isCubic hCubic Q.x
  have hyCard : ({Q.outerY, Q.xy, Q.yz} : Finset E).card = 3 := by
    rw [← hQ.2.2.2.1]
    exact RS.incidentEdges_card_eq_three_of_isCubic hCubic Q.y
  have hzCard : ({Q.outerZ, Q.yz, Q.zw} : Finset E).card = 3 := by
    rw [← hQ.2.2.2.2.1]
    exact RS.incidentEdges_card_eq_three_of_isCubic hCubic Q.z
  have hw := pairwise_ne_of_triple_card_eq_three hwCard
  have hx := pairwise_ne_of_triple_card_eq_three hxCard
  have hy := pairwise_ne_of_triple_card_eq_three hyCard
  have hz := pairwise_ne_of_triple_card_eq_three hzCard
  have adj {v : V} {e f : E} (hne : e ≠ f)
      (he : e ∈ RS.incidentEdges v) (hf : f ∈ RS.incidentEdges v) :
      C e ≠ C f :=
    C.valid (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges hne he hf)
  unfold IsSquareExtension ProperColorTriple
  simp only [FacialSquareData.boundaryWord,
    FacialSquareData.internalColoring, FacialSquareData.colorQuad,
    Fin.isValue, ↓reduceIte]
  constructor
  · have ho : Q.outerW ∈ RS.incidentEdges Q.w := by rw [hQ.2.1]; simp
    have hzwi : Q.zw ∈ RS.incidentEdges Q.w := by rw [hQ.2.1]; simp
    have hwxi : Q.wx ∈ RS.incidentEdges Q.w := by rw [hQ.2.1]; simp
    exact ⟨hC _, hC _, hC _, adj hw.1 ho hzwi, adj hw.2.1 ho hwxi,
      adj hw.2.2 hzwi hwxi⟩
  · constructor
    · have ho : Q.outerX ∈ RS.incidentEdges Q.x := by rw [hQ.2.2.1]; simp
      have hwi : Q.wx ∈ RS.incidentEdges Q.x := by rw [hQ.2.2.1]; simp
      have hyi : Q.xy ∈ RS.incidentEdges Q.x := by rw [hQ.2.2.1]; simp
      exact ⟨hC _, hC _, hC _, adj hx.1 ho hwi, adj hx.2.1 ho hyi,
        adj hx.2.2 hwi hyi⟩
    · constructor
      · have ho : Q.outerY ∈ RS.incidentEdges Q.y := by rw [hQ.2.2.2.1]; simp
        have hxi : Q.xy ∈ RS.incidentEdges Q.y := by rw [hQ.2.2.2.1]; simp
        have hyi : Q.yz ∈ RS.incidentEdges Q.y := by rw [hQ.2.2.2.1]; simp
        exact ⟨hC _, hC _, hC _, adj hy.1 ho hxi, adj hy.2.1 ho hyi,
          adj hy.2.2 hxi hyi⟩
      · have ho : Q.outerZ ∈ RS.incidentEdges Q.z := by rw [hQ.2.2.2.2.1]; simp
        have hyi : Q.yz ∈ RS.incidentEdges Q.z := by rw [hQ.2.2.2.2.1]; simp
        have hzwi : Q.zw ∈ RS.incidentEdges Q.z := by rw [hQ.2.2.2.2.1]; simp
        exact ⟨hC _, hC _, hC _, adj hz.1 ho hyi, adj hz.2.1 ho hzwi,
          adj hz.2.2 hyi hzwi⟩

/-- The outer word extracted from a Tait-colored facial square is nonzero. -/
theorem facialSquare_boundaryWord_nonzero
    (Q : @FacialSquareData V E) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) :
    (Q.boundaryWord C).Nonzero := by
  simp only [SquareBoundaryWord.Nonzero, FacialSquareData.boundaryWord,
    FacialSquareData.colorQuad, Fin.isValue, ↓reduceIte]
  exact ⟨hC Q.outerW, hC Q.outerX, hC Q.outerY, hC Q.outerZ⟩

/-- Graph-level consequence of SQ1: a Tait-colored facial square has either
an all-equal outer word or one of the two adjacent-pair words. -/
theorem facialSquare_boundaryWord_classification
    (Q : @FacialSquareData V E) (hQ : Q.WellFormed RS)
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) :
    (Q.boundaryWord C).AllEqual ∨
      (Q.boundaryWord C).AdjacentPairs := by
  exact squareExtension_boundary_classification
    (Q.boundaryWord C) (Q.internalColoring C)
    (RS.facialSquare_internalColoring_isSquareExtension Q hQ hCubic C hC)

end RotationSystem

end Mettapedia.GraphTheory.FourColor
