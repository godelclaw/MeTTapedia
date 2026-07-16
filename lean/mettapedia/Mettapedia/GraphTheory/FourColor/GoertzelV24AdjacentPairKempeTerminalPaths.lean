import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeBoundaryOrbit
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

namespace SimpleGraph.Coloring

variable {V α : Type*} {G : SimpleGraph V} [DecidableEq α]

/-- The selected two-color subgraph has its canonical Boolean coloring. -/
def bicoloredBoolColoring
    (C : G.Coloring α) (a b : α) (hab : a ≠ b) :
    (C.bicoloredSubgraph a b).Coloring Bool where
  toFun vertex := decide (C vertex.1 = b)
  map_rel' := by
    intro left right hadj
    have hne : C left.1 ≠ C right.1 := C.valid hadj
    rcases left.2 with hleft | hleft <;>
      rcases right.2 with hright | hright
    · exact False.elim (hne (hleft.trans hright.symm))
    · simp [hleft, hright, hab]
    · simp [hleft, hright, hab]
    · exact False.elim (hne (hleft.trans hright.symm))

/-- A walk in a bicolored subgraph whose endpoint graph colors agree has
even length. -/
theorem bicoloredWalk_even_length_of_endpoint_colors_eq
    (C : G.Coloring α) (a b : α) (hab : a ≠ b)
    {left right : C.bicoloredSet a b}
    (path : (C.bicoloredSubgraph a b).Walk left right)
    (hcolor : C left.1 = C right.1) :
    Even path.length := by
  apply ((bicoloredBoolColoring C a b hab).even_length_iff_congr path).2
  simp [bicoloredBoolColoring, hcolor]

end SimpleGraph.Coloring

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary
open GoertzelV24FramedTrail
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality

/-- If two nonzero summands add to the first color of a valid pair, then a
summand selected from that pair must be the second color. -/
theorem selectedSummand_eq_second_of_sum_eq_first :
    ∀ a b x y : Color, ValidColorPair a b →
      x ≠ 0 → y ≠ 0 → x + y = a → (x = a ∨ x = b) → x = b := by
  intro a b x y _hab _hx hy hsum hselected
  rcases hselected with hxa | hxb
  · exfalso
    apply hy
    apply add_left_cancel (a := a)
    simpa [hxa] using hsum
  · exact hxb

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance terminalPathGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- When the missing color at a degree-two port is the first member of a
valid pair, its unique incident selected edge has the second color. -/
theorem incident_bicolored_edge_color_eq_second_of_colorWord_eq_first
    {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {a b : Color} (hab : ValidColorPair a b)
    (port : Fin portCount)
    (hword : data.colorWord C port = a)
    {edge : G.edgeSet}
    (hincident : edge ∈ incidentEdgeFinset G (data.defectVertex port))
    (hselected : C edge = a ∨ C edge = b) :
    C edge = b := by
  rcases Finset.card_eq_two.mp (hdata.2.1 port) with
    ⟨firstEdge, secondEdge, hne, hedges⟩
  have hsum : C firstEdge + C secondEdge = a := by
    simpa [colorWord, vertexKirchhoffSum, hedges, hne] using hword
  rw [hedges] at hincident
  simp only [Finset.mem_insert, Finset.mem_singleton] at hincident
  rcases hincident with hfirst | hsecond
  · subst edge
    exact selectedSummand_eq_second_of_sum_eq_first
      a b (C firstEdge) (C secondEdge) hab (hC firstEdge) (hC secondEdge)
        hsum hselected
  · subst edge
    exact selectedSummand_eq_second_of_sum_eq_first
      a b (C secondEdge) (C firstEdge) hab (hC secondEdge) (hC firstEdge)
        (by simpa [add_comm] using hsum) hselected

/-- A simple selected-color path between two boundary ports. -/
def HasSimpleKempePortPath {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (C : G.EdgeColoring Color) (a b : Color)
    (left right : Fin portCount) : Prop :=
  ∃ leftEdge rightEdge : C.bicoloredSet a b,
    leftEdge.1 ∈ incidentEdgeFinset G (data.defectVertex left) ∧
    rightEdge.1 ∈ incidentEdgeFinset G (data.defectVertex right) ∧
    ∃ path : (C.bicoloredSubgraph a b).Walk leftEdge rightEdge,
      path.IsPath

/-- Port connectivity is equivalent to the existence of a simple path in
the actual bicolored line graph. -/
theorem hasSimpleKempePortPath_iff_kempePortsConnected
    {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (C : G.EdgeColoring Color) (a b : Color)
    (left right : Fin portCount) :
    data.HasSimpleKempePortPath C a b left right ↔
      data.KempePortsConnected C a b left right := by
  constructor
  · rintro ⟨leftEdge, rightEdge, hleft, hright, path, _hpath⟩
    exact ⟨leftEdge, rightEdge, hleft, hright, path.reachable⟩
  · rintro ⟨leftEdge, rightEdge, hleft, hright, hreachable⟩
    rcases hreachable.exists_isPath with ⟨path, hpath⟩
    exact ⟨leftEdge, rightEdge, hleft, hright, path, hpath⟩

/-- At a constant first-color boundary word, every simple selected path
between connected ports has second-colored endpoints and even length. -/
theorem exists_even_simpleKempePortPath_of_constant_colorWord
    {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {a b : Color} (hab : ValidColorPair a b)
    (hconstant : ∀ port : Fin portCount, data.colorWord C port = a)
    (left right : Fin portCount)
    (hconnected : data.KempePortsConnected C a b left right) :
    ∃ leftEdge rightEdge : C.bicoloredSet a b,
      leftEdge.1 ∈ incidentEdgeFinset G (data.defectVertex left) ∧
      rightEdge.1 ∈ incidentEdgeFinset G (data.defectVertex right) ∧
      C leftEdge.1 = b ∧ C rightEdge.1 = b ∧
      ∃ path : (C.bicoloredSubgraph a b).Walk leftEdge rightEdge,
        path.IsPath ∧ Even path.length := by
  rcases (data.hasSimpleKempePortPath_iff_kempePortsConnected
    C a b left right).2 hconnected with
    ⟨leftEdge, rightEdge, hleft, hright, path, hpath⟩
  have hleftColor : C leftEdge.1 = b :=
    data.incident_bicolored_edge_color_eq_second_of_colorWord_eq_first
      hdata C hC hab left (hconstant left) hleft leftEdge.2
  have hrightColor : C rightEdge.1 = b :=
    data.incident_bicolored_edge_color_eq_second_of_colorWord_eq_first
      hdata C hC hab right (hconstant right) hright rightEdge.2
  have heven : Even path.length :=
    C.bicoloredWalk_even_length_of_endpoint_colors_eq
      a b hab.2.2 path (hleftColor.trans hrightColor.symm)
  exact ⟨leftEdge, rightEdge, hleft, hright,
    hleftColor, hrightColor, path, hpath, heven⟩

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance adjacentTerminalPathGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet := Subtype.instDecidableEq

local instance adjacentTerminalPathRetainedVertexSetFintype
    (first second : V) : Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

local instance adjacentTerminalPathRetainedVertexSetDecidableEq
    (first second : V) : DecidableEq (retainedVertexSet first second) :=
  Subtype.instDecidableEq

/-- A constant four-port word in an uncolorable cubic ambient graph forces
the exact same-side reachability partition for every valid color pair
containing that constant request. -/
theorem hasSameSideKempeReachabilityProfile_of_constant_colorWord
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    {a b : Color} (hab : ValidColorPair a b)
    (hconstant : ∀ port : Fin 4,
      data.degreeTwoBoundaryData.colorWord C port = a) :
    data.degreeTwoBoundaryData.HasSameSideKempeReachabilityProfile
      C a b := by
  let boundary := data.degreeTwoBoundaryData
  have hwell := data.degreeTwoBoundaryData_wellFormed hcubic
  have hselected : ∀ port : Fin 4,
      boundary.colorWord C port = a ∨ boundary.colorWord C port = b :=
    fun port => Or.inl (hconstant port)
  have hpaired : ∀ K : (C.bicoloredSubgraph a b).ConnectedComponent,
      (boundary.KempeComponentMeetsPort C a b K 0 ↔
        boundary.KempeComponentMeetsPort C a b K 1) ∧
      (boundary.KempeComponentMeetsPort C a b K 2 ↔
        boundary.KempeComponentMeetsPort C a b K 3) := by
    intro K
    exact ⟨
      data.kempeComponentMeetsPort_zero_iff_one_of_selected_request
        hcubic hnotColorable C hC hab K (Or.inl (hconstant 0)),
      data.kempeComponentMeetsPort_two_iff_three_of_selected_request
        hcubic hnotColorable C hC hab K (Or.inl (hconstant 2))⟩
  have hprofile : boundary.HasTwoSameSideKempeCutProfile C a b :=
    boundary.exists_two_sameSide_kempeComponents
      hwell C hab hselected hpaired
  exact boundary.hasSameSideKempeReachabilityProfile_of_twoComponentProfile
    C a b hprofile

/-- A constant four-port word in an uncolorable cubic ambient graph forces
two same-side simple terminal paths of even length for every valid pair
containing that constant request. -/
theorem exists_two_even_simpleKempePortPaths_of_constant_colorWord
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    {a b : Color} (hab : ValidColorPair a b)
    (hconstant : ∀ port : Fin 4,
      data.degreeTwoBoundaryData.colorWord C port = a) :
    (∃ leftEdge rightEdge : C.bicoloredSet a b,
      leftEdge.1 ∈ incidentEdgeFinset
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
          (data.degreeTwoBoundaryData.defectVertex 0) ∧
      rightEdge.1 ∈ incidentEdgeFinset
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
          (data.degreeTwoBoundaryData.defectVertex 1) ∧
      C leftEdge.1 = b ∧ C rightEdge.1 = b ∧
      ∃ path : (C.bicoloredSubgraph a b).Walk leftEdge rightEdge,
        path.IsPath ∧ Even path.length) ∧
    (∃ leftEdge rightEdge : C.bicoloredSet a b,
      leftEdge.1 ∈ incidentEdgeFinset
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
          (data.degreeTwoBoundaryData.defectVertex 2) ∧
      rightEdge.1 ∈ incidentEdgeFinset
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
          (data.degreeTwoBoundaryData.defectVertex 3) ∧
      C leftEdge.1 = b ∧ C rightEdge.1 = b ∧
      ∃ path : (C.bicoloredSubgraph a b).Walk leftEdge rightEdge,
        path.IsPath ∧ Even path.length) := by
  let boundary := data.degreeTwoBoundaryData
  have hwell := data.degreeTwoBoundaryData_wellFormed hcubic
  have hreachability :
      boundary.HasSameSideKempeReachabilityProfile C a b :=
    data.hasSameSideKempeReachabilityProfile_of_constant_colorWord
      hcubic hnotColorable C hC hab hconstant
  have hconnected01 : boundary.KempePortsConnected C a b 0 1 :=
    (hreachability 0 1).2 (by simp)
  have hconnected23 : boundary.KempePortsConnected C a b 2 3 :=
    (hreachability 2 3).2 (by simp)
  exact ⟨
    boundary.exists_even_simpleKempePortPath_of_constant_colorWord
      hwell C hC hab hconstant 0 1 hconnected01,
    boundary.exists_even_simpleKempePortPath_of_constant_colorWord
      hwell C hC hab hconstant 2 3 hconnected23⟩

end

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
