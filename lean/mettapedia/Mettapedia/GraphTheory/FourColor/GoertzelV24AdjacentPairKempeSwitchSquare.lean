import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeSideSwitch

namespace SimpleGraph.Coloring

variable {V α : Type*} {G : SimpleGraph V} [DecidableEq α]

noncomputable section

def bicoloredSubgraphIsoSwapOnKempeComponent
    (C : G.Coloring α) (a b : α)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    (C.swapOnKempeComponent a b K).bicoloredSubgraph a b ≃g
      C.bicoloredSubgraph a b where
  toFun vertex := ⟨vertex.1,
    (C.mem_bicoloredSet_swapOnKempeComponent_iff a b K vertex.1).1
      vertex.2⟩
  invFun vertex := ⟨vertex.1,
    (C.mem_bicoloredSet_swapOnKempeComponent_iff a b K vertex.1).2
      vertex.2⟩
  left_inv vertex := by ext; rfl
  right_inv vertex := by ext; rfl
  map_rel_iff' := by rfl

@[simp] theorem bicoloredSubgraphIsoSwapOnKempeComponent_apply_val
    (C : G.Coloring α) (a b : α)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (vertex : (C.swapOnKempeComponent a b K).bicoloredSet a b) :
    (bicoloredSubgraphIsoSwapOnKempeComponent C a b K vertex).1 = vertex.1 :=
  rfl

@[simp] theorem bicoloredSubgraphIsoSwapOnKempeComponent_symm_apply_val
    (C : G.Coloring α) (a b : α)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (vertex : C.bicoloredSet a b) :
    ((bicoloredSubgraphIsoSwapOnKempeComponent C a b K).symm vertex).1 = vertex.1 :=
  rfl

def transportKempeComponentAfterSwap
    (C : G.Coloring α) (a b : α)
    (K L : (C.bicoloredSubgraph a b).ConnectedComponent) :
    ((C.swapOnKempeComponent a b K).bicoloredSubgraph a b).ConnectedComponent :=
  (bicoloredSubgraphIsoSwapOnKempeComponent C a b K).symm.connectedComponentEquiv L

theorem mem_kempeComponentSet_transportKempeComponentAfterSwap_iff
    (C : G.Coloring α) (a b : α)
    (K L : (C.bicoloredSubgraph a b).ConnectedComponent)
    (vertex : V) :
    vertex ∈ (C.swapOnKempeComponent a b K).kempeComponentSet a b
        (transportKempeComponentAfterSwap C a b K L) ↔
      vertex ∈ C.kempeComponentSet a b L := by
  let C' := C.swapOnKempeComponent a b K
  let φ := bicoloredSubgraphIsoSwapOnKempeComponent C a b K
  constructor
  · rintro ⟨hselected, hcomponent⟩
    have hold : vertex ∈ C.bicoloredSet a b := by
      rw [← C.bicoloredSet_swapOnKempeComponent a b K]
      exact hselected
    refine ⟨hold, ?_⟩
    calc
      (C.bicoloredSubgraph a b).connectedComponentMk ⟨vertex, hold⟩ =
          (C.bicoloredSubgraph a b).connectedComponentMk
            (φ ⟨vertex, hselected⟩) := by
        congr 1
      _ = φ.connectedComponentEquiv
          ((C'.bicoloredSubgraph a b).connectedComponentMk
            ⟨vertex, hselected⟩) := by rfl
      _ = φ.connectedComponentEquiv
          (transportKempeComponentAfterSwap C a b K L) :=
        congrArg φ.connectedComponentEquiv hcomponent
      _ = L := φ.connectedComponentEquiv.apply_symm_apply L
  · rintro ⟨hselected, hcomponent⟩
    have hnew : vertex ∈ C'.bicoloredSet a b := by
      rw [C.bicoloredSet_swapOnKempeComponent a b K]
      exact hselected
    refine ⟨hnew, ?_⟩
    calc
      (C'.bicoloredSubgraph a b).connectedComponentMk ⟨vertex, hnew⟩ =
          (C'.bicoloredSubgraph a b).connectedComponentMk
            (φ.symm ⟨vertex, hselected⟩) := by
        congr 1
      _ = φ.symm.connectedComponentEquiv
          ((C.bicoloredSubgraph a b).connectedComponentMk
            ⟨vertex, hselected⟩) := by rfl
      _ = φ.symm.connectedComponentEquiv L :=
        congrArg φ.symm.connectedComponentEquiv hcomponent
      _ = transportKempeComponentAfterSwap C a b K L := rfl

theorem kempeComponentSet_transportKempeComponentAfterSwap
    (C : G.Coloring α) (a b : α)
    (K L : (C.bicoloredSubgraph a b).ConnectedComponent) :
    (C.swapOnKempeComponent a b K).kempeComponentSet a b
        (transportKempeComponentAfterSwap C a b K L) =
      C.kempeComponentSet a b L := by
  ext vertex
  exact mem_kempeComponentSet_transportKempeComponentAfterSwap_iff
    C a b K L vertex

omit [DecidableEq α] in
theorem kempeComponent_eq_of_common_vertex
    (C : G.Coloring α) {a b : α}
    {K L : (C.bicoloredSubgraph a b).ConnectedComponent}
    {vertex : V}
    (hK : vertex ∈ C.kempeComponentSet a b K)
    (hL : vertex ∈ C.kempeComponentSet a b L) :
    K = L := by
  rcases hK with ⟨hselectedK, hcomponentK⟩
  rcases hL with ⟨hselectedL, hcomponentL⟩
  have hvertex :
      (⟨vertex, hselectedK⟩ : C.bicoloredSet a b) =
        ⟨vertex, hselectedL⟩ := by
    rfl
  calc
    K = (C.bicoloredSubgraph a b).connectedComponentMk
        ⟨vertex, hselectedK⟩ := hcomponentK.symm
    _ = (C.bicoloredSubgraph a b).connectedComponentMk
        ⟨vertex, hselectedL⟩ := congrArg _ hvertex
    _ = L := hcomponentL

/-- Switching a component and then its canonical transported copy restores
the original coloring. -/
theorem swapOnKempeComponent_transport_self
    (C : G.Coloring α) (a b : α)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    (C.swapOnKempeComponent a b K).swapOnKempeComponent a b
        (transportKempeComponentAfterSwap C a b K K) = C := by
  ext vertex
  by_cases hmem : vertex ∈ C.kempeComponentSet a b K
  · have htransport :
        vertex ∈ (C.swapOnKempeComponent a b K).kempeComponentSet a b
          (transportKempeComponentAfterSwap C a b K K) :=
      (mem_kempeComponentSet_transportKempeComponentAfterSwap_iff
        C a b K K vertex).2 hmem
    rw [(C.swapOnKempeComponent a b K).swapOnKempeComponent_apply_of_mem
      htransport, C.swapOnKempeComponent_apply_of_mem hmem]
    simp
  · have htransport :
        vertex ∉ (C.swapOnKempeComponent a b K).kempeComponentSet a b
          (transportKempeComponentAfterSwap C a b K K) := by
      intro hnew
      exact hmem
        ((mem_kempeComponentSet_transportKempeComponentAfterSwap_iff
          C a b K K vertex).1 hnew)
    rw [(C.swapOnKempeComponent a b K).swapOnKempeComponent_apply_of_not_mem
      htransport, C.swapOnKempeComponent_apply_of_not_mem hmem]

/-- A Kempe-component switch is reversible by switching its canonically
transported component in the new coloring. -/
theorem kempeStep_symm {C C' : G.Coloring α}
    (step : G.KempeStep C C') : G.KempeStep C' C := by
  rcases step with ⟨a, b, K, rfl⟩
  refine ⟨a, b, transportKempeComponentAfterSwap C a b K K, ?_⟩
  exact (swapOnKempeComponent_transport_self C a b K).symm

/-- Kempe reachability is symmetric: reversing each component switch
reverses an arbitrary finite switching sequence. -/
theorem mem_kempeClosure_symm {C₀ C : G.Coloring α}
    (reachable : C ∈ G.KempeClosure C₀) :
    C₀ ∈ G.KempeClosure C := by
  induction reachable with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (kempeStep_symm step)) ih

/-- Any reachable coloring generates exactly the same Kempe closure as its
source coloring. -/
theorem kempeClosure_eq_of_mem {C₀ C : G.Coloring α}
    (reachable : C ∈ G.KempeClosure C₀) :
    G.KempeClosure C₀ = G.KempeClosure C :=
  G.kempeClosure_eq_of_mem_of_mem reachable
    (mem_kempeClosure_symm reachable)

/-- Canonically transported component switches commute at graph level. -/
theorem swapOnKempeComponent_transport_commute
    (C : G.Coloring α) (a b : α)
    (K L : (C.bicoloredSubgraph a b).ConnectedComponent) :
    (C.swapOnKempeComponent a b K).swapOnKempeComponent a b
        (transportKempeComponentAfterSwap C a b K L) =
      (C.swapOnKempeComponent a b L).swapOnKempeComponent a b
        (transportKempeComponentAfterSwap C a b L K) := by
  by_cases hKL : K = L
  · subst L
    rfl
  ext vertex
  by_cases hK : vertex ∈ C.kempeComponentSet a b K
  · have hL : vertex ∉ C.kempeComponentSet a b L := by
      intro hL
      exact hKL (kempeComponent_eq_of_common_vertex C hK hL)
    have hLafterK :
        vertex ∉ (C.swapOnKempeComponent a b K).kempeComponentSet a b
          (transportKempeComponentAfterSwap C a b K L) := by
      intro hnew
      exact hL
        ((mem_kempeComponentSet_transportKempeComponentAfterSwap_iff
          C a b K L vertex).1 hnew)
    have hKafterL :
        vertex ∈ (C.swapOnKempeComponent a b L).kempeComponentSet a b
          (transportKempeComponentAfterSwap C a b L K) :=
      (mem_kempeComponentSet_transportKempeComponentAfterSwap_iff
        C a b L K vertex).2 hK
    rw [(C.swapOnKempeComponent a b K).swapOnKempeComponent_apply_of_not_mem
      hLafterK, C.swapOnKempeComponent_apply_of_mem hK,
      (C.swapOnKempeComponent a b L).swapOnKempeComponent_apply_of_mem
        hKafterL, C.swapOnKempeComponent_apply_of_not_mem hL]
  · by_cases hL : vertex ∈ C.kempeComponentSet a b L
    · have hLafterK :
          vertex ∈ (C.swapOnKempeComponent a b K).kempeComponentSet a b
            (transportKempeComponentAfterSwap C a b K L) :=
        (mem_kempeComponentSet_transportKempeComponentAfterSwap_iff
          C a b K L vertex).2 hL
      have hKafterL :
          vertex ∉ (C.swapOnKempeComponent a b L).kempeComponentSet a b
            (transportKempeComponentAfterSwap C a b L K) := by
        intro hnew
        exact hK
          ((mem_kempeComponentSet_transportKempeComponentAfterSwap_iff
            C a b L K vertex).1 hnew)
      rw [(C.swapOnKempeComponent a b K).swapOnKempeComponent_apply_of_mem
        hLafterK, C.swapOnKempeComponent_apply_of_not_mem hK,
        (C.swapOnKempeComponent a b L).swapOnKempeComponent_apply_of_not_mem
          hKafterL, C.swapOnKempeComponent_apply_of_mem hL]
    · have hLafterK :
          vertex ∉ (C.swapOnKempeComponent a b K).kempeComponentSet a b
            (transportKempeComponentAfterSwap C a b K L) := by
        intro hnew
        exact hL
          ((mem_kempeComponentSet_transportKempeComponentAfterSwap_iff
            C a b K L vertex).1 hnew)
      have hKafterL :
          vertex ∉ (C.swapOnKempeComponent a b L).kempeComponentSet a b
            (transportKempeComponentAfterSwap C a b L K) := by
        intro hnew
        exact hK
          ((mem_kempeComponentSet_transportKempeComponentAfterSwap_iff
            C a b L K vertex).1 hnew)
      rw [(C.swapOnKempeComponent a b K).swapOnKempeComponent_apply_of_not_mem
        hLafterK, C.swapOnKempeComponent_apply_of_not_mem hK,
        (C.swapOnKempeComponent a b L).swapOnKempeComponent_apply_of_not_mem
          hKafterL, C.swapOnKempeComponent_apply_of_not_mem hL]

/-- The four colorings generated by two component switches, with the fourth
corner using the canonical transport of the second component. -/
def kempeSwitchSquareColoring
    (C : G.Coloring α) (a b : α)
    (K L : (C.bicoloredSubgraph a b).ConnectedComponent) :
    Fin 4 → G.Coloring α :=
  ![C,
    C.swapOnKempeComponent a b K,
    C.swapOnKempeComponent a b L,
    (C.swapOnKempeComponent a b K).swapOnKempeComponent a b
      (transportKempeComponentAfterSwap C a b K L)]

@[simp] theorem kempeSwitchSquareColoring_zero
    (C : G.Coloring α) (a b : α)
    (K L : (C.bicoloredSubgraph a b).ConnectedComponent) :
    kempeSwitchSquareColoring C a b K L 0 = C := rfl

@[simp] theorem kempeSwitchSquareColoring_one
    (C : G.Coloring α) (a b : α)
    (K L : (C.bicoloredSubgraph a b).ConnectedComponent) :
    kempeSwitchSquareColoring C a b K L 1 =
      C.swapOnKempeComponent a b K := rfl

@[simp] theorem kempeSwitchSquareColoring_two
    (C : G.Coloring α) (a b : α)
    (K L : (C.bicoloredSubgraph a b).ConnectedComponent) :
    kempeSwitchSquareColoring C a b K L 2 =
      C.swapOnKempeComponent a b L := rfl

@[simp] theorem kempeSwitchSquareColoring_three
    (C : G.Coloring α) (a b : α)
    (K L : (C.bicoloredSubgraph a b).ConnectedComponent) :
    kempeSwitchSquareColoring C a b K L 3 =
      (C.swapOnKempeComponent a b K).swapOnKempeComponent a b
        (transportKempeComponentAfterSwap C a b K L) := rfl

/-- The fourth corner is independent of the order of the two switches. -/
theorem kempeSwitchSquareColoring_three_eq_reverse
    (C : G.Coloring α) (a b : α)
    (K L : (C.bicoloredSubgraph a b).ConnectedComponent) :
    kempeSwitchSquareColoring C a b K L 3 =
      (C.swapOnKempeComponent a b L).swapOnKempeComponent a b
        (transportKempeComponentAfterSwap C a b L K) := by
  exact swapOnKempeComponent_transport_commute C a b K L

theorem kempeSwitchSquare_step_zero_one
    (C : G.Coloring α) (a b : α)
    (K L : (C.bicoloredSubgraph a b).ConnectedComponent) :
    G.KempeStep (kempeSwitchSquareColoring C a b K L 0)
      (kempeSwitchSquareColoring C a b K L 1) := by
  exact G.kempeStep_swapOnKempeComponent C a b K

theorem kempeSwitchSquare_step_zero_two
    (C : G.Coloring α) (a b : α)
    (K L : (C.bicoloredSubgraph a b).ConnectedComponent) :
    G.KempeStep (kempeSwitchSquareColoring C a b K L 0)
      (kempeSwitchSquareColoring C a b K L 2) := by
  exact G.kempeStep_swapOnKempeComponent C a b L

theorem kempeSwitchSquare_step_one_three
    (C : G.Coloring α) (a b : α)
    (K L : (C.bicoloredSubgraph a b).ConnectedComponent) :
    G.KempeStep (kempeSwitchSquareColoring C a b K L 1)
      (kempeSwitchSquareColoring C a b K L 3) := by
  exact G.kempeStep_swapOnKempeComponent
    (C.swapOnKempeComponent a b K) a b
      (transportKempeComponentAfterSwap C a b K L)

theorem kempeSwitchSquare_step_two_three
    (C : G.Coloring α) (a b : α)
    (K L : (C.bicoloredSubgraph a b).ConnectedComponent) :
    G.KempeStep (kempeSwitchSquareColoring C a b K L 2)
      (kempeSwitchSquareColoring C a b K L 3) := by
  rw [kempeSwitchSquareColoring_three_eq_reverse C a b K L]
  exact G.kempeStep_swapOnKempeComponent
    (C.swapOnKempeComponent a b L) a b
      (transportKempeComponentAfterSwap C a b L K)

/-- Every corner of the switch square belongs to the Kempe closure of its
base coloring. -/
theorem kempeSwitchSquareColoring_mem_kempeClosure
    (C : G.Coloring α) (a b : α)
    (K L : (C.bicoloredSubgraph a b).ConnectedComponent)
    (state : Fin 4) :
    kempeSwitchSquareColoring C a b K L state ∈ G.KempeClosure C := by
  fin_cases state
  · exact G.mem_kempeClosure_self C
  · exact G.mem_kempeClosure_of_step (G.mem_kempeClosure_self C)
      (kempeSwitchSquare_step_zero_one C a b K L)
  · exact G.mem_kempeClosure_of_step (G.mem_kempeClosure_self C)
      (kempeSwitchSquare_step_zero_two C a b K L)
  · exact G.mem_kempeClosure_of_step
      (G.mem_kempeClosure_of_step (G.mem_kempeClosure_self C)
        (kempeSwitchSquare_step_zero_one C a b K L))
      (kempeSwitchSquare_step_one_three C a b K L)

end

end SimpleGraph.Coloring

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24AdjacentPairBoundary
open GoertzelV24FramedTrail

namespace GoertzelV24FourDefectBoundary

/-- The four boundary words generated by two ordered Kempe supports. -/
def boundaryKempeSquareWord {portCount : Nat}
    (a b : Color) (first second : Finset (Fin portCount))
    (word : Fin portCount → Color) :
    Fin 4 → (Fin portCount → Color) :=
  ![word,
    boundaryKempeSwap a b first word,
    boundaryKempeSwap a b second word,
    boundaryKempeSwap a b second (boundaryKempeSwap a b first word)]

@[simp] theorem boundaryKempeSquareWord_zero {portCount : Nat}
    (a b : Color) (first second : Finset (Fin portCount))
    (word : Fin portCount → Color) :
    boundaryKempeSquareWord a b first second word 0 = word := rfl

@[simp] theorem boundaryKempeSquareWord_one {portCount : Nat}
    (a b : Color) (first second : Finset (Fin portCount))
    (word : Fin portCount → Color) :
    boundaryKempeSquareWord a b first second word 1 =
      boundaryKempeSwap a b first word := rfl

@[simp] theorem boundaryKempeSquareWord_two {portCount : Nat}
    (a b : Color) (first second : Finset (Fin portCount))
    (word : Fin portCount → Color) :
    boundaryKempeSquareWord a b first second word 2 =
      boundaryKempeSwap a b second word := rfl

@[simp] theorem boundaryKempeSquareWord_three {portCount : Nat}
    (a b : Color) (first second : Finset (Fin portCount))
    (word : Fin portCount → Color) :
    boundaryKempeSquareWord a b first second word 3 =
      boundaryKempeSwap a b second (boundaryKempeSwap a b first word) := rfl

/-- The exact four-state same-side boundary orbit. -/
def sameSideBoundaryKempeOrbit
    (a b : Color) (word : Fin 4 → Color) :
    Fin 4 → (Fin 4 → Color) :=
  ![word,
    boundaryKempeSwap a b {0, 1} word,
    boundaryKempeSwap a b {2, 3} word,
    fun port => Equiv.swap a b (word port)]

/-- When every request is selected, the four same-side boundary states are
distinct. -/
theorem sameSideBoundaryKempeOrbit_injective
    {a b : Color} (hab : ValidColorPair a b)
    (word : Fin 4 → Color)
    (hselected : ∀ port : Fin 4, word port = a ∨ word port = b) :
    Function.Injective (sameSideBoundaryKempeOrbit a b word) := by
  have hzeroNe : Equiv.swap a b (word 0) ≠ word 0 :=
    equivSwap_ne_self_of_validColorPair hab (hselected 0)
  have htwoNe : Equiv.swap a b (word 2) ≠ word 2 :=
    equivSwap_ne_self_of_validColorPair hab (hselected 2)
  intro left right heq
  fin_cases left <;> fin_cases right
  all_goals
    first
    | rfl
    | exfalso
      have hzero := congrFun heq (0 : Fin 4)
      have htwo := congrFun heq (2 : Fin 4)
      simp [sameSideBoundaryKempeOrbit, boundaryKempeSwap,
        hzeroNe, htwoNe] at hzero htwo
      all_goals
        first
        | exact hzeroNe hzero.symm
        | exact htwoNe htwo.symm

namespace DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance transportGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Boundary incidence with a component is preserved by canonical component
transport across another switch. -/
theorem kempeComponentMeetsPort_transportKempeComponentAfterSwap_iff
    {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (C : G.EdgeColoring Color) (a b : Color)
    (K L : (C.bicoloredSubgraph a b).ConnectedComponent)
    (port : Fin portCount) :
    data.KempeComponentMeetsPort (C.swapOnKempeComponent a b K) a b
        (Coloring.transportKempeComponentAfterSwap C a b K L) port ↔
      data.KempeComponentMeetsPort C a b L port := by
  constructor
  · rintro ⟨edge, hincident, hcomponent⟩
    exact ⟨edge, hincident,
      (Coloring.mem_kempeComponentSet_transportKempeComponentAfterSwap_iff
        C a b K L edge).1 hcomponent⟩
  · rintro ⟨edge, hincident, hcomponent⟩
    exact ⟨edge, hincident,
      (Coloring.mem_kempeComponentSet_transportKempeComponentAfterSwap_iff
        C a b K L edge).2 hcomponent⟩

/-- The finite port support itself is invariant under canonical component
transport. -/
theorem kempePortSupport_transportKempeComponentAfterSwap
    {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (C : G.EdgeColoring Color) (a b : Color)
    (K L : (C.bicoloredSubgraph a b).ConnectedComponent) :
    data.kempePortSupport (C.swapOnKempeComponent a b K) a b
        (Coloring.transportKempeComponentAfterSwap C a b K L) =
      data.kempePortSupport C a b L := by
  ext port
  rw [data.mem_kempePortSupport_iff,
    data.mem_kempePortSupport_iff,
    data.kempeComponentMeetsPort_transportKempeComponentAfterSwap_iff]

/-- The graph-level commuting Kempe square induces exactly the corresponding
four-state finite boundary action. -/
theorem colorWord_kempeSwitchSquareColoring
    {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (C : G.EdgeColoring Color) {a b : Color}
    (hab : ValidColorPair a b)
    (K L : (C.bicoloredSubgraph a b).ConnectedComponent)
    (state : Fin 4) :
    data.colorWord (Coloring.kempeSwitchSquareColoring C a b K L state) =
      boundaryKempeSquareWord a b
        (data.kempePortSupport C a b K)
        (data.kempePortSupport C a b L)
        (data.colorWord C) state := by
  fin_cases state
  · rfl
  · exact data.colorWord_swapOnKempeComponent_eq_boundaryKempeSwap
      C hab K
  · exact data.colorWord_swapOnKempeComponent_eq_boundaryKempeSwap
      C hab L
  · change
      data.colorWord
          ((C.swapOnKempeComponent a b K).swapOnKempeComponent a b
            (Coloring.transportKempeComponentAfterSwap C a b K L)) =
        boundaryKempeSwap a b (data.kempePortSupport C a b L)
          (boundaryKempeSwap a b (data.kempePortSupport C a b K)
            (data.colorWord C))
    rw [data.colorWord_swapOnKempeComponent_eq_boundaryKempeSwap
        (C.swapOnKempeComponent a b K) hab
          (Coloring.transportKempeComponentAfterSwap C a b K L),
      data.kempePortSupport_transportKempeComponentAfterSwap C a b K L,
      data.colorWord_swapOnKempeComponent_eq_boundaryKempeSwap C hab K]

/-- Exact same-side supports identify the graph square's boundary words with
the four canonical same-side states. -/
theorem colorWord_kempeSwitchSquareColoring_eq_sameSideOrbit
    (data : DegreeTwoBoundaryData G 4)
    (C : G.EdgeColoring Color) {a b : Color}
    (hab : ValidColorPair a b)
    (K L : (C.bicoloredSubgraph a b).ConnectedComponent)
    (hsupportK : data.kempePortSupport C a b K = {0, 1})
    (hsupportL : data.kempePortSupport C a b L = {2, 3})
    (state : Fin 4) :
    data.colorWord (Coloring.kempeSwitchSquareColoring C a b K L state) =
      sameSideBoundaryKempeOrbit a b (data.colorWord C) state := by
  rw [data.colorWord_kempeSwitchSquareColoring C hab K L state,
    hsupportK, hsupportL]
  fin_cases state
  · rfl
  · rfl
  · rfl
  · change
      boundaryKempeSwap a b {2, 3}
          (boundaryKempeSwap a b {0, 1} (data.colorWord C)) =
        fun port => Equiv.swap a b (data.colorWord C port)
    calc
      boundaryKempeSwap a b {2, 3}
          (boundaryKempeSwap a b {0, 1} (data.colorWord C)) =
        boundaryKempeSwap a b {0, 1}
          (boundaryKempeSwap a b {2, 3} (data.colorWord C)) :=
        (boundaryKempeSwap_commute a b {0, 1} {2, 3}
          (data.colorWord C)).symm
      _ = fun port => Equiv.swap a b (data.colorWord C port) :=
        boundaryKempeSwap_sameSides_eq_global a b (data.colorWord C)

/-- All four corners of a component-switch square remain Tait colorings. -/
theorem isTaitEdgeColoring_kempeSwitchSquareColoring
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {a b : Color} (hab : ValidColorPair a b)
    (K L : (C.bicoloredSubgraph a b).ConnectedComponent)
    (state : Fin 4) :
    IsTaitEdgeColoring G
      (Coloring.kempeSwitchSquareColoring C a b K L state) := by
  fin_cases state
  · exact hC
  · exact isTaitEdgeColoring_swapOnKempeComponent hC hab K
  · exact isTaitEdgeColoring_swapOnKempeComponent hC hab L
  · exact isTaitEdgeColoring_swapOnKempeComponent
      (isTaitEdgeColoring_swapOnKempeComponent hC hab K) hab
        (Coloring.transportKempeComponentAfterSwap C a b K L)

/-- Selected exact same-side supports make the four graph colorings in the
commuting square pairwise distinct. -/
theorem kempeSwitchSquareColoring_injective_of_sameSide_supports
    (data : DegreeTwoBoundaryData G 4)
    (C : G.EdgeColoring Color) {a b : Color}
    (hab : ValidColorPair a b)
    (hselected : ∀ port : Fin 4,
      data.colorWord C port = a ∨ data.colorWord C port = b)
    (K L : (C.bicoloredSubgraph a b).ConnectedComponent)
    (hsupportK : data.kempePortSupport C a b K = {0, 1})
    (hsupportL : data.kempePortSupport C a b L = {2, 3}) :
    Function.Injective (Coloring.kempeSwitchSquareColoring C a b K L) := by
  intro left right heq
  apply sameSideBoundaryKempeOrbit_injective hab
    (data.colorWord C) hselected
  calc
    sameSideBoundaryKempeOrbit a b (data.colorWord C) left =
        data.colorWord
          (Coloring.kempeSwitchSquareColoring C a b K L left) :=
      (data.colorWord_kempeSwitchSquareColoring_eq_sameSideOrbit
        C hab K L hsupportK hsupportL left).symm
    _ = data.colorWord
          (Coloring.kempeSwitchSquareColoring C a b K L right) :=
      congrArg data.colorWord heq
    _ = sameSideBoundaryKempeOrbit a b (data.colorWord C) right :=
      data.colorWord_kempeSwitchSquareColoring_eq_sameSideOrbit
        C hab K L hsupportK hsupportL right

/-- An exact two-component profile realizes a genuine four-state commuting
Kempe square with the canonical same-side boundary action. -/
theorem exists_sameSide_kempeSwitchSquare
    (data : DegreeTwoBoundaryData G 4)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {a b : Color} (hab : ValidColorPair a b)
    (hselected : ∀ port : Fin 4,
      data.colorWord C port = a ∨ data.colorWord C port = b)
    (hprofile : data.HasTwoSameSideKempeCutProfile C a b) :
    ∃ K01 K23 : (C.bicoloredSubgraph a b).ConnectedComponent,
      K01 ≠ K23 ∧
      Function.Injective
        (Coloring.kempeSwitchSquareColoring C a b K01 K23) ∧
      (∀ state : Fin 4, IsTaitEdgeColoring G
        (Coloring.kempeSwitchSquareColoring C a b K01 K23 state)) ∧
      (∀ state : Fin 4,
        data.colorWord
            (Coloring.kempeSwitchSquareColoring C a b K01 K23 state) =
          sameSideBoundaryKempeOrbit a b (data.colorWord C) state) ∧
      G.lineGraph.KempeStep
        (Coloring.kempeSwitchSquareColoring C a b K01 K23 0)
        (Coloring.kempeSwitchSquareColoring C a b K01 K23 1) ∧
      G.lineGraph.KempeStep
        (Coloring.kempeSwitchSquareColoring C a b K01 K23 0)
        (Coloring.kempeSwitchSquareColoring C a b K01 K23 2) ∧
      G.lineGraph.KempeStep
        (Coloring.kempeSwitchSquareColoring C a b K01 K23 1)
        (Coloring.kempeSwitchSquareColoring C a b K01 K23 3) ∧
      G.lineGraph.KempeStep
        (Coloring.kempeSwitchSquareColoring C a b K01 K23 2)
        (Coloring.kempeSwitchSquareColoring C a b K01 K23 3) := by
  rcases hprofile with
    ⟨K01, K23, hne, hsupport01, hsupport23, _hexhaust⟩
  refine ⟨K01, K23, hne,
    data.kempeSwitchSquareColoring_injective_of_sameSide_supports
      C hab hselected K01 K23 hsupport01 hsupport23,
    isTaitEdgeColoring_kempeSwitchSquareColoring
      C hC hab K01 K23,
    data.colorWord_kempeSwitchSquareColoring_eq_sameSideOrbit
      C hab K01 K23 hsupport01 hsupport23,
    Coloring.kempeSwitchSquare_step_zero_one C a b K01 K23,
    Coloring.kempeSwitchSquare_step_zero_two C a b K01 K23,
    Coloring.kempeSwitchSquare_step_one_three C a b K01 K23,
    Coloring.kempeSwitchSquare_step_two_three C a b K01 K23⟩

end

end DegreeTwoBoundaryData

end GoertzelV24FourDefectBoundary

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cyclicSquareGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance cyclicSquareRetainedVertexSetFintype
    (first second : V) : Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

local instance cyclicSquareRetainedVertexSetDecidableEq
    (first second : V) : DecidableEq (retainedVertexSet first second) :=
  Subtype.instDecidableEq

/-- The cyclic adjacent-pair profile realizes a genuine, injective
four-state Kempe square on the deleted graph. -/
theorem CyclicKempeProfile.exists_sameSide_kempeSwitchSquare
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    (profile : CyclicKempeProfile graphData data) :
    ∃ K01 K23 :
        (profile.coloring.bicoloredSubgraph
          profile.firstColor profile.secondColor).ConnectedComponent,
      K01 ≠ K23 ∧
      Function.Injective
        (Coloring.kempeSwitchSquareColoring profile.coloring
          profile.firstColor profile.secondColor K01 K23) ∧
      (∀ state : Fin 4,
        IsTaitEdgeColoring
          (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
          (Coloring.kempeSwitchSquareColoring profile.coloring
            profile.firstColor profile.secondColor K01 K23 state)) ∧
      (∀ state : Fin 4,
        data.degreeTwoBoundaryData.colorWord
            (Coloring.kempeSwitchSquareColoring profile.coloring
              profile.firstColor profile.secondColor K01 K23 state) =
          GoertzelV24FourDefectBoundary.sameSideBoundaryKempeOrbit
            profile.firstColor profile.secondColor
              (data.degreeTwoBoundaryData.colorWord profile.coloring) state) ∧
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).lineGraph.KempeStep
        (Coloring.kempeSwitchSquareColoring profile.coloring
          profile.firstColor profile.secondColor K01 K23 0)
        (Coloring.kempeSwitchSquareColoring profile.coloring
          profile.firstColor profile.secondColor K01 K23 1) ∧
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).lineGraph.KempeStep
        (Coloring.kempeSwitchSquareColoring profile.coloring
          profile.firstColor profile.secondColor K01 K23 0)
        (Coloring.kempeSwitchSquareColoring profile.coloring
          profile.firstColor profile.secondColor K01 K23 2) ∧
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).lineGraph.KempeStep
        (Coloring.kempeSwitchSquareColoring profile.coloring
          profile.firstColor profile.secondColor K01 K23 1)
        (Coloring.kempeSwitchSquareColoring profile.coloring
          profile.firstColor profile.secondColor K01 K23 3) ∧
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).lineGraph.KempeStep
        (Coloring.kempeSwitchSquareColoring profile.coloring
          profile.firstColor profile.secondColor K01 K23 2)
        (Coloring.kempeSwitchSquareColoring profile.coloring
          profile.firstColor profile.secondColor K01 K23 3) :=
  data.degreeTwoBoundaryData.exists_sameSide_kempeSwitchSquare
    profile.coloring profile.isTaitColoring profile.validPair
      profile.allRequestsSelected profile.hasTwoSameSideKempeCutProfile

end

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
