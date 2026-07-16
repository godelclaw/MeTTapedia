import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionDarts
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairCyclicOrder

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Orient a graph edge away from a specified endpoint. -/
noncomputable def edgeDartAt (edge : G.edgeSet) {vertex : V}
    (hvertex : vertex ∈ (edge.1 : Sym2 V)) : G.Dart :=
  ⟨(vertex, Sym2.Mem.other hvertex), by
    rw [← SimpleGraph.mem_edgeSet, Sym2.other_spec hvertex]
    exact edge.2⟩

@[simp] theorem edgeDartAt_fst (edge : G.edgeSet) {vertex : V}
    (hvertex : vertex ∈ (edge.1 : Sym2 V)) :
    (edgeDartAt edge hvertex).fst = vertex :=
  rfl

@[simp] theorem edgeDartAt_edge (edge : G.edgeSet) {vertex : V}
    (hvertex : vertex ∈ (edge.1 : Sym2 V)) :
    (edgeDartAt edge hvertex).edge = edge.1 :=
  Sym2.other_spec hvertex

end SimpleGraph

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FaceDualConnectedness
open GoertzelV24InducedHexCorridorTypes

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- Three pairwise distinct darts based at one cubic vertex exhaust its
dart fiber, so the next cyclic turn from the first is one of the other
two. -/
theorem rho_eq_second_or_third_of_cubic
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    {first second third : RS.D}
    (hsecondBase : RS.vertOf second = RS.vertOf first)
    (hthirdBase : RS.vertOf third = RS.vertOf first)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    RS.rho first = second ∨ RS.rho first = third := by
  let vertex := RS.vertOf first
  have hfirstMem : first ∈ RS.dartsAt vertex := by
    simp [RotationSystem.dartsAt, vertex]
  have hsecondMem : second ∈ RS.dartsAt vertex := by
    simp [RotationSystem.dartsAt, vertex, hsecondBase]
  have hthirdMem : third ∈ RS.dartsAt vertex := by
    simp [RotationSystem.dartsAt, vertex, hthirdBase]
  have htripleSubset : ({first, second, third} : Finset RS.D) ⊆
      RS.dartsAt vertex := by
    intro dart hdart
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdart
    rcases hdart with rfl | rfl | rfl
    · exact hfirstMem
    · exact hsecondMem
    · exact hthirdMem
  have htripleCard : ({first, second, third} : Finset RS.D).card = 3 := by
    simp [hfirstSecond, hfirstThird, hsecondThird]
  have htripleEq : ({first, second, third} : Finset RS.D) =
      RS.dartsAt vertex := by
    apply Finset.eq_of_subset_of_card_le htripleSubset
    rw [hcubic vertex, htripleCard]
  have hrhoMem : RS.rho first ∈ RS.dartsAt vertex := by
    simp [RotationSystem.dartsAt, vertex, RS.vert_rho]
  rw [← htripleEq] at hrhoMem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hrhoMem
  rcases hrhoMem with hfixed | hsecond | hthird
  · have hnontrivialFinset : (RS.dartsAt vertex).Nontrivial := by
      apply Finset.one_lt_card_iff_nontrivial.mp
      rw [hcubic vertex]
      omega
    have hnontrivial : (RS.dartsAt vertex : Set RS.D).Nontrivial := by
      simpa only [Finset.coe_sort_coe] using hnontrivialFinset
    exact False.elim
      ((rho_isCycleOn_dartsAt RS hrotation vertex).apply_ne
        hnontrivial hfirstMem hfixed)
  · exact Or.inl hsecond
  · exact Or.inr hthird

end RotationSystem

/-- Darts supported on edges with distinct colors are distinct. -/
theorem dart_ne_of_edge_colors_ne
    {V α : Type*} {G : SimpleGraph V}
    (C : G.EdgeColoring α)
    {firstEdge secondEdge : G.edgeSet}
    {firstDart secondDart : G.Dart}
    (hfirst : firstDart.edge = firstEdge.1)
    (hsecond : secondDart.edge = secondEdge.1)
    (hcolors : C firstEdge ≠ C secondEdge) :
    firstDart ≠ secondDart := by
  intro hdarts
  apply hcolors
  apply congrArg C
  apply Subtype.ext
  exact hfirst.symm.trans
    ((congrArg SimpleGraph.Dart.edge hdarts).trans hsecond)

open GoertzelV24FourDefectBoundary

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance fusionTurnGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The `(a,b)` neighbor dart based at the entry endpoint of a fusion
edge. -/
def EvenKempeFusionLens.bEntryNeighborDart {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) : G.Dart :=
  SimpleGraph.edgeDartAt (lens.bPreviousVertex site).1
    (lens.bEntryVertex_mem_previousEdge hab site)

/-- The `(a,b)` neighbor dart based at the exit endpoint of a fusion
edge. -/
def EvenKempeFusionLens.bExitNeighborDart {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) : G.Dart :=
  SimpleGraph.edgeDartAt (lens.bNextVertex site).1
    (lens.bExitVertex_mem_nextEdge hab site)

@[simp] theorem EvenKempeFusionLens.bEntryNeighborDart_fst
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    (lens.bEntryNeighborDart hab site).fst =
      lens.bEntryVertex hab site :=
  rfl

@[simp] theorem EvenKempeFusionLens.bExitNeighborDart_fst
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    (lens.bExitNeighborDart hab site).fst =
      lens.bExitVertex hab site :=
  rfl

@[simp] theorem EvenKempeFusionLens.bEntryNeighborDart_edge
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    (lens.bEntryNeighborDart hab site).edge =
      (lens.bPreviousVertex site).1.1 :=
  SimpleGraph.edgeDartAt_edge _ _

@[simp] theorem EvenKempeFusionLens.bExitNeighborDart_edge
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    (lens.bExitNeighborDart hab site).edge =
      (lens.bNextVertex site).1.1 :=
  SimpleGraph.edgeDartAt_edge _ _

/-- The `c`-colored edge incident at the `(a,b)` entry endpoint. Which
side of the `(a,c)` route supplies it is determined by local chirality. -/
def EvenKempeFusionLens.cEdgeAtBEntry {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    G.edgeSet :=
  if lens.fusionChirality hab hac site = true then
    (lens.cPreviousVertex site).1
  else
    (lens.cNextVertex site).1

/-- The `c`-colored edge incident at the `(a,b)` exit endpoint. -/
def EvenKempeFusionLens.cEdgeAtBExit {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    G.edgeSet :=
  if lens.fusionChirality hab hac site = true then
    (lens.cNextVertex site).1
  else
    (lens.cPreviousVertex site).1

theorem EvenKempeFusionLens.bEntryVertex_mem_cEdgeAtBEntry
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    lens.bEntryVertex hab site ∈
      ((lens.cEdgeAtBEntry hab hac site).1 : Sym2 V) := by
  by_cases hchirality : lens.fusionChirality hab hac site = true
  · rw [EvenKempeFusionLens.cEdgeAtBEntry, if_pos hchirality,
      ← (lens.fusionChirality_eq_true_iff_endpoints_agree
        hab hac site).1 hchirality |>.1]
    exact lens.cEntryVertex_mem_previousEdge hac site
  · have hfalse : lens.fusionChirality hab hac site = false :=
      Bool.eq_false_of_not_eq_true hchirality
    rw [EvenKempeFusionLens.cEdgeAtBEntry, if_neg hchirality,
      ← (lens.fusionChirality_eq_false_iff_endpoints_reverse
        hab hac site).1 hfalse |>.2]
    exact lens.cExitVertex_mem_nextEdge hac site

theorem EvenKempeFusionLens.bExitVertex_mem_cEdgeAtBExit
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    lens.bExitVertex hab site ∈
      ((lens.cEdgeAtBExit hab hac site).1 : Sym2 V) := by
  by_cases hchirality : lens.fusionChirality hab hac site = true
  · rw [EvenKempeFusionLens.cEdgeAtBExit, if_pos hchirality,
      ← (lens.fusionChirality_eq_true_iff_endpoints_agree
        hab hac site).1 hchirality |>.2]
    exact lens.cExitVertex_mem_nextEdge hac site
  · have hfalse : lens.fusionChirality hab hac site = false :=
      Bool.eq_false_of_not_eq_true hchirality
    rw [EvenKempeFusionLens.cEdgeAtBExit, if_neg hchirality,
      ← (lens.fusionChirality_eq_false_iff_endpoints_reverse
        hab hac site).1 hfalse |>.1]
    exact lens.cEntryVertex_mem_previousEdge hac site

/-- The `c`-colored companion dart based at the `(a,b)` entry endpoint. -/
def EvenKempeFusionLens.cDartAtBEntry {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) : G.Dart :=
  SimpleGraph.edgeDartAt (lens.cEdgeAtBEntry hab hac site)
    (lens.bEntryVertex_mem_cEdgeAtBEntry hab hac site)

/-- The `c`-colored companion dart based at the `(a,b)` exit endpoint. -/
def EvenKempeFusionLens.cDartAtBExit {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) : G.Dart :=
  SimpleGraph.edgeDartAt (lens.cEdgeAtBExit hab hac site)
    (lens.bExitVertex_mem_cEdgeAtBExit hab hac site)

@[simp] theorem EvenKempeFusionLens.cDartAtBEntry_fst
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cDartAtBEntry hab hac site).fst =
      lens.bEntryVertex hab site :=
  rfl

@[simp] theorem EvenKempeFusionLens.cDartAtBExit_fst
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cDartAtBExit hab hac site).fst =
      lens.bExitVertex hab site :=
  rfl

@[simp] theorem EvenKempeFusionLens.cDartAtBEntry_edge
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cDartAtBEntry hab hac site).edge =
      (lens.cEdgeAtBEntry hab hac site).1 :=
  SimpleGraph.edgeDartAt_edge _ _

@[simp] theorem EvenKempeFusionLens.cDartAtBExit_edge
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cDartAtBExit hab hac site).edge =
      (lens.cEdgeAtBExit hab hac site).1 :=
  SimpleGraph.edgeDartAt_edge _ _

theorem EvenKempeFusionLens.cEdgeAtBEntry_color
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    C (lens.cEdgeAtBEntry hab hac site) = c := by
  rw [EvenKempeFusionLens.cEdgeAtBEntry]
  split_ifs
  · exact lens.cPreviousColor hac site
  · exact lens.cNextColor hac site

theorem EvenKempeFusionLens.cEdgeAtBExit_color
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    C (lens.cEdgeAtBExit hab hac site) = c := by
  rw [EvenKempeFusionLens.cEdgeAtBExit]
  split_ifs
  · exact lens.cNextColor hac site
  · exact lens.cPreviousColor hac site

/-- The three entry-based route darts are pairwise distinct when the three
colors are distinct. -/
theorem EvenKempeFusionLens.entryTurnDarts_pairwise_ne
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite) :
    lens.bFusionDart hab site ≠ lens.bEntryNeighborDart hab site ∧
      lens.bFusionDart hab site ≠ lens.cDartAtBEntry hab hac site ∧
      lens.bEntryNeighborDart hab site ≠
        lens.cDartAtBEntry hab hac site := by
  have hsiteColor := lens.color_eq_of_mem_bFusionSites site.2
  constructor
  · apply dart_ne_of_edge_colors_ne C
      (lens.bFusionDart_edge hab site)
      (lens.bEntryNeighborDart_edge hab site)
    rw [hsiteColor, lens.bPreviousColor hab site]
    exact hab
  constructor
  · apply dart_ne_of_edge_colors_ne C
      (lens.bFusionDart_edge hab site)
      (lens.cDartAtBEntry_edge hab hac site)
    rw [hsiteColor, lens.cEdgeAtBEntry_color hab hac site]
    exact hac
  · apply dart_ne_of_edge_colors_ne C
      (lens.bEntryNeighborDart_edge hab site)
      (lens.cDartAtBEntry_edge hab hac site)
    rw [lens.bPreviousColor hab site,
      lens.cEdgeAtBEntry_color hab hac site]
    exact hbc

/-- The analogous exit-based route darts are pairwise distinct. -/
theorem EvenKempeFusionLens.exitTurnDarts_pairwise_ne
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite) :
    (lens.bFusionDart hab site).symm ≠
        lens.bExitNeighborDart hab site ∧
      (lens.bFusionDart hab site).symm ≠
        lens.cDartAtBExit hab hac site ∧
    lens.bExitNeighborDart hab site ≠
        lens.cDartAtBExit hab hac site := by
  have hsiteColor := lens.color_eq_of_mem_bFusionSites site.2
  have hfusionEdge : (lens.bFusionDart hab site).symm.edge = site.1.1 := by
    rw [SimpleGraph.Dart.edge_symm, lens.bFusionDart_edge hab site]
  constructor
  · apply dart_ne_of_edge_colors_ne C
      hfusionEdge
      (lens.bExitNeighborDart_edge hab site)
    rw [hsiteColor, lens.bNextColor hab site]
    exact hab
  constructor
  · apply dart_ne_of_edge_colors_ne C
      hfusionEdge
      (lens.cDartAtBExit_edge hab hac site)
    rw [hsiteColor, lens.cEdgeAtBExit_color hab hac site]
    exact hac
  · apply dart_ne_of_edge_colors_ne C
      (lens.bExitNeighborDart_edge hab site)
      (lens.cDartAtBExit_edge hab hac site)
    rw [lens.bNextColor hab site,
      lens.cEdgeAtBExit_color hab hac site]
    exact hbc

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance ambientFusionTurnGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance ambientFusionTurnRetainedVertexFintype
    (first second : V) : Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

local instance ambientFusionTurnRetainedVertexDecidableEq
    (first second : V) : DecidableEq (retainedVertexSet first second) :=
  Subtype.instDecidableEq

/-- The `b`-colored entry neighbor dart lifted to the ambient graph. -/
def ambientBEntryNeighborDart (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) : G.Dart :=
  retainedDartToAmbientDart data (lens.bEntryNeighborDart hab site)

/-- The `b`-colored exit neighbor dart lifted to the ambient graph. -/
def ambientBExitNeighborDart (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) : G.Dart :=
  retainedDartToAmbientDart data (lens.bExitNeighborDart hab site)

/-- The `c`-colored companion dart at the `b`-oriented entry endpoint. -/
def ambientCEntryCompanionDart (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) : G.Dart :=
  retainedDartToAmbientDart data (lens.cDartAtBEntry hab hac site)

/-- The `c`-colored companion dart at the `b`-oriented exit endpoint. -/
def ambientCExitCompanionDart (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) : G.Dart :=
  retainedDartToAmbientDart data (lens.cDartAtBExit hab hac site)

/-- The ambient fusion dart based at its `b`-oriented exit endpoint. -/
def ambientBExitFusionDart (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) : G.Dart :=
  retainedDartToAmbientDart data (lens.bFusionDart hab site).symm

@[simp] theorem ambientBExitFusionDart_eq_symm
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    ambientBExitFusionDart data lens hab site =
      (ambientBFusionDart data lens hab site).symm := by
  exact retainedDartToAmbientDart_symm data (lens.bFusionDart hab site)

theorem ambientEntryTurnDarts_pairwise_ne
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite) :
    ambientBFusionDart data lens hab site ≠
        ambientBEntryNeighborDart data lens hab site ∧
      ambientBFusionDart data lens hab site ≠
        ambientCEntryCompanionDart data lens hab hac site ∧
      ambientBEntryNeighborDart data lens hab site ≠
        ambientCEntryCompanionDart data lens hab hac site := by
  have hpairs := lens.entryTurnDarts_pairwise_ne hab hac hbc site
  have hinjective := retainedDartToAmbientDart_injective data
  exact ⟨fun heq ↦ hpairs.1 (hinjective heq),
    fun heq ↦ hpairs.2.1 (hinjective heq),
    fun heq ↦ hpairs.2.2 (hinjective heq)⟩

theorem ambientExitTurnDarts_pairwise_ne
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite) :
    ambientBExitFusionDart data lens hab site ≠
        ambientBExitNeighborDart data lens hab site ∧
      ambientBExitFusionDart data lens hab site ≠
        ambientCExitCompanionDart data lens hab hac site ∧
      ambientBExitNeighborDart data lens hab site ≠
        ambientCExitCompanionDart data lens hab hac site := by
  have hpairs := lens.exitTurnDarts_pairwise_ne hab hac hbc site
  have hinjective := retainedDartToAmbientDart_injective data
  exact ⟨fun heq ↦ hpairs.1 (hinjective heq),
    fun heq ↦ hpairs.2.1 (hinjective heq),
    fun heq ↦ hpairs.2.2 (hinjective heq)⟩

/-- At the entry endpoint, the ambient cyclic rotation sends the fusion
dart to exactly one of its `b`- and `c`-colored neighbor darts. -/
theorem rho_ambientBFusionDart_eq_entryNeighbor_or_companion
    (graphData : SimpleGraphDartRotation.Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite) :
    graphData.toRotationSystem.rho
        (ambientBFusionDart data lens hab site) =
        ambientBEntryNeighborDart data lens hab site ∨
      graphData.toRotationSystem.rho
        (ambientBFusionDart data lens hab site) =
        ambientCEntryCompanionDart data lens hab hac site := by
  have hpairs := ambientEntryTurnDarts_pairwise_ne
    data lens hab hac hbc site
  apply RotationSystem.rho_eq_second_or_third_of_cubic
    graphData.toRotationSystem hcubic hrotation
  · rfl
  · rfl
  · exact hpairs.1
  · exact hpairs.2.1
  · exact hpairs.2.2

/-- The same exhaustive two-turn law holds at the exit endpoint. -/
theorem rho_ambientBExitFusionDart_eq_exitNeighbor_or_companion
    (graphData : SimpleGraphDartRotation.Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite) :
    graphData.toRotationSystem.rho
        (ambientBExitFusionDart data lens hab site) =
        ambientBExitNeighborDart data lens hab site ∨
      graphData.toRotationSystem.rho
        (ambientBExitFusionDart data lens hab site) =
        ambientCExitCompanionDart data lens hab hac site := by
  have hpairs := ambientExitTurnDarts_pairwise_ne
    data lens hab hac hbc site
  apply RotationSystem.rho_eq_second_or_third_of_cubic
    graphData.toRotationSystem hcubic hrotation
  · rfl
  · rfl
  · exact hpairs.1
  · exact hpairs.2.1
  · exact hpairs.2.2

/-- Boolean encoding of the entry-end cyclic turn: `true` selects the
`b`-neighbor and `false` selects the `c`-companion. -/
def fusionEntryTurn (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) : Bool :=
  decide (graphData.toRotationSystem.rho
    (ambientBFusionDart data lens hab site) =
      ambientBEntryNeighborDart data lens hab site)

/-- Boolean encoding of the exit-end cyclic turn. -/
def fusionExitTurn (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) : Bool :=
  decide (graphData.toRotationSystem.rho
    (ambientBExitFusionDart data lens hab site) =
      ambientBExitNeighborDart data lens hab site)

@[simp] theorem fusionEntryTurn_eq_true_iff
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    fusionEntryTurn graphData data lens hab site = true ↔
      graphData.toRotationSystem.rho
        (ambientBFusionDart data lens hab site) =
        ambientBEntryNeighborDart data lens hab site := by
  simp [fusionEntryTurn]

@[simp] theorem fusionExitTurn_eq_true_iff
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    fusionExitTurn graphData data lens hab site = true ↔
      graphData.toRotationSystem.rho
        (ambientBExitFusionDart data lens hab site) =
        ambientBExitNeighborDart data lens hab site := by
  simp [fusionExitTurn]

theorem fusionEntryTurn_eq_false_iff_companion
    (graphData : SimpleGraphDartRotation.Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite) :
    fusionEntryTurn graphData data lens hab site = false ↔
      graphData.toRotationSystem.rho
        (ambientBFusionDart data lens hab site) =
        ambientCEntryCompanionDart data lens hab hac site := by
  have hdichotomy := rho_ambientBFusionDart_eq_entryNeighbor_or_companion
    graphData hcubic hrotation data lens hab hac hbc site
  have hneighbors := (ambientEntryTurnDarts_pairwise_ne
    data lens hab hac hbc site).2.2
  rw [Bool.eq_false_iff]
  constructor
  · intro hnotNeighbor
    rcases hdichotomy with hneighbor | hcompanion
    · exact False.elim (hnotNeighbor
        ((fusionEntryTurn_eq_true_iff graphData data lens hab site).2
          hneighbor))
    · exact hcompanion
  · intro hcompanion hturnTrue
    apply hneighbors
    exact ((fusionEntryTurn_eq_true_iff graphData data lens hab site).1
      hturnTrue).symm.trans hcompanion

theorem fusionExitTurn_eq_false_iff_companion
    (graphData : SimpleGraphDartRotation.Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens.FusionSite) :
    fusionExitTurn graphData data lens hab site = false ↔
      graphData.toRotationSystem.rho
        (ambientBExitFusionDart data lens hab site) =
        ambientCExitCompanionDart data lens hab hac site := by
  have hdichotomy := rho_ambientBExitFusionDart_eq_exitNeighbor_or_companion
    graphData hcubic hrotation data lens hab hac hbc site
  have hneighbors := (ambientExitTurnDarts_pairwise_ne
    data lens hab hac hbc site).2.2
  rw [Bool.eq_false_iff]
  constructor
  · intro hnotNeighbor
    rcases hdichotomy with hneighbor | hcompanion
    · exact False.elim (hnotNeighbor
        ((fusionExitTurn_eq_true_iff graphData data lens hab site).2
          hneighbor))
    · exact hcompanion
  · intro hcompanion hturnTrue
    apply hneighbors
    exact ((fusionExitTurn_eq_true_iff graphData data lens hab site).1
      hturnTrue).symm.trans hcompanion

/-- The two endpoint turns form the local rotation transition symbol of a
fusion site. -/
def fusionTurnSymbol (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    Bool × Bool :=
  (fusionEntryTurn graphData data lens hab site,
    fusionExitTurn graphData data lens hab site)

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
