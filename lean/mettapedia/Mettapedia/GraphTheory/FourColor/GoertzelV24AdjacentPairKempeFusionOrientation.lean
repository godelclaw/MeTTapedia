import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionParity

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The selected common primal vertex of two adjacent line-graph
vertices. -/
noncomputable def lineGraphCommonVertex {first second : G.edgeSet}
    (hadj : G.lineGraph.Adj first second) : V :=
  Classical.choose ((lineGraph_adj_iff_exists).1 hadj).2

theorem lineGraphCommonVertex_mem_left {first second : G.edgeSet}
    (hadj : G.lineGraph.Adj first second) :
    lineGraphCommonVertex hadj ∈ (first.1 : Sym2 V) :=
  (Classical.choose_spec ((lineGraph_adj_iff_exists).1 hadj).2).1

theorem lineGraphCommonVertex_mem_right {first second : G.edgeSet}
    (hadj : G.lineGraph.Adj first second) :
    lineGraphCommonVertex hadj ∈ (second.1 : Sym2 V) :=
  (Classical.choose_spec ((lineGraph_adj_iff_exists).1 hadj).2).2

/-- Distinct simple graph edges have at most one common endpoint. -/
theorem lineGraphCommonVertex_unique {first second : G.edgeSet}
    (hadj : G.lineGraph.Adj first second) {vertex : V}
    (hfirst : vertex ∈ (first.1 : Sym2 V))
    (hsecond : vertex ∈ (second.1 : Sym2 V)) :
    vertex = lineGraphCommonVertex hadj := by
  have hne := ((lineGraph_adj_iff_exists).1 hadj).1
  by_contra hvertex
  apply hne
  apply Subtype.ext
  exact Sym2.eq_of_ne_mem hvertex hfirst
    (lineGraphCommonVertex_mem_left hadj) hsecond
    (lineGraphCommonVertex_mem_right hadj)

end SimpleGraph

namespace Sym2

variable {X : Type*}

/-- Two ordered pairs of distinct members of the same unordered pair
agree either directly or after reversal. -/
theorem ordered_pair_eq_or_swap_of_mem {x y x' y' : X} {pair : Sym2 X}
    (hxy : x ≠ y) (hx : x ∈ pair) (hy : y ∈ pair)
    (hxy' : x' ≠ y') (hx' : x' ∈ pair) (hy' : y' ∈ pair) :
    (x' = x ∧ y' = y) ∨ (x' = y ∧ y' = x) := by
  have hpair : pair = s(x, y) := (mem_and_mem_iff hxy).1 ⟨hx, hy⟩
  rw [hpair] at hx' hy'
  simp only [mem_iff] at hx' hy'
  rcases hx' with hxx | hxy <;> rcases hy' with hyx | hyy
  · exact False.elim (hxy' (hxx.trans hyx.symm))
  · exact Or.inl ⟨hxx, hyy⟩
  · exact Or.inr ⟨hxy, hyx⟩
  · exact False.elim (hxy' (hxy.trans hyy.symm))

end Sym2

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance fusionOrientationGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The route vertex immediately before a fusion site on the `(a,b)`
path. -/
def EvenKempeFusionLens.bPreviousVertex {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) : C.bicoloredSet a b :=
  lens.bRoute.path.getVert (lens.bFusionPathIndex site - 1)

/-- The route vertex immediately after a fusion site on the `(a,b)`
path. -/
def EvenKempeFusionLens.bNextVertex {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) : C.bicoloredSet a b :=
  lens.bRoute.path.getVert (lens.bFusionPathIndex site + 1)

/-- The route vertex immediately before a fusion site on the `(a,c)`
path. -/
def EvenKempeFusionLens.cPreviousVertex {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) : C.bicoloredSet a c :=
  lens.cRoute.path.getVert (lens.cFusionPathIndex site - 1)

/-- The route vertex immediately after a fusion site on the `(a,c)`
path. -/
def EvenKempeFusionLens.cNextVertex {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) : C.bicoloredSet a c :=
  lens.cRoute.path.getVert (lens.cFusionPathIndex site + 1)

@[simp] theorem EvenKempeFusionLens.bRoute_getVert_fusionPathIndex
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    lens.bRoute.path.getVert (lens.bFusionPathIndex site) =
      lens.bFusionVertex site := by
  simpa only [EvenKempeFusionLens.bFusionPathIndex] using
    lens.bRoute.path.getVert_length_takeUntil
      (lens.bFusionVertex_mem_path_support site)

@[simp] theorem EvenKempeFusionLens.cRoute_getVert_fusionPathIndex
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    lens.cRoute.path.getVert (lens.cFusionPathIndex site) =
      lens.cFusionVertex site := by
  simpa only [EvenKempeFusionLens.cFusionPathIndex] using
    lens.cRoute.path.getVert_length_takeUntil
      (lens.cFusionVertex_mem_path_support site)

theorem EvenKempeFusionLens.bPreviousVertex_adj_fusionVertex
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    (C.bicoloredSubgraph a b).Adj
      (lens.bPreviousVertex site) (lens.bFusionVertex site) := by
  have hbounds := lens.bFusionPathIndex_bounds hab site
  have hadj := lens.bRoute.path.adj_getVert_succ
    (i := lens.bFusionPathIndex site - 1) (by omega)
  have hstep : lens.bFusionPathIndex site - 1 + 1 =
      lens.bFusionPathIndex site := by omega
  simpa only [EvenKempeFusionLens.bPreviousVertex, hstep,
    lens.bRoute_getVert_fusionPathIndex site] using hadj

theorem EvenKempeFusionLens.bFusionVertex_adj_nextVertex
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    (C.bicoloredSubgraph a b).Adj
      (lens.bFusionVertex site) (lens.bNextVertex site) := by
  have hbounds := lens.bFusionPathIndex_bounds hab site
  simpa only [EvenKempeFusionLens.bNextVertex,
    lens.bRoute_getVert_fusionPathIndex site] using
      lens.bRoute.path.adj_getVert_succ hbounds.2

theorem EvenKempeFusionLens.cPreviousVertex_adj_fusionVertex
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    (C.bicoloredSubgraph a c).Adj
      (lens.cPreviousVertex site) (lens.cFusionVertex site) := by
  have hbounds := lens.cFusionPathIndex_bounds hac site
  have hadj := lens.cRoute.path.adj_getVert_succ
    (i := lens.cFusionPathIndex site - 1) (by omega)
  have hstep : lens.cFusionPathIndex site - 1 + 1 =
      lens.cFusionPathIndex site := by omega
  simpa only [EvenKempeFusionLens.cPreviousVertex, hstep,
    lens.cRoute_getVert_fusionPathIndex site] using hadj

theorem EvenKempeFusionLens.cFusionVertex_adj_nextVertex
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    (C.bicoloredSubgraph a c).Adj
      (lens.cFusionVertex site) (lens.cNextVertex site) := by
  have hbounds := lens.cFusionPathIndex_bounds hac site
  simpa only [EvenKempeFusionLens.cNextVertex,
    lens.cRoute_getVert_fusionPathIndex site] using
      lens.cRoute.path.adj_getVert_succ hbounds.2

theorem EvenKempeFusionLens.bPreviousEdge_adj_fusionEdge
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    G.lineGraph.Adj (lens.bPreviousVertex site).1 site.1 :=
  lens.bPreviousVertex_adj_fusionVertex hab site

theorem EvenKempeFusionLens.bFusionEdge_adj_nextEdge
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    G.lineGraph.Adj site.1 (lens.bNextVertex site).1 :=
  lens.bFusionVertex_adj_nextVertex hab site

theorem EvenKempeFusionLens.cPreviousEdge_adj_fusionEdge
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    G.lineGraph.Adj (lens.cPreviousVertex site).1 site.1 :=
  lens.cPreviousVertex_adj_fusionVertex hac site

theorem EvenKempeFusionLens.cFusionEdge_adj_nextEdge
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    G.lineGraph.Adj site.1 (lens.cNextVertex site).1 :=
  lens.cFusionVertex_adj_nextVertex hac site

theorem EvenKempeFusionLens.bPreviousColor {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    C (lens.bPreviousVertex site).1 = b := by
  have hsite : C site.1 = a :=
    lens.color_eq_of_mem_bFusionSites site.2
  have hne := C.valid (lens.bPreviousEdge_adj_fusionEdge hab site)
  rcases (lens.bPreviousVertex site).2 with hcolor | hcolor
  · exact False.elim (hne (hcolor.trans hsite.symm))
  · exact hcolor

theorem EvenKempeFusionLens.bNextColor {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    C (lens.bNextVertex site).1 = b := by
  have hsite : C site.1 = a :=
    lens.color_eq_of_mem_bFusionSites site.2
  have hne := C.valid (lens.bFusionEdge_adj_nextEdge hab site)
  rcases (lens.bNextVertex site).2 with hcolor | hcolor
  · exact False.elim (hne (hsite.trans hcolor.symm))
  · exact hcolor

theorem EvenKempeFusionLens.cPreviousColor {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    C (lens.cPreviousVertex site).1 = c := by
  have hsite : C site.1 = a :=
    lens.color_eq_of_mem_bFusionSites site.2
  have hne := C.valid (lens.cPreviousEdge_adj_fusionEdge hac site)
  rcases (lens.cPreviousVertex site).2 with hcolor | hcolor
  · exact False.elim (hne (hcolor.trans hsite.symm))
  · exact hcolor

theorem EvenKempeFusionLens.cNextColor {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    C (lens.cNextVertex site).1 = c := by
  have hsite : C site.1 = a :=
    lens.color_eq_of_mem_bFusionSites site.2
  have hne := C.valid (lens.cFusionEdge_adj_nextEdge hac site)
  rcases (lens.cNextVertex site).2 with hcolor | hcolor
  · exact False.elim (hne (hsite.trans hcolor.symm))
  · exact hcolor

theorem EvenKempeFusionLens.bPreviousVertex_ne_bNextVertex
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    lens.bPreviousVertex site ≠ lens.bNextVertex site := by
  intro heq
  have hbounds := lens.bFusionPathIndex_bounds hab site
  change lens.bRoute.path.getVert (lens.bFusionPathIndex site - 1) =
    lens.bRoute.path.getVert (lens.bFusionPathIndex site + 1) at heq
  have hindices := lens.bRoute.isPath.getVert_injOn
    (by simp only [Set.mem_setOf_eq]; omega)
    (by simp only [Set.mem_setOf_eq]; omega) heq
  omega

theorem EvenKempeFusionLens.cPreviousVertex_ne_cNextVertex
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    lens.cPreviousVertex site ≠ lens.cNextVertex site := by
  intro heq
  have hbounds := lens.cFusionPathIndex_bounds hac site
  change lens.cRoute.path.getVert (lens.cFusionPathIndex site - 1) =
    lens.cRoute.path.getVert (lens.cFusionPathIndex site + 1) at heq
  have hindices := lens.cRoute.isPath.getVert_injOn
    (by simp only [Set.mem_setOf_eq]; omega)
    (by simp only [Set.mem_setOf_eq]; omega) heq
  omega

theorem EvenKempeFusionLens.bPreviousEdge_ne_bNextEdge
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    (lens.bPreviousVertex site).1 ≠ (lens.bNextVertex site).1 := by
  intro heq
  exact lens.bPreviousVertex_ne_bNextVertex hab site (Subtype.ext heq)

theorem EvenKempeFusionLens.cPreviousEdge_ne_cNextEdge
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cPreviousVertex site).1 ≠ (lens.cNextVertex site).1 := by
  intro heq
  exact lens.cPreviousVertex_ne_cNextVertex hac site (Subtype.ext heq)

/-- The endpoint through which the `(a,b)` route enters the shared
edge. -/
def EvenKempeFusionLens.bEntryVertex {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) : V :=
  SimpleGraph.lineGraphCommonVertex
    (lens.bPreviousEdge_adj_fusionEdge hab site)

/-- The endpoint through which the `(a,b)` route leaves the shared
edge. -/
def EvenKempeFusionLens.bExitVertex {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) : V :=
  SimpleGraph.lineGraphCommonVertex
    (lens.bFusionEdge_adj_nextEdge hab site)

/-- The endpoint through which the `(a,c)` route enters the shared
edge. -/
def EvenKempeFusionLens.cEntryVertex {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) : V :=
  SimpleGraph.lineGraphCommonVertex
    (lens.cPreviousEdge_adj_fusionEdge hac site)

/-- The endpoint through which the `(a,c)` route leaves the shared
edge. -/
def EvenKempeFusionLens.cExitVertex {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) : V :=
  SimpleGraph.lineGraphCommonVertex
    (lens.cFusionEdge_adj_nextEdge hac site)

theorem EvenKempeFusionLens.bEntryVertex_mem_previousEdge
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    lens.bEntryVertex hab site ∈
      ((lens.bPreviousVertex site).1.1 : Sym2 V) :=
  SimpleGraph.lineGraphCommonVertex_mem_left
    (lens.bPreviousEdge_adj_fusionEdge hab site)

theorem EvenKempeFusionLens.bEntryVertex_mem_fusionEdge
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    lens.bEntryVertex hab site ∈ (site.1.1 : Sym2 V) :=
  SimpleGraph.lineGraphCommonVertex_mem_right
    (lens.bPreviousEdge_adj_fusionEdge hab site)

theorem EvenKempeFusionLens.bExitVertex_mem_fusionEdge
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    lens.bExitVertex hab site ∈ (site.1.1 : Sym2 V) :=
  SimpleGraph.lineGraphCommonVertex_mem_left
    (lens.bFusionEdge_adj_nextEdge hab site)

theorem EvenKempeFusionLens.bExitVertex_mem_nextEdge
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    lens.bExitVertex hab site ∈
      ((lens.bNextVertex site).1.1 : Sym2 V) :=
  SimpleGraph.lineGraphCommonVertex_mem_right
    (lens.bFusionEdge_adj_nextEdge hab site)

theorem EvenKempeFusionLens.cEntryVertex_mem_previousEdge
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    lens.cEntryVertex hac site ∈
      ((lens.cPreviousVertex site).1.1 : Sym2 V) :=
  SimpleGraph.lineGraphCommonVertex_mem_left
    (lens.cPreviousEdge_adj_fusionEdge hac site)

theorem EvenKempeFusionLens.cEntryVertex_mem_fusionEdge
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    lens.cEntryVertex hac site ∈ (site.1.1 : Sym2 V) :=
  SimpleGraph.lineGraphCommonVertex_mem_right
    (lens.cPreviousEdge_adj_fusionEdge hac site)

theorem EvenKempeFusionLens.cExitVertex_mem_fusionEdge
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    lens.cExitVertex hac site ∈ (site.1.1 : Sym2 V) :=
  SimpleGraph.lineGraphCommonVertex_mem_left
    (lens.cFusionEdge_adj_nextEdge hac site)

theorem EvenKempeFusionLens.cExitVertex_mem_nextEdge
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    lens.cExitVertex hac site ∈
      ((lens.cNextVertex site).1.1 : Sym2 V) :=
  SimpleGraph.lineGraphCommonVertex_mem_right
    (lens.cFusionEdge_adj_nextEdge hac site)

/-- A properly edge-colored route enters and leaves the shared edge at
opposite endpoints. -/
theorem EvenKempeFusionLens.bEntryVertex_ne_bExitVertex
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    lens.bEntryVertex hab site ≠ lens.bExitVertex hab site := by
  intro hvertices
  have hnext : lens.bEntryVertex hab site ∈
      ((lens.bNextVertex site).1.1 : Sym2 V) := by
    rw [hvertices]
    exact lens.bExitVertex_mem_nextEdge hab site
  have hadj : G.lineGraph.Adj (lens.bPreviousVertex site).1
      (lens.bNextVertex site).1 :=
    lineGraph_adj_of_common_vertex_of_ne
      (lens.bEntryVertex_mem_previousEdge hab site) hnext
      (lens.bPreviousEdge_ne_bNextEdge hab site)
  exact (C.valid hadj) ((lens.bPreviousColor hab site).trans
    (lens.bNextColor hab site).symm)

theorem EvenKempeFusionLens.cEntryVertex_ne_cExitVertex
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    lens.cEntryVertex hac site ≠ lens.cExitVertex hac site := by
  intro hvertices
  have hnext : lens.cEntryVertex hac site ∈
      ((lens.cNextVertex site).1.1 : Sym2 V) := by
    rw [hvertices]
    exact lens.cExitVertex_mem_nextEdge hac site
  have hadj : G.lineGraph.Adj (lens.cPreviousVertex site).1
      (lens.cNextVertex site).1 :=
    lineGraph_adj_of_common_vertex_of_ne
      (lens.cEntryVertex_mem_previousEdge hac site) hnext
      (lens.cPreviousEdge_ne_cNextEdge hac site)
  exact (C.valid hadj) ((lens.cPreviousColor hac site).trans
    (lens.cNextColor hac site).symm)

theorem EvenKempeFusionLens.fusionEdge_eq_bEntry_bExit
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    site.1.1 = s(lens.bEntryVertex hab site,
      lens.bExitVertex hab site) := by
  exact (Sym2.mem_and_mem_iff
    (lens.bEntryVertex_ne_bExitVertex hab site)).1
      ⟨lens.bEntryVertex_mem_fusionEdge hab site,
        lens.bExitVertex_mem_fusionEdge hab site⟩

theorem EvenKempeFusionLens.fusionEdge_eq_cEntry_cExit
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    site.1.1 = s(lens.cEntryVertex hac site,
      lens.cExitVertex hac site) := by
  exact (Sym2.mem_and_mem_iff
    (lens.cEntryVertex_ne_cExitVertex hac site)).1
      ⟨lens.cEntryVertex_mem_fusionEdge hac site,
        lens.cExitVertex_mem_fusionEdge hac site⟩

/-- At a fusion edge, the two route traversals either agree on entry and
exit or are exact reversals. -/
theorem EvenKempeFusionLens.fusionEndpointPairing
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cEntryVertex hac site = lens.bEntryVertex hab site ∧
        lens.cExitVertex hac site = lens.bExitVertex hab site) ∨
      (lens.cEntryVertex hac site = lens.bExitVertex hab site ∧
        lens.cExitVertex hac site = lens.bEntryVertex hab site) := by
  exact Sym2.ordered_pair_eq_or_swap_of_mem
    (lens.bEntryVertex_ne_bExitVertex hab site)
    (lens.bEntryVertex_mem_fusionEdge hab site)
    (lens.bExitVertex_mem_fusionEdge hab site)
    (lens.cEntryVertex_ne_cExitVertex hac site)
    (lens.cEntryVertex_mem_fusionEdge hac site)
    (lens.cExitVertex_mem_fusionEdge hac site)

/-- Agreement of the entry endpoints is equivalent to agreement of the
exit endpoints. -/
theorem EvenKempeFusionLens.cEntry_eq_bEntry_iff_cExit_eq_bExit
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    lens.cEntryVertex hac site = lens.bEntryVertex hab site ↔
      lens.cExitVertex hac site = lens.bExitVertex hab site := by
  rcases lens.fusionEndpointPairing hab hac site with hsame | hswap
  · exact ⟨fun _ ↦ hsame.2, fun _ ↦ hsame.1⟩
  · constructor
    · intro hentry
      exact False.elim ((lens.bEntryVertex_ne_bExitVertex hab site)
        (hentry.symm.trans hswap.1))
    · intro hexit
      exact False.elim ((lens.bEntryVertex_ne_bExitVertex hab site)
        (hswap.2.symm.trans hexit))

/-- The local chirality proposition records whether the two alternating
routes traverse the shared edge in the same direction. -/
def EvenKempeFusionLens.FusionEntryAligned {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) : Prop :=
  lens.cEntryVertex hac site = lens.bEntryVertex hab site

/-- A Boolean local chirality observable at a fusion site. -/
def EvenKempeFusionLens.fusionChirality {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) : Bool :=
  decide (lens.cEntryVertex hac site = lens.bEntryVertex hab site)

@[simp] theorem EvenKempeFusionLens.fusionChirality_eq_true_iff
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    lens.fusionChirality hab hac site = true ↔
      lens.FusionEntryAligned hab hac site := by
  simp [EvenKempeFusionLens.fusionChirality,
    EvenKempeFusionLens.FusionEntryAligned]

@[simp] theorem EvenKempeFusionLens.fusionChirality_eq_false_iff
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    lens.fusionChirality hab hac site = false ↔
      ¬ lens.FusionEntryAligned hab hac site := by
  simp [EvenKempeFusionLens.fusionChirality,
    EvenKempeFusionLens.FusionEntryAligned]

theorem EvenKempeFusionLens.fusionChirality_eq_true_iff_endpoints_agree
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    lens.fusionChirality hab hac site = true ↔
      lens.cEntryVertex hac site = lens.bEntryVertex hab site ∧
      lens.cExitVertex hac site = lens.bExitVertex hab site := by
  rw [lens.fusionChirality_eq_true_iff]
  constructor
  · intro hentry
    exact ⟨hentry,
      (lens.cEntry_eq_bEntry_iff_cExit_eq_bExit hab hac site).1 hentry⟩
  · exact fun hagree ↦ hagree.1

theorem EvenKempeFusionLens.fusionChirality_eq_false_iff_endpoints_reverse
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    lens.fusionChirality hab hac site = false ↔
      lens.cEntryVertex hac site = lens.bExitVertex hab site ∧
      lens.cExitVertex hac site = lens.bEntryVertex hab site := by
  rw [lens.fusionChirality_eq_false_iff]
  constructor
  · intro hnotAligned
    rcases lens.fusionEndpointPairing hab hac site with hsame | hreverse
    · exact False.elim (hnotAligned hsame.1)
    · exact hreverse
  · intro hreverse hentry
    apply lens.cEntryVertex_ne_cExitVertex hac site
    exact hentry.trans hreverse.2.symm

end


end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
