import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionSites

namespace SimpleGraph.Coloring

variable {V α : Type*} {G : SimpleGraph V} [DecidableEq α]

/-- A walk in a bicolored subgraph whose endpoint graph colors differ has
odd length. -/
theorem bicoloredWalk_odd_length_of_endpoint_colors_ne
    (C : G.Coloring α) (a b : α) (hab : a ≠ b)
    {left right : C.bicoloredSet a b}
    (path : (C.bicoloredSubgraph a b).Walk left right)
    (hcolor : C left.1 ≠ C right.1) :
    Odd path.length := by
  apply ((bicoloredBoolColoring C a b hab).odd_length_iff_not_congr path).2
  rcases left.2 with hleft | hleft <;>
    rcases right.2 with hright | hright
  · exact False.elim (hcolor (hleft.trans hright.symm))
  · simp [bicoloredBoolColoring, hleft, hright, hab]
  · simp [bicoloredBoolColoring, hleft, hright, hab]
  · exact False.elim (hcolor (hleft.trans hright.symm))

end SimpleGraph.Coloring

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance fusionParityGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- A common route edge, regarded as a fusion site. -/
def EvenKempeFusionLens.FusionSite {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :=
  {edge : G.edgeSet // edge ∈ lens.bFusionSites}

/-- A fusion site as a vertex of the `(a,b)` induced line graph. -/
def EvenKempeFusionLens.bFusionVertex {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) : C.bicoloredSet a b :=
  ⟨site.1, Or.inl (lens.color_eq_of_mem_bFusionSites site.2)⟩

/-- A fusion site as a vertex of the `(a,c)` induced line graph. -/
def EvenKempeFusionLens.cFusionVertex {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) : C.bicoloredSet a c :=
  ⟨site.1, Or.inl (lens.color_eq_of_mem_bFusionSites site.2)⟩

theorem EvenKempeFusionLens.bFusionVertex_mem_path_support
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    lens.bFusionVertex site ∈ lens.bRoute.path.support := by
  have hambient := ((lens.mem_bFusionSites_iff site.1).1 site.2).1
  rcases (lens.bRoute.mem_ambientPath_support_iff site.1).1 hambient with
    ⟨_hcolor, hmem⟩
  simpa only [EvenKempeFusionLens.bFusionVertex] using hmem

theorem EvenKempeFusionLens.cFusionVertex_mem_path_support
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    lens.cFusionVertex site ∈ lens.cRoute.path.support := by
  have hambient := ((lens.mem_bFusionSites_iff site.1).1 site.2).2
  rcases (lens.cRoute.mem_ambientPath_support_iff site.1).1 hambient with
    ⟨_hcolor, hmem⟩
  simpa only [EvenKempeFusionLens.cFusionVertex] using hmem

/-- Position of a fusion site along the `(a,b)` route. -/
def EvenKempeFusionLens.bFusionPathIndex {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) : Nat :=
  (lens.bRoute.path.takeUntil (lens.bFusionVertex site)
    (lens.bFusionVertex_mem_path_support site)).length

/-- Position of a fusion site along the `(a,c)` route. -/
def EvenKempeFusionLens.cFusionPathIndex {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) : Nat :=
  (lens.cRoute.path.takeUntil (lens.cFusionVertex site)
    (lens.cFusionVertex_mem_path_support site)).length

/-- Number of route steps after a fusion site on the `(a,b)` route. -/
def EvenKempeFusionLens.bFusionSuffixLength {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) : Nat :=
  (lens.bRoute.path.dropUntil (lens.bFusionVertex site)
    (lens.bFusionVertex_mem_path_support site)).length

/-- Number of route steps after a fusion site on the `(a,c)` route. -/
def EvenKempeFusionLens.cFusionSuffixLength {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) : Nat :=
  (lens.cRoute.path.dropUntil (lens.cFusionVertex site)
    (lens.cFusionVertex_mem_path_support site)).length

theorem EvenKempeFusionLens.bFusionPathIndex_odd {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    Odd (lens.bFusionPathIndex site) := by
  have hmem := lens.bFusionVertex_mem_path_support site
  have hodd : Odd
      (lens.bRoute.path.takeUntil (lens.bFusionVertex site) hmem).length := by
    apply C.bicoloredWalk_odd_length_of_endpoint_colors_ne a b hab
    intro hcolors
    apply hab
    exact (lens.color_eq_of_mem_bFusionSites site.2).symm.trans
      (hcolors.symm.trans lens.bRoute.leftColor)
  simpa only [EvenKempeFusionLens.bFusionPathIndex] using hodd

theorem EvenKempeFusionLens.bFusionSuffixLength_odd {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    Odd (lens.bFusionSuffixLength site) := by
  have hmem := lens.bFusionVertex_mem_path_support site
  have hodd : Odd
      (lens.bRoute.path.dropUntil (lens.bFusionVertex site) hmem).length := by
    apply C.bicoloredWalk_odd_length_of_endpoint_colors_ne a b hab
    intro hcolors
    apply hab
    exact (lens.color_eq_of_mem_bFusionSites site.2).symm.trans
      (hcolors.trans lens.bRoute.rightColor)
  simpa only [EvenKempeFusionLens.bFusionSuffixLength] using hodd

theorem EvenKempeFusionLens.cFusionPathIndex_odd {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    Odd (lens.cFusionPathIndex site) := by
  have hmem := lens.cFusionVertex_mem_path_support site
  have hodd : Odd
      (lens.cRoute.path.takeUntil (lens.cFusionVertex site) hmem).length := by
    apply C.bicoloredWalk_odd_length_of_endpoint_colors_ne a c hac
    intro hcolors
    apply hac
    exact (lens.color_eq_of_mem_bFusionSites site.2).symm.trans
      (hcolors.symm.trans lens.cRoute.leftColor)
  simpa only [EvenKempeFusionLens.cFusionPathIndex] using hodd

theorem EvenKempeFusionLens.cFusionSuffixLength_odd {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    Odd (lens.cFusionSuffixLength site) := by
  have hmem := lens.cFusionVertex_mem_path_support site
  have hodd : Odd
      (lens.cRoute.path.dropUntil (lens.cFusionVertex site) hmem).length := by
    apply C.bicoloredWalk_odd_length_of_endpoint_colors_ne a c hac
    intro hcolors
    apply hac
    exact (lens.color_eq_of_mem_bFusionSites site.2).symm.trans
      (hcolors.trans lens.cRoute.rightColor)
  simpa only [EvenKempeFusionLens.cFusionSuffixLength] using hodd

/-- Every fusion site is strictly internal to the `(a,b)` route. -/
theorem EvenKempeFusionLens.bFusionPathIndex_bounds {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    0 < lens.bFusionPathIndex site ∧
      lens.bFusionPathIndex site < lens.bRoute.path.length := by
  rcases lens.bFusionPathIndex_odd hab site with ⟨prefixHalf, hprefix⟩
  rcases lens.bFusionSuffixLength_odd hab site with ⟨suffixHalf, hsuffix⟩
  have hmem := lens.bFusionVertex_mem_path_support site
  have hsplit := congrArg (fun walk ↦ walk.length)
    (lens.bRoute.path.take_spec hmem)
  simp only [SimpleGraph.Walk.length_append] at hsplit
  change lens.bFusionPathIndex site + lens.bFusionSuffixLength site =
    lens.bRoute.path.length at hsplit
  constructor <;> omega

/-- Every fusion site is strictly internal to the `(a,c)` route. -/
theorem EvenKempeFusionLens.cFusionPathIndex_bounds {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    0 < lens.cFusionPathIndex site ∧
      lens.cFusionPathIndex site < lens.cRoute.path.length := by
  rcases lens.cFusionPathIndex_odd hac site with ⟨prefixHalf, hprefix⟩
  rcases lens.cFusionSuffixLength_odd hac site with ⟨suffixHalf, hsuffix⟩
  have hmem := lens.cFusionVertex_mem_path_support site
  have hsplit := congrArg (fun walk ↦ walk.length)
    (lens.cRoute.path.take_spec hmem)
  simp only [SimpleGraph.Walk.length_append] at hsplit
  change lens.cFusionPathIndex site + lens.cFusionSuffixLength site =
    lens.cRoute.path.length at hsplit
  constructor <;> omega

/-- The two route coordinates of a fusion site. -/
def EvenKempeFusionLens.fusionPathCoordinates {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) : Nat × Nat :=
  (lens.bFusionPathIndex site, lens.cFusionPathIndex site)

theorem EvenKempeFusionLens.fusionPathCoordinates_odd {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    Odd (lens.fusionPathCoordinates site).1 ∧
      Odd (lens.fusionPathCoordinates site).2 := by
  exact ⟨lens.bFusionPathIndex_odd hab site,
    lens.cFusionPathIndex_odd hac site⟩

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
