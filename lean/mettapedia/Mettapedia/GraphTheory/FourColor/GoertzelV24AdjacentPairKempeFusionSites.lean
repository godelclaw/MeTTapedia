import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionLens
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.List.NodupEquivFin

namespace SimpleGraph.Coloring

variable {V α : Type*} {G : SimpleGraph V}

theorem mem_support_map_bicoloredWalk_iff
    (C : G.Coloring α) (a b : α)
    {left right : C.bicoloredSet a b}
    (path : (C.bicoloredSubgraph a b).Walk left right)
    (vertex : V) :
    vertex ∈ (path.map
      (SimpleGraph.Embedding.induce
        (G := G) (C.bicoloredSet a b)).toHom).support ↔
      vertex ∈ C.bicoloredWalkUnderlyingSupport a b path := by
  rw [SimpleGraph.Walk.support_map]
  constructor
  · intro hvertex
    rcases List.mem_map.mp hvertex with ⟨selected, hselected, hvalue⟩
    subst vertex
    exact ⟨selected.2, hselected⟩
  · rintro ⟨hcolor, hvertex⟩
    exact List.mem_map.mpr ⟨⟨vertex, hcolor⟩, hvertex, rfl⟩

end SimpleGraph.Coloring

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance fusionSiteGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

theorem EvenKempePortPath.mem_ambientPath_support_iff {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b : Color}
    {left right : Fin portCount}
    (route : data.EvenKempePortPath C a b left right)
    (edge : G.edgeSet) :
    edge ∈ route.ambientPath.support ↔
      edge ∈ C.bicoloredWalkUnderlyingSupport a b route.path := by
  exact SimpleGraph.Coloring.mem_support_map_bicoloredWalk_iff
    C a b route.path edge

/-- The common route vertices, ordered as they occur along the `(a,b)`
route. -/
def EvenKempeFusionLens.bFusionSites {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    List G.edgeSet :=
  lens.bRoute.ambientPath.support.filter fun edge ↦
    edge ∈ lens.cRoute.ambientPath.support

/-- The same common route vertices, ordered as they occur along the
`(a,c)` route. -/
def EvenKempeFusionLens.cFusionSites {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    List G.edgeSet :=
  lens.cRoute.ambientPath.support.filter fun edge ↦
    edge ∈ lens.bRoute.ambientPath.support

theorem EvenKempeFusionLens.mem_bFusionSites_iff {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (edge : G.edgeSet) :
    edge ∈ lens.bFusionSites ↔
      edge ∈ lens.bRoute.ambientPath.support ∧
      edge ∈ lens.cRoute.ambientPath.support := by
  simp [EvenKempeFusionLens.bFusionSites]

theorem EvenKempeFusionLens.mem_cFusionSites_iff {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (edge : G.edgeSet) :
    edge ∈ lens.cFusionSites ↔
      edge ∈ lens.cRoute.ambientPath.support ∧
      edge ∈ lens.bRoute.ambientPath.support := by
  simp [EvenKempeFusionLens.cFusionSites]

/-- The two lists enumerate the same fusion sites, differing only in their
path-induced order. -/
theorem EvenKempeFusionLens.bFusionSites_perm_cFusionSites
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    lens.bFusionSites.Perm lens.cFusionSites := by
  apply (List.perm_ext_iff_of_nodup
    (List.Nodup.filter _ lens.bRoute.ambientPath_isPath.support_nodup)
    (List.Nodup.filter _ lens.cRoute.ambientPath_isPath.support_nodup)).2
  intro edge
  simp [and_comm]

theorem EvenKempeFusionLens.bFusionSites_nodup {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    lens.bFusionSites.Nodup :=
  List.Nodup.filter _ lens.bRoute.ambientPath_isPath.support_nodup

theorem EvenKempeFusionLens.cFusionSites_nodup {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    lens.cFusionSites.Nodup :=
  List.Nodup.filter _ lens.cRoute.ambientPath_isPath.support_nodup

theorem EvenKempeFusionLens.fusionSites_length_eq {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    lens.bFusionSites.length = lens.cFusionSites.length :=
  lens.bFusionSites_perm_cFusionSites.length_eq

/-- Every entry of either ordered fusion-site list has the shared color. -/
theorem EvenKempeFusionLens.color_eq_of_mem_bFusionSites
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    {edge : G.edgeSet} (hedge : edge ∈ lens.bFusionSites) :
    C edge = a := by
  rcases (lens.mem_bFusionSites_iff edge).1 hedge with ⟨hb, hc⟩
  exact lens.sharedColor edge
    ((lens.bRoute.mem_ambientPath_support_iff edge).1 hb)
    ((lens.cRoute.mem_ambientPath_support_iff edge).1 hc)

theorem EvenKempeFusionLens.color_eq_of_mem_cFusionSites
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    {edge : G.edgeSet} (hedge : edge ∈ lens.cFusionSites) :
    C edge = a := by
  exact lens.color_eq_of_mem_bFusionSites
    ((lens.bFusionSites_perm_cFusionSites.mem_iff).2 hedge)

/-- A fusion site is internal to both routes: none of the four terminal
edges occurs in the ordered common-support list. -/
theorem EvenKempeFusionLens.endpoints_not_mem_bFusionSites
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) :
    lens.bRoute.leftEdge.1 ∉ lens.bFusionSites ∧
      lens.bRoute.rightEdge.1 ∉ lens.bFusionSites ∧
      lens.cRoute.leftEdge.1 ∉ lens.bFusionSites ∧
      lens.cRoute.rightEdge.1 ∉ lens.bFusionSites := by
  have hendpoints := lens.endpoints_not_shared hab hac
  constructor
  · intro hmem
    exact hendpoints.1 ((lens.cRoute.mem_ambientPath_support_iff _).1
      ((lens.mem_bFusionSites_iff _).1 hmem).2)
  constructor
  · intro hmem
    exact hendpoints.2.1 ((lens.cRoute.mem_ambientPath_support_iff _).1
      ((lens.mem_bFusionSites_iff _).1 hmem).2)
  constructor
  · intro hmem
    exact hendpoints.2.2.1 ((lens.bRoute.mem_ambientPath_support_iff _).1
      ((lens.mem_bFusionSites_iff _).1 hmem).1)
  · intro hmem
    exact hendpoints.2.2.2 ((lens.bRoute.mem_ambientPath_support_iff _).1
      ((lens.mem_bFusionSites_iff _).1 hmem).1)

/-- The fusion list is empty exactly when the two ambient route supports
are disjoint. -/
theorem EvenKempeFusionLens.bFusionSites_eq_nil_iff_disjoint
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    lens.bFusionSites = [] ↔
      lens.bRoute.ambientPath.support.Disjoint
        lens.cRoute.ambientPath.support := by
  simp [EvenKempeFusionLens.bFusionSites, List.disjoint_left]

/-- The number of shared-color fusion sites in either route order. -/
def EvenKempeFusionLens.fusionSiteCount {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) : Nat :=
  lens.bFusionSites.length

@[simp] theorem EvenKempeFusionLens.fusionSiteCount_eq_b_length
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    lens.fusionSiteCount = lens.bFusionSites.length :=
  rfl

theorem EvenKempeFusionLens.fusionSiteCount_eq_c_length
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    lens.fusionSiteCount = lens.cFusionSites.length :=
  lens.fusionSites_length_eq

/-- The identity-on-edges equivalence between the two ordered
fusion-site membership types. -/
def EvenKempeFusionLens.fusionSiteMembershipEquiv {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    {edge : G.edgeSet // edge ∈ lens.bFusionSites} ≃
      {edge : G.edgeSet // edge ∈ lens.cFusionSites} where
  toFun edge := ⟨edge.1,
    lens.bFusionSites_perm_cFusionSites.mem_iff.1 edge.2⟩
  invFun edge := ⟨edge.1,
    lens.bFusionSites_perm_cFusionSites.mem_iff.2 edge.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The canonical correspondence between positions in the two route
orders: a position is sent to the position of the same graph edge in the
other route. -/
def EvenKempeFusionLens.fusionOrderEquiv {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    Fin lens.bFusionSites.length ≃ Fin lens.cFusionSites.length :=
  (List.Nodup.getEquiv lens.bFusionSites lens.bFusionSites_nodup).trans
    (lens.fusionSiteMembershipEquiv.trans
      (List.Nodup.getEquiv lens.cFusionSites
        lens.cFusionSites_nodup).symm)

theorem EvenKempeFusionLens.fusionOrderEquiv_preserves_edge
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (position : Fin lens.bFusionSites.length) :
    lens.cFusionSites.get (lens.fusionOrderEquiv position) =
      lens.bFusionSites.get position := by
  simp [EvenKempeFusionLens.fusionOrderEquiv,
    EvenKempeFusionLens.fusionSiteMembershipEquiv]

/-- Transporting the second order back across the proved length equality
makes the fusion-order correspondence a finite permutation. -/
def EvenKempeFusionLens.fusionMonodromy {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    Equiv.Perm (Fin lens.fusionSiteCount) :=
  lens.fusionOrderEquiv.trans
    (finCongr lens.fusionSites_length_eq.symm)

@[simp] theorem EvenKempeFusionLens.fusionMonodromy_apply_val
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (position : Fin lens.fusionSiteCount) :
    (lens.fusionMonodromy position : Nat) =
      (lens.fusionOrderEquiv position : Nat) :=
  rfl

/-- With zero or one fusion site there is no nontrivial order monodromy. -/
theorem EvenKempeFusionLens.fusionMonodromy_eq_refl_of_count_le_one
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hcount : lens.fusionSiteCount ≤ 1) :
    lens.fusionMonodromy = Equiv.refl (Fin lens.fusionSiteCount) := by
  apply Equiv.ext
  intro position
  apply Fin.ext
  have hposition := position.isLt
  have himage := (lens.fusionMonodromy position).isLt
  omega

/-- Consequently a nonidentity fusion monodromy requires at least two
internal shared-color sites. -/
theorem EvenKempeFusionLens.two_le_fusionSiteCount_of_monodromy_ne_refl
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hmonodromy : lens.fusionMonodromy ≠
      Equiv.refl (Fin lens.fusionSiteCount)) :
    2 ≤ lens.fusionSiteCount := by
  by_contra hcount
  apply hmonodromy
  exact lens.fusionMonodromy_eq_refl_of_count_le_one (by omega)

end


end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
