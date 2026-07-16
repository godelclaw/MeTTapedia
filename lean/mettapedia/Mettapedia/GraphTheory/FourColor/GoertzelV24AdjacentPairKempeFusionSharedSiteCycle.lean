import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionRouteIntervals

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The first ambient route, stopped at a fusion site. -/
def EvenKempeFusionLens.bAmbientPrefixToFusion
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    G.lineGraph.Walk lens.bRoute.leftEdge.1 site.1 :=
  lens.bRoute.ambientPath.takeUntil site.1
    ((lens.mem_bFusionSites_iff site.1).1 site.2).1

/-- The second ambient route, stopped at the same fusion site. -/
def EvenKempeFusionLens.cAmbientPrefixToFusion
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    G.lineGraph.Walk lens.cRoute.leftEdge.1 site.1 :=
  lens.cRoute.ambientPath.takeUntil site.1
    ((lens.mem_bFusionSites_iff site.1).1 site.2).2

/-- Cross the left boundary connector and then follow the second route to
the fusion site. This has the same endpoints as the first prefix. -/
def EvenKempeFusionLens.cLeftConnectedPrefixToFusion
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    G.lineGraph.Walk lens.bRoute.leftEdge.1 site.1 :=
  SimpleGraph.Walk.cons lens.leftConnector
    (lens.cAmbientPrefixToFusion site)

theorem EvenKempeFusionLens.bLeftEdge_not_mem_cAmbientPath_support
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) :
    lens.bRoute.leftEdge.1 ∉ lens.cRoute.ambientPath.support := by
  intro hmem
  exact (lens.endpoints_not_shared hab hac).1
    ((lens.cRoute.mem_ambientPath_support_iff _).1 hmem)

theorem EvenKempeFusionLens.cLeftEdge_not_mem_bAmbientPath_support
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) :
    lens.cRoute.leftEdge.1 ∉ lens.bRoute.ambientPath.support := by
  intro hmem
  exact (lens.endpoints_not_shared hab hac).2.2.1
    ((lens.bRoute.mem_ambientPath_support_iff _).1 hmem)

theorem EvenKempeFusionLens.bAmbientPrefixToFusion_isPath
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    (lens.bAmbientPrefixToFusion site).IsPath := by
  exact lens.bRoute.ambientPath_isPath.takeUntil
    ((lens.mem_bFusionSites_iff site.1).1 site.2).1

theorem EvenKempeFusionLens.cAmbientPrefixToFusion_isPath
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    (lens.cAmbientPrefixToFusion site).IsPath := by
  exact lens.cRoute.ambientPath_isPath.takeUntil
    ((lens.mem_bFusionSites_iff site.1).1 site.2).2

theorem EvenKempeFusionLens.cLeftConnectedPrefixToFusion_isPath
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cLeftConnectedPrefixToFusion site).IsPath := by
  rw [EvenKempeFusionLens.cLeftConnectedPrefixToFusion,
    SimpleGraph.Walk.cons_isPath_iff]
  refine ⟨lens.cAmbientPrefixToFusion_isPath site, ?_⟩
  intro hmem
  exact lens.bLeftEdge_not_mem_cAmbientPath_support hab hac
    ((lens.cRoute.ambientPath.support_takeUntil_subset_support
      ((lens.mem_bFusionSites_iff site.1).1 site.2).2) hmem)

theorem EvenKempeFusionLens.bAmbientPrefixToFusion_support_subset
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    (lens.bAmbientPrefixToFusion site).support ⊆
      lens.bRoute.ambientPath.support :=
  lens.bRoute.ambientPath.support_takeUntil_subset_support
    ((lens.mem_bFusionSites_iff site.1).1 site.2).1

theorem EvenKempeFusionLens.cAmbientPrefixToFusion_support_subset
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    (lens.cAmbientPrefixToFusion site).support ⊆
      lens.cRoute.ambientPath.support :=
  lens.cRoute.ambientPath.support_takeUntil_subset_support
    ((lens.mem_bFusionSites_iff site.1).1 site.2).2

/-- The two left-to-site paths are distinct because the connected second
prefix contains its own left terminal edge, which the first route never
visits. -/
theorem EvenKempeFusionLens.bAmbientPrefixToFusion_ne_cLeftConnectedPrefixToFusion
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    lens.bAmbientPrefixToFusion site ≠
      lens.cLeftConnectedPrefixToFusion site := by
  intro heq
  have hcLeftMemConnected : lens.cRoute.leftEdge.1 ∈
      (lens.cLeftConnectedPrefixToFusion site).support := by
    simp [EvenKempeFusionLens.cLeftConnectedPrefixToFusion,
      EvenKempeFusionLens.cAmbientPrefixToFusion]
  have hcLeftMemBPrefix : lens.cRoute.leftEdge.1 ∈
      (lens.bAmbientPrefixToFusion site).support := by
    rw [heq]
    exact hcLeftMemConnected
  exact lens.cLeftEdge_not_mem_bAmbientPath_support hab hac
    (lens.bAmbientPrefixToFusion_support_subset site hcLeftMemBPrefix)

theorem EvenKempeFusionLens.bAmbientPrefixToFusion_length_lt_ambientPath
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.bAmbientPrefixToFusion site).length <
      lens.bRoute.ambientPath.length := by
  apply lens.bRoute.ambientPath.length_takeUntil_lt_length
  intro heq
  exact (lens.endpoints_not_mem_bFusionSites hab hac).2.1
    (heq ▸ site.2)

theorem EvenKempeFusionLens.cAmbientPrefixToFusion_length_lt_ambientPath
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cAmbientPrefixToFusion site).length <
      lens.cRoute.ambientPath.length := by
  apply lens.cRoute.ambientPath.length_takeUntil_lt_length
  intro heq
  exact (lens.endpoints_not_mem_bFusionSites hab hac).2.2.2
    (heq ▸ site.2)

@[simp] theorem EvenKempeFusionLens.cLeftConnectedPrefixToFusion_length
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    (lens.cLeftConnectedPrefixToFusion site).length =
      (lens.cAmbientPrefixToFusion site).length + 1 := by
  simp [EvenKempeFusionLens.cLeftConnectedPrefixToFusion]

/-- Every fusion site already supplies a shorter cycle, by comparing the
first route prefix with the left-connected second route prefix. -/
theorem EvenKempeFusionLens.exists_isCycle_length_lt_closedWalk_of_fusionSite
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    ∃ edge, ∃ cycle : G.lineGraph.Walk edge edge,
      cycle.IsCycle ∧ cycle.length < lens.closedWalk.length := by
  rcases (lens.bAmbientPrefixToFusion_isPath site).exists_isCycle_length_le_add_of_ne
      (lens.cLeftConnectedPrefixToFusion_isPath hab hac site)
      (lens.bAmbientPrefixToFusion_ne_cLeftConnectedPrefixToFusion
        hab hac site) with
    ⟨edge, _hedgeB, _hedgeC, cycle, hcycle, hcycleLength⟩
  refine ⟨edge, cycle, hcycle, ?_⟩
  calc
    cycle.length ≤
        (lens.bAmbientPrefixToFusion site).length +
          (lens.cLeftConnectedPrefixToFusion site).length := hcycleLength
    _ < lens.bRoute.ambientPath.length +
        lens.cRoute.ambientPath.length + 2 := by
      rw [lens.cLeftConnectedPrefixToFusion_length site]
      have hb := lens.bAmbientPrefixToFusion_length_lt_ambientPath
        hab hac site
      have hc := lens.cAmbientPrefixToFusion_length_lt_ambientPath
        hab hac site
      omega
    _ = lens.closedWalk.length := by
      rw [lens.closedWalk_length]
      simp only [EvenKempePortPath.ambientPath_length]

/-- Thus every nontrivial signed fusion monodromy forces a strictly shorter
cycle: an order inversion uses the two inversion intervals, while the
remaining negative-chirality case supplies a fusion site directly. -/
theorem EvenKempeFusionLens.exists_isCycle_length_lt_closedWalk_of_signedMonodromy_ne_refl
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (hsigned : lens.signedFusionMonodromy hab hac ≠
      Equiv.refl (Fin lens.fusionSiteCount × Bool)) :
    ∃ edge, ∃ cycle : G.lineGraph.Walk edge edge,
      cycle.IsCycle ∧ cycle.length < lens.closedWalk.length := by
  rcases lens.exists_orderInversion_or_negativeChirality_of_signedMonodromy_ne_refl
    hab hac hsigned with hinversion | hnegative
  · rcases hinversion with ⟨first, second, hfirstSecond, hsecondFirst⟩
    apply lens.exists_isCycle_length_lt_closedWalk_of_monodromy_ne_refl
    intro htrivial
    rw [htrivial] at hsecondFirst
    exact lt_asymm hfirstSecond hsecondFirst
  · rcases hnegative with ⟨position, _hnegative⟩
    exact lens.exists_isCycle_length_lt_closedWalk_of_fusionSite
      hab hac (lens.bFusionSiteAt position)

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
