import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionZeroFusionResolution

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance singleCrossIntersectionGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The vertices visited by a fusion-lens closed walk are exactly the edge
vertices visited by either of its two terminal routes. -/
theorem EvenKempeFusionLens.mem_closedWalk_support_iff_routeSupport
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (edge : G.edgeSet) :
    edge ∈ lens.closedWalk.support ↔
      edge ∈ lens.bRoute.ambientPath.support ∨
        edge ∈ lens.cRoute.ambientPath.support := by
  constructor
  · intro hmem
    simp [EvenKempeFusionLens.closedWalk] at hmem
    rcases hmem with hmem | hright | hmem | hleft | hleft
    · exact Or.inl hmem
    · exact Or.inl (hright ▸ lens.bRoute.ambientPath.end_mem_support)
    · exact Or.inr hmem
    · exact Or.inr (hleft ▸ lens.cRoute.ambientPath.start_mem_support)
    · exact Or.inl (hleft ▸ lens.bRoute.ambientPath.start_mem_support)
  · rintro (hmem | hmem)
    · simp [EvenKempeFusionLens.closedWalk, hmem]
    · simp [EvenKempeFusionLens.closedWalk, hmem]

/-- A selected `bc` cross is the complete cross-channel list when that list
has length at most one. -/
theorem EvenKempeFusionLens.bcCrossSites_eq_singleton_of_length_le_one
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hcount : (lens01.bcCrossSites lens23).length ≤ 1)
    (site : lens01.bRoute.CrossSite lens23.cRoute) :
    lens01.bcCrossSites lens23 = [site.1] := by
  have hsite : site.1 ∈ lens01.bcCrossSites lens23 :=
    (lens01.mem_bcCrossSites_iff lens23 site.1).2 site.2
  cases hlist : lens01.bcCrossSites lens23 with
  | nil =>
      rw [hlist] at hsite
      simp at hsite
  | cons head tail =>
      have htail : tail = [] := by
        cases tail with
        | nil => rfl
        | cons second rest =>
            rw [hlist] at hcount
            simp only [List.length_cons] at hcount
            omega
      subst tail
      rw [hlist] at hsite
      simp only [List.mem_singleton] at hsite
      simpa only using congrArg (fun edge : G.edgeSet ↦ [edge]) hsite.symm

/-- The complementary singleton-channel identity. -/
theorem EvenKempeFusionLens.cbCrossSites_eq_singleton_of_length_le_one
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hcount : (lens01.cbCrossSites lens23).length ≤ 1)
    (site : lens01.cRoute.CrossSite lens23.bRoute) :
    lens01.cbCrossSites lens23 = [site.1] := by
  have hsite : site.1 ∈ lens01.cbCrossSites lens23 :=
    (lens01.mem_cbCrossSites_iff lens23 site.1).2 site.2
  cases hlist : lens01.cbCrossSites lens23 with
  | nil =>
      rw [hlist] at hsite
      simp at hsite
  | cons head tail =>
      have htail : tail = [] := by
        cases tail with
        | nil => rfl
        | cons second rest =>
            rw [hlist] at hcount
            simp only [List.length_cons] at hcount
            omega
      subst tail
      rw [hlist] at hsite
      simp only [List.mem_singleton] at hsite
      simpa only using congrArg (fun edge : G.edgeSet ↦ [edge]) hsite.symm

/-- If `bc` is the sole sparse cross channel, the two complete lens walks
share exactly its selected edge vertex. -/
theorem EvenKempeFusionLens.mem_both_closedWalk_supports_iff_eq_bcCrossSite
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hcount : (lens01.bcCrossSites lens23).length ≤ 1)
    (hcbEmpty : lens01.cbCrossSites lens23 = [])
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (edge : G.edgeSet) :
    (edge ∈ lens01.closedWalk.support ∧
        edge ∈ lens23.closedWalk.support) ↔
      edge = site.1 := by
  constructor
  · rintro ⟨hlens01, hlens23⟩
    have hunion01 : edge ∈ lens01.bRoute.ambientPath.support ++
        lens01.cRoute.ambientPath.support := by
      rw [List.mem_append]
      exact (lens01.mem_closedWalk_support_iff_routeSupport edge).1 hlens01
    have hunion23 : edge ∈ lens23.bRoute.ambientPath.support ++
        lens23.cRoute.ambientPath.support := by
      rw [List.mem_append]
      exact (lens23.mem_closedWalk_support_iff_routeSupport edge).1 hlens23
    rcases (lens01.mem_routeUnions_iff_crossFamily lens23
        hbDisjoint hcDisjoint edge).1 ⟨hunion01, hunion23⟩ with
      hbc | hcb
    · exact lens01.bcCrossSite_eq_of_length_le_one
        lens23 hcount site edge hbc.1 hbc.2
    · have hmem : edge ∈ lens01.cbCrossSites lens23 :=
        (lens01.mem_cbCrossSites_iff lens23 edge).2 hcb
      rw [hcbEmpty] at hmem
      simp at hmem
  · rintro rfl
    constructor
    · apply (lens01.mem_closedWalk_support_iff_routeSupport site.1).2
      exact Or.inl site.2.1
    · apply (lens23.mem_closedWalk_support_iff_routeSupport site.1).2
      exact Or.inr site.2.2

/-- If `cb` is the sole sparse cross channel, it likewise is the exact
intersection of the two complete lens-walk supports. -/
theorem EvenKempeFusionLens.mem_both_closedWalk_supports_iff_eq_cbCrossSite
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hcount : (lens01.cbCrossSites lens23).length ≤ 1)
    (hbcEmpty : lens01.bcCrossSites lens23 = [])
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (edge : G.edgeSet) :
    (edge ∈ lens01.closedWalk.support ∧
        edge ∈ lens23.closedWalk.support) ↔
      edge = site.1 := by
  constructor
  · rintro ⟨hlens01, hlens23⟩
    have hunion01 : edge ∈ lens01.bRoute.ambientPath.support ++
        lens01.cRoute.ambientPath.support := by
      rw [List.mem_append]
      exact (lens01.mem_closedWalk_support_iff_routeSupport edge).1 hlens01
    have hunion23 : edge ∈ lens23.bRoute.ambientPath.support ++
        lens23.cRoute.ambientPath.support := by
      rw [List.mem_append]
      exact (lens23.mem_closedWalk_support_iff_routeSupport edge).1 hlens23
    rcases (lens01.mem_routeUnions_iff_crossFamily lens23
        hbDisjoint hcDisjoint edge).1 ⟨hunion01, hunion23⟩ with
      hbc | hcb
    · have hmem : edge ∈ lens01.bcCrossSites lens23 :=
        (lens01.mem_bcCrossSites_iff lens23 edge).2 hbc
      rw [hbcEmpty] at hmem
      simp at hmem
    · exact lens01.cbCrossSite_eq_of_length_le_one
        lens23 hcount site edge hcb.1 hcb.2
  · rintro rfl
    constructor
    · apply (lens01.mem_closedWalk_support_iff_routeSupport site.1).2
      exact Or.inr site.2.1
    · apply (lens23.mem_closedWalk_support_iff_routeSupport site.1).2
      exact Or.inl site.2.2

/-- A one-channel residual can be repackaged without losing its channel
certificate: there is one shared edge, it is the complete surviving channel,
and it is exactly the intersection of the two lens-walk supports. -/
theorem EvenKempeFusionLens.exists_exact_sharedEdge_of_singleCrossChannel
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hcounts : (lens01.bcCrossSites lens23).length ≤ 1 ∧
      (lens01.cbCrossSites lens23).length ≤ 1)
    (Pbc : lens01.bRoute.CrossSite lens23.cRoute → Prop)
    (Pcb : lens01.cRoute.CrossSite lens23.bRoute → Prop)
    (hchannel :
      ((∃ site : lens01.bRoute.CrossSite lens23.cRoute, Pbc site) ∧
          lens01.cbCrossSites lens23 = []) ∨
        (lens01.bcCrossSites lens23 = [] ∧
          ∃ site : lens01.cRoute.CrossSite lens23.bRoute, Pcb site)) :
    ∃ shared : G.edgeSet,
      (∀ edge : G.edgeSet,
        (edge ∈ lens01.closedWalk.support ∧
            edge ∈ lens23.closedWalk.support) ↔ edge = shared) ∧
      ((lens01.bcCrossSites lens23 = [shared] ∧
          lens01.cbCrossSites lens23 = [] ∧
          ∃ site : lens01.bRoute.CrossSite lens23.cRoute,
            site.1 = shared ∧ Pbc site) ∨
        (lens01.bcCrossSites lens23 = [] ∧
          lens01.cbCrossSites lens23 = [shared] ∧
          ∃ site : lens01.cRoute.CrossSite lens23.bRoute,
            site.1 = shared ∧ Pcb site)) := by
  rcases hchannel with ⟨⟨site, hsite⟩, hcbEmpty⟩ |
      ⟨hbcEmpty, site, hsite⟩
  · refine ⟨site.1, ?_, Or.inl ⟨?_, hcbEmpty, site, rfl, hsite⟩⟩
    · intro edge
      exact lens01.mem_both_closedWalk_supports_iff_eq_bcCrossSite
        lens23 hbDisjoint hcDisjoint hcounts.1 hcbEmpty site edge
    · exact lens01.bcCrossSites_eq_singleton_of_length_le_one
        lens23 hcounts.1 site
  · refine ⟨site.1, ?_, Or.inr ⟨hbcEmpty, ?_, site, rfl, hsite⟩⟩
    · intro edge
      exact lens01.mem_both_closedWalk_supports_iff_eq_cbCrossSite
        lens23 hbDisjoint hcDisjoint hcounts.2 hbcEmpty site edge
    · exact lens01.cbCrossSites_eq_singleton_of_length_le_one
        lens23 hcounts.2 site

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
