import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionContainerInteraction

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance crossChannelGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Intersections of the first lens's `(a,b)` route with the complementary
lens's `(a,c)` route, ordered along the first route. -/
def EvenKempeFusionLens.bcCrossSites
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    List G.edgeSet :=
  lens01.bRoute.ambientPath.support.filter fun edge ↦
    edge ∈ lens23.cRoute.ambientPath.support

/-- The same cross channel, ordered along the complementary `(a,c)` route. -/
def EvenKempeFusionLens.bcCrossSitesOnSecond
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    List G.edgeSet :=
  lens23.cRoute.ambientPath.support.filter fun edge ↦
    edge ∈ lens01.bRoute.ambientPath.support

/-- Intersections of the first lens's `(a,c)` route with the complementary
lens's `(a,b)` route, ordered along the first route. -/
def EvenKempeFusionLens.cbCrossSites
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    List G.edgeSet :=
  lens01.cRoute.ambientPath.support.filter fun edge ↦
    edge ∈ lens23.bRoute.ambientPath.support

/-- The same second cross channel, ordered along the complementary `(a,b)`
route. -/
def EvenKempeFusionLens.cbCrossSitesOnSecond
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    List G.edgeSet :=
  lens23.bRoute.ambientPath.support.filter fun edge ↦
    edge ∈ lens01.cRoute.ambientPath.support

theorem EvenKempeFusionLens.mem_bcCrossSites_iff
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (edge : G.edgeSet) :
    edge ∈ lens01.bcCrossSites lens23 ↔
      edge ∈ lens01.bRoute.ambientPath.support ∧
      edge ∈ lens23.cRoute.ambientPath.support := by
  simp [EvenKempeFusionLens.bcCrossSites]

theorem EvenKempeFusionLens.mem_bcCrossSitesOnSecond_iff
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (edge : G.edgeSet) :
    edge ∈ lens01.bcCrossSitesOnSecond lens23 ↔
      edge ∈ lens23.cRoute.ambientPath.support ∧
      edge ∈ lens01.bRoute.ambientPath.support := by
  simp [EvenKempeFusionLens.bcCrossSitesOnSecond]

theorem EvenKempeFusionLens.mem_cbCrossSites_iff
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (edge : G.edgeSet) :
    edge ∈ lens01.cbCrossSites lens23 ↔
      edge ∈ lens01.cRoute.ambientPath.support ∧
      edge ∈ lens23.bRoute.ambientPath.support := by
  simp [EvenKempeFusionLens.cbCrossSites]

theorem EvenKempeFusionLens.mem_cbCrossSitesOnSecond_iff
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (edge : G.edgeSet) :
    edge ∈ lens01.cbCrossSitesOnSecond lens23 ↔
      edge ∈ lens23.bRoute.ambientPath.support ∧
      edge ∈ lens01.cRoute.ambientPath.support := by
  simp [EvenKempeFusionLens.cbCrossSitesOnSecond]

/-- Each cross channel has the same sites in the two route-induced orders. -/
theorem EvenKempeFusionLens.bcCrossSites_perm_onSecond
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    (lens01.bcCrossSites lens23).Perm
      (lens01.bcCrossSitesOnSecond lens23) := by
  apply (List.perm_ext_iff_of_nodup
    (List.Nodup.filter _ lens01.bRoute.ambientPath_isPath.support_nodup)
    (List.Nodup.filter _ lens23.cRoute.ambientPath_isPath.support_nodup)).2
  intro edge
  simp [and_comm]

theorem EvenKempeFusionLens.cbCrossSites_perm_onSecond
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    (lens01.cbCrossSites lens23).Perm
      (lens01.cbCrossSitesOnSecond lens23) := by
  apply (List.perm_ext_iff_of_nodup
    (List.Nodup.filter _ lens01.cRoute.ambientPath_isPath.support_nodup)
    (List.Nodup.filter _ lens23.bRoute.ambientPath_isPath.support_nodup)).2
  intro edge
  simp [and_comm]

theorem EvenKempeFusionLens.bcCrossSites_nodup
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    (lens01.bcCrossSites lens23).Nodup :=
  List.Nodup.filter _ lens01.bRoute.ambientPath_isPath.support_nodup

theorem EvenKempeFusionLens.cbCrossSites_nodup
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    (lens01.cbCrossSites lens23).Nodup :=
  List.Nodup.filter _ lens01.cRoute.ambientPath_isPath.support_nodup

/-- Same-family separation makes the two cross channels edge-disjoint. -/
theorem EvenKempeFusionLens.crossChannels_disjoint
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support) :
    (lens01.bcCrossSites lens23).Disjoint
      (lens01.cbCrossSites lens23) := by
  rw [List.disjoint_left]
  intro edge hbc hcb
  rcases (lens01.mem_bcCrossSites_iff lens23 edge).1 hbc with
    ⟨hb01, _⟩
  rcases (lens01.mem_cbCrossSites_iff lens23 edge).1 hcb with
    ⟨_, hb23⟩
  exact (List.disjoint_left.mp hbDisjoint) hb01 hb23

/-- Every cross-channel site carries the unique shared color `a`. -/
theorem EvenKempeFusionLens.color_eq_first_of_mem_bcCrossSites
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hbc : b ≠ c) {edge : G.edgeSet}
    (hedge : edge ∈ lens01.bcCrossSites lens23) :
    C edge = a := by
  rcases (lens01.mem_bcCrossSites_iff lens23 edge).1 hedge with
    ⟨hb01, hc23⟩
  exact lens01.bRoute.color_eq_first_of_mem_ambientPath_supports
    hbc lens23.cRoute hb01 hc23

theorem EvenKempeFusionLens.color_eq_first_of_mem_cbCrossSites
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hbc : b ≠ c) {edge : G.edgeSet}
    (hedge : edge ∈ lens01.cbCrossSites lens23) :
    C edge = a := by
  rcases (lens01.mem_cbCrossSites_iff lens23 edge).1 hedge with
    ⟨hc01, hb23⟩
  exact lens23.bRoute.color_eq_first_of_mem_ambientPath_supports
    hbc lens01.cRoute hb23 hc01

/-- The two complementary route containers overlap exactly when at least
one of their ordered cross-channel lists is nonempty. -/
theorem EvenKempeFusionLens.routeUnions_intersect_iff_crossChannel_nonempty
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support) :
    (∃ edge : G.edgeSet,
        edge ∈ lens01.bRoute.ambientPath.support ++
          lens01.cRoute.ambientPath.support ∧
        edge ∈ lens23.bRoute.ambientPath.support ++
          lens23.cRoute.ambientPath.support) ↔
      lens01.bcCrossSites lens23 ≠ [] ∨
        lens01.cbCrossSites lens23 ≠ [] := by
  constructor
  · rintro ⟨edge, hboth⟩
    rcases (lens01.mem_routeUnions_iff_crossFamily
        lens23 hbDisjoint hcDisjoint edge).1 hboth with hcross | hcross
    · exact Or.inl (List.ne_nil_of_mem
        ((lens01.mem_bcCrossSites_iff lens23 edge).2 hcross))
    · exact Or.inr (List.ne_nil_of_mem
        ((lens01.mem_cbCrossSites_iff lens23 edge).2 hcross))
  · rintro (hbcSites | hcbSites)
    · rcases List.exists_mem_of_ne_nil _ hbcSites with ⟨edge, hedge⟩
      rcases (lens01.mem_bcCrossSites_iff lens23 edge).1 hedge with
        ⟨hb01, hc23⟩
      refine ⟨edge, ?_, ?_⟩
      · simpa only [List.mem_append] using Or.inl hb01
      · simpa only [List.mem_append] using Or.inr hc23
    · rcases List.exists_mem_of_ne_nil _ hcbSites with ⟨edge, hedge⟩
      rcases (lens01.mem_cbCrossSites_iff lens23 edge).1 hedge with
        ⟨hc01, hb23⟩
      refine ⟨edge, ?_, ?_⟩
      · simpa only [List.mem_append] using Or.inr hc01
      · simpa only [List.mem_append] using Or.inl hb23

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
