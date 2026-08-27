import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierMenu
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebInnerTouching
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierMenuProfileSemantics

/-!
# The open-tangle menu predicate is vacuous

This is a regression fixture, not a target.

The menu-B predicate currently stated on the open tangle asks that two distinct
components of the selected bichromatic support graph meet the inner cap.  On
the open tangle that condition is automatic whenever three of the five inner
ports carry support vertices, which a majority pair always achieves — it has
four active ports.

The reason is degree.  A boundary stub has selected-pair degree one and every
other support vertex has degree two, so once two distinct boundary stubs of one
component are named, every boundary stub of that component is one of them.
Three distinct inner stubs therefore cannot share a component, and two distinct
components meeting the cap always exist.

Consequently the seed count built from this predicate is the whole good fibre,
not the source's seed count, and the transition and profile theorems stated for
it do not discharge the Seed Lemma.  The source's condition is the cap-composed
one: components of the strand pairing joined with the cap pairing, after the
pentagonal cap is restored.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularFrontierMenuVacuity

open SimpleGraph
open GoertzelV24AnnularFrontierMenu
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebInnerTouching
open GoertzelV24ClosedWebRadialComponents

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {outerCount : Nat}

/-- **Three inner ports in the support force the open predicate.**  Two of
their components must differ, since one component holds at most two boundary
stubs. -/
theorem menuBForPair_of_three_inner_support_vertices
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {first second : Color} (hpair : ValidColorPair first second)
    {i j k : Fin 5} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (vi vj vk : ColorPairSupportVertex C first second)
    (hvi : vi.1 = data.innerStub i) (hvj : vj.1 = data.innerStub j)
    (hvk : vk.1 = data.innerStub k) :
    AnnularFrontierMenuBForPair data C first second := by
  classical
  set graph := colorPairSupportGraph C first second with hgraph
  have hstub : ∀ {v : ColorPairSupportVertex C first second} {n : Fin 5},
      v.1 = data.innerStub n → IsBoundaryStub data v := by
    intro v n hv
    exact Or.inl ⟨n, hv⟩
  have hne : ∀ {v w : ColorPairSupportVertex C first second} {m n : Fin 5},
      v.1 = data.innerStub m → w.1 = data.innerStub n → m ≠ n → v ≠ w := by
    intro v w m n hv hw hmn hcontra
    exact hmn (data.innerStub.injective (by rw [← hv, ← hw, hcontra]))
  have hmem : ∀ v : ColorPairSupportVertex C first second,
      v ∈ (graph.connectedComponentMk v).supp := fun v => rfl
  by_cases hcase : graph.connectedComponentMk vi = graph.connectedComponentMk vj
  · -- both in one component; compare with the third
    refine ⟨graph.connectedComponentMk vi, graph.connectedComponentMk vk, ?_,
      ⟨i, vi, hmem vi, hvi⟩, ⟨k, vk, hmem vk, hvk⟩⟩
    intro hsame
    have hvjmem : vj ∈ (graph.connectedComponentMk vi).supp := by
      rw [hcase]; exact hmem vj
    have hvkmem : vk ∈ (graph.connectedComponentMk vi).supp := by
      rw [hsame]; exact hmem vk
    rcases boundaryStub_eq_start_or_finish_of_mem_component data hdata C hC
      hpair (graph.connectedComponentMk vi) vi vj vk (hmem vi) hvjmem hvkmem
      (hne hvi hvj hij) (hstub hvi) (hstub hvj) (hstub hvk) with hk | hk
    · exact hne hvk hvi hik.symm hk
    · exact hne hvk hvj hjk.symm hk
  · exact ⟨graph.connectedComponentMk vi, graph.connectedComponentMk vj, hcase,
      ⟨i, vi, hmem vi, hvi⟩, ⟨j, vj, hmem vj, hvj⟩⟩

/-- **The open predicate is automatic at four active ports.**  A majority pair
of a good word always has four, so this fires on every realizable state. -/
theorem menuBForPair_of_activeSupport_card_eq_four
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {first second : Color} (hpair : ValidColorPair first second)
    (hcard : (cap5ActiveSupport first second (data.innerBoundaryWord C)).card = 4) :
    AnnularFrontierMenuBForPair data C first second := by
  classical
  have hlt : 2 < (cap5ActiveSupport first second (data.innerBoundaryWord C)).card := by
    omega
  rcases Finset.two_lt_card_iff.mp hlt with ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩
  refine menuBForPair_of_three_inner_support_vertices data hdata C hC hpair
    hij hik hjk
    ⟨data.innerStub i, innerStub_mem_colorPairGraph_support_of_mem_activeSupport
      data hdata C first second i hi⟩
    ⟨data.innerStub j, innerStub_mem_colorPairGraph_support_of_mem_activeSupport
      data hdata C first second j hj⟩
    ⟨data.innerStub k, innerStub_mem_colorPairGraph_support_of_mem_activeSupport
      data hdata C first second k hk⟩ rfl rfl rfl

/-- Both majority pairs of a good inner word satisfy the open predicate. -/
theorem menuBForPair_of_majorityTriple
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {majority singletonFirst singletonSecond : Color}
    (htriple : AnnularFrontierMajorityTriple (data.innerBoundaryWord C)
      majority singletonFirst singletonSecond) :
    AnnularFrontierMenuBForPair data C majority singletonFirst ∧
      AnnularFrontierMenuBForPair data C majority singletonSecond := by
  have hcolors := htriple.1
  refine ⟨menuBForPair_of_activeSupport_card_eq_four data hdata C hC
      ⟨hcolors.1, hcolors.2.1, hcolors.2.2.2.1⟩
      htriple.activeSupport_majority_singletonFirst_card,
    menuBForPair_of_activeSupport_card_eq_four data hdata C hC
      ⟨hcolors.1, hcolors.2.2.1, hcolors.2.2.2.2.1⟩
      htriple.activeSupport_majority_singletonSecond_card⟩

/-- **The whole open Menu-B state is automatic on a good word.**  Nothing about
the colouring is used beyond properness, so this predicate cannot separate a
seed from the rest of its fibre. -/
theorem menuBState_of_goodWord
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (hgood : CAP5BoundaryWordHasColoredBlock311 (data.innerBoundaryWord C)) :
    AnnularFrontierMenuBState data C := by
  rcases exists_annularFrontierMajorityTriple_of_goodWord hgood with
    ⟨majority, singletonFirst, singletonSecond, htriple⟩
  exact ⟨majority, singletonFirst, singletonSecond, htriple,
    Or.inl (menuBForPair_of_majorityTriple data hdata C hC htriple).1⟩

/-- **The profile predicate is automatic too.**  The uniform carrier's
`connectionTable` encodes the same open relation, so transporting the graph
predicate onto the profile does not restore any content. -/
theorem menuBForPairOfProfile_of_majorityTriple
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {majority singletonFirst singletonSecond : Color}
    (htriple : AnnularFrontierMajorityTriple (data.innerBoundaryWord C)
      majority singletonFirst singletonSecond) :
    AnnularFrontierMenuBForPairOfProfile
        (annularFrontierMenuUniformProfile data hdata C) majority singletonFirst ∧
      AnnularFrontierMenuBForPairOfProfile
        (annularFrontierMenuUniformProfile data hdata C) majority singletonSecond := by
  obtain ⟨hfirst, hsecond⟩ := menuBForPair_of_majorityTriple data hdata C hC htriple
  exact ⟨(annularFrontierMenuBForPair_iff_of_uniformProfile
      data hdata C majority singletonFirst).mp hfirst,
    (annularFrontierMenuBForPair_iff_of_uniformProfile
      data hdata C majority singletonSecond).mp hsecond⟩

/-- The complete profile-level Menu-B state is likewise automatic on every
realizable good-word profile. -/
theorem menuBStateOfProfile_of_goodWord
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (hgood : CAP5BoundaryWordHasColoredBlock311 (data.innerBoundaryWord C)) :
    AnnularFrontierMenuBStateOfProfile
      (annularFrontierMenuUniformProfile data hdata C) := by
  rcases exists_annularFrontierMajorityTriple_of_goodWord hgood with
    ⟨majority, singletonFirst, singletonSecond, htriple⟩
  exact ⟨majority, singletonFirst, singletonSecond, htriple,
    Or.inl (menuBForPairOfProfile_of_majorityTriple data hdata C hC htriple).1⟩

end GoertzelV24AnnularFrontierMenuVacuity

end Mettapedia.GraphTheory.FourColor
