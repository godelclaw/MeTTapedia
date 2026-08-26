import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierMenu
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebInnerTouching

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

end GoertzelV24AnnularFrontierMenuVacuity

end Mettapedia.GraphTheory.FourColor
