import Mettapedia.GraphTheory.FourColor.GoertzelV24ForkInterfaceSupport
import Mettapedia.GraphTheory.FourColor.GoertzelV24RouteNativeInterfaceReflection
import Mettapedia.GraphTheory.FourColor.GoertzelV24TaitMatchingDecomposition
import Mettapedia.GraphTheory.FourColor.GoertzelV24ForkFold

/-!
# The colour-support fork law on literal rotation maps

The finite fork support uses `Fin 3`; the route's open Tait semantics uses
`Color = 𝔽₂ × 𝔽₂`, reserving zero for absent edges. This module identifies
proper colourings of an arbitrary edge piece on the same rotation system.
It then uses the fork law to state closed Tait colourability in terms of
compatible behaviours of two disjoint pieces.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelV24ForkTaitBridge

open GoertzelV24ForkInterfaceSupport
open GoertzelV24RouteNativeInterfaceReflection
open GoertzelV24TaitMatchingDecomposition
open GoertzelV24TwoEdgeCutMinimality

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- Edge adjacency in the route's rotation system is exactly intersection of
the endpoint incidence sets used by the fork evaluator. -/
theorem proper_iff_pieceColoring (RS : RotationSystem V E)
    (S : Finset E) (c : E → Fin 3) :
    Proper RS.endpoints S c ↔
      IsPieceColoring RS S (fun e => taitColor (c e)) := by
  constructor
  · intro h
    refine ⟨fun e _ => taitColor_ne_zero (c e), ?_⟩
    intro e he f hf hadj
    obtain ⟨hne, v, hve, hvf⟩ := RS.edgeAdjacencyGraph_adj_iff.mp hadj
    exact taitColor_injective.ne
      (h e he f hf hne ⟨v, Finset.mem_inter.mpr ⟨hve, hvf⟩⟩)
  · intro h e he f hf hne hmeet
    obtain ⟨v, hv⟩ := hmeet
    obtain ⟨hve, hvf⟩ := Finset.mem_inter.mp hv
    have hadj : RS.edgeAdjacencyGraph.Adj e f :=
      RS.edgeAdjacencyGraph_adj_iff.mpr ⟨hne, v, hve, hvf⟩
    exact fun heq => h.2 e he f hf hadj (congrArg taitColor heq)

/-- Every route-level open Tait colouring of an edge piece can be indexed by
the three nonzero colours on that piece. Values outside it are irrelevant. -/
theorem exists_fin3_of_pieceColoring (RS : RotationSystem V E)
    (S : Finset E) (C : E → Color) (h : IsPieceColoring RS S C) :
    ∃ c : E → Fin 3, Proper RS.endpoints S c ∧
      ∀ e ∈ S, taitColor (c e) = C e := by
  classical
  let c : E → Fin 3 := fun e =>
    if he : e ∈ S then
      Classical.choose (exists_unique_taitColor_index (C e) (h.1 e he))
    else 0
  have hc : ∀ e ∈ S, taitColor (c e) = C e := by
    intro e he
    dsimp [c]
    rw [dif_pos he]
    exact (Classical.choose_spec
      (exists_unique_taitColor_index (C e) (h.1 e he))).1
  refine ⟨c, ?_, hc⟩
  apply (proper_iff_pieceColoring RS S c).2
  refine ⟨fun e _ => taitColor_ne_zero (c e), ?_⟩
  intro e he f hf hadj
  change taitColor (c e) ≠ taitColor (c f)
  rw [hc e he, hc f hf]
  exact h.2 e he f hf hadj

/-- The fork evaluator has a state precisely when an actual open Tait
colouring of the displayed rotation-map piece exists. -/
theorem support_nonempty_iff_pieceColoring (RS : RotationSystem V E)
    (S : Finset E) :
    (GoertzelV24ForkInterfaceSupport.support RS.endpoints S).Nonempty ↔
      ∃ C : E → Color, IsPieceColoring RS S C := by
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨c, hc, _⟩ := mem_support.mp hp
    exact ⟨fun e => taitColor (c e), (proper_iff_pieceColoring RS S c).mp hc⟩
  · rintro ⟨C, hC⟩
    obtain ⟨c, hc, _⟩ := exists_fin3_of_pieceColoring RS S C hC
    exact ⟨profile RS.endpoints S c, mem_support.mpr ⟨c, hc, rfl⟩⟩

/-- The terminal behaviour of the fork semantics is the route's literal
Tait-colourability predicate. -/
theorem support_univ_nonempty_iff_taitColorable (RS : RotationSystem V E) :
    (GoertzelV24ForkInterfaceSupport.support RS.endpoints Finset.univ).Nonempty ↔
      RotationSystemTaitColorable RS := by
  rw [support_nonempty_iff_pieceColoring]
  exact (taitColorable_iff_exists_pieceColoring RS).symm

/-- A fork of two edge-disjoint pieces covers a closed rotation map exactly
when their realized boundary signatures have a compatible pair. This uses the
literal support composition law and the existing Tait terminal semantics. -/
theorem taitColorable_iff_compatible_fork (RS : RotationSystem V E)
    (A B : Finset E) (hdisj : Disjoint A B)
    (hcover : A ∪ B = Finset.univ) :
    RotationSystemTaitColorable RS ↔
      ∃ p ∈ GoertzelV24ForkInterfaceSupport.support RS.endpoints A,
        ∃ q ∈ GoertzelV24ForkInterfaceSupport.support RS.endpoints B,
          Compatible p q := by
  rw [← support_univ_nonempty_iff_taitColorable RS, ← hcover,
    support_union RS.endpoints A B hdisj]
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨⟨p, q⟩, hpq, _⟩ := Finset.mem_image.mp hr
    obtain ⟨hprod, hcompat⟩ := Finset.mem_filter.mp hpq
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hprod
    exact ⟨p, hp, q, hq, hcompat⟩
  · rintro ⟨p, hp, q, hq, hcompat⟩
    exact ⟨merge p q, Finset.mem_image.mpr
      ⟨(p, q), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hcompat⟩, rfl⟩⟩

/-- A complete fork fold over the physical edge-leaf tree decides exactly the
route's Tait-colourability predicate. The cubic incidence hypothesis follows
from the rotation system itself rather than being a new base assumption. -/
theorem fold_root_nonempty_iff_taitColorable (RS : RotationSystem V E)
    (hCubic : RS.IsCubic)
    (tree : GoertzelV24ConnectedBranchDecompositionForest.EdgeLeafTree E)
    (hnodup : tree.leafList.Nodup)
    (hcover : tree.shore = Finset.univ) :
    (GoertzelV24ForkFold.fold RS.endpoints tree).Nonempty ↔
      RotationSystemTaitColorable RS := by
  have hcubic : ∀ v : V,
      (Finset.univ.filter fun e => v ∈ RS.endpoints e).card = 3 := by
    intro v
    have hinc : (Finset.univ.filter fun e => v ∈ RS.endpoints e) =
        RS.incidentEdges v := by
      ext e
      simp [RS.mem_endpoints_iff_mem_incidentEdges]
    rw [hinc]
    exact RS.incidentEdges_card_eq_three_of_isCubic hCubic v
  rw [GoertzelV24ForkFold.fold_root_nonempty_iff
    RS.endpoints hcubic tree hnodup hcover]
  constructor
  · rintro ⟨c, hc⟩
    exact (taitColorable_iff_exists_pieceColoring RS).2
      ⟨fun e => taitColor (c e), (proper_iff_pieceColoring RS Finset.univ c).1 hc⟩
  · intro h
    obtain ⟨C, hC⟩ := (taitColorable_iff_exists_pieceColoring RS).1 h
    obtain ⟨c, hc, _⟩ := exists_fin3_of_pieceColoring RS Finset.univ C hC
    exact ⟨c, hc⟩

section GraphBacked

variable {W : Type*} [Fintype W] [DecidableEq W]
  {G : SimpleGraph W} [DecidableRel G.Adj] [G.LocallyFinite]

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- The route's graph-backed branch decomposition is enough to run the exact
colour fold. Its edge leaves have exactly the edge type of the associated
rotation system; no new edge-label equivalence is assumed. -/
theorem fold_rooted_nonempty_iff_taitColorable
    (data : SimpleGraphDartRotation.Data G)
    (hCubic : data.toRotationSystem.IsCubic)
    (decomposition :
      GoertzelV24ConnectedBranchDecompositionAdapter.RootedBranchDecomposition
        (G := G)) :
    (GoertzelV24ForkFold.fold data.toRotationSystem.endpoints
      (GoertzelV24ForkFold.wholeTree decomposition)).Nonempty ↔
        RotationSystemTaitColorable data.toRotationSystem :=
  fold_root_nonempty_iff_taitColorable data.toRotationSystem hCubic
    (GoertzelV24ForkFold.wholeTree decomposition)
    (GoertzelV24ForkFold.wholeTree_nodup decomposition)
    (GoertzelV24ForkFold.wholeTree_cover decomposition)

end GraphBacked

end GoertzelV24ForkTaitBridge
end Mettapedia.GraphTheory.FourColor
