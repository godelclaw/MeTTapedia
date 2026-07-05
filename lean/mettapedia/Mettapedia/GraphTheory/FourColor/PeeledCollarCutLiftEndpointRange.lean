import Mettapedia.GraphTheory.FourColor.PeeledCollarCutLiftPreimage

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V W : Type*}

namespace SimpleGraph.Embedding

/--
If both endpoints of an ambient edge lie in the range of a graph embedding,
then the ambient edge has a source-edge preimage.
-/
theorem edge_preimage_of_forall_mem_range
    {H : SimpleGraph W} {G : SimpleGraph V} (φ : H ↪g G)
    {e : G.edgeSet}
    (hrange : ∀ v : V, v ∈ (e : Sym2 V) → ∃ w : W, φ w = v) :
    ∃ eH : H.edgeSet, φ.mapEdgeSet eH = e := by
  let x : V := (e : Sym2 V).out.1
  let y : V := (e : Sym2 V).out.2
  have hxmem : x ∈ (e : Sym2 V) := by
    dsimp [x]
    exact Sym2.out_fst_mem (e : Sym2 V)
  have hymem : y ∈ (e : Sym2 V) := by
    dsimp [y]
    exact Sym2.out_snd_mem (e : Sym2 V)
  rcases hrange x hxmem with ⟨xH, hxH⟩
  rcases hrange y hymem with ⟨yH, hyH⟩
  have hAdjG : G.Adj x y := by
    rw [← SimpleGraph.mem_edgeSet]
    convert e.property using 1
    simp [x, y, Sym2.mk, Quot.out_eq]
  have hAdjH : H.Adj xH yH := by
    rw [← φ.map_adj_iff]
    simpa [hxH, hyH] using hAdjG
  refine ⟨⟨s(xH, yH), by simpa [SimpleGraph.mem_edgeSet] using hAdjH⟩, ?_⟩
  apply Subtype.ext
  simp [SimpleGraph.Embedding.mapEdgeSet, SimpleGraph.Hom.mapEdgeSet,
    hxH, hyH, x, y, Sym2.mk, Quot.out_eq]

end SimpleGraph.Embedding

/--
Endpoint-range datum for lifting one peeled-collar cut.  The ambient side
agrees with the collar side on embedded vertices, and every endpoint of every
ambient side-crossing edge lies in the embedded collar vertex range.

The general embedding lemma then turns endpoint range into a source-edge
preimage, so this is the graph-facing target expected from a planar annulus
boundary theorem.
-/
structure PeeledCollarCutAmbientSideEndpointRange
    {H : SimpleGraph W} {G : SimpleGraph V}
    (φ : H ↪g G) (cut : SmallCyclicEdgeCut H) where
  side : V → Prop
  side_comp_embedding : ∀ w, side (φ w) ↔ cut.side w
  crossingEdge_endpointRange :
    ∀ e : G.edgeSet,
      EdgeCrossesVertexSide G side e →
        ∀ v : V, v ∈ (e : Sym2 V) → ∃ w : W, φ w = v

namespace PeeledCollarCutAmbientSideEndpointRange

/-- Endpoint-range data give preimage data. -/
def toAmbientSidePreimage
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (endpointRange : PeeledCollarCutAmbientSideEndpointRange φ cut) :
    PeeledCollarCutAmbientSidePreimage φ cut where
  side := endpointRange.side
  side_comp_embedding := endpointRange.side_comp_embedding
  crossingEdge_preimage := by
    intro e hcross
    exact SimpleGraph.Embedding.edge_preimage_of_forall_mem_range φ
      (endpointRange.crossingEdge_endpointRange e hcross)

/-- Endpoint-range data give edge-barrier data. -/
def toAmbientSideBarrier
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (endpointRange : PeeledCollarCutAmbientSideEndpointRange φ cut) :
    PeeledCollarCutAmbientSideBarrier φ cut :=
  endpointRange.toAmbientSidePreimage.toAmbientSideBarrier

/-- Endpoint-range data give the no-avoiding-walk separation datum. -/
def toAmbientSideSeparation
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (endpointRange : PeeledCollarCutAmbientSideEndpointRange φ cut) :
    PeeledCollarCutAmbientSideSeparation φ cut :=
  endpointRange.toAmbientSidePreimage.toAmbientSideSeparation

/-- Endpoint-range data give the concrete side-extension datum. -/
def toCutSideExtension
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    {cut : SmallCyclicEdgeCut H}
    (endpointRange : PeeledCollarCutAmbientSideEndpointRange φ cut) :
    PeeledCollarCutSideExtension φ cut :=
  endpointRange.toAmbientSidePreimage.toCutSideExtension

end PeeledCollarCutAmbientSideEndpointRange

/--
Endpoint-range foundation target: every small cyclic cut in the peeled collar
has an ambient side such that every ambient side-crossing edge has all endpoints
in the embedded collar vertex range.
-/
def PeeledCollarCutAmbientSideEndpointRangesToAmbient
    {H : SimpleGraph W} {G : SimpleGraph V} (φ : H ↪g G) : Prop :=
  ∀ cut : SmallCyclicEdgeCut H,
    Nonempty (PeeledCollarCutAmbientSideEndpointRange φ cut)

/-- Endpoint-range data imply preimage data. -/
theorem peeledCollarCutAmbientSidePreimagesToAmbient_of_ambientSideEndpointRanges
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hrange : PeeledCollarCutAmbientSideEndpointRangesToAmbient φ) :
    PeeledCollarCutAmbientSidePreimagesToAmbient φ := by
  intro cut
  rcases hrange cut with ⟨endpointRange⟩
  exact ⟨endpointRange.toAmbientSidePreimage⟩

/-- Endpoint-range data imply edge barriers. -/
theorem peeledCollarCutAmbientSideBarriersToAmbient_of_ambientSideEndpointRanges
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hrange : PeeledCollarCutAmbientSideEndpointRangesToAmbient φ) :
    PeeledCollarCutAmbientSideBarriersToAmbient φ :=
  peeledCollarCutAmbientSideBarriersToAmbient_of_ambientSidePreimages
    (peeledCollarCutAmbientSidePreimagesToAmbient_of_ambientSideEndpointRanges
      hrange)

/-- Endpoint-range data imply no-avoiding-walk side separations. -/
theorem peeledCollarCutAmbientSideSeparationsToAmbient_of_ambientSideEndpointRanges
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hrange : PeeledCollarCutAmbientSideEndpointRangesToAmbient φ) :
    PeeledCollarCutAmbientSideSeparationsToAmbient φ :=
  peeledCollarCutAmbientSideSeparationsToAmbient_of_ambientSidePreimages
    (peeledCollarCutAmbientSidePreimagesToAmbient_of_ambientSideEndpointRanges
      hrange)

/-- Endpoint-range data imply concrete side extensions. -/
theorem peeledCollarCutSideExtensionsToAmbient_of_ambientSideEndpointRanges
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hrange : PeeledCollarCutAmbientSideEndpointRangesToAmbient φ) :
    PeeledCollarCutSideExtensionsToAmbient φ :=
  peeledCollarCutSideExtensionsToAmbient_of_ambientSidePreimages
    (peeledCollarCutAmbientSidePreimagesToAmbient_of_ambientSideEndpointRanges
      hrange)

/-- Endpoint-range data imply the graph-facing small-cut lift. -/
theorem peeledCollarSmallCyclicCutLiftsToAmbient_of_ambientSideEndpointRanges
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (hrange : PeeledCollarCutAmbientSideEndpointRangesToAmbient φ) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G H :=
  peeledCollarSmallCyclicCutLiftsToAmbient_of_ambientSidePreimages
    (peeledCollarCutAmbientSidePreimagesToAmbient_of_ambientSideEndpointRanges
      hrange)

/-- Regime-facing inheritance theorem from endpoint-range data. -/
theorem peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_ambientSideEndpointRanges
    [DecidableEq V] [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} {φ : H ↪g G}
    (regime : MinimalCounterexamplePeeledCollarRegime G W H)
    (hrange : PeeledCollarCutAmbientSideEndpointRangesToAmbient φ) :
    CyclicallyFiveEdgeConnected H :=
  peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_ambientSidePreimages
    regime
    (peeledCollarCutAmbientSidePreimagesToAmbient_of_ambientSideEndpointRanges
      hrange)

end Mettapedia.GraphTheory.FourColor
