import Mettapedia.GraphTheory.FourColor.ZigzagTubeTwistReduction
import Mettapedia.GraphTheory.FourColor.HexagonalCollarProgress

/-!
# Strict reduction of any three-row hexagonal tube

The actual row recognizer and seam geometry produce the literal tube and
its genuine exterior. Removing two rows and cyclically shifting one seam
preserves the source map class and reconstructs every smaller colouring.
Consequently a least counterexample has at most two rows at any width at
least two. In the all-five/six face class a supplied row meets a pentagonal
seam after at most one successful extension.

Initial-row supply and reduction of the pentagonal stop remain separate.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24OpenTangleComposition SerialTangleSmallCutTransfer
open GoertzelV24TwoEdgeCutMinimality GoertzelV24VertexSideReassembly
open ZigzagRing TubeSlab PhysicalForkCodeFaces

noncomputable section
universe u
attribute [local instance] Classical.propDecidable tubeVertexFintype tubeInteriorFintype
set_option backward.isDefEq.respectTransparency false
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {RS : RotationSystem.{u, u, u} V E} {inner : V → Prop} {k n : ℕ} [NeZero k]

namespace TubeSlab.SlabOf
variable (S : SlabOf RS (tube k (n + 2)).data inner)

abbrev twistShortened := S.exterior.composeRotationSystem (asOpen (twistedTube k n))
  S.outsideBoundaryEquiv.symm

theorem twist_vertex_loss :
    Fintype.card V = Fintype.card ({v : V // S.outsideKeep v} ⊕ (tube k n).V) + 4 * k := by
  rw [← Fintype.card_congr S.exteriorVertexEquiv]
  exact twistedTube_vertex_loss k n

/-- The original geometric class is retained; exactly `4k` vertices disappear. -/
theorem twist_reduction (hk : 2 ≤ k) (hS : S.RotationCompatible)
    (h : BridgelessSphericalCubicMapData RS) :
    Fintype.card ({v : V // S.outsideKeep v} ⊕ (tube k n).V) < Fintype.card V ∧
      BridgelessSphericalCubicMapData S.twistShortened ∧
      (RotationSystemTaitColorable S.twistShortened → RotationSystemTaitColorable RS) := by
  obtain ⟨hcard, hclass, hcolour⟩ := strict_twistedTube_reduction k S.exterior
    S.outsideBoundaryEquiv.symm hk n (S.reassembled_class hS h)
  refine ⟨?_, hclass, fun hc => S.reassembled_colorable_iff.mp (hcolour hc)⟩
  rwa [Fintype.card_congr S.exteriorVertexEquiv] at hcard

/-- The witness transport preserves every actual exterior edge colour. -/
theorem twist_reconstruct (c : S.twistShortened.EdgeColoring Color)
    (hc : S.twistShortened.IsTaitEdgeColoring c) :
    ∃ result : RS.EdgeColoring Color, RS.IsTaitEdgeColoring result ∧
      ∀ d, result (RS.edgeOf (S.exteriorDart d)) =
        c (S.twistShortened.edgeOf (composeDartEquiv (.inl d))) := by
  obtain ⟨old, hold, hexterior⟩ := twistedTube_closed_reconstruct k S.exterior
    S.outsideBoundaryEquiv.symm n c hc
  obtain ⟨result, hresult, hmap⟩ := exists_taitColoring_of_dartEquiv S.reassembled RS
    S.reassemblyDartEquiv S.exteriorVertexEquiv S.reassemblyDartEquiv_alpha
    S.reassemblyDartEquiv_vert old hold
  refine ⟨result, hresult, ?_⟩
  intro d
  have h := hmap (composeDartEquiv (.inl d))
  rw [S.reassemblyDartEquiv_left] at h
  exact h.trans (hexterior d)

end TubeSlab.SlabOf

variable {G : SimpleGraph V} [DecidableRel G.Adj]
local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

namespace TubeSlab.Tube

/-- Width is unrestricted beyond the two-port minimum. The reduction changes
the right seam matching, rather than equating the two ordered supports. -/
theorem hexagonal_length_le_two (hk : 2 ≤ k) (rotation : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {inner : V → Prop} {n : ℕ} (t : Tube rotation.toRotationSystem k inner n)
    (ht : t.Hexagonal) : n ≤ 2 := by
  by_contra hlong
  cases t with
  | nil => omega
  | @cons inner R n rest =>
    obtain ⟨s, rfl⟩ : ∃ s, n = s + 2 := ⟨n - 2, by omega⟩
    obtain ⟨S, hS, _, _, _⟩ := literalSlab (.cons R rest) ht
    obtain ⟨hcard, hclass, hcolour⟩ := S.twist_reduction hk hS
      minimal.toBridgelessSphericalCubicMapData
    exact minimal.notColorable (hcolour (minimal.smallerColorable S.twistShortened hcard hclass))

end TubeSlab.Tube

namespace TubeSlab.ZigzagSlab

/-- A wider row cannot avoid the pentagonal stopping problem merely by
growing a long constant-width hexagonal corridor. -/
theorem pentagonWithin_one (hk : 2 ≤ k) (rotation : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (faces : ∀ d : rotation.toRotationSystem.D,
      (rotation.toRotationSystem.faceOrbit d).card = 5 ∨
      (rotation.toRotationSystem.faceOrbit d).card = 6)
    {inner : V → Prop} (S : ZigzagSlab rotation.toRotationSystem k inner)
    (hS : S.RotationCompatible) :
    PentagonWithin (cubic3_of _ minimal.spherical.cubic minimal.vertexRotationCyclic)
      faces S hS 1 := by
  apply (S.stopsWithin_iff_pentagonWithin
    (cubic3_of _ minimal.spherical.cubic minimal.vertexRotationCyclic) faces hS 1).mp
  by_contra h
  obtain ⟨t, ht⟩ := S.tube_of_not_stops
    (cubic3_of _ minimal.spherical.cubic minimal.vertexRotationCyclic) faces hS 1 h
  have := t.hexagonal_length_le_two hk rotation minimal ht
  omega

end TubeSlab.ZigzagSlab
end
end Mettapedia.GraphTheory.FourColor
