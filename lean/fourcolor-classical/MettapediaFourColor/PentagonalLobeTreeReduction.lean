import MettapediaFourColor.PentagonalLobeTreeGeometry
import MettapediaFourColor.PentagonalLobePhysicalRepair
import Mettapedia.GraphTheory.FourColor.OpenTangleCompositionSwap

/-!
# A strict tree reduction with colouring reconstruction

Replace the sixteen-vertex patch by its four-vertex six-port tree. The
whole map remains connected, bridgeless, spherical and cubic when its
exterior is connected. A colouring of the smaller map supplies a genuine
exterior assignment. Physical noncrossing then lets joint Kempe repair
reconstruct a colouring of the original map.

Physical noncrossing is an explicit hypothesis. Recognizing this sewing
inside a target map, deriving its ordered exterior geometry and proving
coverage are separate obligations.
-/

namespace FourColor.PentagonalLobePatch.Tangle

open Mettapedia.GraphTheory.FourColor
open GoertzelV24OpenTangleComposition SerialTangleSmallCutTransfer
open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTangleCutParity GoertzelV24PhysicalKempeNoncrossingClosure
open GoertzelV24HexagonPairingTargetAwareBoundary GoertzelV24TwoEdgeCutMinimality
open GoertzelV24CompositeSeamMultigraph

noncomputable section
universe u
variable {W J L R : Type u}
  [Fintype W] [DecidableEq W] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
  (outside : TwoSidedOpenTangleData W J L R) (seam : Fin 6 ≃ L ⊕ R)

/-- The exterior's cubicity is inherited from the actual source map. -/
theorem exterior_cubic_of_sewn
    (h : BridgelessSphericalCubicMapData (OpenTangleClosedWitness.sewn piece outside seam)) :
    IsCubic (exteriorTangle outside) := by
  have hs := OpenTangleCompositionSwap.mapClass piece (asOpen outside) seam h
  exact isCubic_ofOpenTangleData (asOpen outside)
    (OpenTangleVertexReflection.exterior_isCubic (asOpen outside) piece seam.symm
      hs.spherical.cubic)

/-- The four-vertex replacement has exactly the geometry required by
vertex minimality; the change of displayed side is an exact dart transport. -/
theorem sewn_tree_class
    (hout : (sideMultigraph (asOpen outside)).Connected)
    (h : BridgelessSphericalCubicMapData (OpenTangleClosedWitness.sewn piece outside seam)) :
    BridgelessSphericalCubicMapData (OpenTangleClosedWitness.sewn Tree.piece outside seam) := by
  have hs := OpenTangleCompositionSwap.mapClass piece (asOpen outside) seam h
  have ht := tree_replacement_class (asOpen outside) seam.symm hout hs
  exact OpenTangleCompositionSwap.mapClass (asOpen outside) Tree.piece seam.symm ht

variable (h : BridgelessSphericalCubicMapData
  (OpenTangleClosedWitness.sewn piece outside seam))
  (hnoncrossing : ∀ (c : PortTangle.Coloring (exteriorTangle outside)) (hc : IsProper c)
    (pair : TaitColorPair),
    IsNoncrossingMatching (orderedPhysicalMate seam (exteriorTangle outside)
      (exterior_cubic_of_sewn outside seam h) c hc pair))

include h hnoncrossing

/-- Restriction of a smaller-map colouring and joint repair reconstruct
actual edge colours. The exterior assignment may change during repair. -/
theorem reconstruct_from_tree
    (hc : RotationSystemTaitColorable (OpenTangleClosedWitness.sewn Tree.piece outside seam)) :
    RotationSystemTaitColorable (OpenTangleClosedWitness.sewn piece outside seam) := by
  obtain ⟨c, hc⟩ := hc
  obtain ⟨_, r, _, hr, _, _⟩ := OpenTangleClosedWitness.restrict Tree.piece outside seam c hc
  exact sewn_colorable_of_physical_noncrossing outside seam
    (exterior_cubic_of_sewn outside seam h) hnoncrossing r hr

/-- One contextual operation includes all new vertices in its strict size
decrease, preserves the source class and supplies colouring reconstruction. -/
theorem strict_tree_reduction (hout : (sideMultigraph (asOpen outside)).Connected) :
    Fintype.card (Fin 4 ⊕ W) + 12 = Fintype.card (Fin 16 ⊕ W) ∧
      Fintype.card (Fin 4 ⊕ W) < Fintype.card (Fin 16 ⊕ W) ∧
      BridgelessSphericalCubicMapData (OpenTangleClosedWitness.sewn Tree.piece outside seam) ∧
      (RotationSystemTaitColorable (OpenTangleClosedWitness.sewn Tree.piece outside seam) →
        RotationSystemTaitColorable (OpenTangleClosedWitness.sewn piece outside seam)) := by
  refine ⟨by simp [Fintype.card_sum]; omega,
    by simp [Fintype.card_sum], sewn_tree_class outside seam hout h,
    reconstruct_from_tree outside seam h hnoncrossing⟩

/-- Vertex minimality supplies the smaller colouring; no global Four Colour
theorem or catalogue reducibility result is used. -/
theorem colorable_of_smallerColorable
    (hout : (sideMultigraph (asOpen outside)).Connected)
    (hminimal : ∀ {V' E' : Type u} [Fintype V'] [DecidableEq V']
      [Fintype E'] [DecidableEq E'] (candidate : RotationSystem.{u, u, u} V' E'),
      Fintype.card V' < Fintype.card (Fin 16 ⊕ W) →
      BridgelessSphericalCubicMapData candidate → RotationSystemTaitColorable candidate) :
    RotationSystemTaitColorable (OpenTangleClosedWitness.sewn piece outside seam) := by
  obtain ⟨_, hlt, ht, hr⟩ := strict_tree_reduction outside seam h hnoncrossing hout
  exact hr (hminimal (OpenTangleClosedWitness.sewn Tree.piece outside seam) hlt ht)

end
end FourColor.PentagonalLobePatch.Tangle
