import Mettapedia.GraphTheory.FourColor.GoertzelV24DigonTwoEdgeCut
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutCapGeometry
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutCapBridge
import Mettapedia.GraphTheory.FourColor.GoertzelV24DigonSuppressionColor

/-!
# Digon suppression: the complementary cap and its class

With a digon exhibited as an exact two-edge cut, the suppressed map is the
complementary cap of that cut: delete `u`, `v`, the parallel pair and the two
exterior edges, and join the two exposed half-edges into one edge.  The cap
theorems then deliver, on the literal cap rotation system:

* strictly fewer vertices (two fewer);
* cubic;
* primal-connected, from connectivity of the complement;
* bridge-free, from bridge-freeness of the ambient map;
* cyclic vertex rotations;
* not Tait colourable when the ambient map is not.

Sphericity of the cap is the remaining field and is proved separately, from
the exact digon face.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace RotationSystem

open GoertzelV24RotationEdgeBridge
open GoertzelV24FaceDualConnectedness
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24DigonSuppressionColor

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

noncomputable section

namespace DigonPatchData

variable {RS : RotationSystem V E} (D : @DigonPatchData V E)
  (hD : D.WellFormed RS) (hCubic : RS.IsCubic)
  (hfree : EdgeBridgeFree RS) (houter : D.vFar hD ≠ D.u)

/-- **The suppressed map**: the complementary cap of the digon's two-edge cut. -/
abbrev suppressed :=
  (D.twoEdgeCut hD hCubic hfree houter).complementData.capRotationSystem

/-- Suppression removes exactly the two digon vertices. -/
theorem card_suppressed_vertex :
    Fintype.card (D.twoEdgeCut hD hCubic hfree houter).complementData.CapVertex + 2 =
      Fintype.card V := by
  classical
  have h : Fintype.card (D.twoEdgeCut hD hCubic hfree houter).complementData.CapVertex =
      (D.twoEdgeCut hD hCubic hfree houter).sideᶜ.card := by
    rw [Fintype.card_subtype]
    congr 1
    ext v
    simp [RotationSystem.TwoEdgeCutSideData.keep, RotationSystem.TwoEdgeCutPairData.complementData]
  rw [h, Finset.card_compl]
  change Fintype.card V - (D.side).card + 2 = Fintype.card V
  rw [D.side_card hD]
  have : 2 ≤ Fintype.card V := by
    have := Finset.card_le_univ (D.side)
    rw [D.side_card hD] at this
    exact this
  omega

theorem card_suppressed_vertex_lt :
    Fintype.card (D.twoEdgeCut hD hCubic hfree houter).complementData.CapVertex <
      Fintype.card V :=
  (D.twoEdgeCut hD hCubic hfree houter).card_complementCapVertex_lt

theorem suppressed_isCubic : (D.suppressed hD hCubic hfree houter).IsCubic :=
  (D.twoEdgeCut hD hCubic hfree houter).complementCap_isCubic hCubic

theorem suppressed_primalConnected (hconn : (rotationPrimalGraph RS).Connected) :
    (rotationPrimalGraph (D.suppressed hD hCubic hfree houter)).Connected :=
  GoertzelV24TwoEdgeCutCapGeometry.RotationSystem.TwoEdgeCutPairData.complementCap_primal_connected
    _ (D.complement_connected hD hCubic hfree hconn houter)

theorem suppressed_edgeBridgeFree (hconn : (rotationPrimalGraph RS).Connected) :
    EdgeBridgeFree (D.suppressed hD hCubic hfree houter) :=
  GoertzelV24TwoEdgeCutCapBridge.RotationSystem.TwoEdgeCutPairData.complementCap_edgeBridgeFree
    _ hfree (D.complement_connected hD hCubic hfree hconn houter)

theorem suppressed_vertexRotationCyclic (hcyclic : VertexRotationCyclic RS) :
    VertexRotationCyclic (D.suppressed hD hCubic hfree houter) :=
  GoertzelV24TwoEdgeCutMinimality.RotationSystem.TwoEdgeCutPairData.complementCap_vertexRotationCyclic
    _ hcyclic

/-- **Uncolourability descends to the suppressed map.** -/
theorem not_suppressed_taitColorable (hnot : ¬ RotationSystemTaitColorable RS) :
    ¬ RotationSystemTaitColorable (D.suppressed hD hCubic hfree houter) :=
  GoertzelV24DigonSuppressionColor.RotationSystem.TwoEdgeCutPairData.not_complementCap_taitColorable_of_not_ambient
    _ hCubic (D.side_card hD) hnot

end DigonPatchData

end

end RotationSystem

end Mettapedia.GraphTheory.FourColor
