import Mettapedia.GraphTheory.FourColor.HexagonalTubeAssembly
import Mettapedia.GraphTheory.FourColor.HexagonalTubeExclusion
import Mettapedia.GraphTheory.FourColor.SlabExterior
import Mettapedia.GraphTheory.FourColor.OpenTangleClosedWitness
import Mettapedia.GraphTheory.FourColor.ZigzagTubeFiniteNormalization

/-!
# Four-ring reduction of recognized five-port hexagonal strips

Hexagonal seam geometry supplies the literal tube embedding. Exact exterior
sewing then permits the four-ring normal form in the original map's class.
The result reconstructs a genuine ambient colouring and preserves every
exterior edge colour. Suitable row supply remains a separate obligation.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24OpenTangleComposition SerialTangleSmallCutTransfer
open GoertzelV24TwoEdgeCutMinimality GoertzelV24VertexSideReassembly
open ZigzagRing TubeSlab

noncomputable section
universe u
attribute [local instance] Classical.propDecidable tubeVertexFintype tubeInteriorFintype
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {RS : RotationSystem.{u, u, u} V E} {inner : V → Prop} {n : ℕ}

namespace TubeSlab.SlabOf

variable (S : SlabOf RS (tube 5 n).data inner)

/-- Replace the strip by four literal rings in its original exterior. -/
abbrev fiveShortened := S.exterior.composeRotationSystem (asOpen (tube 5 3).data)
  S.outsideBoundaryEquiv.symm

/-- Each eliminated ring removes exactly ten original vertices. -/
theorem five_vertex_loss (hn : 3 ≤ n) :
    Fintype.card V = Fintype.card ({v : V // S.outsideKeep v} ⊕ (tube 5 3).V) +
      10 * (n - 3) := by
  have old := tube_vertex_card 5 n
  have short := tube_vertex_card 5 3
  simp only [Nat.card_eq_fintype_card] at old short
  rw [← Fintype.card_congr S.exteriorVertexEquiv, Fintype.card_sum, Fintype.card_sum,
    old, short]
  omega

/-- A strict physical reduction, independent of the classical catalogue. -/
theorem five_reduction (hn : 4 ≤ n) (hS : S.RotationCompatible)
    (h : BridgelessSphericalCubicMapData RS) :
    Fintype.card ({v : V // S.outsideKeep v} ⊕ (tube 5 3).V) < Fintype.card V ∧
      BridgelessSphericalCubicMapData S.fiveShortened ∧
      (RotationSystemTaitColorable RS ↔ RotationSystemTaitColorable S.fiveShortened) := by
  refine ⟨?_, tube_replacement_class 5 (by omega) n 3 S.exterior
    S.outsideBoundaryEquiv.symm (S.reassembled_class hS h), ?_⟩
  · have smaller : Nat.card (tube 5 3).V < Nat.card (tube 5 n).V := by
      rw [tube_vertex_card, tube_vertex_card]
      omega
    rw [← Fintype.card_congr S.exteriorVertexEquiv, Fintype.card_sum, Fintype.card_sum]
    exact Nat.add_lt_add_left (by simpa only [Nat.card_eq_fintype_card] using smaller) _
  · exact S.reassembled_colorable_iff.symm.trans
      (OpenTangleClosedWitness.colorable_iff S.exterior (tube 5 n).data
        S.outsideBoundaryEquiv.symm (tube 5 3).data
        (five_tube_support n 3 (by omega) (by omega)))

/-- Restore all original strip vertices while leaving every exterior edge
colour untouched. This is a witness theorem, not a counting identity or an
algorithmic Kempe-path claim. -/
theorem five_reconstruct (hn : 3 ≤ n)
    (c : S.fiveShortened.EdgeColoring Color) (hc : S.fiveShortened.IsTaitEdgeColoring c) :
    ∃ result : RS.EdgeColoring Color, RS.IsTaitEdgeColoring result ∧
      ∀ d, result (RS.edgeOf (S.exteriorDart d)) =
        c (S.fiveShortened.edgeOf (composeDartEquiv (.inl d))) := by
  obtain ⟨old, hold, hexterior⟩ := OpenTangleClosedWitness.replace
    S.exterior (tube 5 3).data S.outsideBoundaryEquiv.symm (tube 5 n).data
    (fun x y => (five_tube_support 3 n (by omega) hn x y).mp) c hc
  obtain ⟨result, hresult, hmap⟩ := exists_taitColoring_of_dartEquiv S.reassembled RS
    S.reassemblyDartEquiv S.exteriorVertexEquiv
    S.reassemblyDartEquiv_alpha S.reassemblyDartEquiv_vert old hold
  refine ⟨result, hresult, ?_⟩
  intro d
  have h := hmap (composeDartEquiv (.inl d))
  rw [S.reassemblyDartEquiv_left] at h
  exact h.trans (hexterior d)

end TubeSlab.SlabOf

namespace TubeSlab.Tube

variable {G : SimpleGraph V} [DecidableRel G.Adj]
local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- A least counterexample contains at most four rows in any recognized
oriented five-port hexagonal strip. Complete slab boundaries and geometric
seams suffice; no extra connected-shore hypothesis or common origin is used. -/
theorem hexagonal_five_length_le_four (rotation : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {inner : V → Prop} {n : ℕ} (t : Tube rotation.toRotationSystem 5 inner n)
    (ht : t.Hexagonal) : n ≤ 4 := by
  by_contra hlong
  cases t with
  | nil => omega
  | @cons inner R n rest =>
    obtain ⟨S, hS, _, _, _⟩ := literalSlab (.cons R rest) ht
    obtain ⟨hcard, hclass, hcolor⟩ := S.five_reduction (by omega) hS
      minimal.toBridgelessSphericalCubicMapData
    exact minimal.notColorable (hcolor.mpr (minimal.smallerColorable S.fiveShortened hcard hclass))

end TubeSlab.Tube

namespace FacialCycleChord

open InducedCycleLayer FacialCycleLayer
open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open GoertzelV24PrimalCycleFacialBond PhysicalForkCodeFaces

variable {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]
  {C : Frame G 5} {hk : 2 ≤ (5 : ℕ)} {hG : G.IsRegularOfDegree 3}
  {data : SimpleGraphDartRotation.Data G} {R : Finset (OrbitFace (data.toRotationSystem))}
  (h : BoundsFaces C hk hG data R) (ha : AlternatingDegrees C data R)
  (hs : ∀ v, ((data.toRotationSystem).faceOrbit (C.star hk hG v 0)).card = 5 ∨
    ((data.toRotationSystem).faceOrbit (C.star hk hG v 0)).card = 6)
  (ambient : BridgelessSphericalCubicMapData (data.toRotationSystem))
  (hR : ((orbitFaceDualGraph data).induce (R : Set _)).Connected)
  (hRc : ((orbitFaceDualGraph data).induce (R : Set _)ᶜ).Connected)

/-- The actual facial-row recognizer feeds the four-ring reduction directly. -/
theorem chain_length_le_four
    (minimal : GraphBackedVertexMinimalTaitCounterexample data) {n : ℕ}
    (rest : Tube (data.toRotationSystem) 5 (toSlab h ha hs ambient hR hRc).inner' n)
    (hrest : rest.Hexagonal)
    (hseam : match rest with
      | .nil _ e => e = (toSlab h ha hs ambient hR hRc).outEquiv
      | .cons _ _ => (toSlab h ha hs ambient hR hRc).HexagonalSeam) :
    n + 1 ≤ 4 := by
  apply Tube.hexagonal_five_length_le_four data minimal
    (.cons (toSlab h ha hs ambient hR hRc) rest)
  cases rest <;> exact prepend_hexagonal h ha hs ambient hR hRc _ hrest hseam

end FacialCycleChord
end
end Mettapedia.GraphTheory.FourColor
