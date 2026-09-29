import Mettapedia.GraphTheory.FourColor.HexagonalTubeChain
import Mettapedia.GraphTheory.FourColor.GoertzelV24FiveTubeExclusion
import Mettapedia.GraphTheory.FourColor.FacialCycleChord

/-!
# Physical tube exclusion with seam alignment derived from geometry

The existing strict shore-splice argument now accepts oriented slab chains
whose intervening faces are hexagons. Their boundary origins need not agree:
alignment and stationary supports are proved from the actual face geometry.
The facial-row adapter derives the required rotation property from retained
degrees and face incidences, rather than assuming it for the recognized row.

The endpoint remains conditional on finding these rows and on the stated
inner/outer shore hypotheses. It does not assert their universal supply.
-/

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraphDartRotation GoertzelV24TwoEdgeCutMinimality
open GoertzelV24MajorityShoreStateDescent GoertzelV24ConnectedEdgeShoreMajority
open TubeSlab TubeRingOrbit

noncomputable section

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

namespace TubeSlab.Tube

variable (rotation : Data G) {k : ℕ} [NeZero k]

/-- The geometric chain supplies the same finite-state bound as a chain
with an assumed common port labelling. Strict descent is the existing
literal shore splice inside the graph-backed minimal-counterexample class. -/
theorem le_of_hexagonal
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hk : stabilizes k = true) (hk2 : 2 ≤ k) {inner : V → Prop} {n : ℕ}
    (t : Tube rotation.toRotationSystem k inner n) (ht : t.Hexagonal)
    (hgood : GoodSide (G := G) inner)
    (hinside : EdgeShoreConnected G (sideShore inner))
    (houtside : EdgeShoreConnected G (ZigzagSlab.compShore (t.side n))) :
    n + 2 - k ≤ Nat.factorial k * (Nat.factorial k * (6 * k + 1)) := by
  let nodes : Fin (n + 1) → LiteralShoreNode rotation k k := fun r =>
    mkNode ⟨t.goodSide_side hgood r (by omega), t.conn_side hgood hinside r (by omega),
      t.cconn_side houtside r (by omega)⟩ (t.alignedEquiv r) hk2
  exact le_of_stationary_nodes minimal t.side t.alignedEquiv nodes
    (fun r => mkNode_keep _ _ _)
    (fun r r' hrr' => t.sideShore_ssubset_of_lt r r' hrr' (by omega))
    (fun j hj => t.sideSet_aligned_eq_of_le (ht.cyclicCoherent t) hk j hj)

/-- The checked five-port relation is consumed without any seam-alignment
hypothesis. The deliberately coarse shore-splice bound is unchanged. -/
theorem hexagonal_five_length_bound
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {inner : V → Prop} {n : ℕ}
    (t : Tube rotation.toRotationSystem 5 inner n) (ht : t.Hexagonal)
    (hgood : GoodSide (G := G) inner)
    (hinside : EdgeShoreConnected G (sideShore inner))
    (houtside : EdgeShoreConnected G (ZigzagSlab.compShore (t.side n))) :
    n ≤ 446403 := by
  have h := le_of_hexagonal rotation minimal
    GoertzelV24FiveTubeExclusion.five_ring_stabilizes (by omega) t ht hgood hinside houtside
  norm_num at h
  omega

end TubeSlab.Tube

namespace FacialCycleChord

open InducedCycleLayer FacialCycleLayer ZigzagRing
open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open GoertzelV24PrimalCycleFacialBond PhysicalForkCodeFaces

variable {k : ℕ} [NeZero k] {C : Frame G k} {hk : 2 ≤ k}
  {hG : G.IsRegularOfDegree 3} {data : Data G}
  {R : Finset (OrbitFace (RS data))}
  (h : BoundsFaces C hk hG data R) (ha : AlternatingDegrees C data R)
  (hs : ∀ v, ((RS data).faceOrbit (C.star hk hG v 0)).card = 5 ∨
    ((RS data).faceOrbit (C.star hk hG v 0)).card = 6)
  (ambient : BridgelessSphericalCubicMapData (RS data))
  (hR : ((orbitFaceDualGraph data).induce (R : Set _)).Connected)
  (hRc : ((orbitFaceDualGraph data).induce (R : Set _)ᶜ).Connected)

/-- The facial recognition theorem discharges the new geometric premise
using the original graph's rotations, face incidences and retained degrees. -/
theorem toSlab_rotationCompatible :
    (toSlab h ha hs ambient hR hRc).RotationCompatible :=
  h.embedding_rho
    (cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic) ha

/-- A recognized facial row can be prepended to a geometric chain. Only
actual seam-face sizes (or the terminal choice of boundary origin) remain. -/
theorem prepend_hexagonal {n : ℕ}
    (rest : Tube (RS data) k (toSlab h ha hs ambient hR hRc).inner' n)
    (hrest : rest.Hexagonal)
    (hseam : match rest with
      | .nil _ e => e = (toSlab h ha hs ambient hR hRc).outEquiv
      | .cons _ _ => (toSlab h ha hs ambient hR hRc).HexagonalSeam) :
    (Tube.cons (toSlab h ha hs ambient hR hRc) rest).Hexagonal := by
  cases rest <;>
    exact ⟨toSlab_rotationCompatible h ha hs ambient hR hRc, hseam, hrest⟩

/-- Facial recognition, seam alignment, colouring support and the strict
shore splice meet in one original-graph consumer. -/
theorem chain_length_bound
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (hstable : stabilizes k = true) {n : ℕ}
    (rest : Tube (RS data) k (toSlab h ha hs ambient hR hRc).inner' n)
    (hrest : rest.Hexagonal)
    (hseam : match rest with
      | .nil _ e => e = (toSlab h ha hs ambient hR hRc).outEquiv
      | .cons _ _ => (toSlab h ha hs ambient hR hRc).HexagonalSeam)
    (hgood : GoodSide (G := G) (Interior data R))
    (hinside : EdgeShoreConnected G (sideShore (Interior data R)))
    (houtside : EdgeShoreConnected G (TubeSlab.ZigzagSlab.compShore (rest.side n))) :
    n + 3 - k ≤ Nat.factorial k * (Nat.factorial k * (6 * k + 1)) := by
  exact Tube.le_of_hexagonal data minimal hstable hk
    (.cons (toSlab h ha hs ambient hR hRc) rest)
    (prepend_hexagonal h ha hs ambient hR hRc rest hrest hseam) hgood hinside houtside

end FacialCycleChord
end
end Mettapedia.GraphTheory.FourColor
