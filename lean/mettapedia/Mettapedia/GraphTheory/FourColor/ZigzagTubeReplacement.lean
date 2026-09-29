import Mettapedia.GraphTheory.FourColor.ZigzagTubeStructural
import Mettapedia.GraphTheory.FourColor.OpenTanglePortReplacement
import Mettapedia.GraphTheory.FourColor.ZigzagTubeVertexGeometry
import Mettapedia.GraphTheory.FourColor.OpenTangleVertexReflection
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality
import Mettapedia.GraphTheory.FourColor.OpenTangleClosedBoundary

/-!
# Literal tubes in arbitrary closed sewing contexts

The same ordered face return and open Euler mass give equal Euler
characteristics after sewing to a fixed exterior. All exterior cofaciality
is retained. Connectivity and bridges are handled independently by the
small-cut theorem for the actual tube interiors.
-/

namespace Mettapedia.GraphTheory.FourColor.ZigzagRing

open GoertzelV24OpenTangleComposition SerialTangleSmallCutTransfer
open OpenTanglePortReplacement OpenTangleReplacementEuler OpenTangleRewireFaces
open GoertzelV24CompositeSeamCubic OpenTangleVertexReflection
open GoertzelV24TwoEdgeCutMinimality

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] tubeVertexFintype tubeInteriorFintype

variable (k : Nat) [NeZero k]

theorem tube_returnCode (n : Nat) : returnCode (asOpen (tube k n).data) = boundaryPerm k :=
  (returnCode_asOpen _).trans (tube_face_code k n)

section Geometry
variable {V I B : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  [Fintype B] [DecidableEq B]

/-- Equal Euler characteristics of the actual closed rotation systems,
without any planar or connected-exterior assumption. -/
theorem tube_replacement_euler (r s : Nat) (outside : OpenTangleData V I B)
    (m : B ≃ Fin k ⊕ Fin k) :
    compositeEuler outside (asOpen (tube k r).data) m =
      compositeEuler outside (asOpen (tube k s).data) m := by
  apply (OpenTanglePortReplacement.euler_eq_iff_mass
    (asOpen (tube k r).data) (asOpen (tube k s).data)
    ((tube_returnCode k r).trans (tube_returnCode k s).symm) outside m).mpr
  exact (tube_eulerMass k r).trans (tube_eulerMass k s).symm

/-- Exterior darts keep exactly the same face-incidence relation. -/
theorem tube_replacement_exterior_faces (r s : Nat) (outside : OpenTangleData V I B)
    (m : B ≃ Fin k ⊕ Fin k) (a b : I ⊕ B) :
    (outside.composeRotationSystem (asOpen (tube k r).data) m).phi.SameCycle
        (composeDartEquiv (.inl a)) (composeDartEquiv (.inl b)) ↔
      (outside.composeRotationSystem (asOpen (tube k s).data) m).phi.SameCycle
        (composeDartEquiv (.inl a)) (composeDartEquiv (.inl b)) :=
  exterior_sameCycle_iff (asOpen (tube k r).data) (asOpen (tube k s).data)
    ((tube_returnCode k r).trans (tube_returnCode k s).symm) outside m a b

/-- Full preservation of the source's connected bridgeless spherical cubic
map class. Exterior cubicity and cyclicity are recovered from the input
map, so no separate geometric assumptions about the exterior are needed. -/
theorem tube_replacement_class (hk : 2 ≤ k) (r s : Nat) (outside : OpenTangleData V I B)
    (m : B ≃ Fin k ⊕ Fin k)
    (h : BridgelessSphericalCubicMapData
      (outside.composeRotationSystem (asOpen (tube k r).data) m)) :
    BridgelessSphericalCubicMapData
      (outside.composeRotationSystem (asOpen (tube k s).data) m) where
  spherical := {
    cubic := isCubic_composeRotationSystem outside (asOpen (tube k s).data) m
      (exterior_isCubic outside (asOpen (tube k r).data) m h.spherical.cubic)
      (tube_isCubic k s)
    euler := by
      change compositeEuler outside (asOpen (tube k s).data) m = 2
      rw [← tube_replacement_euler k r s outside m]
      exact h.spherical.euler }
  primalConnected := ((tube_replacement_structural k hk r s outside m).mp
    ⟨h.primalConnected, h.edgeBridgeFree⟩).1
  vertexRotationCyclic := vertexRotationCyclic_composeRotationSystem outside
    (asOpen (tube k s).data) m
    (exterior_rotationCyclic outside (asOpen (tube k r).data) m h.vertexRotationCyclic)
    (tube_rotationCyclic k s)
  edgeBridgeFree := ((tube_replacement_structural k hk r s outside m).mp
    ⟨h.primalConnected, h.edgeBridgeFree⟩).2

end Geometry

variable {V I B : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  [Fintype B] [DecidableEq B]

/-- The stable ordered support gives equivalence of actual Tait-colourability
in every fixed closed exterior, with no restrictions on its topology. -/
theorem tube_replacement_colorable (hk : 3 ≤ k) (r s : Nat)
    (hr : compressionBound k ≤ r + 1) (hs : compressionBound k ≤ s + 1)
    (outside : OpenTangleData V I B) (m : B ≃ Fin k ⊕ Fin k) :
    RotationSystemTaitColorable (outside.composeRotationSystem (asOpen (tube k r).data) m) ↔
      RotationSystemTaitColorable (outside.composeRotationSystem (asOpen (tube k s).data) m) :=
  OpenTangleClosedBoundary.compose_colorable_iff (tube k r).data (tube k s).data
    (fun x y => tube_support_eq k hk x y hr hs) outside m

variable (hk : 3 ≤ k) (r s : Nat)
  (hr : compressionBound k ≤ r + 1) (hs : compressionBound k ≤ s + 1)
  (outside : OpenTangleData V I B) (m : B ≃ Fin k ⊕ Fin k)
  (c : (outside.composeRotationSystem (asOpen (tube k r).data) m).EdgeColoring Color)
  (hc : (outside.composeRotationSystem (asOpen (tube k r).data) m).IsTaitEdgeColoring c)

/-- Change the length by replacing an inner witness of the same seam word,
retaining the given exterior colouring throughout the construction. -/
def replaceTubeEdgeColoring :
    (outside.composeRotationSystem (asOpen (tube k s).data) m).EdgeColoring Color :=
  OpenTangleClosedBoundary.replaceEdgeColoring (tube k r).data (tube k s).data
    (fun x y => (tube_support_eq k hk x y hr hs).mp) outside m c hc

theorem replaceTubeEdgeColoring_isTait :
    (outside.composeRotationSystem (asOpen (tube k s).data) m).IsTaitEdgeColoring
      (replaceTubeEdgeColoring k hk r s hr hs outside m c hc) :=
  OpenTangleClosedBoundary.replaceEdgeColoring_isTait (tube k r).data (tube k s).data
    (fun x y => (tube_support_eq k hk x y hr hs).mp) outside m c hc

theorem replaceTubeEdgeColoring_exterior (d : I ⊕ B) :
    replaceTubeEdgeColoring k hk r s hr hs outside m c hc
        ((GoertzelV24CompositeSeamMultigraph.compositeDarts outside (asOpen (tube k s).data) m).edgeOf
          (composeDartEquiv (.inl d))) =
      c ((GoertzelV24CompositeSeamMultigraph.compositeDarts outside (asOpen (tube k r).data) m).edgeOf
        (composeDartEquiv (.inl d))) :=
  OpenTangleClosedBoundary.replaceEdgeColoring_exterior (tube k r).data (tube k s).data
    (fun x y => (tube_support_eq k hk x y hr hs).mp) outside m c hc d

/-- A long physical tube admits a strictly smaller map in the same source
class, with equivalent Tait-colourability. The exterior and seam matching
are unchanged; only the number of tube rings decreases. -/
theorem strict_tube_reduction (hk : 3 ≤ k) (n : Nat) (hn : compressionBound k ≤ n)
    (outside : OpenTangleData V I B) (m : B ≃ Fin k ⊕ Fin k)
    (h : BridgelessSphericalCubicMapData
      (outside.composeRotationSystem (asOpen (tube k n).data) m)) :
    Fintype.card (V ⊕ (tube k (compressionBound k - 1)).V) <
        Fintype.card (V ⊕ (tube k n).V) ∧
      BridgelessSphericalCubicMapData
        (outside.composeRotationSystem (asOpen (tube k (compressionBound k - 1)).data) m) ∧
      (RotationSystemTaitColorable (outside.composeRotationSystem (asOpen (tube k n).data) m) ↔
        RotationSystemTaitColorable
          (outside.composeRotationSystem (asOpen (tube k (compressionBound k - 1)).data) m)) := by
  have hb : 0 < compressionBound k := by
    unfold compressionBound
    exact Nat.mul_pos (by decide) (Nat.mul_pos (by omega) (by omega))
  refine ⟨?_, tube_replacement_class k (by omega) n _ outside m h,
    tube_replacement_colorable k hk n _ (by omega) (by omega) outside m⟩
  have hs := (strict_tube_shortening k hk n hn).1
  simpa only [Fintype.card_sum, Nat.add_lt_add_iff_left, Nat.card_eq_fintype_card] using hs

end
end Mettapedia.GraphTheory.FourColor.ZigzagRing
